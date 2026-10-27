module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnExc
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutEntrywise
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Field
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerMore

public section

namespace CFSG.StandardType.UpD42Out

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)

section Bridge


theorem hom_ext_adjointGroup {τ : Tag} {K : Type} [Field K] {M : Type*} [Monoid M]
    {f g : ↥(adjointGroup τ K) →* M}
    (hx : ∀ i c, f (xElement i c) = g (xElement i c))
    (hy : ∀ i c, f (yElement i c) = g (yElement i c)) : f = g := by
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹'
      {g | ∃ (i : Fin τ.rank) (c : K), (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  refine MonoidHom.eq_of_eqOn_dense hcl ?_
  rintro u ⟨i, c, h | h⟩
  · rw [show u = xElement i c from Subtype.ext (Units.ext h)]
    exact hx i c
  · rw [show u = yElement i c from Subtype.ext (Units.ext h)]
    exact hy i c

theorem coe_rootDiagAut_transport {τ : Tag} {K : Type} [Field K]
    (T : ↥(adjointGroup τ K) ≃* ↥(LargeEvenChevGroup τ.cartan K))
    (hTx : ∀ (i : Fin τ.rank) (c : K), ((T (xElement i c) : LargeEvenChevGL τ.cartan K) :
        Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenXOp τ.cartan K i c)
    (hTy : ∀ (i : Fin τ.rank) (c : K), ((T (yElement i c) : LargeEvenChevGL τ.cartan K) :
        Module.End K (LargeEvenChevModule τ.cartan K)) = LargeEvenYOp τ.cartan K i c)
    (a : Fin τ.rank → Kˣ) (g : ↥(adjointGroup τ K)) :
    (T (rootDiagAut τ K a g) : LargeEvenChevGL τ.cartan K) =
      TableB.diagHom τ.cartan K a * (T g : LargeEvenChevGL τ.cartan K) *
        (TableB.diagHom τ.cartan K a)⁻¹ := by
  let F₁ : ↥(adjointGroup τ K) →* LargeEvenChevGL τ.cartan K :=
    (LargeEvenChevGroup τ.cartan K).subtype.comp
      (T.toMonoidHom.comp (rootDiagAut τ K a).toMonoidHom)
  let F₂ : ↥(adjointGroup τ K) →* LargeEvenChevGL τ.cartan K :=
    (MulAut.conj (TableB.diagHom τ.cartan K a)).toMonoidHom.comp
      ((LargeEvenChevGroup τ.cartan K).subtype.comp T.toMonoidHom)
  have hF : F₁ = F₂ := by
    refine hom_ext_adjointGroup (fun i c => ?_) (fun i c => ?_)
    · have h1 : rootDiagAut τ K a (xElement i c) = xElement i ((a i : K) * c) :=
        Subtype.ext ((root_diagonal_conjugation τ K a).1 i c)
      show ((T (rootDiagAut τ K a (xElement i c)) : LargeEvenChevGL τ.cartan K)) =
        TableB.diagHom τ.cartan K a * (T (xElement i c) : LargeEvenChevGL τ.cartan K) *
          (TableB.diagHom τ.cartan K a)⁻¹
      rw [h1]
      apply Units.ext
      rw [hTx, InnerDiagE6.diagHom_conj_xOp τ a (hTx i c)]
    · have h1 : rootDiagAut τ K a (yElement i c) = yElement i ((((a i)⁻¹ : Kˣ) : K) * c) :=
        Subtype.ext ((root_diagonal_conjugation τ K a).2.1 i c)
      show ((T (rootDiagAut τ K a (yElement i c)) : LargeEvenChevGL τ.cartan K)) =
        TableB.diagHom τ.cartan K a * (T (yElement i c) : LargeEvenChevGL τ.cartan K) *
          (TableB.diagHom τ.cartan K a)⁻¹
      rw [h1]
      apply Units.ext
      rw [hTy, InnerDiagE6.diagHom_conj_yOp τ a (hTy i c)]
  exact DFunLike.congr_fun hF g

theorem congr_mem_chevIDImage_of_mem_e6Inndiag {K : Type} [Field K]
    (T : ↥(adjointGroup Tag.E6 K) ≃* ↥(LargeEvenChevGroup Tag.E6.cartan K))
    (hTx : ∀ (i : Fin Tag.E6.rank) (c : K), ((T (xElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) = LargeEvenXOp Tag.E6.cartan K i c)
    (hTy : ∀ (i : Fin Tag.E6.rank) (c : K), ((T (yElement i c) : LargeEvenChevGL Tag.E6.cartan K) :
        Module.End K (LargeEvenChevModule Tag.E6.cartan K)) = LargeEvenYOp Tag.E6.cartan K i c)
    (hZ : Subgroup.center ↥(LargeEvenChevGroup Tag.E6.cartan K) = ⊥)
    {ψ : MulAut ↥(adjointGroup Tag.E6 K)}
    (hψ : ψ ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag K) :
    MulAut.congr (T.trans (centerQuotEquivOfBot hZ).symm) ψ ∈
      LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevGroup Tag.E6.cartan K) := by
  let ε := T.trans (centerQuotEquivOfBot hZ).symm
  let M : Subgroup (MulAut (LargeEvenCenterQuot (LargeEvenChevGroup Tag.E6.cartan K))) :=
    Subgroup.closure (LargeEvenInnSet _ ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevGroup Tag.E6.cartan K))
  have hle : CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag K ≤
      M.comap (MulAut.congr ε).toMonoidHom := by
    refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      refine Subgroup.mem_comap.2 (Subgroup.subset_closure (Or.inl ⟨ε g, ?_⟩))
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    · rintro _ ⟨a, rfl⟩
      obtain ⟨φa, hφaD, hφa⟩ := InnerDiagE6.exists_diagAut hZ a
        (fun _ hh => InnerDiagE6.diagHom_conj_mem .E6 a hh)
        (fun _ hh => InnerDiagE6.diagHom_inv_conj_mem .E6 a hh)
      have heq : MulAut.congr ε (rootDiagAutHom Tag.E6 K a) = φa := by
        ext y
        obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
          (Subgroup.center ↥(LargeEvenChevGroup Tag.E6.cartan K)) y
        show MulAut.congr ε (rootDiagAutHom Tag.E6 K a)
            (LargeEvenCenterMk (LargeEvenChevGroup Tag.E6.cartan K) h) =
          φa (LargeEvenCenterMk (LargeEvenChevGroup Tag.E6.cartan K) h)
        rw [hφa h, MulAut.congr_apply]
        simp only [ε, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
          centerQuotEquivOfBot_mk, centerQuotEquivOfBot_symm]
        congr 1
        apply Subtype.ext
        rw [show rootDiagAutHom Tag.E6 K a = rootDiagAut Tag.E6 K a from rfl,
          coe_rootDiagAut_transport T hTx hTy a, MulEquiv.apply_symm_apply]
      refine Subgroup.mem_comap.2 ?_
      show MulAut.congr ε (rootDiagAutHom Tag.E6 K a) ∈ M
      rw [heq]
      exact Subgroup.subset_closure (Or.inr hφaD)
  exact Subgroup.mem_comap.1 (hle hψ)

theorem rawMarking_of_mem_e6Inndiag {S : Type} [Group S] (hZS : Subgroup.center S = ⊥) {f : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (θ : S ≃* ↥(adjointGroup Tag.E6 K)) {α : MulAut S}
    (hα : MulAut.congr θ α ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag K) :
    LargeEvenRawDatum ⟨.E6, 0, f⟩ fun R _ I _ =>
      ∃ θ' : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ' (fun a b => b = α a) β := by
  obtain ⟨T, hTx, hTy⟩ := InnerDiagE6.exists_largeEvenChevEquiv Tag.E6 (K := K)
  have hZ : Subgroup.center ↥(LargeEvenChevGroup Tag.E6.cartan K) = ⊥ :=
    InnerDiagE6.center_eq_bot_of_mulEquiv (θ.trans T) hZS
  let ε := T.trans (centerQuotEquivOfBot hZ).symm
  let θ' : S ⧸ Subgroup.center S ≃* LargeEvenCenterQuot (LargeEvenChevGroup Tag.E6.cartan K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot).trans (θ.trans ε)
  have hind : LargeEvenInduces θ' (fun a b => b = α a) (MulAut.congr ε (MulAut.congr θ α)) := by
    have hθ' : ∀ a : S, θ' (QuotientGroup.mk a) = ε (θ a) := by
      intro a
      have hq : QuotientGroup.quotientBot
          (QuotientGroup.quotientMulEquivOfEq hZS (QuotientGroup.mk a)) = a := by
        rw [QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.apply_eq_iff_symm_apply,
          QuotientGroup.quotientBot_symm_apply]
      show ε (θ (QuotientGroup.quotientBot
        (QuotientGroup.quotientMulEquivOfEq hZS (QuotientGroup.mk a)))) = ε (θ a)
      rw [hq]
    intro a b hb
    subst hb
    rw [hθ', hθ']
    simp [MulAut.congr_apply]
  have hraw : LargeEvenRecipeChevalley (Tag.cartan .E6) (2 ^ f) false fun R _ I _ =>
      ∃ θ' : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ' (fun a b => b = α a) β :=
    ⟨K, inferInstance, inferInstance, hK, θ', MulAut.congr ε (MulAut.congr θ α),
      congr_mem_chevIDImage_of_mem_e6Inndiag T hTx hTy hZ hα, hind⟩
  exact hraw

end Bridge

end CFSG.StandardType.UpD42Out

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator


theorem upD42Chev2Out_e6 : UpD42Chev2Out (fun d => match d with | .E6 _ => True | _ => False) := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α _ hp
  cases d with
  | E6 q =>
    exfalso
    haveI := hs
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_E6 q hv e
    have hU : UntwistedChevalleyModel S .E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := I923.exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    by_cases hdiag : MulAut.congr θ α ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag F
    · have hZS : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup_noncomm hnab
      obtain ⟨K, hK, hD⟩ := exists_D41_component_of_upD42Pumpup hs hnab ⟨.E6 q, hv⟩ rfl
        (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩ hp
      obtain ⟨n, hn⟩ : ∃ n, q.exponent = n := ⟨_, rfl⟩
      rw [hn] at hFcard
      have hmark := CFSG.StandardType.UpD42Out.rawMarking_of_mem_e6Inndiag hZS hFcard θ hdiag
      have hΛ : CFSG.Assembly.LargeEvenInLambda2 ⟨.E6, 0, n⟩ := ⟨hn ▸ q.exponent_pos, rfl⟩
      have hf : n = 1 := CFSG.StandardType.UpD42Inn.field_eq_one_of_D41_component hs hnab hΛ
        (CFSG.StandardType.UpD42Inn.ggKacRE_three (Or.inl rfl)) hmark hp.1 hK hD
      subst hf
      exact CFSG.StandardType.UpD42Inn.false_of_D41_component_list hs hnab
        CFSG.StandardType.E6TwoThree.ggE6TwoThreeComp_holds
        (by simp [CFSG.Assembly.LargeEvenInLambda2]) hmark hp.1 hp.2.1 hK hD
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two q.exponent_pos hFcard
      obtain ⟨σ, hσo, hpf, δ, hδ⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_entrywise_of_not_mem_e6Inndiag
          Nat.prime_two q.exponent_pos F hFcard Nat.prime_three (by norm_num) hβ3 hdiag
      have hd : 1 ≤ q.exponent / 3 :=
        Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) (by norm_num)
      have hcard : Nat.card (fixSubfield σ) = 2 ^ (q.exponent / 3) := by
        have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
          q.exponent_pos hFcard σ).2
        rwa [hσo] at this
      haveI : Finite ↥(fixSubfield σ) := Subtype.finite
      have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 2
          (q.exponent / 3) :=
        ⟨⟨Nat.prime_two, hd, rfl⟩, I923.untwisted_adjointGroup hcard⟩
      obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 (q.exponent / 3) hM
      haveI := hsimp
      have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
        center_adjointGroup_eq_bot
      have hpump : UpD42Pumpup ↥(adjointGroup Tag.E6 F) (entrywiseAdjointAut Tag.E6 σ) := by
        have h1 := (hp.congr θ).congr δ
        have h2 : MulAut.congr δ (MulAut.congr θ α) = entrywiseAdjointAut Tag.E6 σ := by
          rw [← hδ]
          ext x
          simp [MulAut.congr_apply]
        rwa [h2] at h1
      exact hpump.false_of_entrywise σ (t := .E6) (by decide) (n := 0)
        (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (I923.exists_noncomm_of_center_bot hZ)
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
