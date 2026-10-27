module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Plane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Order
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFivePBig

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration
open scoped Matrix

set_option linter.unusedSectionVars false


theorem localDeltaIn_zpowers_E8_two {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [IsAlgClosure K L] (hK : Nat.card K = 2) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    {d : adjointGroup Tag.E8 K} (hd1 : d ≠ 1)
    (hdT : baseChangeGL (algebraMap K L) (d : ModGL Tag.E8 K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
        (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    {H : Subgroup (MulAut (adjointGroup Tag.E8 K))} (hH : innerAut (adjointGroup Tag.E8 K) ≤ H) :
    localDeltaIn 5 H ((Subgroup.zpowers d).map
      (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K))) = ⊥ := by
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)) :=
    mulAut_conj_injective_adjointGroup
  have hbot := SmallQ5.gLAPPrimeCoreOf_centralizer_eq_bot_E8_five_two hK hFr hg0C hg0 (d := d)
    hd1 hdT
  have hHeq : H ⊓ Subgroup.centralizer {(MulAut.conj d : MulAut (adjointGroup Tag.E8 K))} =
      innerAut (adjointGroup Tag.E8 K) ⊓
        Subgroup.centralizer {(MulAut.conj d : MulAut (adjointGroup Tag.E8 K))} := by
    ext φ
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨mem_innerAut_of_card_two hK (Or.inr rfl) φ, h.2⟩, fun h => ⟨hH h.1, h.2⟩⟩
  refine localDeltaIn_eq_bot_of_core_eq_bot
    (d := (MulAut.conj d : MulAut (adjointGroup Tag.E8 K)))
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers d))
    (fun h => hd1 (hinj (h.trans (map_one _).symm))) ?_
  rw [hHeq, inner_inf_centralizer_conj hinj, gLAPPrimeCoreOf_map_of_injective 5 _ hinj, hbot,
    Subgroup.map_bot]

theorem localDeltaIn_zpowers_of_mulEquiv {C G : Type*} [Group C] [Group G] {p : ℕ} (φ : C ≃* G)
    {d : C} (h : ∀ H : Subgroup (MulAut C), innerAut C ≤ H →
      localDeltaIn p H ((Subgroup.zpowers d).map (MulAut.conj : C →* MulAut C)) = ⊥)
    {H : Subgroup (MulAut G)} (hH : innerAut G ≤ H) :
    localDeltaIn p H ((Subgroup.zpowers (φ d)).map (MulAut.conj : G →* MulAut G)) = ⊥ := by
  set ψ : MulAut G →* MulAut C := (MulAut.congr φ.symm).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr φ.symm).injective
  have hψconj : ∀ g : G, ψ (MulAut.conj g) = MulAut.conj (φ.symm g) := fun g => by
    ext z
    simp [hψ, MulAut.congr_apply, MulAut.conj_apply]
  have hinn : innerAut C ≤ H.map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (φ y), hH ⟨φ y, rfl⟩, ?_⟩
    rw [hψconj]
    simp
  have hmap : ((Subgroup.zpowers (φ d)).map (MulAut.conj : G →* MulAut G)).map ψ =
      (Subgroup.zpowers d).map (MulAut.conj : C →* MulAut C) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hψconj,
      MulEquiv.symm_apply_apply]
  have key := h (H.map ψ) hinn
  have hle := map_localDeltaIn_le p ψ hψinj H ((Subgroup.zpowers (φ d)).map (MulAut.conj : G →* MulAut G))
  rw [hmap, key, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψinj] at hle
  exact hle

section Main


theorem innerPlaneBalance_adjointE8_four_five (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K ^ 2 + 1) (hcp : LangComponentPieces) (hAK : AnyKindCommute)
    (hAK3 : AnyKindCommuteThreeFull)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot .E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hrig : SetupRigidAtFrobenius .E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 ∧ 3 ≤ q) :
    InnerPlaneBalance 5 (adjointGroup Tag.E8 K) := by
  classical
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_conjugator_E8 K e8PhiFourWeyl
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  let D : LangDatum Tag.E8 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr e8PhiFourWeyl hg0C hg0
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup Tag.E8 K).subtype) :=
    langDescent_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hFr D rfl Nat.prime_seven (by norm_num)
      (commutator_adjointGroup_E8_eq_top K)
  have hΓ : D.Γ = langModel Tag.E8 K (AlgebraicClosure K) g0 := by
    rw [hd.Γ_eq, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E8 (AlgebraicClosure K) D
  have hK0 : ((Nat.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.card_eq_fintype_card,
      FiniteField.cast_card_eq_zero K, map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨by
      rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card K, hK0⟩
  have hpq : ¬ 5 ∣ D.q := not_five_dvd_of_dvd_sq_add_one h5
  let S : LangSetup Tag.E8 (AlgebraicClosure K) 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model
  have hSD : S.D = D := rfl
  have hq : S.D.q = Nat.card K := rfl
  have hFr' : ∀ c, Fr c = c ^ S.D.q := hFr
  have hΦ : S.D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8PhiFourWeyl := rfl
  have hMΓ : S.D.model ≤ S.Γ := model_le_Γ_ofFrobenius_E8 e8PhiFourWeyl K hFr hg0C hg0
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [hq, pow_one])
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) := by
    show Function.Injective (MulAut.conj : ↥D.Γ →* MulAut ↥D.Γ)
    rw [hΓ]
    exact CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv
      (langModelMulEquiv Tag.E8 K (AlgebraicClosure K) g0).symm
      (mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K))
  let φ : adjointGroup Tag.E8 K ≃* ↥S.Γ :=
    (langModelMulEquiv Tag.E8 K (AlgebraicClosure K) g0).trans (MulEquiv.subgroupCongr hΓ.symm)
  have hφ : ∀ x : adjointGroup Tag.E8 K,
      ((φ x : ↥S.Γ) : ModGL Tag.E8 (AlgebraicClosure K)) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E8 K) * g0 :=
    fun x => coe_langModelMulEquiv Tag.E8 K (AlgebraicClosure K) g0 x
  have hcardΓ : Nat.card ↥S.Γ = Nat.card (adjointGroup Tag.E8 K) :=
    (Nat.card_congr φ.toEquiv).symm
  have hcardT : Nat.card ↥(S.D.torus.subgroupOf S.Γ) =
      ((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torus_le_Γ S hMΓ)).toEquiv]
    exact card_twistedTorus_E8_four K hFr
  have hord : (Nat.card ↥S.Γ).factorization 5 =
      (Nat.card ↥(S.D.torus.subgroupOf S.Γ)).factorization 5 + 1 := by
    rw [hcardΓ, hcardT]
    exact factorization_card_adjointE8_eq_torus_add_one K h5
  refine InnerPlaneBalance.of_mulEquiv φ ?_
  by_cases hq3 : 3 ≤ Nat.card K
  · exact innerPlaneBalance_Gamma_E8_ge3 S hFr' hΦ hn hw4 hMΓ hAlg hcp hinj hAK hAK3
      (by rw [hq]; exact h5) (by rw [hq]; exact hq3)
      (hrig K Fr hFr g0 hg0C hg0 S hSD ⟨h5, hq3⟩) hord
  · have hK2 : Nat.card K = 2 := by
      have := Finite.one_lt_card (α := K)
      omega
    refine innerPlaneBalance_Gamma_E8_two S hFr' hΦ hn hMΓ hinj hord ?_
    intro u hu1 huT H hH
    set d : adjointGroup Tag.E8 K := φ.symm u with hd'
    have hdu : φ d = u := φ.apply_symm_apply u
    have hd1 : d ≠ 1 := fun h => hu1 (by rw [← hdu, h, map_one])
    have hdT : baseChangeGL (algebraMap K (AlgebraicClosure K)) (d : ModGL Tag.E8 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8PhiFourWeyl)
          (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
      refine ⟨(u : ModGL Tag.E8 (AlgebraicClosure K)), huT, ?_⟩
      have h1 := hφ d
      rw [hdu] at h1
      show g0 * (u : ModGL Tag.E8 (AlgebraicClosure K)) * g0⁻¹ = _
      rw [h1]
      group
    have hcore := fun (H' : Subgroup (MulAut (adjointGroup Tag.E8 K)))
        (hH' : innerAut (adjointGroup Tag.E8 K) ≤ H') =>
      localDeltaIn_zpowers_E8_two hK2 hFr hg0C hg0 hd1 hdT hH'
    have := localDeltaIn_zpowers_of_mulEquiv (p := 5) φ (d := d) hcore hH
    rwa [hdu] at this

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
