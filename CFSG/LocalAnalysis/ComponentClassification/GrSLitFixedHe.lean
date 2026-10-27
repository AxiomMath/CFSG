module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHeY
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ker_eq_center_of_quasisimple {Q K : Type*} [Group Q] [Group K] (hQ : IsQuasisimple Q)
    [IsSimpleGroup K] (hK : ∃ a b : K, a * b ≠ b * a) (f : Q →* K)
    (hf : Function.Surjective f) : f.ker = center Q := by
  apply le_antisymm
  · rcases LocalCores.quasisimple_normal_subgroups hQ f.normal_ker with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hK
      obtain ⟨a', rfl⟩ := hf a
      obtain ⟨b', rfl⟩ := hf b
      have ha : f a' = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top a')
      have hb : f b' = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top b')
      exact hab (by rw [ha, hb])
    · exact h
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hc : f z ∈ center K := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hf y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y']
    have hZ : center K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hK
        exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
    rw [hZ] at hc
    exact hc

theorem nonempty_mulEquiv_heOuterD_of_isPComponent
    (L : Subgroup ↥(heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))))
    (hL : IsPComponent 2 L) :
    Nonempty (↥L ≃* ↥heOuterD) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDcomm, hDq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hCC : ⁅(heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))),
      heP ⊓ centralizer {heAutU}⁆ = heOuterD := by
    rw [← heOuterC_eq, ← hDcomm]
  have hDC : heOuterD ≤ heP ⊓ centralizer {heAutU} := by
    rw [← hCC]
    exact Subgroup.commutator_le_self _
  obtain ⟨D', hD'⟩ : ∃ D' : Subgroup ↥(heP ⊓ centralizer {heAutU} :
      Subgroup (Equiv.Perm (Fin 8330))), D' = heOuterD.subgroupOf _ := ⟨_, rfl⟩
  have eD : ↥D' ≃* ↥heOuterD := (MulEquiv.subgroupCongr hD').trans (subgroupOfEquivOfLe hDC)
  have hD'q : IsQuasisimple ↥D' := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eD).mpr hDq
  obtain ⟨hLs, -, hLq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).mp hL
  have : Group.IsPerfect L := CatalogueBHeldSmallCore.pComponent_perfect 2 L hL
  have hLD : L ≤ D' := by
    intro x hx
    have hx' : x ∈ ⁅L, L⁆ := by rw [Subgroup.commutator_eq_self]; exact hx
    have h1 : x ∈ commutator ↥(heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top hx'
    have h2 : (x : Equiv.Perm (Fin 8330)) ∈ ⁅(heP ⊓ centralizer {heAutU} :
        Subgroup (Equiv.Perm (Fin 8330))), heP ⊓ centralizer {heAutU}⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨x, h1, rfl⟩
    rw [hCC] at h2
    rw [hD']
    exact h2
  have hLs' : (L.subgroupOf D').IsSubnormal := hLs.comap D'.subtype
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hD'q hLs' with htop | hcen
  · have hLeq : L = D' := le_antisymm hLD fun x hx => by
      have : (⟨x, hx⟩ : D') ∈ L.subgroupOf D' := htop ▸ mem_top _
      exact this
    exact ⟨(MulEquiv.subgroupCongr hLeq).trans eD⟩
  · exfalso
    have : Nontrivial L := nontrivial_of_isPComponent hL
    have : IsMulCommutative L := ⟨⟨fun a b => by
      have ha : (⟨a, hLD a.2⟩ : D') ∈ center ↥D' := hcen (show (⟨a, hLD a.2⟩ : D') ∈
        L.subgroupOf D' from a.2)
      have h := congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hLD b.2⟩)
      exact Subtype.ext h.symm⟩⟩
    exact false_of_nontrivial_of_subsingleton L

theorem isA7Type_of_pComponent_heOuter
    (L : Subgroup ↥(heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))))
    (hL : IsPComponent 2 L) : IsA7Type (L ⧸ Open.fusionZStar L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eLD⟩ := nonempty_mulEquiv_heOuterD_of_isPComponent L hL
  obtain ⟨-, hDq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  obtain ⟨-, -, hLq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).mp hL
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_fusionZStar L
  obtain ⟨-, hs, x, y, hxy⟩ := hLq
  have hs' : IsSimpleGroup (L ⧸ Open.fusionZStar L) := eZ.symm.isSimpleGroup
  have hna : ∃ a b : L ⧸ Open.fusionZStar L, a * b ≠ b * a :=
    ⟨eZ x, eZ y, fun h => hxy (eZ.injective (by rw [map_mul, map_mul, h]))⟩
  let f : ↥heOuterD →* L ⧸ Open.fusionZStar L :=
    (QuotientGroup.mk' (Open.fusionZStar L)).comp eLD.symm.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp eLD.symm.surjective
  have hker : f.ker = center heOuterD := ker_eq_center_of_quasisimple hDq hna f hf
  obtain ⟨e7⟩ := nonempty_heOuterQuot_equiv_alternatingGroup
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans e7⟩

@[expose] def HeldTwoAFixedInput : Prop :=
  ∀ L : Subgroup ↥(centralizerIn heP (heGenPerm 0)), IsPComponent 2 L →
    IsL34Type (L ⧸ Open.fusionZStar L)

theorem isPComponent_map_and_fusionZStar_equiv {F F' : Type*} [Group F] [Group F'] [Finite F]
    [Finite F'] (φ : F ≃* F') {L : Subgroup F} (hL : IsPComponent 2 L) :
    IsPComponent 2 (L.map φ.toMonoidHom) ∧ Nonempty (L ⧸ Open.fusionZStar L ≃*
      (L.map φ.toMonoidHom) ⧸ Open.fusionZStar (L.map φ.toMonoidHom)) :=
  ⟨LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hL,
    nonempty_fusionZStar_equiv_of_mulEquiv' (L.equivMapOfInjective φ.toMonoidHom φ.injective)⟩

theorem simpleFixedComponents_held (h2A : HeldTwoAFixedInput) (h2B : ∀ L : Subgroup ↥(centralizerIn
    heP heT1P), ¬ IsPComponent 2 L) :
    SimpleFixedComponents IsHeldType fun K _ => IsL34Type K ∨ IsA7Type K := by
  intro S _ _ hS hnab hτ σ hσ P hPF hP hPne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2A' : ∀ L : Subgroup ↥(centralizerIn heP (heGenPerm 0)), IsPComponent 2 L →
      IsL34Type (L ⧸ Open.fusionZStar L) := h2A
  have h2B' : ∀ L : Subgroup ↥(centralizerIn heP heT1P), ¬ IsPComponent 2 L := h2B
  obtain ⟨θ₀⟩ := hτ
  have θ : S ≃* heP := θ₀.trans heEquivP
  by_cases hσ1 : σ = 1
  · exfalso
    have hFtop : fixedSubgroup σ = ⊤ := by
      rw [hσ1, eq_top_iff]
      intro x _
      rfl
    have : IsSimpleGroup (fixedSubgroup σ) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have h := eq_top_of_isPComponent_of_isSimpleGroup hP
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup σ) ∈ P.subgroupOf (fixedSubgroup σ) :=
      h ▸ mem_top _
    exact hx
  have hσ2' : σ * σ = 1 := MulEquiv.ext fun t => hσ t
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2') hσ1
  have hβ : orderOf (MulAut.congr θ σ) = 2 := by rw [orderOf_congr, hσ2]
  have hL : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) := hP
  obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  suffices hsuff : ∀ (F' : Type) [Group F'] [Finite F'] (φ : fixedSubgroup σ ≃* F'),
      (∀ L' : Subgroup F', IsPComponent 2 L' →
        IsL34Type (L' ⧸ Open.fusionZStar L') ∨ IsA7Type (L' ⧸ Open.fusionZStar L')) →
      IsL34Type (P ⧸ Open.fusionZStar P) ∨ IsA7Type (P ⧸ Open.fusionZStar P) by
    by_cases hinn : MulAut.congr θ σ ∈ (MulAut.conj : heP →* MulAut heP).range
    · obtain ⟨t, ht⟩ := hinn
      have ht2 : orderOf t = 2 := by
        rw [← orderOf_injective _ (conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
      let f : fixedSubgroup σ ≃* centralizerIn heP (t : Equiv.Perm (Fin 8330)) :=
        ((fixedSubgroupCongr θ σ).trans
          (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))).trans
          (heCentralizerEquiv t)
      rcases involution_conj_cases t.2 (by rw [Subgroup.orderOf_coe]; exact ht2) with
        ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
      · refine hsuff _ (f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
          (infCentralizerConjEquiv hc (heGenPerm 0)))) fun L' hL' => Or.inl (h2A' L' hL')
      · exact hsuff _ (f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
          (infCentralizerConjEquiv hc heT1P))) fun L' hL' => (h2B' L' hL').elim
    · obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
        (MulAut.congr θ σ) hβ hinn
      obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
      exact hsuff _ (((fixedSubgroupCongr θ σ).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
        (fixedSubgroupEquivOfConj x hg heAutU hxg)) fun L' hL' =>
          Or.inr (isA7Type_of_pComponent_heOuter L' hL')
  intro F' _ _ φ hF'
  obtain ⟨hL', ⟨eL⟩⟩ := isPComponent_map_and_fusionZStar_equiv φ hL
  rcases hF' _ hL' with h | h
  · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eL).symm h)
  · exact Or.inr (h.map fun e => (eP.trans eL).trans e)

theorem heldFixedInput_of_inner (h2A : HeldTwoAFixedInput) (h2B : ∀ L : Subgroup ↥(centralizerIn heP
    heT1P), ¬ IsPComponent 2 L) :
    HeldFixedInput :=
  properFixedComponents_of_simple (fun _ _ _ _ e h => h.map fun f => e.trans f)
    (fun _ _ _ _ e h => h.imp (LieType.CurtisTits.lieModel_of_mulEquiv e.symm)
      fun h' => h'.map fun f => e.trans f)
    (simpleFixedComponents_held h2A h2B)

end CFSG.ComponentClassification.GrSLit
