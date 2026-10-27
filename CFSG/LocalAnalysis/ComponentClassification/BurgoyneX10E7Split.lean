module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Typed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Split

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.LieType.Chevalley.ToralSign CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

theorem excCompModel_pairSpan_of_frame
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (rt : Fin r → Fin τ.rank → ℤ)
    (hrt : ∀ k, IsRoot τ (rt k)) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f)
    (hlie : Blueprint.LieModel (↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k))) ⧸ Subgroup.center
          ↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
            (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k)))) t n p f)
    (ht : ExcCompTag t n := by unfold ExcCompTag; decide) :
    ExcCompModel p (pairSpan τ K (Set.range rt)) :=
  ⟨t, n, f, ht, hadm, lieModel_pairSpan_of_frame rt hrt hlie⟩

theorem excCompModel_pairSpan_E7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ExcCompModel p (pairSpan .E7 K (Set.range e7SimpleRoot)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7Node e7_adj e7_nadj
  obtain ⟨-, -, -, -, hlie⟩ := e7_frame_subgroup hadm hK hcomm hρ hψ
  exact excCompModel_pairSpan_of_frame e7SimpleRoot (fun k => isRoot_single _ _) hadm
    hlie

theorem excCompModel_pairSpan_D6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ExcCompModel p (pairSpan .E7 K (Set.range e7D6Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7D6Node e7D6_adj e7D6_nadj
  obtain ⟨-, -, -, -, hlie⟩ := spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ
  exact excCompModel_pairSpan_of_frame e7D6Root (fun k => isRoot_single _ _) hadm hlie

theorem excCompModel_pairSpan_A1
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : IsQuasisimple (pairSpan .E7 K {e7Theta})) :
    ExcCompModel p (pairSpan .E7 K {e7Theta}) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E7 K hK2 isRoot_e7Theta
  let e₀ : pairSpan .E7 K {e7Theta} ≃*
      (rootSubgroup .E7 K e7Theta ⊔ rootSubgroup .E7 K (-e7Theta) : Subgroup (ModGL .E7 K)) :=
    MulEquiv.subgroupCongr (pairSpan_singleton .E7 K e7Theta)
  by_cases h5 : 5 ≤ Nat.card K
  · let e : pairSpan .E7 K {e7Theta} ≃* SL2 K := e₀.trans eQ.symm
    exact excCompModel_of_equiv_psl_two hp hf hK (by omega) (by omega)
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
  · exfalso
    have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have := (hfin.1 h3').1
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq
      (Group.isSolvable_of_isSolvable_injective (f := e₀.toMonoidHom) e₀.injective)

theorem excCompModel_pairSpan_A7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ExcCompModel p (pairSpan .E7 K (Set.range e7A7Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 8 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  exact ⟨.PSL, 8, f, (by unfold ExcCompTag; decide), hadm, lieModel_pairSpan_A7 hp hp2 hK⟩

theorem excCompModel_pairSpan_E6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ExcCompModel p (pairSpan .E7 K (Set.range e7E6Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  exact ⟨.E6, 0, f, (by unfold ExcCompTag; decide), hadm, lieModel_pairSpan_E6 hp hp2 hK⟩

theorem e7_pairSpan_excCompModel
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : S = ∅ ∨ S = Set.range e7SimpleRoot ∨ S = Set.range e7D6Root ∨ S = {e7Theta} ∨
      S = Set.range e7A7Root ∨ S = Set.range e7E6Root)
    (hq : IsQuasisimple (pairSpan .E7 K S)) : ExcCompModel p (pairSpan .E7 K S) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    rw [Subgroup.nontrivial_iff_ne_bot] at this
    exact this (by rw [pairSpan]; exact iSup_emptyset)
  · exact excCompModel_pairSpan_E7 hp hp2 hK
  · exact excCompModel_pairSpan_D6 hp hp2 hK
  · exact excCompModel_pairSpan_A1 hp hp2 hK hq
  · exact excCompModel_pairSpan_A7 hp hp2 hK
  · exact excCompModel_pairSpan_E6 hp hp2 hK

theorem e7_split_orbitGroup_excCompModel
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ}
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal γ) (J' : Set.range D.classOrbit)
    (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    ExcCompModel p (D.withOrbit J').orbitGroup := by
  obtain ⟨i₀, hi₀⟩ := J'.2
  have hJ : ∀ i, i ∈ (J' : Set (KernelComponent D.χ)) ↔ i = i₀ := fun i => by
    rw [← hi₀, classOrbit_eq_singleton D hθ, Set.mem_singleton_iff]
  have hS : (D.withOrbit J').simpleRootsJ = simpleUnion D.χ ∩ componentRoots D.χ i₀ := by
    ext β
    constructor
    · rintro ⟨⟨i, -, hβi⟩, h, hJβ⟩
      exact ⟨Set.mem_iUnion.2 ⟨i, hβi⟩, h, (hJ _).1 hJβ⟩
    · rintro ⟨hβ, h, hβi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hβ
      exact ⟨⟨i, Set.mem_univ _, hi⟩, h, (hJ _).2 hβi⟩
  have horb := orbitGroup_eq_map_pairSpan (D.withOrbit J') fun β _ => hθ β
  rw [hS] at horb
  have hK : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let e : (D.withOrbit J').orbitGroup ≃*
      pairSpan .E7 (frobeniusFixedField k p D.e) (simpleUnion D.χ ∩ componentRoots D.χ i₀) :=
    (MulEquiv.subgroupCongr horb).trans
      ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm)
  exact ExcCompModel.of_mulEquiv e
    (e7_pairSpan_excCompModel (Fact.out : p.Prime) D.odd hK
      (e7_simple_inter_cases hm hχ i₀) (LocalCores.isQuasisimple_of_mulEquiv e hq))

end CFSG.ComponentClassification.Burgoyne.X10
