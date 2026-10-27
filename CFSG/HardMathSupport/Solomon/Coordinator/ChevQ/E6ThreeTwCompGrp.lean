module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompInner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompQuot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU

open scoped Fin.NatCast

set_option linter.unusedSectionVars false

section Group

theorem twCard_three_mul_le {G : Type*} [Group G] {T S : Subgroup G} [Finite S] (hTS : T ≤ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {e : G} (he : e ∈ S) (heT : e ∉ T)
    (he3 : e ^ 3 = 1) :
    3 * Nat.card {τ : G // τ ∈ T ∧ τ ^ 3 = 1} ≤ Nat.card {τ : G // τ ∈ S ∧ τ ^ 3 = 1} := by
  haveI : Finite {τ : G // τ ∈ S ∧ τ ^ 3 = 1} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : S)) fun a b hab =>
      Subtype.ext (congrArg (fun x : S => (x : G)) hab)
  let F : Fin 3 × {τ : G // τ ∈ T ∧ τ ^ 3 = 1} → {τ : G // τ ∈ S ∧ τ ^ 3 = 1} := fun p =>
    ⟨e ^ (p.1 : ℕ) * p.2.1, S.mul_mem (S.pow_mem he _) (hTS p.2.2.1), by
      rw [Commute.mul_pow (hS _ (S.pow_mem he (p.1 : ℕ)) _ (hTS p.2.2.1)), pow_right_comm e, he3,
        one_pow, one_mul]
      exact p.2.2.2⟩
  have hF : Function.Injective F := by
    rintro ⟨k, x⟩ ⟨k', x'⟩ heq
    have h1 : e ^ (k : ℕ) * x.1 = e ^ (k' : ℕ) * x'.1 :=
      congrArg (fun y : {τ : G // τ ∈ S ∧ τ ^ 3 = 1} => (y : G)) heq
    have hinv : (e ^ (k' : ℕ))⁻¹ = e ^ (2 * (k' : ℕ)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (k' : ℕ) + 2 * (k' : ℕ) = 3 * (k' : ℕ) by omega, pow_mul, he3,
        one_pow]
    have hmem : e ^ (2 * (k' : ℕ) + (k : ℕ)) ∈ T := by
      have h2 : e ^ (2 * (k' : ℕ) + (k : ℕ)) = x'.1 * x.1⁻¹ := by
        rw [pow_add, ← hinv, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
        exact h1
      rw [h2]
      exact T.mul_mem x'.2.1 (T.inv_mem x.2.1)
    have h3 := twCompQuot_dvd_of_pow_mem he3 heT hmem
    have hk : k = k' := by
      apply Fin.ext
      have := k.isLt
      have := k'.isLt
      omega
    subst hk
    obtain rfl : x = x' := Subtype.ext (mul_left_cancel h1)
    rfl
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_fin] at h

end Group

section Line

variable
  {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}

theorem TwE6ThreeA2Line.conj_mem_iSup (hl : TwE6ThreeA2Line K σ h₀ L T n)
    (g : ModGL TwistTag.E6.tag K) : g ∈ ⨆ i, L i ↔ n * g * n⁻¹ ∈ ⨆ i, L i := by
  have hmap : (⨆ i, L i).map (MulAut.conj n).toMonoidHom = ⨆ i, L i := by
    rw [Subgroup.map_iSup]
    simp_rw [hl.n_conj]
    exact (Equiv.addRight (1 : Fin 3)).iSup_comp
  constructor
  · intro hg
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hg
  · intro hg
    rw [← hmap] at hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyg
    rwa [← mul_left_cancel (mul_right_cancel hyg)]

theorem TwE6ThreeA2Line.pow_three_comm_mem (hl : TwE6ThreeA2Line K σ h₀ L T n)
    (hnT : ∀ τ, τ ∈ T ↔ n * τ * n⁻¹ ∈ T) {τ : ModGL TwistTag.E6.tag K} (hτ : τ ∈ T) :
    n ^ 3 * τ * (n ^ 3)⁻¹ * τ⁻¹ ∈ T ⊓ ⨆ i, L i := by
  have hT3 : n ^ 3 * τ * (n ^ 3)⁻¹ ∈ T := by
    have h := (hnT _).1 ((hnT _).1 ((hnT _).1 hτ))
    convert h using 1
    simp only [pow_three, mul_inv_rev, mul_assoc]
  refine Subgroup.mem_inf.2 ⟨T.mul_mem hT3 (T.inv_mem hτ), ?_⟩
  have hTN : T ≤ Subgroup.normalizer
      ((⨆ i, L i : Subgroup (ModGL TwistTag.E6.tag K)) : Set (ModGL TwistTag.E6.tag K)) := by
    intro t ht
    apply hl.le_normalizer
    rw [hl.centralizer_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ht)
  have h3 := twComp_pow_three_mem hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at h3
  obtain ⟨t₀, ht₀, m, hm, he⟩ := Set.mem_mul.1 h3
  have ht₀' : t₀ ∈ T := ht₀
  have hm' : m ∈ ⨆ i, L i := hm
  have hc : t₀⁻¹ * τ⁻¹ = τ⁻¹ * t₀⁻¹ := hl.T_comm _ (T.inv_mem ht₀') _ (T.inv_mem hτ)
  have key : n ^ 3 * τ * (n ^ 3)⁻¹ * τ⁻¹ = t₀ * (m * (τ * m⁻¹ * τ⁻¹)) * t₀⁻¹ := by
    rw [← he, mul_inv_rev]
    simp only [mul_assoc]
    rw [hc]
  rw [key]
  have hτm : τ * m⁻¹ * τ⁻¹ ∈ ⨆ i, L i :=
    (Subgroup.mem_normalizer_iff.1 (hTN hτ) m⁻¹).1 (inv_mem hm')
  exact (Subgroup.mem_normalizer_iff.1 (hTN ht₀') _).1 (mul_mem hm' hτm)

end Line

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
