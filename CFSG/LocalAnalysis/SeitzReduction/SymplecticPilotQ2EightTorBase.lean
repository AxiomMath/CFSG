module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaTorOne
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaTorTwo

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

section SLTwo

variable [CharP K 2]

theorem mem_zpowers_zThreeSL_of_odd (hK : Nat.card K = 2) {B : SL(2, K)}
    (hB : Odd (orderOf B)) : B ∈ zpowers (zThreeSL (K := K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact B.2
  rcases eq_zero_or_eq_one_of_natCard_two hK
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0 + (B : Matrix (Fin 2) (Fin 2) K) 1 1) with ht | ht
  ·
    have e00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      linear_combination (B : Matrix (Fin 2) (Fin 2) K) 0 0 * ht - hdet - h2
    have e01 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
      linear_combination (B : Matrix (Fin 2) (Fin 2) K) 0 1 * ht
    have e10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      linear_combination (B : Matrix (Fin 2) (Fin 2) K) 1 0 * ht
    have e11 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (B : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      linear_combination (B : Matrix (Fin 2) (Fin 2) K) 1 1 * ht - hdet - h2
    have hsq : B ^ 2 = 1 := by
      refine Subtype.ext ?_
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]
    have h1 : orderOf B = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsq) with h | h
      · exact h
      · rw [h] at hB
        exact absurd hB (by decide)
    rw [orderOf_eq_one_iff.1 h1]
    exact one_mem _
  ·
    have haa : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 =
        (B : Matrix (Fin 2) (Fin 2) K) 0 0 := by
      rcases eq_zero_or_eq_one_of_natCard_two hK ((B : Matrix (Fin 2) (Fin 2) K) 0 0) with h | h <;>
        rw [h] <;> ring
    have hbc : (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      linear_combination -hdet + (B : Matrix (Fin 2) (Fin 2) K) 0 0 * ht - haa - h2
    have hone : ∀ x y : K, x * y = 1 → x = 1 := by
      intro x y hxy
      rcases eq_zero_or_eq_one_of_natCard_two hK x with h | h
      · rw [h, zero_mul] at hxy
        exact absurd hxy zero_ne_one
      · exact h
    have hb1 := hone _ _ hbc
    have hc1 := hone _ _ ((mul_comm _ _).trans hbc)
    refine mem_zpowers_zThreeSL_of_entries hK ?_ ?_
    · linear_combination hc1 + hb1 + h2
    · linear_combination ht + hb1 + (1 - (B : Matrix (Fin 2) (Fin 2) K) 0 0) * h2

end SLTwo

section OddClosure

variable {G H : Type*} [Group G] [Group H]

@[expose] def oddElemClosure (C : Subgroup G) : Subgroup G :=
  closure {y | y ∈ C ∧ Odd (orderOf y)}

theorem mem_oddElemClosure {C : Subgroup G} {y : G} (hy : y ∈ C) (ho : Odd (orderOf y)) :
    y ∈ oddElemClosure C :=
  subset_closure ⟨hy, ho⟩

theorem map_oddElemClosure_le {C : Subgroup G} {Φ₁ Φ₂ : G →* H} (h₁ : Function.Injective Φ₁)
    (h₂ : Function.Injective Φ₂) (hodd : ∀ y ∈ C, Odd (orderOf y) → Φ₁ y ∈ C.map Φ₂) :
    (oddElemClosure C).map Φ₁ ≤ (oddElemClosure C).map Φ₂ := by
  rw [oddElemClosure, MonoidHom.map_closure, closure_le]
  rintro _ ⟨y, ⟨hyC, hyo⟩, rfl⟩
  obtain ⟨y', hy'C, hy'⟩ := hodd y hyC hyo
  refine ⟨y', subset_closure ⟨hy'C, ?_⟩, hy'⟩
  rw [← orderOf_injective Φ₂ h₂ y', hy', orderOf_injective Φ₁ h₁ y]
  exact hyo

theorem comap_map_le_commutator_oddElemClosure {C : Subgroup G} {Φ₁ Φ₂ : G →* H}
    (h₁ : Function.Injective Φ₁) (h₂ : Function.Injective Φ₂)
    (hodd : ∀ y ∈ C, Odd (orderOf y) → Φ₁ y ∈ C.map Φ₂) {X : Subgroup G}
    (hX : X ≤ ⁅oddElemClosure C, oddElemClosure C⁆) :
    (X.map Φ₁).comap Φ₂ ≤ ⁅oddElemClosure C, oddElemClosure C⁆ := by
  have hle := map_oddElemClosure_le h₁ h₂ hodd
  set Γ := oddElemClosure C with hΓ
  have h1 : X.map Φ₁ ≤ ⁅Γ, Γ⁆.map Φ₂ := by
    calc X.map Φ₁ ≤ ⁅Γ, Γ⁆.map Φ₁ := map_mono hX
      _ = ⁅Γ.map Φ₁, Γ.map Φ₁⁆ := map_commutator _ _ _
      _ ≤ ⁅Γ.map Φ₂, Γ.map Φ₂⁆ := commutator_mono hle hle
      _ = ⁅Γ, Γ⁆.map Φ₂ := (map_commutator _ _ _).symm
  calc (X.map Φ₁).comap Φ₂ ≤ (⁅Γ, Γ⁆.map Φ₂).comap Φ₂ := comap_mono h1
    _ = ⁅Γ, Γ⁆ := comap_map_eq_self_of_injective h₂ _

end OddClosure

section SpFour

variable [Finite K]

theorem isSimpleGroup_commutator_statedSp_two (hK : Nat.card K = 2) :
    IsSimpleGroup (commutator (StatedSp 2 K)) := by
  set e := F4Pilot.sp4EquivSympFour (K := K) hK with he
  have hmap : (commutator (StatedSp 2 K)).map e.toMonoidHom = commutator sympFour := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have : IsSimpleGroup (commutator sympFour) := isSimpleGroup_commutator_sympFour
  exact (((commutator (StatedSp 2 K)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)).isSimpleGroup_congr.2 this

theorem commutator_statedSp_two_le_closure_odd [CharP K 2] (hK : Nat.card K = 2) :
    commutator (StatedSp 2 K) ≤
      closure {y | y ∈ commutator (StatedSp 2 K) ∧ Odd (orderOf y)} := by
  set M := commutator (StatedSp 2 K) with hM
  have : IsSimpleGroup M := isSimpleGroup_commutator_statedSp_two hK
  set y₀ : M := ⟨nsElt 0, nsElt_mem_commutator_statedSp_two⟩ with hy₀
  have ho : orderOf y₀ = 3 := by rw [hy₀, Subgroup.orderOf_mk, orderOf_nsElt]
  have htop := closure_odd_eq_top_of_isSimpleGroup (M := M) (y₀ := y₀)
    (fun h => by rw [h, orderOf_one] at ho; omega) (by rw [ho]; decide)
  intro g hg
  have hmem : (⟨g, hg⟩ : M) ∈ closure {y : M | Odd (orderOf y)} := htop ▸ mem_top _
  have h := mem_map_of_mem M.subtype hmem
  rw [MonoidHom.map_closure] at h
  refine closure_mono ?_ h
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩

end SpFour

section ATwo

variable [CharP K 2] {n : ℕ} {p q : Fin n}

theorem commutator_oddElemClosure_le_map_ker_a2Coord (hK : Nat.card K = 2) (hpq : p ≠ q)
    {b : K} (hb : b ≠ 0) :
    ⁅oddElemClosure (centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K))),
      oddElemClosure (centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K)))⁆ ≤
      (a2Coord hpq hb).ker.map
        (centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K))).subtype := by
  set C := centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K)) with hC
  set α := a2Coord hpq hb with hα
  have hΓ : oddElemClosure C ≤ ((zpowers (zThreeSL (K := K))).comap α).map C.subtype := by
    rw [oddElemClosure, closure_le]
    rintro y ⟨hyC, hyo⟩
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show α ⟨y, hyC⟩ ∈ zpowers zThreeSL
    refine mem_zpowers_zThreeSL_of_odd hK (Odd.of_dvd_nat (n := orderOf y) hyo ?_)
    rw [← Subgroup.orderOf_mk y hyC]
    exact orderOf_map_dvd α _
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨c₁, hc₁, rfl⟩ := hΓ hg₁
  obtain ⟨c₂, hc₂, rfl⟩ := hΓ hg₂
  refine ⟨(⁅c₁, c₂⁆ : C), MonoidHom.mem_ker.2 ?_, by simp [commutatorElement_def]⟩
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (show α c₁ ∈ zpowers zThreeSL from hc₁)
  obtain ⟨l, hl⟩ := mem_zpowers_iff.1 (show α c₂ ∈ zpowers zThreeSL from hc₂)
  rw [← hk, ← hl]
  exact Commute.zpow_zpow_self _ k l

omit [CharP K 2] in
theorem twoCentralElt_mem_suppGroup (a b : K) :
    twoCentralElt n p q a b ∈ suppGroup (coords p ∪ coords q) := by
  intro r t hrt
  rw [mat_twoCentralElt]
  rcases r with x | x <;> rcases t with y | y
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, twoCentralMat_apply, Matrix.one_apply_ne Sum.inl_ne_inr]
    have hx : (Sum.inl x : Fin n ⊕ Fin n) ∈ coords p ∪ coords q ↔ x = p ∨ x = q := by
      simp [mem_coords]
    have hy : (Sum.inr y : Fin n ⊕ Fin n) ∈ coords p ∪ coords q ↔ y = p ∨ y = q := by
      simp [mem_coords]
    rw [hx, hy, not_and_or, not_or, not_or] at hrt
    rcases hrt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Ne.symm h1, Ne.symm h2]
    · simp [Ne.symm h1, Ne.symm h2]
  · simp
  · simp [Matrix.one_apply]

theorem leviHom_mem_suppGroup_compl (hpq : p ≠ q) {b : K} (hb : b ≠ 0)
    {s : centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K))}
    (hs : a2Coord hpq hb s = 1) :
    leviHom hpq 0 hb s ∈ suppGroup (coords p ∪ coords q)ᶜ := by
  have hW : wBlock p q (mat n K s) = 1 := congrArg Subtype.val hs
  have hpp : mat n K s (Sum.inl p) (Sum.inl p) = 1 := by
    simpa [wBlock] using congrFun (congrFun hW 0) 0
  have hpq' : mat n K s (Sum.inl p) (Sum.inl q) = 0 := by
    simpa [wBlock] using congrFun (congrFun hW 0) 1
  have hqp : mat n K s (Sum.inl q) (Sum.inl p) = 0 := by
    simpa [wBlock] using congrFun (congrFun hW 1) 0
  have hqq : mat n K s (Sum.inl q) (Sum.inl q) = 1 := by
    simpa [wBlock] using congrFun (congrFun hW 1) 1
  obtain ⟨-, f1, f2, f3, f4⟩ := a2_blocks hpq hb
    ((commute_twoCentralElt_iff 0 b).1 (mem_centralizer_singleton_iff.1 s.2))
  have hS : ∀ r : Fin n ⊕ Fin n, r ∈ coords p ∪ coords q ↔
      r = Sum.inl p ∨ r = Sum.inl q ∨ r = Sum.inr p ∨ r = Sum.inr q := by
    intro r
    simp only [Set.mem_union, mem_coords]
    tauto
  have hblk : ∀ r : Fin n ⊕ Fin n, r ∈ coords p ∪ coords q ↔ blk p q r ≠ 2 := by
    intro r
    rw [hS, Ne, blk_eq_two_iff, OffPQ, mem_coords, mem_coords]
    tauto
  intro r t hrt
  rw [mat_leviHom, leviPart_apply]
  split_ifs with hrt'
  · have hr : r ∈ coords p ∪ coords q := by
      by_contra hr
      exact hrt ⟨hr, fun ht => hr ((hblk r).2 (hrt' ▸ (hblk t).1 ht))⟩
    have ht : t ∈ coords p ∪ coords q := (hblk t).2 (hrt' ▸ (hblk r).1 hr)
    rcases (hS r).1 hr with rfl | rfl | rfl | rfl <;> rcases (hS t).1 ht with rfl | rfl | rfl | rfl
    all_goals first
      | rw [Matrix.one_apply_eq]; simp only [f1, f4, hpp, hqq]
      | (rw [Matrix.one_apply_ne (by simp [hpq, Ne.symm hpq])]
         simp only [f2, f3, hpq', hqp])
      | (exfalso; simp [blk, hpq, Ne.symm hpq] at hrt')
  · rw [Matrix.one_apply_ne (by rintro rfl; exact hrt' rfl)]

end ATwo

end CFSG.SeitzReduction.SymplecticPilot
