module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

theorem exists_comm_image [Finite G] {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    ∃ N : Subgroup G, N ≤ A ∧ (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ N) ∧
      (∀ n ∈ N, ∃ a ∈ A, n = a * g * a⁻¹ * g⁻¹) ∧
      Nat.card A = Nat.card N * Nat.card ↥(A ⊓ centralizer ({g} : Set G)) := by
  classical
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun x y => Subtype.ext (hA x.1 x.2 y.1 y.2) }
  let ψ : A →* A :=
    { toFun := fun a => ⟨g * a.1 * g⁻¹, hg a.1 a.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show g * (a.1 * b.1) * g⁻¹ = (g * a.1 * g⁻¹) * (g * b.1 * g⁻¹)
        group }
  let f : A →* A := MonoidHom.id A * ψ⁻¹
  have hf : ∀ a : A, (f a : G) = a.1 * g * a.1⁻¹ * g⁻¹ := by
    intro a
    change (a.1 * (g * a.1 * g⁻¹)⁻¹ : G) = a.1 * g * a.1⁻¹ * g⁻¹
    group
  let N : Subgroup G := f.range.map A.subtype
  have hNA : N ≤ A := Subgroup.map_subtype_le _
  have hmem : ∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ N := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ f.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    have h2 : A.subtype (f ⟨a, ha⟩) ∈ N := Subgroup.mem_map_of_mem A.subtype h1
    have hv : A.subtype (f ⟨a, ha⟩) = a * g * a⁻¹ * g⁻¹ := by
      change (f ⟨a, ha⟩ : G) = a * g * a⁻¹ * g⁻¹
      exact hf ⟨a, ha⟩
    rwa [hv] at h2
  have hsurj : ∀ n ∈ N, ∃ a ∈ A, n = a * g * a⁻¹ * g⁻¹ := by
    intro n hn
    rw [Subgroup.mem_map] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨a.1, a.2, hf a⟩
  refine ⟨N, hNA, hmem, hsurj, ?_⟩
  have hker : f.ker = (A ⊓ centralizer ({g} : Set G)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx' : x.1 * g * x.1⁻¹ * g⁻¹ = 1 := by
        have h : (f x : G) = 1 := by rw [hx]; rfl
        rwa [hf x] at h
      calc x.1 * g = (x.1 * g * x.1⁻¹ * g⁻¹) * (g * x.1) := by group
        _ = g * x.1 := by rw [hx']; simp
    · intro hx
      apply Subtype.ext
      rw [hf x]
      change x.1 * g * x.1⁻¹ * g⁻¹ = 1
      rw [hx.2]
      group
  have hkerCard : Nat.card f.ker = Nat.card ↥(A ⊓ centralizer ({g} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrangeCard : Nat.card N = Nat.card f.range := by
    dsimp [N]
    exact Subgroup.card_map_of_injective A.subtype_injective
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hkerCard, ← hrangeCard] at hcard
  rw [← hcard, mul_comm]

theorem mem_closure_pair_of_invol {a b x : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    x ∈ Subgroup.closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem exists_isElemAbelian_card_sixteen [Finite G] {W : Subgroup G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hcard : 16 ≤ Nat.card W) :
    ∃ Y' : Subgroup G, Y' ≤ W ∧ CFSG.Open.IsElemAbelian 2 Y' ∧ Nat.card Y' = 16 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 W := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hW.2 (x : G) x.2
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  have hle : 4 ≤ n := by
    have h : 2 ^ 4 ≤ 2 ^ n := by rw [← hn]; norm_num at hcard ⊢; exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have h4 : 2 ^ 4 ∣ Nat.card W := by
    rw [hn]
    exact pow_dvd_pow 2 hle
  obtain ⟨K, hKcard, -, hKW⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 4)
      (H := ⊥) (L := W) (by simp) h4 bot_le
  refine ⟨K, hKW, ⟨?_, ?_⟩, ?_⟩
  · refine IsMulCommutative.of_comm (fun x y => ?_)
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    exact congrArg Subtype.val (hW.1.is_comm.comm ⟨x.1, hKW x.2⟩ ⟨y.1, hKW y.2⟩)
  · intro x hx
    exact hW.2 x (hKW hx)
  · rw [hKcard]; norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

end
