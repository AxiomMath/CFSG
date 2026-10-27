module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParS2
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

theorem par_exists_fixed_aux {α : Type*} [Finite α] (ι σ : α → α) (hι2 : ∀ x, ι (ι x) = x)
    (hι : ∀ x, ι x ≠ x) (hσ : Function.Injective σ) (hσι : ∀ x, σ (ι x) = ι (σ x))
    (hσσ : ∀ x, σ (σ x) = x ∨ σ (σ x) = ι x) (hcard : Nat.card α = 6) :
    ∃ x, σ x = x ∨ σ x = ι x := by
  classical
  by_contra hcon
  push Not at hcon
  letI := Fintype.ofFinite α
  have hpos : 0 < Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hpos
  let A : Finset α := {x₀, ι x₀, σ x₀, ι (σ x₀)}
  have hAcard : A.card = 4 := by
    have h1 : x₀ ≠ ι x₀ := (hι x₀).symm
    have h2 : x₀ ≠ σ x₀ := ((hcon x₀).1).symm
    have h3 : x₀ ≠ ι (σ x₀) := fun h => (hcon x₀).2 (by
      have hh := congrArg ι h
      rw [hι2 (σ x₀)] at hh
      exact hh.symm)
    have h4 : ι x₀ ≠ σ x₀ := ((hcon x₀).2).symm
    have h5 : ι x₀ ≠ ι (σ x₀) := fun h => (hcon x₀).1 (by
      have hh := congrArg ι h
      rw [hι2 x₀, hι2 (σ x₀)] at hh
      exact hh.symm)
    have h6 : σ x₀ ≠ ι (σ x₀) := (hι (σ x₀)).symm
    exact Finset.card_eq_four.mpr
      ⟨x₀, ι x₀, σ x₀, ι (σ x₀), h1, h2, h3, h4, h5, h6, rfl⟩
  have hAι : ∀ a ∈ A, ι a ∈ A := by
    intro a ha
    change a ∈ ({x₀, ι x₀, σ x₀, ι (σ x₀)} : Finset α) at ha
    change ι a ∈ ({x₀, ι x₀, σ x₀, ι (σ x₀)} : Finset α)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hι2 x₀)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (hι2 (σ x₀))))
  have hAσ : ∀ a ∈ A, σ a ∈ A := by
    intro a ha
    change a ∈ ({x₀, ι x₀, σ x₀, ι (σ x₀)} : Finset α) at ha
    change σ a ∈ ({x₀, ι x₀, σ x₀, ι (σ x₀)} : Finset α)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (hσι x₀)))
    · rcases hσσ x₀ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have h1 : σ (ι (σ x₀)) = ι (σ (σ x₀)) := hσι (σ x₀)
      rw [h1]
      rcases hσσ x₀ with h | h
      · rw [h]; exact Or.inr (Or.inl rfl)
      · rw [h, hι2 x₀]; exact Or.inl rfl
  let B : Finset α := Finset.univ \ A
  have hBcard : B.card = 2 := by
    have hu : Fintype.card α = 6 := by
      rw [← Nat.card_eq_fintype_card, hcard]
    change (Finset.univ \ A).card = 2
    rw [Finset.card_univ_sdiff, hAcard, hu]
  obtain ⟨y, hyB⟩ := Finset.card_pos.mp (by rw [hBcard]; norm_num)
  have hyA : y ∉ A := (Finset.mem_sdiff.mp hyB).2
  have hιyB : ι y ∈ B := by
    change ι y ∈ Finset.univ \ A
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hιyA
    exact hyA (by
      have := hAι (ι y) hιyA
      rwa [hι2 y] at this)
  have hσyB : σ y ∈ B := by
    change σ y ∈ Finset.univ \ A
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hσyA
    have hImage_sub : A.image σ ⊆ A :=
      Finset.image_subset_iff.mpr (fun a ha => hAσ a ha)
    have hcard_img : (A.image σ).card = A.card :=
      Finset.card_image_of_injective A hσ
    have hImage_eq : A.image σ = A :=
      Finset.eq_of_subset_of_card_le hImage_sub (le_of_eq hcard_img.symm)
    have hmem : σ y ∈ A.image σ := by rwa [hImage_eq]
    rw [Finset.mem_image] at hmem
    obtain ⟨a, ha, hay⟩ := hmem
    exact hyA (hσ hay ▸ ha)
  have hsub : ({y, ι y} : Finset α) ⊆ B := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hyB
    · exact hιyB
  have hcard2 : ({y, ι y} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using (hι y).symm), Finset.card_singleton]
  have hBeq : B = {y, ι y} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, hBcard])).symm
  have hmem : σ y ∈ ({y, ι y} : Finset α) := by rwa [← hBeq]
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact (hcon y).1 h
  · exact (hcon y).2 h

theorem par_exists_fixed_class [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {w : G}
    (hwz : w * z = z * w) (hwK : CFSG.conjugate (K i) w = K i)
    (hw2 : ∀ q ∈ K i, q ^ 4 = 1 →
      (w * w)⁻¹ * q * (w * w) = q ∨ (w * w)⁻¹ * q * (w * w) = q * z) :
    ∃ a ∈ K i, a * a = z ∧ (w⁻¹ * a * w = a ∨ w⁻¹ * a * w = a * z) := by
  classical
  let α := {x : G // x ∈ K i ∧ x * x = z}
  have hmem_conj : ∀ x : α, w⁻¹ * x.1 * w ∈ K i := by
    intro x
    have h : w⁻¹ * x.1 * w ∈ CFSG.conjugate (K i) w := by
      rw [CFSG.conjugate, Subgroup.mem_map]
      refine ⟨w * (w⁻¹ * x.1 * w) * w⁻¹, ?_, ?_⟩
      · rw [show w * (w⁻¹ * x.1 * w) * w⁻¹ = x.1 by group]
        exact x.2.1
      · change (MulAut.conj w⁻¹) (w * (w⁻¹ * x.1 * w) * w⁻¹) = w⁻¹ * x.1 * w
        rw [MulAut.conj_apply]
        group
    rwa [hwK] at h
  have hconjz : w⁻¹ * z * w = z := by
    have hwz' : z * w = w * z := hwz.symm
    rw [mul_assoc, hwz', ← mul_assoc, inv_mul_cancel, one_mul]
  have hsq_sigma : ∀ x : α, (w⁻¹ * x.1 * w) * (w⁻¹ * x.1 * w) = z := by
    intro x
    rw [show (w⁻¹ * x.1 * w) * (w⁻¹ * x.1 * w) = w⁻¹ * (x.1 * x.1) * w by group]
    rw [x.2.2, hconjz]
  have hsq_iota : ∀ x : α, (x.1 * z) * (x.1 * z) = z := by
    intro x
    have hcomm : z * x.1 = x.1 * z := hq.z_comm x.2.1
    calc
      (x.1 * z) * (x.1 * z) = x.1 * (z * x.1) * z := by group
      _ = x.1 * (x.1 * z) * z := by rw [hcomm]
      _ = (x.1 * x.1) * (z * z) := by group
      _ = z := by rw [x.2.2, hq.z_sq, mul_one]
  let iota : α → α := fun x => ⟨x.1 * z, (K i).mul_mem x.2.1 (hq.z_mem i), hsq_iota x⟩
  let sigma : α → α := fun x => ⟨w⁻¹ * x.1 * w, hmem_conj x, hsq_sigma x⟩
  have hι2 : ∀ x : α, iota (iota x) = x := by
    intro x
    refine Subtype.ext ?_
    change (x.1 * z) * z = x.1
    rw [mul_assoc, hq.z_sq, mul_one]
  have hι : ∀ x : α, iota x ≠ x := by
    intro x h
    have h' : x.1 * z = x.1 := congrArg Subtype.val h
    exact hq.z_ne (mul_left_cancel (a := x.1) (by rw [mul_one]; exact h'))
  have hσ : Function.Injective sigma := by
    intro x y hxy
    have hxy' : w⁻¹ * x.1 * w = w⁻¹ * y.1 * w := congrArg Subtype.val hxy
    refine Subtype.ext ?_
    have hx' : w * (w⁻¹ * x.1 * w) * w⁻¹ = x.1 := by group
    have hy' : w * (w⁻¹ * y.1 * w) * w⁻¹ = y.1 := by group
    rw [← hx', ← hy']
    exact congrArg (fun t => w * t * w⁻¹) hxy'
  have hσι : ∀ x : α, sigma (iota x) = iota (sigma x) := by
    intro x
    refine Subtype.ext ?_
    change w⁻¹ * (x.1 * z) * w = (w⁻¹ * x.1 * w) * z
    calc
      w⁻¹ * (x.1 * z) * w = w⁻¹ * x.1 * (z * w) := by group
      _ = w⁻¹ * x.1 * (w * z) := by rw [hwz.symm]
      _ = (w⁻¹ * x.1 * w) * z := by group
  have hσσ : ∀ x : α, sigma (sigma x) = x ∨ sigma (sigma x) = iota x := by
    intro x
    have hx4 : x.1 ^ 4 = 1 := by
      have h : x.1 ^ 4 = (x.1 * x.1) * (x.1 * x.1) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [h, x.2.2, hq.z_sq]
    have hww : w⁻¹ * (w⁻¹ * x.1 * w) * w = (w * w)⁻¹ * x.1 * (w * w) := by group
    rcases hw2 x.1 x.2.1 hx4 with h | h
    · left
      refine Subtype.ext ?_
      change w⁻¹ * (w⁻¹ * x.1 * w) * w = x.1
      rw [hww]
      exact h
    · right
      refine Subtype.ext ?_
      change w⁻¹ * (w⁻¹ * x.1 * w) * w = x.1 * z
      rw [hww]
      exact h
  have hcard : Nat.card α = 6 := par_card_sq_eq_z hq i
  obtain ⟨x, hx⟩ := par_exists_fixed_aux iota sigma hι2 hι hσ hσι hσσ hcard
  refine ⟨x.1, x.2.1, x.2.2, ?_⟩
  rcases hx with h | h
  · left; simpa using congrArg Subtype.val h
  · right; simpa using congrArg Subtype.val h

end CFSG.OddStandard.SmallF3.Omega
