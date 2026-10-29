module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Twist
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {Y : Set (Matrix (Fin 2) (Fin 2) K × SpecialLinearGroup (Fin 2) K)}

@[expose] def TwistClosed.proj (hY : TwistClosed Y) : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {A | ∃ X, (X, A) ∈ Y}
  one_mem' := ⟨0, hY.one_mem⟩
  mul_mem' := fun ⟨X, hX⟩ ⟨X', hX'⟩ => ⟨_, hY.mul_mem hX hX'⟩
  inv_mem' := fun ⟨X, hX⟩ => ⟨_, hY.inv_mem hX⟩

theorem TwistClosed.mem_proj (hY : TwistClosed Y) {A : SpecialLinearGroup (Fin 2) K} :
    A ∈ hY.proj ↔ ∃ X, (X, A) ∈ Y := Iff.rfl

private theorem line_coe_mul_inv (A : SpecialLinearGroup (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem line_eq_top_of_root_pair [Finite K] [CharP K 2]
    {k : Subfield K} (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) {a γ : K} (ha : a ∉ k) (hγ : γ ≠ 0)
    {M : Subgroup (SpecialLinearGroup (Fin 2) K)} (h1 : u2 1 ∈ M) (ha' : u2 a ∈ M)
    (hl : l2 γ ∈ M) : M = ⊤ := by
  refine sl2_eq_top_of_root_groups hp hp2 hK (a₁ := 1) (a₂ := a) (b₀ := γ) one_ne_zero
    (by rw [div_one]; exact ha) hγ ?_ hl
  intro c₁ hc₁ c₂ hc₂
  rcases eq_zero_or_eq_one_of_card_two' hk hc₁ with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card_two' hk hc₂ with rfl | rfl
  · rw [show (0 : K) * 1 + 0 * a = 0 by ring, u2_zero]; exact M.one_mem
  · rw [show (0 : K) * 1 + 1 * a = a by ring]; exact ha'
  · rw [show (1 : K) * 1 + 0 * a = 1 by ring]; exact h1
  · rw [show (1 : K) * 1 + 1 * a = 1 + a by ring, u2_add]; exact M.mul_mem h1 ha'

theorem proj_eq_top [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) {α β γ : K} (hαβ : α ∉ k ∨ β ∉ k) (hγ : γ ≠ 0)
    (hY : TwistClosed Y) (h1 : ((0 : Matrix (Fin 2) (Fin 2) K), u2 1) ∈ Y)
    (hx : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 β) ∈ Y)
    (hy : ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 α) ∈ Y)
    (hl : ((0 : Matrix (Fin 2) (Fin 2) K), l2 γ) ∈ Y) : hY.proj = ⊤ := by
  have h1' : u2 1 ∈ hY.proj := hY.mem_proj.mpr ⟨_, h1⟩
  have hl' : l2 γ ∈ hY.proj := hY.mem_proj.mpr ⟨_, hl⟩
  rcases hαβ with hα | hβ
  · exact line_eq_top_of_root_pair hk hp hp2 hK hα hγ h1' (hY.mem_proj.mpr ⟨_, hy⟩) hl'
  · exact line_eq_top_of_root_pair hk hp hp2 hK hβ hγ h1' (hY.mem_proj.mpr ⟨_, hx⟩) hl'

private theorem line_eq_of_mem_of_mem (hY : TwistClosed Y)
    (h0 : ∀ X : Matrix (Fin 2) (Fin 2) K, (X, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y → X = 0)
    {X X' : Matrix (Fin 2) (Fin 2) K} {A : SpecialLinearGroup (Fin 2) K}
    (hX : (X, A) ∈ Y) (hX' : (X', A) ∈ Y) : X = X' := by
  have hm := hY.mul_mem (hY.inv_mem hX) hX'
  rw [inv_mul_cancel] at hm
  have hz : -(((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X) +
      ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X' = 0 := h0 _ hm
  have hBX : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X' =
      ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X :=
    (neg_add_eq_zero.mp hz).symm
  calc X = (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * X := by rw [line_coe_mul_inv, Matrix.one_mul]
    _ = (A : Matrix (Fin 2) (Fin 2) K) * (((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * X) := by rw [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 2) (Fin 2) K) * (((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * X') := by rw [hBX]
    _ = (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * X' := by rw [Matrix.mul_assoc]
    _ = X' := by rw [line_coe_mul_inv, Matrix.one_mul]

theorem exists_kernel_ne_zero [Finite K] [CharP K 2] (hs : ∃ s : K, s ≠ 0 ∧ s ≠ 1)
    (hY : TwistClosed Y) (hproj : hY.proj = ⊤) (h1 : ((0 : Matrix (Fin 2) (Fin 2) K), u2 1) ∈ Y)
    (α β : K) (hx : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 β) ∈ Y)
    (hy : ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 α) ∈ Y) :
    ∃ X : Matrix (Fin 2) (Fin 2) K, X ≠ 0 ∧ (X, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  by_contra hcon
  have h0 : ∀ X : Matrix (Fin 2) (Fin 2) K, (X, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y → X = 0 :=
    fun X hX => by
      by_contra hne
      exact hcon ⟨X, hne, hX⟩
  have hex : ∀ A : SpecialLinearGroup (Fin 2) K, ∃ X, (X, A) ∈ Y := fun A =>
    hY.mem_proj.mp (by rw [hproj]; exact Subgroup.mem_top A)
  choose κ hκ using hex
  have hcoc : IsCocycle κ := by
    intro a b
    exact line_eq_of_mem_of_mem hY h0 (hκ (a * b)) (hY.mul_mem (hκ a) (hκ b))
  have hκ1 : κ (u2 1) = 0 := line_eq_of_mem_of_mem hY h0 (hκ (u2 1)) h1
  have hβ : κ (u2 β) = !![1, 0; 0, 0] := line_eq_of_mem_of_mem hY h0 (hκ (u2 β)) hx
  have hα : κ (u2 α) = !![0, 1; 0, 0] := line_eq_of_mem_of_mem hY h0 (hκ (u2 α)) hy
  exact no_cocycle hs hcoc hκ1 α β hβ hα

private theorem line_conj_mem (hY : TwistClosed Y) {X : Matrix (Fin 2) (Fin 2) K}
    {A : SpecialLinearGroup (Fin 2) K} (hX : (X, A) ∈ Y)
    {w : Matrix (Fin 2) (Fin 2) K} (hw : (w, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y) :
    ((A : Matrix (Fin 2) (Fin 2) K) * w, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  have hm := hY.mul_mem (hY.mul_mem hX hw) (hY.inv_mem hX)
  have key : ((A : Matrix (Fin 2) (Fin 2) K) * w, (1 : SpecialLinearGroup (Fin 2) K)) =
      (X + (A : Matrix (Fin 2) (Fin 2) K) * w +
        ((A * 1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          -(((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X),
        A * 1 * A⁻¹) := by
    refine Prod.ext ?_ ?_
    · simp only [mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, line_coe_mul_inv, Matrix.one_mul]
      abel
    · simp only [mul_one, mul_inv_cancel]
  rw [key]
  exact hm

private theorem line_stab (hY : TwistClosed Y) (hproj : hY.proj = ⊤)
    (A : SpecialLinearGroup (Fin 2) K) {w : Matrix (Fin 2) (Fin 2) K}
    (hw : (w, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y) :
    ((A : Matrix (Fin 2) (Fin 2) K) * w, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  obtain ⟨X, hX⟩ : ∃ X, (X, A) ∈ Y :=
    hY.mem_proj.mp (by rw [hproj]; exact Subgroup.mem_top A)
  exact line_conj_mem hY hX hw

private theorem line_sub_mem (hY : TwistClosed Y) {w w' : Matrix (Fin 2) (Fin 2) K}
    (hw : (w, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y)
    (hw' : (w', (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y) :
    (w - w', (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  have hn := hY.inv_mem hw'
  rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at hn
  have hm := hY.mul_mem hw hn
  rw [mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ← sub_eq_add_neg] at hm
  exact hm

private theorem line_full_of_mem (hY : TwistClosed Y) (hproj : hY.proj = ⊤)
    {W : Matrix (Fin 2) (Fin 2) K} (hW : (W, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y) (t : K) :
    ((!![t * W 1 0, t * W 1 1; 0, 0] : Matrix (Fin 2) (Fin 2) K),
      (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  have h1 := line_sub_mem hY (line_stab hY hproj (u2 t) hW) hW
  have e : (u2 t : Matrix (Fin 2) (Fin 2) K) * W - W = !![t * W 1 0, t * W 1 1; 0, 0] := by
    ext i j
    rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, u2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [e] at h1
  exact h1

theorem root_line_of_kernel (hY : TwistClosed Y) (hproj : hY.proj = ⊤)
    {X₀ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀ ≠ 0)
    (hker : (X₀, (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y) :
    ∃ a₁ a₂ : K, (a₁ ≠ 0 ∨ a₂ ≠ 0) ∧ ∀ t : K,
      ((!![t * a₁, t * a₂; 0, 0] : Matrix (Fin 2) (Fin 2) K),
        (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  by_cases hcase : X₀ 1 0 ≠ 0 ∨ X₀ 1 1 ≠ 0
  · exact ⟨X₀ 1 0, X₀ 1 1, hcase, fun t => line_full_of_mem hY hproj hker t⟩
  · push Not at hcase
    obtain ⟨h10, h11⟩ := hcase
    have hrow : X₀ 0 0 ≠ 0 ∨ X₀ 0 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hX₀
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hcon.1, hcon.2, h10, h11]
    have e2 : (l2 (1 : K) : Matrix (Fin 2) (Fin 2) K) * X₀ - X₀ = !![0, 0; X₀ 0 0, X₀ 0 1] := by
      ext i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, l2_coe]
      fin_cases i <;> fin_cases j <;> simp [h10, h11] <;> ring
    have hW : ((!![0, 0; X₀ 0 0, X₀ 0 1] : Matrix (Fin 2) (Fin 2) K),
        (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
      rw [← e2]
      exact line_sub_mem hY (line_stab hY hproj (l2 (1 : K)) hker) hker
    have h10' : (!![0, 0; X₀ 0 0, X₀ 0 1] : Matrix (Fin 2) (Fin 2) K) 1 0 = X₀ 0 0 := by
      simp
    have h11' : (!![0, 0; X₀ 0 0, X₀ 0 1] : Matrix (Fin 2) (Fin 2) K) 1 1 = X₀ 0 1 := by
      simp
    refine ⟨X₀ 0 0, X₀ 0 1, hrow, fun t => ?_⟩
    have h := line_full_of_mem hY hproj hW t
    rw [h10', h11'] at h
    exact h

theorem exists_root_line [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) {α β γ : K} (hαβ : α ∉ k ∨ β ∉ k) (hγ : γ ≠ 0)
    (hY : TwistClosed Y) (h1 : ((0 : Matrix (Fin 2) (Fin 2) K), u2 1) ∈ Y)
    (hx : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 β) ∈ Y)
    (hy : ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 α) ∈ Y)
    (hl : ((0 : Matrix (Fin 2) (Fin 2) K), l2 γ) ∈ Y) :
    ∃ a₁ a₂ : K, (a₁ ≠ 0 ∨ a₂ ≠ 0) ∧ ∀ t : K,
      ((!![t * a₁, t * a₂; 0, 0] : Matrix (Fin 2) (Fin 2) K),
        (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y := by
  have hproj := proj_eq_top hk hp hp2 hK hαβ hγ hY h1 hx hy hl
  have hs : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
    rcases hαβ with h | h
    · exact ⟨α, fun h0 => h (by rw [h0]; exact k.zero_mem),
        fun h1' => h (by rw [h1']; exact k.one_mem)⟩
    · exact ⟨β, fun h0 => h (by rw [h0]; exact k.zero_mem),
        fun h1' => h (by rw [h1']; exact k.one_mem)⟩
  obtain ⟨X₀, hX₀, hker⟩ := exists_kernel_ne_zero hs hY hproj h1 α β hx hy
  exact root_line_of_kernel hY hproj hX₀ hker

end CFSG.LieType.SeitzGeneration.OmegaF2
