module

public import CFSG.GF2Type.Aschbacher1976Full.WidthBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem closure_pair_normal_form {z x y : G} {F : Subgroup G} (hz2 : z ^ 2 = 1)
    (hzF : ∀ f ∈ F, z * f = f * z) (hsq : ∀ f ∈ F, f ^ 2 = 1 ∨ f ^ 2 = z)
    (hcomm : ∀ f ∈ F, ∀ g ∈ F, ⁅f, g⁆ = 1 ∨ ⁅f, g⁆ = z) (hx : x ∈ F) (hy : y ∈ F)
    {f : G} (hf : f ∈ closure ({x, y} : Set G)) :
    ∃ a b c : ℕ, a < 4 ∧ b < 4 ∧ c < 2 ∧ f = x ^ a * y ^ b * z ^ c := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have h4 : ∀ u ∈ F, u ^ 2 = 1 ∨ u ^ 2 = z → u ^ 4 = 1 := by
    intro u hu h
    have e : u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e]
    rcases h with h | h
    · rw [h, one_pow]
    · rw [h]
      exact hz2
  have hx4 : x ^ 4 = 1 := h4 x hx (hsq x hx)
  have hy4 : y ^ 4 = 1 := h4 y hy (hsq y hy)
  have hzx : z * x = x * z := hzF x hx
  have hzy : z * y = y * z := hzF y hy
  obtain ⟨e, hyx⟩ : ∃ e : ℕ, y * x = x * y * z ^ e := by
    rcases hcomm x hx y hy with h | h
    · refine ⟨0, ?_⟩
      have h' : x * y * x⁻¹ * y⁻¹ = 1 := by rw [← commutatorElement_def]; exact h
      have hxy : x * y = y * x := by
        calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
          _ = y * x := by rw [h', one_mul]
      rw [pow_zero, mul_one, hxy]
    · refine ⟨1, ?_⟩
      have h' : x * y * x⁻¹ * y⁻¹ = z := by rw [← commutatorElement_def]; exact h
      have h2 : x * y = z * (y * x) := by
        calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
          _ = z * (y * x) := by rw [h']
      have hxyF : x * y ∈ F := F.mul_mem hx hy
      calc y * x = z * (z * (y * x)) := by rw [← mul_assoc, hzz, one_mul]
        _ = z * (x * y) := by rw [← h2]
        _ = x * y * z := hzF (x * y) hxyF
        _ = x * y * z ^ 1 := by rw [pow_one]
  have hyb : ∀ n : ℕ, y ^ n * x = x * y ^ n * z ^ (n * e) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcz : z ^ e * y ^ n = y ^ n * z ^ e := ((Commute.pow_pow (show Commute z y from hzy) e n)).eq
      calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
        _ = y * (x * y ^ n * z ^ (n * e)) := by rw [ih]
        _ = (y * x) * y ^ n * z ^ (n * e) := by simp only [mul_assoc]
        _ = (x * y * z ^ e) * y ^ n * z ^ (n * e) := by rw [hyx]
        _ = x * y * (z ^ e * y ^ n) * z ^ (n * e) := by simp only [mul_assoc]
        _ = x * y * (y ^ n * z ^ e) * z ^ (n * e) := by rw [hcz]
        _ = x * y ^ (n + 1) * z ^ ((n + 1) * e) := by
          rw [pow_succ', show (n + 1) * e = e + n * e by ring, pow_add]
          simp only [mul_assoc]
  let PP : G → Prop := fun f => ∃ a b c : ℕ, a < 4 ∧ b < 4 ∧ c < 2 ∧ f = x ^ a * y ^ b * z ^ c
  have hS1 : ∀ f, PP f → PP (f * x) := by
    rintro f ⟨a, b, c, ha, hb, hc, rfl⟩
    refine ⟨(a + 1) % 4, b, (b * e + c) % 2, Nat.mod_lt _ (by norm_num), hb,
      Nat.mod_lt _ (by norm_num), ?_⟩
    have hzxc : z ^ c * x = x * z ^ c := ((Commute.pow_left (show Commute z x from hzx) c)).eq
    have h1 : x ^ a * y ^ b * z ^ c * x = x ^ (a + 1) * y ^ b * z ^ (b * e + c) := by
      calc x ^ a * y ^ b * z ^ c * x = x ^ a * y ^ b * (z ^ c * x) := by simp only [mul_assoc]
        _ = x ^ a * y ^ b * (x * z ^ c) := by rw [hzxc]
        _ = x ^ a * (y ^ b * x) * z ^ c := by simp only [mul_assoc]
        _ = x ^ a * (x * y ^ b * z ^ (b * e)) * z ^ c := by rw [hyb b]
        _ = x ^ (a + 1) * y ^ b * z ^ (b * e + c) := by
          rw [pow_succ, pow_add]
          simp only [mul_assoc]
    rw [h1, pow_eq_pow_mod (a + 1) hx4, pow_eq_pow_mod (b * e + c) hz2]
  have hS3 : ∀ f, PP f → PP (f * y) := by
    rintro f ⟨a, b, c, ha, hb, hc, rfl⟩
    refine ⟨a, (b + 1) % 4, c, ha, Nat.mod_lt _ (by norm_num), hc, ?_⟩
    have hzyc : z ^ c * y = y * z ^ c := ((Commute.pow_left (show Commute z y from hzy) c)).eq
    calc x ^ a * y ^ b * z ^ c * y = x ^ a * y ^ b * (z ^ c * y) := by simp only [mul_assoc]
      _ = x ^ a * y ^ b * (y * z ^ c) := by rw [hzyc]
      _ = x ^ a * y ^ (b + 1) * z ^ c := by rw [pow_succ]; simp only [mul_assoc]
      _ = x ^ a * y ^ ((b + 1) % 4) * z ^ c := by rw [pow_eq_pow_mod (b + 1) hy4]
  have hxinv : ∀ f, PP f → PP (f * x⁻¹) := by
    intro f hf
    have e3 : x⁻¹ = x * x * x := by
      apply inv_eq_of_mul_eq_one_right
      calc x * (x * x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hx4
    have e4 : f * x⁻¹ = ((f * x) * x) * x := by rw [e3]; simp only [mul_assoc]
    rw [e4]
    exact hS1 _ (hS1 _ (hS1 f hf))
  have hyinv : ∀ f, PP f → PP (f * y⁻¹) := by
    intro f hf
    have e3 : y⁻¹ = y * y * y := by
      apply inv_eq_of_mul_eq_one_right
      calc y * (y * y * y) = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hy4
    have e4 : f * y⁻¹ = ((f * y) * y) * y := by rw [e3]; simp only [mul_assoc]
    rw [e4]
    exact hS3 _ (hS3 _ (hS3 f hf))
  have hmem : ∀ f ∈ closure ({x, y} : Set G), PP f := by
    intro f hf
    refine Subgroup.closure_induction_right (p := fun f _ => PP f) ?_ ?_ ?_ hf
    · exact ⟨0, 0, 0, by norm_num, by norm_num, by norm_num, by simp⟩
    · intro f hf' g hg ih
      rcases Set.mem_insert_iff.mp hg with hg | hg
      · rw [hg]
        exact hS1 f ih
      · rw [Set.mem_singleton_iff.mp hg]
        exact hS3 f ih
    · intro f hf' g hg ih
      rcases Set.mem_insert_iff.mp hg with hg | hg
      · rw [hg]
        exact hxinv f ih
      · rw [Set.mem_singleton_iff.mp hg]
        exact hyinv f ih
  exact hmem f hf

theorem card_closure_pair_le [Finite G] {z x y : G} {F : Subgroup G} (hz2 : z ^ 2 = 1)
    (hzF : ∀ f ∈ F, z * f = f * z) (hsq : ∀ f ∈ F, f ^ 2 = 1 ∨ f ^ 2 = z)
    (hcomm : ∀ f ∈ F, ∀ g ∈ F, ⁅f, g⁆ = 1 ∨ ⁅f, g⁆ = z) (hx : x ∈ F) (hy : y ∈ F) :
    Nat.card (closure ({x, y} : Set G)) ≤ 32 := by
  classical
  let T : Finset G := (Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 2).image
    (fun p : ℕ × ℕ × ℕ => x ^ p.1 * y ^ p.2.1 * z ^ p.2.2)
  have hsub : (closure ({x, y} : Set G) : Set G) ⊆ (T : Set G) := by
    intro f hf
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := closure_pair_normal_form hz2 hzF hsq hcomm hx hy hf
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, b, c), ?_, rfl⟩)
    simp [Finset.mem_product, ha, hb, hc]
  calc Nat.card ↥(closure ({x, y} : Set G)) = (closure ({x, y} : Set G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ (T : Set G).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ (Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 2).card := Finset.card_image_le
    _ = 32 := by simp

end CFSG.GF2Type.Aschbacher1976Full.Width
