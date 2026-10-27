module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilNFForm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilForm

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure U3PencilNF {G : Type} [Group G] (U₁ R₂ : Subgroup G) (t : G) (f : ℕ) {E : Type}
    [Field E] (σ : E →+* E) (a Y χ₁ χ₂ : G → E) (δ : E) : Prop where
  card : Nat.card E = (2 ^ f) ^ 2
  sigma : ∀ x, σ x = x ^ 2 ^ f
  sigma_sigma : ∀ x, σ (σ x) = x
  exists_ne : ∃ β, σ β ≠ β
  le : R₂ ≤ U₁
  card_R₂ : Nat.card R₂ = (2 ^ f) ^ 2
  sq_R₂ : ∀ r ∈ R₂, r ^ 2 = 1
  comm_mem : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ R₂
  sq_mem : ∀ x ∈ U₁, x ^ 2 ∈ R₂
  t_sq : t * t = 1
  t_mem : ∀ x ∈ U₁, t * x * t⁻¹ ∈ U₁
  t_mem_R₂ : ∀ r ∈ R₂, t * r * t⁻¹ ∈ R₂
  a_mul : ∀ x ∈ U₁, ∀ y ∈ U₁, a (x * y) = a x + a y
  Y_mul : ∀ x ∈ U₁, ∀ y ∈ U₁, Y (x * y) = Y x + Y y
  a_R₂ : ∀ r ∈ R₂, a r = 0
  Y_R₂ : ∀ r ∈ R₂, Y r = 0
  inj : ∀ x ∈ U₁, a x = 0 → Y x = 0 → x ∈ R₂
  surj : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ Y x = β
  a_t : ∀ x ∈ U₁, a (t * x * t⁻¹) = a x
  Y_t : ∀ x ∈ U₁, Y (t * x * t⁻¹) = Y x + a x
  chi₁_mul : ∀ r ∈ R₂, ∀ r' ∈ R₂, χ₁ (r * r') = χ₁ r + χ₁ r'
  chi₂_mul : ∀ r ∈ R₂, ∀ r' ∈ R₂, χ₂ (r * r') = χ₂ r + χ₂ r'
  chi_inj : ∀ r ∈ R₂, χ₁ r = 0 → χ₂ r = 0 → r = 1
  chi₁_t : ∀ r ∈ R₂, χ₁ (t * r * t⁻¹) = χ₁ r
  chi₂_t : ∀ r ∈ R₂, χ₂ (t * r * t⁻¹) = χ₁ r + χ₂ r
  delta : σ δ = δ
  comm₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₁ ⁅x, y⁆ = TraceForm.form σ (Y x) (a y) +
    TraceForm.form σ (a x) (Y y) + TraceForm.form σ (a x) (a y)
  comm₂ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₂ ⁅x, y⁆ = TraceForm.form σ (Y x) (Y y) +
    δ * TraceForm.form σ (a x) (a y)
  sq₁ : ∀ x ∈ U₁, χ₁ (x ^ 2) = TraceForm.form σ (Y x) (a x) + a x * σ (a x)
  sq₂ : ∀ x ∈ U₁, χ₂ (x ^ 2) = Y x * σ (Y x) + δ * (a x * σ (a x))

theorem pencilNF_eq_zero_of_form {E : Type} [Field E] [CharP E 2] {σ : E →+* E}
    (hσσ : ∀ x, σ (σ x) = x) {β₀ : E} (hβ₀ : σ β₀ ≠ β₀) {p : E}
    (h : ∀ p', TraceForm.form σ p p' = 0) : p = 0 := by
  by_contra hp
  have e := h (σ (β₀ / p))
  rw [TraceForm.form, hσσ, ← map_mul, mul_div_cancel₀ _ hp] at e
  apply hβ₀
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination e - β₀ * h2

theorem pencilNF_le_or_le_of_forall_mem {G : Type} [Group G] {A B W : Subgroup G}
    (h : ∀ x ∈ W, x ∈ A ∨ x ∈ B) : W ≤ A ∨ W ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨x, hxW, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨y, hyW, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have hxB := (h x hxW).resolve_left hxA
  have hyA := (h y hyW).resolve_right hyB
  rcases h (x * y) (mul_mem hxW hyW) with hA | hB
  · exact hxA (by simpa using mul_mem hA (inv_mem hyA))
  · exact hyB (by simpa using mul_mem (inv_mem hxB) hB)

theorem pencilNF_map_conj_map_conj {G : Type} [Group G] (H : Subgroup G) (k k' : G) :
    (H.map (MulAut.conj k').toMonoidHom).map (MulAut.conj k).toMonoidHom =
      H.map (MulAut.conj (k * k')).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem pencilNF_map_conj_eq {G : Type} [Group G] {H : Subgroup G} {k : G}
    (hk : k ∈ normalizer (H : Set G)) : H.map (MulAut.conj k).toMonoidHom = H := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hk y).mp hy
  · intro hx
    exact ⟨k⁻¹ * x * k, (mem_normalizer_iff''.mp hk x).mp hx, by group⟩

theorem pencilNF_mem_normalizer_of_map_eq {G : Type} [Group G] {H : Subgroup G} {k : G}
    (h : H.map (MulAut.conj k).toMonoidHom = H) : k ∈ normalizer (H : Set G) := by
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, rfl⟩
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    rwa [mul_left_cancel (mul_right_cancel hyx)] at hy

namespace U3PencilNF

variable {G : Type} [Group G] {U₁ R₂ : Subgroup G} {t : G} {f : ℕ} {E : Type}
  [Field E] {σ : E →+* E} {a Y χ₁ χ₂ : G → E} {δ : E}
  (hN : U3PencilNF U₁ R₂ t f σ a Y χ₁ χ₂ δ)
include hN

theorem a_inv {x : G} (hx : x ∈ U₁) : a x⁻¹ = -a x := by
  have h := hN.a_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hN.a_R₂ 1 (one_mem _)] at h
  linear_combination -h

theorem Y_inv {x : G} (hx : x ∈ U₁) : Y x⁻¹ = -Y x := by
  have h := hN.Y_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hN.Y_R₂ 1 (one_mem _)] at h
  linear_combination -h

theorem chi₁_one : χ₁ 1 = 0 := by
  have h := hN.chi₁_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem chi₂_one : χ₂ 1 = 0 := by
  have h := hN.chi₂_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem eq_of_chi_eq [CharP E 2] {r r' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂) (h₁ : χ₁ r = χ₁ r')
    (h₂ : χ₂ r = χ₂ r') : r = r' := by
  have hinv : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hN.sq_R₂ r' hr')
  have e1 : χ₁ (r * r'⁻¹) = 0 := by
    rw [hinv, hN.chi₁_mul r hr r' hr', h₁]
    exact CharTwo.add_self_eq_zero _
  have e2 : χ₂ (r * r'⁻¹) = 0 := by
    rw [hinv, hN.chi₂_mul r hr r' hr', h₂]
    exact CharTwo.add_self_eq_zero _
  rw [← mul_inv_eq_one]
  exact hN.chi_inj _ (mul_mem hr (inv_mem hr')) e1 e2

theorem t_conj_t (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [hN.t_sq]; group

theorem exists_line (ρ : E) : ∃ L : Subgroup G, ∀ x, x ∈ L ↔ x ∈ U₁ ∧ Y x = ρ * a x :=
  ⟨{ carrier := {x | x ∈ U₁ ∧ Y x = ρ * a x}
     mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
       rw [hN.Y_mul _ hx.1 _ hy.1, hN.a_mul _ hx.1 _ hy.1, hx.2, hy.2]
       ring⟩
     one_mem' := ⟨one_mem _, by rw [hN.Y_R₂ 1 (one_mem _), hN.a_R₂ 1 (one_mem _), mul_zero]⟩
     inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
       rw [hN.Y_inv hx.1, hN.a_inv hx.1, hx.2]
       ring⟩ }, fun x => Iff.rfl⟩

theorem card_line [Finite G] {ρ : E} {L : Subgroup G} (hL : ∀ x, x ∈ L ↔ x ∈ U₁ ∧ Y x = ρ * a x) :
    Nat.card L = (2 ^ f) ^ 4 := by
  classical
  choose s hsU hsa hsY using hN.surj
  let φ : E × R₂ → L := fun p => ⟨s p.1 (ρ * p.1) * p.2, (hL _).mpr
    ⟨mul_mem (hsU _ _) (hN.le p.2.2), by
      rw [hN.Y_mul _ (hsU _ _) _ (hN.le p.2.2), hN.a_mul _ (hsU _ _) _ (hN.le p.2.2),
        hN.Y_R₂ _ p.2.2, hN.a_R₂ _ p.2.2, hsY, hsa]
      ring⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨α, r⟩ ⟨α', r'⟩ h
      have h' : s α (ρ * α) * r = s α' (ρ * α') * r' := congrArg Subtype.val h
      have ha : α = α' := by
        have := congrArg a h'
        rwa [hN.a_mul _ (hsU _ _) _ (hN.le r.2), hN.a_mul _ (hsU _ _) _ (hN.le r'.2),
          hN.a_R₂ _ r.2, hN.a_R₂ _ r'.2, hsa, hsa, add_zero, add_zero] at this
      subst ha
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
    · rintro ⟨x, hx⟩
      obtain ⟨hxU, hxY⟩ := (hL x).mp hx
      have hm := inv_mem (hsU (a x) (ρ * a x))
      have hR : (s (a x) (ρ * a x))⁻¹ * x ∈ R₂ := hN.inj _ (mul_mem hm hxU)
        (by rw [hN.a_mul _ hm _ hxU, hN.a_inv (hsU _ _), hsa, neg_add_cancel])
        (by rw [hN.Y_mul _ hm _ hxU, hN.Y_inv (hsU _ _), hsY, hxY, neg_add_cancel])
      refine ⟨(a x, ⟨_, hR⟩), Subtype.ext ?_⟩
      show s (a x) (ρ * a x) * ((s (a x) (ρ * a x))⁻¹ * x) = x
      group
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_prod, hN.card, hN.card_R₂]
  ring

theorem map_t_line [CharP E 2] {ρ : E} {L L' : Subgroup G}
    (hL : ∀ x, x ∈ L ↔ x ∈ U₁ ∧ Y x = ρ * a x)
    (hL' : ∀ x, x ∈ L' ↔ x ∈ U₁ ∧ Y x = (ρ + 1) * a x) :
    L.map (MulAut.conj t).toMonoidHom = L' := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyU, hyY⟩ := (hL y).mp hy
    refine (hL' _).mpr ⟨hN.t_mem _ hyU, ?_⟩
    rw [hN.Y_t _ hyU, hN.a_t _ hyU, hyY]
    ring
  · intro hx
    obtain ⟨hxU, hxY⟩ := (hL' x).mp hx
    refine ⟨t * x * t⁻¹, (hL _).mpr ⟨hN.t_mem _ hxU, ?_⟩, hN.t_conj_t x⟩
    rw [hN.Y_t _ hxU, hN.a_t _ hxU, hxY]
    linear_combination a x * h2

theorem nonsplit [Finite G] [CharP E 2] {z : E} (hz : z ^ 2 + z = δ) (hzσ : σ z ≠ z) :
    ∃ X : Subgroup G, R₂ ≤ X ∧ X ≤ U₁ ∧ (∀ x ∈ X, x ^ 2 = 1) ∧ (2 ^ f) ^ 4 ≤ Nat.card X ∧
      (∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂) ∧
      ∀ W : Subgroup G, R₂ ≤ W → W ≤ U₁ → (∀ y ∈ W, y ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card W →
        W = X ∨ W = X.map (MulAut.conj t).toMonoidHom := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hσσ := hN.sigma_sigma
  have hσz : σ z = z + 1 := by
    have h1 : σ z ^ 2 + σ z = δ := by rw [← map_pow, ← map_add, hz, hN.delta]
    have h3 : (σ z - z) * (σ z + z + 1) = 0 := by linear_combination h1 - hz
    have h4 : σ z + z + 1 = 0 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hzσ)
    linear_combination h4 - (z + 1) * h2
  obtain ⟨X, hX⟩ := hN.exists_line z
  obtain ⟨X', hX'⟩ := hN.exists_line (z + 1)
  have hXt : X.map (MulAut.conj t).toMonoidHom = X' := hN.map_t_line hX hX'
  have hcardX := hN.card_line hX
  have hcardX' := hN.card_line hX'
  refine ⟨X, fun r hr => (hX r).mpr ⟨hN.le hr, by rw [hN.Y_R₂ r hr, hN.a_R₂ r hr, mul_zero]⟩,
    fun x hx => ((hX x).mp hx).1, ?_, hcardX.ge, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxU, hxY⟩ := (hX x).mp hx
    refine hN.chi_inj _ (hN.sq_mem x hxU) ?_ ?_
    · rw [hN.sq₁ x hxU, hxY, TraceForm.form, map_mul, hσz]
      linear_combination (z + 1) * a x * σ (a x) * h2
    · rw [hN.sq₂ x hxU, hxY, map_mul, hσz, ← hz]
      linear_combination (z ^ 2 + z) * a x * σ (a x) * h2
  · intro x hx htx
    obtain ⟨hxU, hxY⟩ := (hX x).mp hx
    obtain ⟨-, htY⟩ := (hX _).mp htx
    rw [hN.Y_t _ hxU, hN.a_t _ hxU, hxY] at htY
    have ha : a x = 0 := by linear_combination htY
    exact hN.inj x hxU ha (by rw [hxY, ha, mul_zero])
  · intro W hRW hWU hW2 hcardW
    have key : ∀ x ∈ W, x ∈ X ∨ x ∈ X' := by
      intro x hx
      have hxU := hWU hx
      have e₁ := hN.sq₁ x hxU
      have e₂ := hN.sq₂ x hxU
      rw [hW2 x hx, hN.chi₁_one, TraceForm.form] at e₁
      rw [hW2 x hx, hN.chi₂_one] at e₂
      by_cases ha : a x = 0
      · have hY : Y x = 0 := by
          rw [ha, zero_mul, mul_zero, add_zero] at e₂
          rcases mul_eq_zero.mp e₂.symm with h | h
          · exact h
          · rw [← hσσ (Y x), h, map_zero]
        exact Or.inl ((hX x).mpr ⟨hxU, by rw [hY, ha, mul_zero]⟩)
      · have hσa : σ (a x) ≠ 0 := fun h => ha (by rw [← hσσ (a x), h, map_zero])
        have e₃ : σ (a x) * (Y x ^ 2 + a x * Y x + δ * a x ^ 2) = 0 := by
          linear_combination (-Y x) * e₁ + a x * e₂ + δ * a x ^ 2 * σ (a x) * h2
        have e₄ := (mul_eq_zero.mp e₃).resolve_left hσa
        have e₅ : (Y x - z * a x) * (Y x - (z + 1) * a x) = 0 := by
          linear_combination e₄ + a x ^ 2 * hz - (z + 1) * a x * Y x * h2
        rcases mul_eq_zero.mp e₅ with h | h
        · exact Or.inl ((hX x).mpr ⟨hxU, by linear_combination h⟩)
        · exact Or.inr ((hX' x).mpr ⟨hxU, by linear_combination h⟩)
    rcases pencilNF_le_or_le_of_forall_mem key with hle | hle
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardX]; exact hcardW))
    · exact Or.inr (hXt ▸ Subgroup.eq_of_le_of_card_ge hle (by rw [hcardX']; exact hcardW))

theorem mem_line_of_comm [CharP E 2] {r : E} (hr : r ^ 2 + r = δ) {Z : Subgroup G}
    (hZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) {x : G} (hx : x ∈ U₁)
    (hxZ : ∀ y ∈ U₁, ⁅x, y⁆ ∈ Z) : Y x = r * a x ∨ Y x = (r + 1) * a x := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨β₀, hβ₀⟩ := hN.exists_ne
  have hσσ := hN.sigma_sigma
  have hA : ∀ y ∈ U₁, χ₁ ⁅x, y⁆ = 0 → χ₂ ⁅x, y⁆ = 0 := by
    intro y hy h1
    have hc := hN.comm_mem x hx y hy
    have heq : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆ := hN.eq_of_chi_eq (hN.t_mem_R₂ _ hc) hc
      (hN.chi₁_t _ hc) (by rw [hN.chi₂_t _ hc, h1, zero_add])
    have h1' : ⁅x, y⁆ = 1 := hZ _ (hxZ y hy) (by rw [heq]; exact hxZ y hy)
    rw [h1', hN.chi₂_one]
  choose s hsU hsa hsY using hN.surj
  by_cases ha : a x = 0
  · left
    have hY : Y x = 0 := pencilNF_eq_zero_of_form hσσ hβ₀ fun p => by
      have h1 : χ₁ ⁅x, s 0 p⁆ = 0 := by
        rw [hN.comm₁ x hx _ (hsU _ _), ha, hsa, hsY]
        simp [TraceForm.form]
      have h := hA _ (hsU _ _) h1
      rw [hN.comm₂ x hx _ (hsU _ _), ha, hsa, hsY] at h
      simpa [TraceForm.form] using h
    rw [hY, ha, mul_zero]
  · obtain ⟨c, hAc⟩ : ∃ c, a x * c = Y x + a x := ⟨(Y x + a x) / a x, mul_div_cancel₀ _ ha⟩
    have hAcσ : σ (a x) * σ c = σ (Y x) + σ (a x) := by rw [← map_mul, hAc, map_add]
    have hkey : ∀ p, TraceForm.form σ (Y x * c + δ * a x) p = 0 := by
      intro p
      have h1 : χ₁ ⁅x, s p (σ c * p)⁆ = 0 := by
        rw [hN.comm₁ x hx _ (hsU _ _), hsa, hsY]
        simp only [TraceForm.form, map_mul, hσσ]
        linear_combination σ p * hAc + p * hAcσ +
          (Y x * σ p + σ (Y x) * p + a x * σ p + σ (a x) * p) * h2
      have h := hA _ (hsU _ _) h1
      rw [hN.comm₂ x hx _ (hsU _ _), hsa, hsY] at h
      simp only [TraceForm.form, map_mul, map_add, hσσ, hN.delta] at h ⊢
      linear_combination h
    have h0 := pencilNF_eq_zero_of_form hσσ hβ₀ hkey
    have e : Y x ^ 2 + a x * Y x + δ * a x ^ 2 = 0 := by
      linear_combination a x * h0 - Y x * hAc
    have e' : (Y x - r * a x) * (Y x - (r + 1) * a x) = 0 := by
      linear_combination e + a x ^ 2 * hr - (r + 1) * a x * Y x * h2
    rcases mul_eq_zero.mp e' with h | h
    · left
      linear_combination h
    · right
      linear_combination h

theorem comm_line_cond [CharP E 2] {ρ : E} (hρ : ρ ^ 2 + ρ = δ) (hρσ : σ ρ = ρ)
    {J : Subgroup G} (hJ : ∀ x, x ∈ J ↔ x ∈ U₁ ∧ Y x = ρ * a x) :
    ∀ z ∈ ⁅J, U₁⁆, t * z * t⁻¹ ∈ ⁅J, U₁⁆ → z = 1 := by
  have hinv : ∀ z ∈ R₂, z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hN.sq_R₂ z hz)
  obtain ⟨Zρ, hZρ⟩ : ∃ Zρ : Subgroup G, ∀ z, z ∈ Zρ ↔ z ∈ R₂ ∧ χ₂ z = ρ * χ₁ z :=
    ⟨{ carrier := {z | z ∈ R₂ ∧ χ₂ z = ρ * χ₁ z}
       mul_mem' := fun {z z'} hz hz' => ⟨mul_mem hz.1 hz'.1, by
         rw [hN.chi₂_mul _ hz.1 _ hz'.1, hN.chi₁_mul _ hz.1 _ hz'.1, hz.2, hz'.2]
         ring⟩
       one_mem' := ⟨one_mem _, by rw [hN.chi₂_one, hN.chi₁_one, mul_zero]⟩
       inv_mem' := fun {z} hz => ⟨inv_mem hz.1, by rw [hinv z hz.1]; exact hz.2⟩ },
      fun z => Iff.rfl⟩
  have hle : ⁅J, U₁⁆ ≤ Zρ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨hxU, hxY⟩ := (hJ x).mp hx
    refine (hZρ _).mpr ⟨hN.comm_mem x hxU y hy, ?_⟩
    rw [hN.comm₁ x hxU y hy, hN.comm₂ x hxU y hy, hxY]
    simp only [TraceForm.form, map_mul, hρσ]
    linear_combination (-(a x * σ (a y) + σ (a x) * a y)) * hρ
  intro z hz htz
  obtain ⟨hzR, hz2⟩ := (hZρ z).mp (hle hz)
  obtain ⟨-, htz2⟩ := (hZρ _).mp (hle htz)
  rw [hN.chi₂_t z hzR, hN.chi₁_t z hzR] at htz2
  have h1 : χ₁ z = 0 := by linear_combination htz2 - hz2
  exact hN.chi_inj z hzR h1 (by rw [hz2, h1, mul_zero])

theorem eq_line_of_comm [Finite G] [CharP E 2] {r : E} (hr : r ^ 2 + r = δ) {J₁ J₂ : Subgroup G}
    (hJ₁ : ∀ x, x ∈ J₁ ↔ x ∈ U₁ ∧ Y x = r * a x)
    (hJ₂ : ∀ x, x ∈ J₂ ↔ x ∈ U₁ ∧ Y x = (r + 1) * a x) {J : Subgroup G} (hJU : J ≤ U₁)
    (hJcard : (2 ^ f) ^ 4 ≤ Nat.card J) {Z : Subgroup G} (hZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1)
    (hJZ : ∀ x ∈ J, ∀ y ∈ U₁, ⁅x, y⁆ ∈ Z) : J = J₁ ∨ J = J₂ := by
  have key : ∀ x ∈ J, x ∈ J₁ ∨ x ∈ J₂ := fun x hx =>
    (hN.mem_line_of_comm hr hZ (hJU hx) (hJZ x hx)).imp (fun h => (hJ₁ x).mpr ⟨hJU hx, h⟩)
      (fun h => (hJ₂ x).mpr ⟨hJU hx, h⟩)
  rcases pencilNF_le_or_le_of_forall_mem key with hle | hle
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [hN.card_line hJ₁]; exact hJcard))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by rw [hN.card_line hJ₂]; exact hJcard))

theorem map_conj_eq [Finite G] [CharP E 2] {r : E} (hr : r ^ 2 + r = δ) {J₁ J₂ : Subgroup G}
    (hJ₁ : ∀ x, x ∈ J₁ ↔ x ∈ U₁ ∧ Y x = r * a x)
    (hJ₂ : ∀ x, x ∈ J₂ ↔ x ∈ U₁ ∧ Y x = (r + 1) * a x) {ρ : E} (hρ : ρ ^ 2 + ρ = δ)
    (hρσ : σ ρ = ρ) {H : Subgroup G} (hH : ∀ x, x ∈ H ↔ x ∈ U₁ ∧ Y x = ρ * a x) {k : G}
    (hkU : k ∈ normalizer (U₁ : Set G)) (hkt : k * t = t * k) :
    H.map (MulAut.conj k).toMonoidHom = J₁ ∨ H.map (MulAut.conj k).toMonoidHom = J₂ := by
  refine hN.eq_line_of_comm hr hJ₁ hJ₂ ?_ ?_ (Z := ⁅H, U₁⁆.map (MulAut.conj k).toMonoidHom) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hkU x).mp ((hH x).mp hx).1
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hN.card_line hH]
  · intro w hw htw
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    obtain ⟨z', hz', he⟩ := mem_map.mp htw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he ⊢
    have e1 : t * (k * z * k⁻¹) * t⁻¹ = k * (t * z * t⁻¹) * k⁻¹ := by
      calc t * (k * z * k⁻¹) * t⁻¹ = (t * k) * z * (t * k)⁻¹ := by group
        _ = (k * t) * z * (k * t)⁻¹ := by rw [hkt]
        _ = k * (t * z * t⁻¹) * k⁻¹ := by group
    rw [e1] at he
    have hz'' : z' = t * z * t⁻¹ := mul_left_cancel (mul_right_cancel he)
    rw [hN.comm_line_cond hρ hρσ hH z hz (hz'' ▸ hz'), mul_one, mul_inv_cancel]
  · rintro _ ⟨x, hx, rfl⟩ y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨⁅x, k⁻¹ * y * k⁆, Subgroup.commutator_mem_commutator hx
      ((mem_normalizer_iff''.mp hkU y).mp hy), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
    group

theorem split [Finite G] [CharP E 2] {r : E} (hr : r ^ 2 + r = δ) (hrσ : σ r = r) :
    ∃ Z J : Subgroup G, (∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) ∧
      (∀ k : G, k ∈ normalizer (U₁ : Set G) → k ∈ normalizer (R₂ : Set G) → k * t = t * k →
        Odd (orderOf k) → k ∈ normalizer (Z : Set G)) ∧
      J ≤ U₁ ∧ (∀ x ∈ J, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (2 ^ f) ^ 4 ≤ Nat.card J := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hr' : (r + 1) ^ 2 + (r + 1) = δ := by linear_combination hr + (r + 1) * h2
  have hrσ' : σ (r + 1) = r + 1 := by rw [map_add, map_one, hrσ]
  obtain ⟨J₁, hJ₁⟩ := hN.exists_line r
  obtain ⟨J₂, hJ₂⟩ := hN.exists_line (r + 1)
  have hne : J₁ ≠ J₂ := by
    intro heq
    obtain ⟨x, hxU, hxa, hxY⟩ := hN.surj 1 r
    have hx : x ∈ J₁ := (hJ₁ x).mpr ⟨hxU, by rw [hxY, hxa, mul_one]⟩
    rw [heq] at hx
    have := ((hJ₂ x).mp hx).2
    rw [hxY, hxa, mul_one] at this
    exact one_ne_zero (by linear_combination -this)
  refine ⟨⁅J₁, U₁⁆, J₁, hN.comm_line_cond hr hrσ hJ₁, ?_, fun x hx => ((hJ₁ x).mp hx).1,
    fun x hx y hy => by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hx hy, (hN.card_line hJ₁).ge⟩
  intro k hkU _ hkt hodd
  have hφ₁ := hN.map_conj_eq hr hJ₁ hJ₂ hr hrσ hJ₁ hkU hkt
  have hφ₂ := hN.map_conj_eq hr hJ₁ hJ₂ hr' hrσ' hJ₂ hkU hkt
  have hsq : J₁.map (MulAut.conj (k * k)).toMonoidHom = J₁ := by
    rw [← pencilNF_map_conj_map_conj]
    rcases hφ₁ with h1 | h1
    · rw [h1, h1]
    · rw [h1]
      rcases hφ₂ with h3 | h3
      · exact h3
      · exact absurd (Subgroup.map_injective (MulAut.conj k).injective (h1.trans h3.symm)) hne
  obtain ⟨m, hm⟩ := hodd
  have hk : (k * k) ^ (m + 1) = k := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hkJ : k ∈ normalizer (J₁ : Set G) :=
    hk ▸ pow_mem (pencilNF_mem_normalizer_of_map_eq hsq) (m + 1)
  refine pencilNF_mem_normalizer_of_map_eq ?_
  rw [Subgroup.map_commutator, pencilNF_map_conj_eq hkJ, pencilNF_map_conj_eq hkU]

theorem dichotomy [Finite G] [CharP E 2] :
    (∃ Z J : Subgroup G, (∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) ∧
      (∀ k : G, k ∈ normalizer (U₁ : Set G) → k ∈ normalizer (R₂ : Set G) → k * t = t * k →
        Odd (orderOf k) → k ∈ normalizer (Z : Set G)) ∧
      J ≤ U₁ ∧ (∀ x ∈ J, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (2 ^ f) ^ 4 ≤ Nat.card J) ∨
    ∃ X : Subgroup G, R₂ ≤ X ∧ X ≤ U₁ ∧ (∀ x ∈ X, x ^ 2 = 1) ∧ (2 ^ f) ^ 4 ≤ Nat.card X ∧
      (∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂) ∧
      ∀ W : Subgroup G, R₂ ≤ W → W ≤ U₁ → (∀ y ∈ W, y ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card W →
        W = X ∨ W = X.map (MulAut.conj t).toMonoidHom := by
  obtain ⟨β₀, hβ₀⟩ := hN.exists_ne
  obtain ⟨z, hz⟩ := pencilNF_exists_sq_add_self_eq hN.sigma hN.sigma_sigma hβ₀ hN.delta
  by_cases hzσ : σ z = z
  · exact Or.inl (hN.split hz hzσ)
  · exact Or.inr (hN.nonsplit hz hzσ)

end U3PencilNF

section Certificates

theorem u3EndingPencilFormInput : U3EndingPencilFormInput := by
  intro G _ _ L f t T R₂ U₁ s E _ _ _ σ u w d μ a b χ₁ χ₂ hD hP h1 h2 h3 h4 h5 h6
  have hS := hP.semilinear
  have hf : 2 ≤ f := hD.start.two_le
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, δ, hδ, hcomm, hsq⟩ := hP.exists_normalForm hf hD.r2 hD.u1 h1 h2 h3 h4 h5 h6
  have hU := hD.u1
  have hR := hD.r2
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have hbR : ∀ r ∈ R₂, b r = 0 := fun r hr => by
    have := h2 1 (one_mem _) r hr
    rwa [one_mul, hS.coords.u_one] at this
  have haR : ∀ r ∈ R₂, a r = 0 := fun r hr => hP.a_eq_zero_of_mem hRU hR.tN hr
  have hN : U3PencilNF U₁ R₂ t f σ a (fun x => b x + σ g * a x) χ₁ χ₂ δ :=
    { card := hS.card
      sigma := hS.sigma
      sigma_sigma := TraceForm.sigma_sigma hS.sigma hS.card
      exists_ne := pencilNF_exists_sigma_ne hq hS.card hS.card_fixed
      le := hRU
      card_R₂ := hR.card
      sq_R₂ := hU.sq_R₂
      comm_mem := fun x hx y hy => by
        rw [commutatorElement_def]
        exact hU.comm_mem x hx y hy
      sq_mem := hU.sq_mem
      t_sq := by
        rw [← sq]
        exact hR.t_sq
      t_mem := fun x hx => (mem_normalizer_iff.mp htU x).mp hx
      t_mem_R₂ := hR.tN
      a_mul := hP.a_mul
      Y_mul := fun x hx y hy => by
        show b (x * y) + σ g * a (x * y) = (b x + σ g * a x) + (b y + σ g * a y)
        rw [h1 x hx y hy, hP.a_mul x hx y hy]
        ring
      a_R₂ := haR
      Y_R₂ := fun r hr => by
        show b r + σ g * a r = 0
        rw [hbR r hr, haR r hr, mul_zero, add_zero]
      inj := fun x hx hax hYx => h5 x hx hax (by
        have : b x + σ g * a x = 0 := hYx
        rwa [hax, mul_zero, add_zero] at this)
      surj := fun α β => by
        obtain ⟨x, hx, hxa, hxb⟩ := h6 α (β - σ g * α)
        refine ⟨x, hx, hxa, ?_⟩
        show b x + σ g * a x = β
        rw [hxa, hxb]
        ring
      a_t := hP.a_conj_t
      Y_t := fun x hx => by
        show b (t * x * t⁻¹) + σ g * a (t * x * t⁻¹) = (b x + σ g * a x) + a x
        rw [h4 x hx, hP.a_conj_t x hx]
        ring
      chi₁_mul := hP.chi₁_mul
      chi₂_mul := hP.chi₂_mul
      chi_inj := hP.chi_inj
      chi₁_t := hP.chi₁_conj_t
      chi₂_t := hP.chi₂_conj_t
      delta := hδ
      comm₁ := fun x hx y hy => (hcomm x hx y hy).1
      comm₂ := fun x hx y hy => (hcomm x hx y hy).2
      sq₁ := fun x hx => (hsq x hx).1
      sq₂ := fun x hx => (hsq x hx).2 }
  rcases hN.dichotomy with ⟨Z, J, hZ, hk, hJU, hJZ, hJcard⟩ | hX
  · refine Or.inl ⟨Z, J, hZ, fun k hkL hkT hodd => ?_, hJU, hJZ, hJcard⟩
    obtain ⟨hkR, hkU⟩ := hD.mem_normalizer_of_mem_borel hkL hkT
    exact hk k hkU hkR (mem_centralizer_iff.mp hD.start.mem k hkL) hodd
  · exact Or.inr hX

theorem u3EndingInput_of_sylow (hsyl : U3EndingSylowInput) : U3EndingInput :=
  u3EndingInput_of_form u3EndingPencilFormInput hsyl

end Certificates

end CFSG.SeitzReduction.RankOne
