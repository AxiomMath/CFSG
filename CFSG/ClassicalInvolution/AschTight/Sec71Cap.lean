module

public import CFSG.ClassicalInvolution.AschTight.Sec71Basic
public import CFSG.ClassicalInvolution.AschTight.Sec71Setup

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ H ⊔ N) : ∃ a ∈ H, ∃ b ∈ N, x = a * b := by
  have hx' : x ∈ (H : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H N hLE]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_normalizer_Y₀ [Finite G] {W UV : Subgroup G} {g : G}
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgUV : g ∈ Subgroup.normalizer (UV : Set G)) :
    g ∈ Subgroup.normalizer ((UV ⊔ OCW W : Subgroup G) : Set G) :=
  Sec7.mem_normalizer_sup hgUV (Sec7.normalizer_le_normalizer_OCW W hgW)

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem zpowers_sup_zpowers (u v : G) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers v = Subgroup.closure {u, v} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.insert_eq]

theorem sup_sup_eq_closure (R T X : Subgroup G) :
    R ⊔ T ⊔ X = Subgroup.closure ((R : Set G) ∪ T ∪ X) := by
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
    Subgroup.closure_eq]

theorem step_of_table {Y₀ R T X : Subgroup G} {u v r t : G} {F : Set G} (hX : X ≤ Y₀)
    (hU : Subgroup.zpowers u ≤ Y₀) (hV : Subgroup.zpowers v ≤ Y₀)
    (hFN : ∀ f ∈ F, f ∈ Subgroup.normalizer (Y₀ : Set G))
    (hRc : ∀ x ∈ R, x ∈ Subgroup.zpowers u ∨ ∃ y ∈ Subgroup.zpowers u, x = y * r)
    (hTc : ∀ x ∈ T, x ∈ Subgroup.zpowers v ∨ ∃ y ∈ Subgroup.zpowers v, x = y * t)
    (hr : ∀ f ∈ F, ∃ y ∈ Y₀, ∃ f' ∈ F, f * r = y * f')
    (ht : ∀ f ∈ F, ∃ y ∈ Y₀, ∃ f' ∈ F, f * t = y * f') :
    ∀ f ∈ F, ∀ s ∈ (R : Set G) ∪ T ∪ X, ∃ y ∈ Y₀, ∃ f' ∈ F, f * s = y * f' := by
  have hY : ∀ f ∈ F, ∀ s ∈ Y₀, ∃ y ∈ Y₀, ∃ f' ∈ F, f * s = y * f' := fun f hf s hs =>
    ⟨f * s * f⁻¹, conj_mem_of_mem_normalizer (hFN f hf) hs, f, hf, by group⟩
  have hgen : ∀ {c g : G}, (∀ f ∈ F, ∃ y ∈ Y₀, ∃ f' ∈ F, f * g = y * f') → c ∈ Y₀ →
      ∀ f ∈ F, ∃ y ∈ Y₀, ∃ f' ∈ F, f * (c * g) = y * f' := by
    intro c g hg hc f hf
    obtain ⟨y, hy, f', hf', he⟩ := hg f hf
    refine ⟨f * c * f⁻¹ * y, Y₀.mul_mem (conj_mem_of_mem_normalizer (hFN f hf) hc) hy, f', hf', ?_⟩
    calc f * (c * g) = f * c * f⁻¹ * (f * g) := by group
      _ = f * c * f⁻¹ * (y * f') := by rw [he]
      _ = f * c * f⁻¹ * y * f' := by group
  intro f hf s hs
  rcases hs with (hsR | hsT) | hsX
  · rcases hRc s hsR with hsU | ⟨c, hc, rfl⟩
    · exact hY f hf s (hU hsU)
    · exact hgen hr (hU hc) f hf
  · rcases hTc s hsT with hsV | ⟨c, hc, rfl⟩
    · exact hY f hf s (hV hsV)
    · exact hgen ht (hV hc) f hf
  · exact hY f hf s (hX hsX)

theorem inf_eq_of_table [Finite G] {W R T : Subgroup G} {u v : G} {F : Set G}
    (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (huW : u ∈ W) (hvW : v ∈ W)
    (huR : u ∈ R) (hvT : v ∈ T) (hF1 : (1 : G) ∈ F)
    (hstep : ∀ f ∈ F, ∀ s ∈ (R : Set G) ∪ T ∪ OCW W,
      ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W, ∃ f' ∈ F, f * s = y * f')
    (hFc : ∀ f ∈ F, f * u = u * f → f * v = v * f → f = 1) :
    (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} := by
  have hUVW : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ W :=
    sup_le (Subgroup.zpowers_le.mpr huW) (Subgroup.zpowers_le.mpr hvW)
  apply le_antisymm
  · intro w hw
    obtain ⟨hwY, hwW⟩ := Subgroup.mem_inf.mp hw
    rw [sup_sup_eq_closure] at hwY
    have hS : ∀ s ∈ (R : Set G) ∪ T ∪ OCW W, s⁻¹ ∈ (R : Set G) ∪ T ∪ OCW W := by
      rintro s ((h | h) | h)
      · exact Or.inl (Or.inl (R.inv_mem h))
      · exact Or.inl (Or.inr (T.inv_mem h))
      · exact Or.inr ((OCW W).inv_mem h)
    obtain ⟨y, hy, f, hf, rfl⟩ := exists_mul_of_mem_closure hF1 hS hstep hwY
    have hYc : Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W ≤
        Subgroup.centralizer ({u, v} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro h (rfl | rfl)
        · rfl
        · exact hWc h hvW u huW
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro h (rfl | rfl)
        · exact hWc h huW v hvW
        · rfl
      · refine (OCW_le_centralizer W).trans (Subgroup.centralizer_le ?_)
        rintro h (rfl | rfl)
        · exact huW
        · exact hvW
    have hyc := Subgroup.mem_centralizer_iff.mp (hYc hy)
    have hyu : u * y = y * u := hyc u (by simp)
    have hyv : v * y = y * v := hyc v (by simp)
    have hwu : y * f * u = u * (y * f) := hWc _ hwW u huW
    have hwv : y * f * v = v * (y * f) := hWc _ hwW v hvW
    have hf1 : f = 1 := hFc f hf
      (by
        calc f * u = y⁻¹ * (y * f * u) := by group
          _ = y⁻¹ * (u * y) * f := by rw [hwu]; group
          _ = u * f := by rw [hyu]; group)
      (by
        calc f * v = y⁻¹ * (y * f * v) := by group
          _ = y⁻¹ * (v * y) * f := by rw [hwv]; group
          _ = v * f := by rw [hyv]; group)
    subst hf1
    rw [mul_one] at hwW ⊢
    have hLE : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
        Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
      hUVW.trans ((Subgroup.le_normalizer).trans (Sec7.normalizer_le_normalizer_OCW W))
    obtain ⟨c, hc, x, hx, rfl⟩ := exists_mul_of_mem_sup hLE hy
    have hxW : x ∈ W := by
      have := W.mul_mem (W.inv_mem (hUVW hc)) hwW
      rwa [inv_mul_cancel_left] at this
    have hx1 : x = 1 := by
      have : x ∈ OCW W ⊓ W := ⟨hx, hxW⟩
      rw [OCW_inf_eq_bot hW2] at this
      exact this
    rw [hx1, mul_one, ← zpowers_sup_zpowers]
    exact hc
  · rw [← zpowers_sup_zpowers]
    exact sup_le
      (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left huR), huW⟩)
      (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right hvT), hvW⟩)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
