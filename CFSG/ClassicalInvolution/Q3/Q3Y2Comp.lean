module

public import CFSG.ClassicalInvolution.Q3.Q3Y2Twin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem eq_one_of_map_central_m11 {X : Type} [Group X] {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) (hc : c = CompData.m11) {x : X}
    (hx : x ∈ ψ.range) (hxc : ∀ y : X, x * y = y * x) : x = 1 := by
  subst hc
  have hbot := Q3.center_m11_eq_bot Q3.m11Facts
  obtain ⟨a, rfl⟩ := hx
  have hac : a ∈ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := by
    rw [Subgroup.mem_center_iff]
    intro m
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hbot ▸ hker
    apply hinj
    rw [map_mul, map_mul]
    exact (hxc (ψ m)).symm
  rw [hbot, Subgroup.mem_bot] at hac
  rw [hac, map_one]

theorem comp_commute3 {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i j : ι} (h : i ≠ j) {a b : X} (ha : a ∈ (D.hom i).range)
    (hb : b ∈ (D.hom j).range) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact D.commute i j h x y

theorem component_le_of_not_centralized {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (hTwin : ModelTwinGen3) {K₁ K₂ K₃ : Subgroup X}
    {ζ₁ ζ₂ θ₁ θ₂ θ₃ : X} (hK₁ : K₁ ∈ Φ) (hK₂ : K₂ ∈ Φ) (hK₃ : K₃ ∈ Φ) (hne : K₂ ≠ K₃)
    (hK₂₃ : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a) (hζ₁c : ∀ x : X, ζ₁ * x = x * ζ₁)
    (hζ₁sq : ζ₁ * ζ₁ = 1) (hζ₁ : ζ₁ ≠ 1) (hζ₂ : ζ₂ ≠ 1)
    (hζ₂sq : ζ₂ * ζ₂ = 1) (hζ₃ : ζ₁ * ζ₂ ≠ 1) (hζ₁K : ζ₁ ∈ K₁) (hζ₂K : ζ₂ ∈ K₂)
    (hζ₃K : ζ₁ * ζ₂ ∈ K₃) (hθ₁K : θ₁ ∈ K₁) (hθ₂K : θ₂ ∈ K₂) (hθ₃K : θ₃ ∈ K₃)
    (hθ₂ : θ₂ * θ₂ = ζ₂) (hθ₃ : θ₃ * θ₃ = ζ₁ * ζ₂) (hθ₁ζ : ζ₂ * θ₁ = θ₁ * ζ₂) (i : ι)
    (hi : ¬ ∀ q ∈ (D.hom i).range, ζ₂ * q = q * ζ₂) :
    (D.hom i).range ≤ Subgroup.centralizer ({ζ₂} : Set X) ⊔
      Subgroup.centralizer ({θ₁ * θ₂ * θ₃} : Set X) ⊔
      Subgroup.centralizer ({ζ₂ * (θ₁ * θ₂ * θ₃)} : Set X) := by
  obtain ⟨i₂, R₂, hR₂, hK₂e⟩ := D.fundamental K₂ hK₂
  obtain ⟨i₃, R₃, hR₃, hK₃e⟩ := D.fundamental K₃ hK₃
  obtain ⟨i₁, R₁, hR₁, hK₁e⟩ := D.fundamental K₁ hK₁
  have hmem : ∀ {j : ι} {K : Subgroup X} {R : Subgroup (D.kind j).G},
      K = R.map (D.hom j) → ∀ {x : X}, x ∈ K → x ∈ (D.hom j).range := by
    intro j K R hK x hx
    rw [hK] at hx
    exact Subgroup.map_le_range _ _ hx
  have hi₂ : i₂ = i := by
    by_contra h
    refine hi fun q hq => ?_
    exact comp_commute3 D h (hmem hK₂e hζ₂K) hq
  have hi₃ : i₃ = i := by
    by_contra h
    refine hi fun q hq => ?_
    have h3 : (ζ₁ * ζ₂) * q = q * (ζ₁ * ζ₂) := comp_commute3 D h (hmem hK₃e hζ₃K) hq
    calc ζ₂ * q = ζ₁ * ((ζ₁ * ζ₂) * q) := by
          calc ζ₂ * q = (ζ₁ * ζ₁) * ζ₂ * q := by rw [hζ₁sq, one_mul]
            _ = ζ₁ * ((ζ₁ * ζ₂) * q) := by group
      _ = ζ₁ * (q * (ζ₁ * ζ₂)) := by rw [h3]
      _ = (ζ₁ * q) * (ζ₁ * ζ₂) := by group
      _ = (q * ζ₁) * (ζ₁ * ζ₂) := by rw [hζ₁c q]
      _ = q * ((ζ₁ * ζ₁) * ζ₂) := by group
      _ = q * ζ₂ := by rw [hζ₁sq, one_mul]
  subst hi₂
  subst hi₃
  rcases D.valid i₃ with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
  ·
    have h24₂ : Nat.card (R₂.map (D.hom i₃)) = 24 := hK₂e ▸ D.card_eq K₂ hK₂
    have h24₃ : Nat.card (R₃.map (D.hom i₃)) = 24 := hK₃e ▸ D.card_eq K₃ hK₃
    have hne' : R₂.map (D.hom i₃) ≠ R₃.map (D.hom i₃) := hK₂e ▸ hK₃e ▸ hne
    have hθ₁ : ∀ q ∈ (D.hom i₃).range, θ₁ * q = q * θ₁ := by
      have hi₁ : i₁ ≠ i₃ := by
        intro h
        have hc₁ : D.kind i₁ = CompData.model t n := h ▸ hc
        obtain ⟨x, hx, hxζ⟩ : ζ₁ ∈ R₁.map (D.hom i₁) := hK₁e ▸ hζ₁K
        have := eq_one_of_map_central (D.hom i₁) (D.ker_le_center i₁) hfund hadm hc₁ hR₁ hx
          (fun y => by rw [hxζ]; exact hζ₁c y)
        exact hζ₁ (by rw [← hxζ, this, map_one])
      intro q hq
      exact comp_commute3 D hi₁ (hmem hK₁e hθ₁K) hq
    exact model_twin_component (D.hom i₃) (D.ker_le_center i₃) hfund hadm hc hTwin hR₂ hR₃ h24₂
      h24₃ hne' (hK₂e ▸ hK₃e ▸ hK₂₃) hζ₁c hζ₁ hζ₂ hζ₂sq hζ₃ hζ₁sq (hK₂e ▸ hζ₂K) (hK₃e ▸ hζ₃K)
      (hK₂e ▸ hθ₂K)
      (hK₃e ▸ hθ₃K) hθ₂ hθ₃ hθ₁ hθ₁ζ
  ·
    exfalso
    have h2 := Q3Y.eq_top_of_mem_fund_sl23 hc hR₂
    have h3 := Q3Y.eq_top_of_mem_fund_sl23 hc hR₃
    exact hne (by rw [hK₂e, hK₃e, h2, h3])
  ·
    exfalso
    have hz2 : ζ₂ ∈ (D.hom i₃).range := hmem hK₂e hζ₂K
    have hz3 : ζ₁ * ζ₂ ∈ (D.hom i₃).range := hmem hK₃e hζ₃K
    have hz1 : ζ₁ ∈ (D.hom i₃).range := by
      have := Subgroup.mul_mem _ hz3 hz2
      rwa [mul_assoc, hζ₂sq, mul_one] at this
    exact hζ₁ (eq_one_of_map_central_m11 (D.hom i₃) (D.ker_le_center i₃) hc hz1 hζ₁c)

end CFSG.ClassicalInvolution.Q3.Q3Y2
