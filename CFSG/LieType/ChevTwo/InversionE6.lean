module

public import CFSG.RankThree.E6.NativeTwoA2
public import CFSG.LieType.ChevTwo.InversionLinear

public section

namespace CFSG.LieType.ChevTwo.Inversion

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Matrix


variable {K : Type} [Field K]

noncomputable abbrev e6Twist (σ : K →+* K) : ModGL Tag.E6 K →* ModGL Tag.E6 K :=
  twistHom TwistTag.E6 K σ

theorem e6Rho_involutive (i : Fin Tag.E6.rank) : e6Rho (e6Rho i) = i := by
  revert i
  decide

theorem twistHom_xUnit_E6 (σ : K →+* K) (i : Fin Tag.E6.rank) (c : K) :
    e6Twist σ (xUnit Tag.E6 K i c) = xUnit Tag.E6 K (e6Rho i) (σ c) :=
  twistHom_xUnit TwistTag.E6 K σ i c

theorem twistHom_yUnit_E6 (σ : K →+* K) (i : Fin Tag.E6.rank) (c : K) :
    e6Twist σ (yUnit Tag.E6 K i c) = yUnit Tag.E6 K (e6Rho i) (σ c) :=
  twistHom_yUnit TwistTag.E6 K σ i c

theorem twistHom_mem_Q₂ (σ : K →+* K) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    e6Twist σ g ∈ subsystemGroup Tag.E6 K support56 := by
  obtain ⟨r0, r2, -, -⟩ := e6Rho_values
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [twistHom_xUnit_E6]
      rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [r0]; exact xUnit_mem_subsystemGroup e6Index_5_mem_support56 _
      · rw [r2]; exact xUnit_mem_subsystemGroup e6Index_4_mem_support56 _
    · rw [twistHom_yUnit_E6]
      rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [r0]; exact yUnit_mem_subsystemGroup e6Index_5_mem_support56 _
      · rw [r2]; exact yUnit_mem_subsystemGroup e6Index_4_mem_support56 _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem twistHom_twistHom (σ : K →+* K) {J : Set (Fin Tag.E6.rank)} {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K J) :
    e6Twist σ (e6Twist σ g) = baseChangeGL (σ.comp σ) g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [twistHom_xUnit_E6, twistHom_xUnit_E6, e6Rho_involutive, baseChangeGL_xUnit]
      rfl
    · rw [twistHom_yUnit_E6, twistHom_yUnit_E6, e6Rho_involutive, baseChangeGL_yUnit]
      rfl
  | one => simp only [map_one]
  | mul x y _ _ hx hy => simp only [map_mul, hx, hy]
  | inv x _ hx => simp only [map_inv, hx]

theorem subsystemGroup_le_adjointGroup_E6 (J : Set (Fin Tag.E6.rank)) :
    subsystemGroup Tag.E6 K J ≤ adjointGroup Tag.E6 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem m7_map_hom [CharP K 2] (σ : K →+* K) : (m7 K).map σ = m7 K := by
  have h : σ.comp (ι₂ K) = ι₂ K := RingHom.ext_zmod _ _
  rw [m7, RingHom.mapMatrix_apply, Matrix.map_map]
  exact congrArg (fun f : ZMod 2 →+* K => x7.map f) h

theorem e6_twistHom_inverts_order_seven [CharP K 2] (σ : K →+* K) :
    ∃ x ∈ adjointGroup Tag.E6 K, orderOf x = 7 ∧ e6Twist σ x = x⁻¹ := by
  classical
  set X7 : SpecialLinearGroup (Fin 3) K := ⟨m7 K, m7_det⟩ with hX7
  have hX7pow : X7 ^ 7 = 1 := by
    have h0 : (m7 K) ^ 7 = (1 : Matrix (Fin 3) (Fin 3) K) := m7_pow
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact h0
  obtain ⟨⟨g, hgQ⟩, hh⟩ := a2Rep₁_surjective (K := K) X7
  have hhM : a2Mat₁ g = m7 K := congrArg Subtype.val hh
  have hFg : e6Twist σ g ∈ subsystemGroup Tag.E6 K support56 :=
    twistHom_mem_Q₂ σ hgQ
  have hfix : baseChangeGL (σ.comp σ) g = g := by
    have hmem := baseChangeGL_mem_subsystemGroupE6 (σ.comp σ) hgQ
    have h1 : a2Rep₁ K ⟨baseChangeGL (σ.comp σ) g, hmem⟩ = a2Rep₁ K ⟨g, hgQ⟩ := by
      apply Subtype.ext
      change a2Mat₁ (baseChangeGL (σ.comp σ) g) = a2Mat₁ g
      rw [a2Mat₁_baseChangeGL (σ.comp σ) hgQ, hhM]
      exact m7_map_hom _
    exact congrArg Subtype.val (a2Rep₁_injective h1)
  have hFFg : e6Twist σ (e6Twist σ g) = g := by
    rw [twistHom_twistHom σ hgQ]; exact hfix
  have hcomm : Commute g (e6Twist σ g) := commute_Q₁_Q₂ hgQ hFg
  have hg7 : g ^ 7 = 1 := by
    have h1 : a2Rep₁ K (⟨g, hgQ⟩ ^ 7) = 1 := by rw [map_pow, hh, hX7pow]
    have h2 : (⟨g, hgQ⟩ : subsystemGroup Tag.E6 K support13) ^ 7 = 1 :=
      a2Rep₁_injective (h1.trans (map_one _).symm)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hFg7 : (e6Twist σ g) ^ 7 = 1 := by rw [← map_pow, hg7, map_one]
  refine ⟨g * (e6Twist σ g)⁻¹, ?_, ?_, ?_⟩
  · exact mul_mem (subsystemGroup_le_adjointGroup_E6 _ hgQ)
      (inv_mem (subsystemGroup_le_adjointGroup_E6 _ hFg))
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · rw [hcomm.inv_right.mul_pow, hg7, inv_pow, hFg7, inv_one, mul_one]
    · intro hx
      have hgF : g = e6Twist σ g := mul_inv_eq_one.1 hx
      have hgQ2 : g ∈ subsystemGroup Tag.E6 K support56 := hgF ▸ hFg
      have hcen : X7 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
        rw [Subgroup.mem_center_iff]
        intro Y
        obtain ⟨k, rfl⟩ := a2Rep₁_surjective (K := K) Y
        rw [← hh, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (commute_Q₁_Q₂ k.2 hgQ2).eq
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
      have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hr
      simp [hX7, m7, x7, ι₂, Matrix.scalar_apply, Matrix.diagonal_apply] at h02
  · rw [map_mul, map_inv, hFFg, _root_.mul_inv_rev, inv_inv]

end CFSG.LieType.ChevTwo.Inversion
