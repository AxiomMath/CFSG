module

public import CFSG.ClassicalInvolution.Q3.Q3WFin
public import CFSG.ClassicalInvolution.Q3.Q3WL65
public import CFSG.ClassicalInvolution.Q3.Q3ZAutFin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.ClassicalInvolution.WeakCT (blockSL B12 B23 LinearBlockStandardPair pair_normalize)
open CFSG.ClassicalInvolution.Q3.Q3W (xp xm b0 b1 comm_b0_xp_iff comm_b0_xm_iff xm_cases xp_cases
  center_eq_bot slEquiv nonempty_ringEquiv_zmod_three)
open CFSG.ClassicalInvolution.Q3.Q3Z (autXp autXm hom_ext_of_gens)
open scoped MatrixGroups

theorem fixes_of_cube {X : Type} [Group X] {s w : X} (hs3 : s ^ 3 = 1)
    (h : s * w * s⁻¹ = 1 ∨ s * w * s⁻¹ = w ∨ s * w * s⁻¹ = w⁻¹) : s * w * s⁻¹ = w := by
  rcases h with h | h | h
  · have hw : w = 1 := by
      have h' := congrArg (fun x => s⁻¹ * x * s) h
      simpa [mul_assoc] using h'
    rw [hw]
    group
  · exact h
  · have h2 : s * w⁻¹ * s⁻¹ = w := by
      have h' := congrArg (fun x => x⁻¹) h
      simpa [mul_assoc] using h'
    have h3 : s * (s * w * s⁻¹) * s⁻¹ = w := by rw [h, h2]
    have h3' : s * s * w * s⁻¹ * s⁻¹ = w := by simpa [mul_assoc] using h3
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul] at h3'
    have hs3' : s * s * s = 1 := by simpa [pow_succ, mul_assoc] using hs3
    have hs : s⁻¹ = s * s := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc]
      exact hs3'
    rw [hs]
    calc s * w * (s * s) = s * (w * s * s) := by simp [mul_assoc]
      _ = s * (s * s * w) := by rw [h3']
      _ = s * s * s * w := by simp [mul_assoc]
      _ = w := by rw [hs3', one_mul]

theorem commutes_of_cube_one_zmod {X : Type} [Group X] (θ : SL(3, ZMod 3) →* X)
    (hθ : θ.ker ≤ Subgroup.center SL(3, ZMod 3)) {s : X} (hs3 : s ^ 3 = 1)
    (hsK : ∀ A : SL(2, ZMod 3), s * θ (b0 A) * s⁻¹ = θ (b0 A))
    (hsN : ∀ B : SL(2, ZMod 3), ∃ B' : SL(2, ZMod 3), s * θ (b1 B) * s⁻¹ = θ (b1 B')) :
    ∀ B : SL(2, ZMod 3), s * θ (b1 B) * s⁻¹ = θ (b1 B) := by
  have hcomm : ∀ g h : SL(3, ZMod 3), θ g * θ h = θ h * θ g → g * h = h * g := fun g h hc => by
    have hk : g * h * (h * g)⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc]
      group
    have := hθ hk
    rw [center_eq_bot, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.mp this
  have hu : s * θ (b1 (xm 1)) * s⁻¹ = θ (b1 (xm 1)) := by
    obtain ⟨B', hB'⟩ := hsN (xm 1)
    have ha := hsK (xp 1)
    have hcu : b0 (xp 1) * b1 (xm 1) = b1 (xm 1) * b0 (xp 1) :=
      (comm_b0_xp_iff 1 one_ne_zero (xm 1)).2 ⟨1, rfl⟩
    have hc : θ (b0 (xp 1)) * θ (b1 B') = θ (b1 B') * θ (b0 (xp 1)) := by
      rw [← hB']
      calc θ (b0 (xp 1)) * (s * θ (b1 (xm 1)) * s⁻¹)
          = (s * θ (b0 (xp 1)) * s⁻¹) * (s * θ (b1 (xm 1)) * s⁻¹) := by rw [ha]
        _ = s * (θ (b0 (xp 1) * b1 (xm 1))) * s⁻¹ := by simp only [map_mul]; group
        _ = s * (θ (b1 (xm 1) * b0 (xp 1))) * s⁻¹ := by rw [hcu]
        _ = (s * θ (b1 (xm 1)) * s⁻¹) * (s * θ (b0 (xp 1)) * s⁻¹) := by simp only [map_mul]; group
        _ = (s * θ (b1 (xm 1)) * s⁻¹) * θ (b0 (xp 1)) := by rw [ha]
    obtain ⟨t, rfl⟩ := (comm_b0_xp_iff 1 one_ne_zero B').1 (hcomm _ _ hc)
    apply fixes_of_cube hs3
    rw [hB']
    rcases xm_cases t with h | h | h <;> rw [h]
    · left; simp
    · right; left; rfl
    · right; right; simp
  have hv : s * θ (b1 (xp 1)) * s⁻¹ = θ (b1 (xp 1)) := by
    obtain ⟨B', hB'⟩ := hsN (xp 1)
    have ha := hsK (xm 1)
    have hcu : b0 (xm 1) * b1 (xp 1) = b1 (xp 1) * b0 (xm 1) :=
      (comm_b0_xm_iff 1 one_ne_zero (xp 1)).2 ⟨1, rfl⟩
    have hc : θ (b0 (xm 1)) * θ (b1 B') = θ (b1 B') * θ (b0 (xm 1)) := by
      rw [← hB']
      calc θ (b0 (xm 1)) * (s * θ (b1 (xp 1)) * s⁻¹)
          = (s * θ (b0 (xm 1)) * s⁻¹) * (s * θ (b1 (xp 1)) * s⁻¹) := by rw [ha]
        _ = s * (θ (b0 (xm 1) * b1 (xp 1))) * s⁻¹ := by simp only [map_mul]; group
        _ = s * (θ (b1 (xp 1) * b0 (xm 1))) * s⁻¹ := by rw [hcu]
        _ = (s * θ (b1 (xp 1)) * s⁻¹) * (s * θ (b0 (xm 1)) * s⁻¹) := by simp only [map_mul]; group
        _ = (s * θ (b1 (xp 1)) * s⁻¹) * θ (b0 (xm 1)) := by rw [ha]
    obtain ⟨t, rfl⟩ := (comm_b0_xm_iff 1 one_ne_zero B').1 (hcomm _ _ hc)
    apply fixes_of_cube hs3
    rw [hB']
    rcases xp_cases t with h | h | h <;> rw [h]
    · left; simp
    · right; left; rfl
    · right; right; simp
  have hext : ((MulAut.conj s).toMonoidHom.comp (θ.comp (blockSL (ZMod 3) 3 2 1 (by omega)))) =
      θ.comp (blockSL (ZMod 3) 3 2 1 (by omega)) := by
    apply hom_ext_of_gens
    · exact hv
    · exact hu
  intro B
  exact DFunLike.congr_fun hext B

section Transport

variable {K K' : Type} [Field K] [Field K']

theorem slMap_blockSL_zero' (φ : K →+* K') (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL K 3 2 0 (by omega) A) =
      blockSL K' 3 2 0 (by omega) (Matrix.SpecialLinearGroup.map φ A) := by
  apply Subtype.ext
  show φ.mapMatrix ((blockSL K 3 2 0 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL_three_zero,
    CFSG.ClassicalInvolution.WeakCT.coe_blockSL_three_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem slMap_blockSL_one' (φ : K →+* K') (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL K 3 2 1 (by omega) A) =
      blockSL K' 3 2 1 (by omega) (Matrix.SpecialLinearGroup.map φ A) := by
  apply Subtype.ext
  show φ.mapMatrix ((blockSL K 3 2 1 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL_three_one,
    CFSG.ClassicalInvolution.WeakCT.coe_blockSL_three_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

end Transport

theorem lin_pair_zmod {G : Type} [Group G] {W K N : Subgroup G}
    (h : LinearBlockStandardPair (GaloisField 3 1) W K N) :
    ∃ θ : SL(3, ZMod 3) →* G, θ.ker ≤ Subgroup.center SL(3, ZMod 3) ∧
      (blockSL (ZMod 3) 3 2 0 (by omega)).range.map θ = K ∧
      (blockSL (ZMod 3) 3 2 1 (by omega)).range.map θ = N := by
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_three (K := GaloisField 3 1) hcard
  obtain ⟨θ, -, hker, h0, h1⟩ := pair_normalize h
  let Φ3 : SL(3, ZMod 3) →* SL(3, GaloisField 3 1) :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let Φ2 : SL(2, ZMod 3) →* SL(2, GaloisField 3 1) :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hΦ3 : Function.Injective Φ3 := by
    intro a b hab
    apply Subtype.ext
    have h' := congrArg Subtype.val hab
    simp only [Φ3, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
    exact Matrix.map_injective e.symm.injective h'
  have hΦ2 : Function.Surjective Φ2 := by
    intro b
    refine ⟨Matrix.SpecialLinearGroup.map e.toRingHom b, ?_⟩
    apply Subtype.ext
    ext i j
    simp [Φ2]
  have hΦ3s : Function.Surjective Φ3 := by
    intro b
    refine ⟨Matrix.SpecialLinearGroup.map e.toRingHom b, ?_⟩
    apply Subtype.ext
    ext i j
    simp [Φ3]
  have c0 : Φ3.comp (blockSL (ZMod 3) 3 2 0 (by omega)) =
      (blockSL (GaloisField 3 1) 3 2 0 (by omega)).comp Φ2 := by
    ext A : 1
    exact slMap_blockSL_zero' e.symm.toRingHom A
  have c1 : Φ3.comp (blockSL (ZMod 3) 3 2 1 (by omega)) =
      (blockSL (GaloisField 3 1) 3 2 1 (by omega)).comp Φ2 := by
    ext A : 1
    exact slMap_blockSL_one' e.symm.toRingHom A
  have hrange : ∀ (b : SL(2, GaloisField 3 1) →* SL(3, GaloisField 3 1))
      (a : SL(2, ZMod 3) →* SL(3, ZMod 3)), Φ3.comp a = b.comp Φ2 →
      a.range.map Φ3 = b.range := by
    intro b a hab
    rw [← MonoidHom.range_comp, hab, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hΦ2,
      Subgroup.map_top]
  refine ⟨θ.comp Φ3, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : Φ3 g ∈ θ.ker := hg
    have hc := Subgroup.mem_center_iff.mp (hker hg')
    rw [Subgroup.mem_center_iff]
    intro x
    apply hΦ3
    rw [map_mul, map_mul]
    exact hc (Φ3 x)
  · rw [← Subgroup.map_map, hrange _ _ c0]
    exact h0
  · rw [← Subgroup.map_map, hrange _ _ c1]
    exact h1

theorem centralizes_of_cube_one {G : Type} [Group G] {K N : Subgroup G} {s : G} (hs3 : s ^ 3 = 1)
    (hKN : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ = k) (hsN : ∀ n ∈ N, s * n * s⁻¹ ∈ N) :
    ∀ n ∈ N, s * n * s⁻¹ = n := by
  obtain ⟨W, hW⟩ := hKN
  obtain ⟨θ, hker, hK, hN⟩ := lin_pair_zmod hW
  have key := commutes_of_cube_one_zmod θ hker hs3
    (fun A => hsK _ (hK ▸ ⟨_, ⟨A, rfl⟩, rfl⟩))
    (fun B => by
      have hmem : s * θ (b1 B) * s⁻¹ ∈ N := hsN _ (hN ▸ ⟨_, ⟨B, rfl⟩, rfl⟩)
      rw [← hN] at hmem
      obtain ⟨_, ⟨B', rfl⟩, h⟩ := hmem
      exact ⟨B', h.symm⟩)
  intro n hn
  rw [← hN] at hn
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hn
  exact key B

end CFSG.ClassicalInvolution.Q3.Q3TPS
