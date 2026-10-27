module

public import CFSG.CGT.PushingUpLit.A78L3.Heis
public import CFSG.CGT.PushingUpLit.A78L3.Fields
public import CFSG.CGT.PushingUpLit.A78L3.Base

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78T2 (T2Heis T2Tori)
open Matrix
open scoped commutatorElement

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}
  {h : L3Side G L V W T e} {D : NatCoord G L V (GaloisField 2 e)}

namespace Frame

variable (fr : Frame h D)

theorem det2_comb (α β γ δ : GaloisField 2 e) (x y : Fin 2 → GaloisField 2 e) :
    det2 (α • x + β • y) (γ • x + δ • y) = (α * δ - β * γ) * det2 x y := by
  simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

omit [Finite G] in
theorem det_eq_det2_cols (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) :
    M.det = det2 (M *ᵥ Pi.single 0 1) (M *ᵥ Pi.single 1 1) := by
  rw [det_fin_two, mulVec_single_one, mulVec_single_one]
  simp [det2]
  ring

theorem torus {t : GaloisField 2 e} (ht : t ≠ 0) :
    ∃ x ∈ L, (∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W) ∧
      (∀ j ∈ V ⊔ W, fr.a (x * j * x⁻¹) = t⁻¹ * fr.a j ∧ fr.b (x * j * x⁻¹) = t ^ 2 * fr.b j) ∧
      ∀ z ∈ V ⊓ W, x * z * x⁻¹ ∈ V ⊓ W ∧ fr.c (x * z * x⁻¹) = t * fr.c z := by
  have hdet0 : det2 (D.κ fr.z₀) fr.y₀ = 1 := fr.hdet
  let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e) := Matrix.of fun i k =>
    (t * det2 (Pi.single k 1) fr.y₀) * D.κ fr.z₀ i +
      (t⁻¹ * det2 (D.κ fr.z₀) (Pi.single k 1)) * fr.y₀ i
  have hM : ∀ u, M *ᵥ u = (t * det2 u fr.y₀) • D.κ fr.z₀ +
      (t⁻¹ * det2 (D.κ fr.z₀) u) • fr.y₀ := by
    intro u
    ext i
    fin_cases i <;> simp [M, mulVec, dotProduct, Fin.sum_univ_two, det2] <;> ring
  have hdet : M.det = 1 := by
    rw [det_eq_det2_cols, hM, hM, det2_comb, hdet0, mul_one]
    have key : det2 (Pi.single 0 1) fr.y₀ * det2 (D.κ fr.z₀) (Pi.single 1 1) -
        det2 (D.κ fr.z₀) (Pi.single 0 1) * det2 (Pi.single 1 1) fr.y₀ =
          det2 (D.κ fr.z₀) fr.y₀ := by
      simp [det2]; ring
    calc t * det2 (Pi.single 0 1) fr.y₀ * (t⁻¹ * det2 (D.κ fr.z₀) (Pi.single 1 1)) -
          t⁻¹ * det2 (D.κ fr.z₀) (Pi.single 0 1) * (t * det2 (Pi.single 1 1) fr.y₀)
        = (t * t⁻¹) * (det2 (Pi.single 0 1) fr.y₀ * det2 (D.κ fr.z₀) (Pi.single 1 1) -
          det2 (D.κ fr.z₀) (Pi.single 0 1) * det2 (Pi.single 1 1) fr.y₀) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ ht, one_mul, key, hdet0]
  obtain ⟨x, hx, hxM⟩ := D.ρ_surj ⟨M, hdet⟩
  have hxM' : (D.ρ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hxM]
  have hMx₀ : M *ᵥ D.κ fr.z₀ = t • D.κ fr.z₀ := by
    rw [hM, det2_self, mul_zero, zero_smul, add_zero, hdet0, mul_one]
  have hMy : M *ᵥ fr.y₀ = t⁻¹ • fr.y₀ := by
    rw [hM, det2_self, mul_zero, zero_smul, zero_add, hdet0, mul_one]
  have hMy₀ : M *ᵥ (t • fr.y₀) = fr.y₀ := by
    rw [mulVec_smul, hMy, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hZ : ∀ z ∈ V ⊓ W, x * z * x⁻¹ ∈ V ⊓ W ∧ fr.c (x * z * x⁻¹) = t * fr.c z := by
    intro z hz
    have hκ : D.κ (x * z * x⁻¹) = (t * fr.c z) • D.κ fr.z₀ := by
      rw [D.conj x hx z hz.1, hxM', fr.κ_eq_c hz, mulVec_smul, hMx₀, smul_smul, mul_comm]
    have hmem : x * z * x⁻¹ ∈ V ⊓ W :=
      (h.mem_Z_iff D fr.hz₀ fr.hz₀1 (D.norm x hx z hz.1)).2 ⟨_, hκ⟩
    refine ⟨hmem, ?_⟩
    rw [c, hκ, det2_smul_left, hdet0, mul_one]
  have hJ : ∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W := by
    intro j hj
    have hz₁ := (hZ fr.z₀ fr.hz₀).1
    have hz₁1 : x * fr.z₀ * x⁻¹ ≠ 1 := fun h1 => fr.hz₀1 (by
      have : fr.z₀ = x⁻¹ * (x * fr.z₀ * x⁻¹) * x := by group
      rw [this, h1]; group)
    rw [← h.cent_L hz₁ hz₁1]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx (h.J_le_L hj)) (inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hc := (h.jst.commute_of_mem_inf fr.hz₀ hj).eq
    calc x * j * x⁻¹ * (x * fr.z₀ * x⁻¹) = x * (j * fr.z₀) * x⁻¹ := by group
      _ = x * (fr.z₀ * j) * x⁻¹ := by rw [hc]
      _ = x * fr.z₀ * x⁻¹ * (x * j * x⁻¹) := by group
  have hW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    have hle : cj x W ≤ V ⊔ W := by
      intro y hy
      rw [mem_cj_iff] at hy
      have := hJ _ (Subgroup.mem_sup_right hy)
      simpa [mul_assoc] using this
    have hsq : ∀ y ∈ cj x W, y * y = 1 := fun y hy => by
      rw [mem_cj_iff] at hy
      have h1 := h.jst.sq_V₂ _ hy
      calc y * y = x * (x⁻¹ * y * x * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hcard : Nat.card (cj x W) = Nat.card V := by
      rw [card_cj, h.jst.card_V₂_eq]
    rcases h.jst.mem_of_card hle hsq hcard with hV | hW'
    · exfalso
      have hxV : cj x V = V := cj_eq_of_mem_normalizer_set (D.le_normalizer hx)
      have := cj_injective (hV.trans hxV.symm)
      exact h.jst.not_le_V (this ▸ le_rfl)
    · intro w hw
      rw [← hW']
      exact mul_mem_cj x hw
  refine ⟨x, hx, hJ, fun j hj => ?_, hZ⟩
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hj
  have hxv : x * v * x⁻¹ ∈ V := D.norm x hx v hv
  have hxw : x * w * x⁻¹ ∈ W := hW w hw
  have e1 : x * (v * w) * x⁻¹ = (x * v * x⁻¹) * (x * w * x⁻¹) := by group
  refine ⟨?_, ?_⟩
  · rw [e1, fr.a_vw hxv hxw, fr.a_vw hv hw, D.conj x hx v hv, hxM', hM, det2_add_right,
      det2_smul_right, det2_self, mul_zero, zero_add, det2_smul_right, hdet0, mul_one]
  ·
    have hxi : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = t • fr.y₀ := by
      have h1 : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ (M *ᵥ (t • fr.y₀)) =
          (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ := by rw [hMy₀]
      rw [← hxM', ← D.ρ_mulVec_mul (inv_mem hx) hx, inv_mul_cancel,
        D.ρ_mulVec_of_mem (Subgroup.one_mem _) (Subgroup.one_mem _)] at h1
      exact h1.symm
    have hj' : v * w ∈ V ⊔ W := hj
    have hb1 : (D.ρ (v * w) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
        fr.y₀ + fr.b (v * w) • D.κ fr.z₀ := by
      rw [fr.ρ_mulVec hj', hdet0, one_mul]
    have hcomp : (D.ρ (x * (v * w) * x⁻¹) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
        fr.y₀ + (t ^ 2 * fr.b (v * w)) • D.κ fr.z₀ := by
      rw [D.ρ_mulVec_mul (mul_mem hx (h.J_le_L hj')) (inv_mem hx),
        D.ρ_mulVec_mul hx (h.J_le_L hj'), hxi, mulVec_smul, hb1, hxM', mulVec_smul, mulVec_add,
        mulVec_smul, hMy, hMx₀, smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul, smul_smul,
        smul_smul]
      congr 2
      ring
    rw [b, hcomp, det2_add_left, det2_self, zero_add, det2_smul_left, hdet0, mul_one]

end Frame

end L3Side

namespace L3Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W T : Subgroup G} {e : ℕ}
  (P : L3Pair G L₁ L₂ V W T e)

include P in
theorem tori {D : NatCoord G L₁ V (GaloisField 2 e)} (fr : L3Side.Frame P.side₁ D) :
    T2Tori G (V ⊔ W) (V ⊓ W) L₁ L₂ (GaloisField 2 e) fr.a fr.b fr.c := by
  classical
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr₂⟩ := P.side₂.exists_frame D₂
  have hJ : W ⊔ V = V ⊔ W := sup_comm W V
  have hZ : W ⊓ V = V ⊓ W := inf_comm W V
  choose xa hxa using fun u : GaloisField 2 e => fr.surj_ab u 0
  choose xb hxb using fun r : GaloisField 2 e => fr.surj_ab 0 r
  choose zc hzc using fun r : GaloisField 2 e => fr.c_surj r
  let φa : GaloisField 2 e → GaloisField 2 e := fun u => fr₂.b (xa u)
  let φb : GaloisField 2 e → GaloisField 2 e := fun r => fr₂.a (xb r)
  let φc : GaloisField 2 e → GaloisField 2 e := fun r => fr₂.c (zc r)
  have hJ' : ∀ {j : G}, j ∈ V ⊔ W → j ∈ W ⊔ V := fun hj => hJ ▸ hj
  have hZ' : ∀ {z : G}, z ∈ V ⊓ W → z ∈ W ⊓ V := fun hz => hZ ▸ hz
  have hb₂ : ∀ j ∈ V ⊔ W, fr₂.b j = φa (fr.a j) := by
    intro j hj
    have hxaJ := (hxa (fr.a j)).1
    have hd : j * (xa (fr.a j))⁻¹ ∈ W := by
      rw [fr.mem_W_iff_a (mul_mem hj (inv_mem hxaJ)), fr.a_mul hj (inv_mem hxaJ)]
      have h1 := fr.a_mul hxaJ (inv_mem hxaJ)
      rw [mul_inv_cancel] at h1
      have h0 : fr.a 1 = 0 := (fr.mem_W_iff_a (Subgroup.one_mem _)).1 (Subgroup.one_mem _)
      rw [h0, (hxa (fr.a j)).2.1] at h1
      linear_combination -h1
    have h1 := fr₂.b_mul (hJ' (mul_mem hj (inv_mem hxaJ))) (hJ' hxaJ)
    rw [inv_mul_cancel_right, fr₂.b_of_mem_V hd, zero_add] at h1
    exact h1
  have ha₂ : ∀ j ∈ V ⊔ W, fr₂.a j = φb (fr.b j) := by
    intro j hj
    have hxbJ := (hxb (fr.b j)).1
    have hd : j * (xb (fr.b j))⁻¹ ∈ V := by
      rw [fr.mem_V_iff_b (mul_mem hj (inv_mem hxbJ)), fr.b_mul hj (inv_mem hxbJ)]
      have h1 := fr.b_mul hxbJ (inv_mem hxbJ)
      rw [mul_inv_cancel] at h1
      have h0 : fr.b 1 = 0 := fr.b_of_mem_V (Subgroup.one_mem _)
      rw [h0, (hxb (fr.b j)).2.2] at h1
      linear_combination -h1
    have hdW2 : j * (xb (fr.b j))⁻¹ ∈ W ⊔ V := hJ' (mul_mem hj (inv_mem hxbJ))
    have h1 := fr₂.a_mul hdW2 (hJ' hxbJ)
    rw [inv_mul_cancel_right, (fr₂.mem_W_iff_a hdW2).1 hd, zero_add] at h1
    exact h1
  have hc₂ : ∀ z ∈ V ⊓ W, fr₂.c z = φc (fr.c z) := by
    intro z hz
    have : zc (fr.c z) = z := fr.c_inj (hzc (fr.c z)).1 hz (hzc (fr.c z)).2
    show fr₂.c z = fr₂.c (zc (fr.c z))
    rw [this]
  have hφc_add : ∀ x y, φc (x + y) = φc x + φc y := by
    intro x y
    have h1 : zc (x + y) = zc x * zc y :=
      fr.c_inj (hzc (x + y)).1 (mul_mem (hzc x).1 (hzc y).1)
        (by rw [fr.c_mul (hzc x).1 (hzc y).1, (hzc x).2, (hzc y).2, (hzc (x + y)).2])
    show fr₂.c (zc (x + y)) = fr₂.c (zc x) + fr₂.c (zc y)
    rw [h1, fr₂.c_mul (hZ' (hzc x).1) (hZ' (hzc y).1)]
  have hφc_inj : Function.Injective φc := by
    intro x y hxy
    have h1 := fr₂.c_inj (hZ' (hzc x).1) (hZ' (hzc y).1) hxy
    rw [← (hzc x).2, ← (hzc y).2, h1]
  have hmulφ : ∀ u r, φc (u * r) = φa u * φb r := by
    intro u r
    have hy := (hxa u).1
    have hx := (hxb r).1
    have hyV : xa u ∈ V := (fr.mem_V_iff_b hy).2 (hxa u).2.2
    have hxW : xb r ∈ W := (fr.mem_W_iff_a hx).2 (hxb r).2.1
    have hcz : ⁅xa u, xb r⁆ ∈ V ⊓ W := P.side₁.jst.commutator_mem hyV hxW
    have h1 := fr.c_comm_J hy hx
    rw [(hxa u).2.1, (hxa u).2.2, (hxb r).2.1, (hxb r).2.2, mul_zero, add_zero] at h1
    have h2 := fr₂.c_comm_J (hJ' hy) (hJ' hx)
    rw [(fr₂.mem_W_iff_a (hJ' hy)).1 hyV, zero_mul, zero_add, ha₂ _ hx, hb₂ _ hy,
      (hxb r).2.2, (hxa u).2.1] at h2
    rw [← h1, ← hc₂ _ hcz, h2, mul_comm]
  obtain ⟨τ, hτa, hτb, hτc, ha1, hb1⟩ := exists_ringEquiv_of_mul hφc_add hφc_inj hmulφ
  refine ⟨fun t ht => fr.torus ht, fun t ht => ?_⟩
  have hs : τ t ≠ 0 := by rw [map_ne_zero]; exact ht
  obtain ⟨x, hx, hxJ, hxab, hxZ⟩ := fr₂.torus hs
  refine ⟨x, hx, fun j hj => hJ ▸ hxJ j (hJ' hj), fun j hj => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · have hj2 := hJ' hj
    have hxj : x * j * x⁻¹ ∈ V ⊔ W := hJ ▸ hxJ j hj2
    have h1 := (hxab j hj2).2
    rw [hb₂ _ hxj, hb₂ _ hj, hτa (fr.a (x * j * x⁻¹)), hτa (fr.a j)] at h1
    have h2 : τ (fr.a (x * j * x⁻¹)) = τ (t ^ 2 * fr.a j) := by
      rw [map_mul, map_pow]
      apply mul_left_cancel₀ ha1
      rw [h1]; ring
    exact τ.injective h2
  · have hj2 := hJ' hj
    have hxj : x * j * x⁻¹ ∈ V ⊔ W := hJ ▸ hxJ j hj2
    have h1 := (hxab j hj2).1
    rw [ha₂ _ hxj, ha₂ _ hj, hτb (fr.b (x * j * x⁻¹)), hτb (fr.b j)] at h1
    have h2 : τ (fr.b (x * j * x⁻¹)) = τ (t⁻¹ * fr.b j) := by
      rw [map_mul, map_inv₀]
      apply mul_left_cancel₀ hb1
      rw [h1]; ring
    exact τ.injective h2
  · exact hZ ▸ (hxZ z (hZ' hz)).1
  · have hz2 := hZ' hz
    have hxz : x * z * x⁻¹ ∈ V ⊓ W := hZ ▸ (hxZ z hz2).1
    have h1 := (hxZ z hz2).2
    rw [hc₂ _ hxz, hc₂ _ hz, hτc (fr.c (x * z * x⁻¹)), hτc (fr.c z)] at h1
    have h2 : τ (fr.c (x * z * x⁻¹)) = τ (t * fr.c z) := by
      rw [map_mul]
      apply mul_left_cancel₀ (mul_ne_zero ha1 hb1)
      rw [h1]; ring
    exact τ.injective h2

end L3Pair

end CFSG.CGT.PushingUpLit.A78L3
