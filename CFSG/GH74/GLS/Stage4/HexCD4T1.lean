module

public import CFSG.GH74.GLS.Stage4.HexCD4Act
public import CFSG.GH74.GLS.Stage4.HexCD4Gal

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

section T1

variable (D : HexData4 root F K)

theorem t1_conj_comm (ρ : Kˣ) (x y : G) :
    D.T₁ ρ * ⁅x, y⁆ * (D.T₁ ρ)⁻¹ = ⁅D.T₁ ρ * x * (D.T₁ ρ)⁻¹, D.T₁ ρ * y * (D.T₁ ρ)⁻¹⁆ := by
  simp only [commutatorElement_def]; group

theorem t1_cent4 (ρ : Kˣ) (f : F) : D.T₁ ρ * D.p4 f * (D.T₁ ρ)⁻¹ = D.p4 f := by
  rw [mul_inv_eq_iff_eq_mul]; exact D.T₁_cent4 ρ _ (D.p4_mem f)

theorem t1_p6 (h2 : (2 : F) ≠ 0) (ρ : Kˣ) :
    ∃ χ : F, χ ≠ 0 ∧ ∀ c, D.T₁ ρ * D.p6 c * (D.T₁ ρ)⁻¹ = D.p6 (χ * c) := by
  have hmem : ∀ c, D.T₁ ρ * D.p6 c * (D.T₁ ρ)⁻¹ ∈ root 6 := fun c =>
    D.T₁_norm ρ 6 (by norm_num) (by norm_num) _ (D.p6_mem c)
  choose f hf using fun c => D.p6_surj _ (hmem c)
  have hadd : ∀ c d, f (c + d) = f c + f d := by
    intro c d
    apply D.p6_inj
    rw [D.p6_add, hf, hf, hf, D.p6_add]
    group
  have hhom : ∀ t : Fˣ, ∀ c, f ((t : F) ^ 2 * c) = (t : F) ^ 2 * f c := by
    intro t c
    apply D.p6_inj
    have hc' : D.T₁ ρ * D.T t * (D.T₁ ρ)⁻¹ = D.T t := by
      rw [mul_inv_eq_iff_eq_mul]; exact D.T₁_comm ρ t
    calc D.p6 (f ((t : F) ^ 2 * c)) = D.T₁ ρ * D.p6 ((t : F) ^ 2 * c) * (D.T₁ ρ)⁻¹ := hf _
      _ = D.T₁ ρ * (D.T t * D.p6 c * (D.T t)⁻¹) * (D.T₁ ρ)⁻¹ := by rw [D.w6]
      _ = (D.T₁ ρ * D.T t * (D.T₁ ρ)⁻¹) * (D.T₁ ρ * D.p6 c * (D.T₁ ρ)⁻¹) *
          (D.T₁ ρ * D.T t * (D.T₁ ρ)⁻¹)⁻¹ := by group
      _ = D.T t * D.p6 (f c) * (D.T t)⁻¹ := by rw [hc', hf]
      _ = D.p6 ((t : F) ^ 2 * f c) := by rw [D.w6]
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact add_eq_left.1 this.symm
  have hneg : ∀ c, f (-c) = - f c := by
    intro c
    have := hadd (-c) c
    rw [neg_add_cancel, h0] at this
    linear_combination -this
  have hsq : ∀ x : F, f (x ^ 2) = x ^ 2 * f 1 := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [h0]
    · have := hhom (Units.mk0 x hx) 1
      simpa using this
  have hlin : ∀ c, f c = c * f 1 := by
    intro c
    have hc : ((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2)) = c := by field_simp; ring
    calc f c = f (((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2))) := by rw [hc]
      _ = ((c + 1) / 2) ^ 2 * f 1 - ((c - 1) / 2) ^ 2 * f 1 := by
          rw [hadd, hneg, hsq, hsq]; ring
      _ = c * f 1 := by field_simp; ring
  refine ⟨f 1, ?_, fun c => ?_⟩
  · intro h0'
    have h1 := hf 1
    rw [h0', map_zero_of_add' D.p6_add] at h1
    have h3 : D.p6 1 = 1 := mul_eq_left.1 (mul_inv_eq_one.1 h1.symm)
    have : D.p6 1 = D.p6 0 := by rw [h3, map_zero_of_add' D.p6_add]
    exact one_ne_zero (D.p6_inj this)
  · rw [← hf, hlin c, mul_comm]

theorem t1_p2 (ρ : Kˣ) {χ : F} (hχ : χ ≠ 0)
    (h6 : ∀ c, D.T₁ ρ * D.p6 c * (D.T₁ ρ)⁻¹ = D.p6 (χ * c)) :
    ∀ d, D.T₁ ρ * D.p2 d * (D.T₁ ρ)⁻¹ = D.p2 (χ⁻¹ * d) := by
  intro d
  obtain ⟨f, hf⟩ := D.p2_surj _ (D.T₁_norm ρ 2 (by norm_num) (by norm_num) _ (D.p2_mem d))
  have h := t1_conj_comm D ρ (D.p6 1) (D.p2 d)
  rw [D.rel_long, t1_cent4, h6, ← hf, D.rel_long] at h
  have h' := D.p4_inj h
  have hχf : χ * f = d := by linear_combination -h'
  rw [← hf]
  congr 1
  rw [← hχf]; field_simp

theorem t1_conj_Nel4 (ρ : Kˣ) {χ : F}
    (h2 : ∀ d, D.T₁ ρ * D.p2 d * (D.T₁ ρ)⁻¹ = D.p2 (χ⁻¹ * d)) (e f : F) (u : G) :
    D.T₁ ρ * Nel4 D e u f * (D.T₁ ρ)⁻¹ = Nel4 D (χ⁻¹ * e) (D.T₁ ρ * u * (D.T₁ ρ)⁻¹) f := by
  unfold Nel4
  calc D.T₁ ρ * (D.p2 e * u * D.p4 f) * (D.T₁ ρ)⁻¹
      = (D.T₁ ρ * D.p2 e * (D.T₁ ρ)⁻¹) * (D.T₁ ρ * u * (D.T₁ ρ)⁻¹) *
        (D.T₁ ρ * D.p4 f * (D.T₁ ρ)⁻¹) := by group
    _ = _ := by rw [h2, t1_cent4]

theorem V24_X5_unique (R : RGD2 6 H r₁ r₂ U root) {v v' : G} (hv : v ∈ Vsub root 2 4)
    (hv' : v' ∈ Vsub root 2 4) {t t' : K} (h : v * D.p5 t = v' * D.p5 t') : v = v' ∧ t = t' := by
  have h5 : D.p5 t' * (D.p5 t)⁻¹ ∈ root 5 :=
    (root 5).mul_mem (D.p5_mem _) ((root 5).inv_mem (D.p5_mem _))
  have hV : D.p5 t' * (D.p5 t)⁻¹ ∈ Vsub root 2 4 := by
    have e : D.p5 t' * (D.p5 t)⁻¹ = v'⁻¹ * v := by
      have : v = v' * D.p5 t' * (D.p5 t)⁻¹ := by
        calc v = v * D.p5 t * (D.p5 t)⁻¹ := by group
          _ = v' * D.p5 t' * (D.p5 t)⁻¹ := by rw [h]
      rw [this]; group
    rw [e]; exact (Vsub root 2 4).mul_mem ((Vsub root 2 4).inv_mem hv') hv
  have h1 := (rgd2_unique_15 R (root 1).one_mem h5 (by simpa using hV)).2
  have ht : t' = t := D.p5_inj (mul_inv_eq_one.1 h1)
  subst ht
  exact ⟨mul_right_cancel h, rfl⟩

end T1

section Cov

variable (R : RGD2 6 H r₁ r₂ U root) (D : HexData4 root F K) (Gl : GalData F K)

include R in
theorem t1_cov (h2 : (2 : F) ≠ 0) {β : K → G → F} (hβ : PairData D β) {p3 : K → G}
    (hp3mem : ∀ a, p3 a ∈ root 3) (hp3surj : ∀ u ∈ root 3, ∃ a, p3 a = u)
    (hp3inj : Function.Injective p3) (hp3β : ∀ a s, β s (p3 a) = Gl.trF (a * s))
    {A2 A4 : F → K → F} {g3 : F → K → G} (had : ActData4 D A2 A4 g3) {gh : F → K → K}
    (hgh : ∀ c s, g3 c s = p3 (gh c s)) (ρ : Kˣ) :
    ∃ χ : F, χ ≠ 0 ∧ ∀ c s, A2 (χ * c) ((ρ : K) ^ 2 * s) = χ⁻¹ * A2 c s ∧
      gh (χ * c) ((ρ : K) ^ 2 * s) = ((ρ : K) ^ 2)⁻¹ * (Gl.θ χ)⁻¹ * gh c s ∧
      A4 (χ * c) ((ρ : K) ^ 2 * s) = A4 c s := by
  obtain ⟨χ, hχ, h6⟩ := t1_p6 D h2 ρ
  have hX2 := t1_p2 D ρ hχ h6
  have hρ : ((ρ : K) ^ 2) ≠ 0 := pow_ne_zero 2 ρ.ne_zero
  have hχ' : Gl.θ χ ≠ 0 := (map_ne_zero Gl.θ).2 hχ
  have hf3 : ∀ a : K, D.T₁ ρ * p3 a * (D.T₁ ρ)⁻¹ = p3 (((ρ : K) ^ 2)⁻¹ * (Gl.θ χ)⁻¹ * a) := by
    intro a
    obtain ⟨f, hf⟩ := hp3surj _ (D.T₁_norm ρ 3 (by norm_num) (by norm_num) _ (hp3mem a))
    have hmain : f * (ρ : K) ^ 2 = Gl.θ χ⁻¹ * a := by
      apply Gl.eq_of_trF_eq
      intro s'
      have h := t1_conj_comm D ρ (D.p1 s') (p3 a)
      rw [hβ.r1 s' _ (hp3mem a), hp3β, hX2, ← hf, D.w1', hβ.r1 _ _ (hp3mem f), hp3β] at h
      have h' := D.p2_inj h
      calc Gl.trF (f * (ρ : K) ^ 2 * s') = Gl.trF (f * ((ρ : K) ^ 2 * s')) := by rw [mul_assoc]
        _ = χ⁻¹ * Gl.trF (a * s') := h'.symm
        _ = Gl.trF (Gl.θ χ⁻¹ * (a * s')) := (Gl.trF_smul _ _).symm
        _ = Gl.trF (Gl.θ χ⁻¹ * a * s') := by rw [mul_assoc]
    rw [← hf]
    congr 1
    have : f = f * (ρ : K) ^ 2 * ((ρ : K) ^ 2)⁻¹ := by field_simp
    rw [this, hmain, map_inv₀]; ring
  have hmem5 : ∀ t : K, D.T₁ ρ * D.p5 t * (D.T₁ ρ)⁻¹ ∈ root 5 := fun t =>
    D.T₁_norm ρ 5 (by norm_num) (by norm_num) _ (D.p5_mem t)
  refine ⟨χ, hχ, fun c s => ?_⟩
  obtain ⟨t₅, ht₅⟩ := D.p5_surj _ (hmem5 (D.θ c * s))
  have hc := t1_conj_comm D ρ (D.p6 c) (D.p1 s)
  rw [had.eq c s, h6 c, D.w1' ρ s, had.eq (χ * c) ((ρ : K) ^ 2 * s)] at hc
  have hL : D.T₁ ρ * (Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s)) * (D.T₁ ρ)⁻¹ =
      Nel4 D (χ⁻¹ * A2 c s) (D.T₁ ρ * g3 c s * (D.T₁ ρ)⁻¹) (A4 c s) * D.p5 t₅ := by
    calc _ = (D.T₁ ρ * Nel4 D (A2 c s) (g3 c s) (A4 c s) * (D.T₁ ρ)⁻¹) *
          (D.T₁ ρ * D.p5 (D.θ c * s) * (D.T₁ ρ)⁻¹) := by group
      _ = _ := by rw [t1_conj_Nel4 D ρ hX2, ← ht₅]
  rw [hL] at hc
  have hu : D.T₁ ρ * g3 c s * (D.T₁ ρ)⁻¹ ∈ root 3 :=
    D.T₁_norm ρ 3 (by norm_num) (by norm_num) _ (had.g3_mem c s)
  obtain ⟨hV, -⟩ := V24_X5_unique D R (Nel4_mem D hu) (Nel4_mem D (had.g3_mem _ _)) hc
  obtain ⟨e1, e2, e3⟩ := Nel4_inj R D hu (had.g3_mem _ _) hV
  refine ⟨e1.symm, ?_, e3.symm⟩
  apply hp3inj
  rw [← hgh, ← e2, hgh c s, hf3]

end Cov

end CFSG.GH74.GLS.Stage4.Hex
