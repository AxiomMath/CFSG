module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229Tr
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229

open CFSG.GH74.GLS.Bg.TwoGroups

namespace SU

@[expose] def pa (x : SylSU3_4) : F16 := x.1.a

@[expose] def pb (x : SylSU3_4) : F16 := x.1.b

theorem pa_mul (x y : SylSU3_4) : pa (x * y) = pa x + pa y := rfl

theorem pb_mul (x y : SylSU3_4) : pb (x * y) = pb x + pb y + pa x * bar (pa y) := rfl

theorem pa_one : pa (1 : SylSU3_4) = 0 := rfl

theorem pb_one : pb (1 : SylSU3_4) = 0 := rfl

theorem pa_inv (x : SylSU3_4) : pa x⁻¹ = - pa x := rfl

theorem mem_pb (x : SylSU3_4) : pb x + bar (pb x) + pa x * bar (pa x) = 0 :=
  (mem_sylSU3 x.1).1 x.2

theorem T_ext {x y : SylSU3_4} (ha : pa x = pa y) (hb : pb x = pb y) : x = y :=
  Subtype.ext (UH.ext ha hb)

theorem add_self' (x : F16) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem sq_pa (x : SylSU3_4) : pa (x * x) = 0 := by rw [pa_mul]; exact add_self' _

theorem sq_pb (x : SylSU3_4) : pb (x * x) = pa x * bar (pa x) := by
  rw [pb_mul, add_self', zero_add]

theorem central_of_pa_zero {z : SylSU3_4} (hz : pa z = 0) (y : SylSU3_4) : z * y = y * z := by
  apply T_ext
  · rw [pa_mul, pa_mul, add_comm]
  · rw [pb_mul, pb_mul, hz, map_zero, mul_zero, zero_mul, add_zero, add_zero, add_comm]

theorem mul_self_of_pa_zero {z : SylSU3_4} (hz : pa z = 0) : z * z = 1 := by
  apply T_ext
  · rw [pa_mul, pa_one, hz, add_zero]
  · rw [pb_mul, pb_one, hz, map_zero, mul_zero, add_zero, add_self']

theorem exists_lift (a : F16) : ∃ x : SylSU3_4, pa x = a := by
  obtain ⟨b, hb⟩ := F16_trace_surj a
  exact ⟨⟨⟨a, b⟩, (mem_sylSU3 _).2 hb⟩, rfl⟩

theorem exists_sqrt {z : SylSU3_4} (hz : pa z = 0) : ∃ w : SylSU3_4, w * w = z := by
  have h := mem_pb z
  rw [hz, map_zero, mul_zero, add_zero] at h
  obtain ⟨a, ha⟩ := F16_norm_surj (pb z) h
  obtain ⟨b, hb'⟩ := F16_trace_surj a
  refine ⟨⟨⟨a, b⟩, (mem_sylSU3 _).2 hb'⟩, T_ext ?_ ?_⟩
  · rw [sq_pa, hz]
  · rw [sq_pb]
    exact ha

theorem pa_aut_zero (φ : MulAut SylSU3_4) {z : SylSU3_4} (hz : pa z = 0) : pa (φ z) = 0 := by
  obtain ⟨w, rfl⟩ := exists_sqrt hz
  rw [map_mul]
  exact sq_pa _

@[expose] noncomputable def lift (a : F16) : SylSU3_4 := (exists_lift a).choose

theorem pa_lift (a : F16) : pa (lift a) = a := (exists_lift a).choose_spec

@[expose] noncomputable def fbar (φ : MulAut SylSU3_4) (a : F16) : F16 := pa (φ (lift a))

theorem pa_aut (φ : MulAut SylSU3_4) (x : SylSU3_4) : pa (φ x) = fbar φ (pa x) := by
  have hz : pa ((lift (pa x))⁻¹ * x) = 0 := by
    rw [pa_mul, pa_inv, pa_lift]; exact neg_add_cancel _
  calc pa (φ x) = pa (φ (lift (pa x) * ((lift (pa x))⁻¹ * x))) := by rw [mul_inv_cancel_left]
    _ = pa (φ (lift (pa x))) + pa (φ ((lift (pa x))⁻¹ * x)) := by rw [map_mul, pa_mul]
    _ = fbar φ (pa x) := by rw [pa_aut_zero φ hz, add_zero]; rfl

theorem fbar_add (φ : MulAut SylSU3_4) (a b : F16) : fbar φ (a + b) = fbar φ a + fbar φ b := by
  have h := pa_aut φ (lift a * lift b)
  rw [pa_mul, pa_lift, pa_lift] at h
  rw [← h, map_mul, pa_mul]
  rfl

theorem fbar_mul (φ ψ : MulAut SylSU3_4) (a : F16) : fbar (φ * ψ) a = fbar φ (fbar ψ a) := by
  have h := pa_aut φ (ψ (lift a))
  show pa (φ (ψ (lift a))) = _
  rw [h]
  rfl

theorem fbar_one (a : F16) : fbar (1 : MulAut SylSU3_4) a = a := pa_lift a

theorem fbar_compat (φ : MulAut SylSU3_4) (a b : F16) (h : a * bar a = b * bar b) :
    fbar φ a * bar (fbar φ a) = fbar φ b * bar (fbar φ b) := by
  have hsq : lift a * lift a = lift b * lift b := by
    apply T_ext
    · rw [sq_pa, sq_pa]
    · rw [sq_pb, sq_pb, pa_lift, pa_lift]; exact h
  have := congrArg (fun x => pb (φ x)) hsq
  simp only [map_mul, sq_pb] at this
  exact this

theorem aut_eq_one (σ : MulAut SylSU3_4) (h3 : σ ^ 3 = 1) (hid : ∀ a, fbar σ a = a) : σ = 1 := by
  have hpa : ∀ x, pa (σ x) = pa x := fun x => by rw [pa_aut, hid]
  have hc : ∀ x, pa (x⁻¹ * σ x) = 0 := fun x => by
    rw [pa_mul, pa_inv, hpa]; exact neg_add_cancel _
  have hfix : ∀ z, pa z = 0 → σ z = z := by
    intro z hz
    obtain ⟨w, rfl⟩ := exists_sqrt hz
    have hcw := hc w
    have hσw : σ w = w * (w⁻¹ * σ w) := by rw [mul_inv_cancel_left]
    rw [map_mul]
    generalize hcdef : w⁻¹ * σ w = c at hσw hcw
    have hcw' : c * w = w * c := central_of_pa_zero hcw w
    rw [hσw]
    calc w * c * (w * c) = w * (c * w) * c := by group
      _ = w * (w * c) * c := by rw [hcw']
      _ = w * w * (c * c) := by group
      _ = w * w := by rw [mul_self_of_pa_zero hcw, mul_one]
  have h2 : σ * σ = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    have hcx := hc x
    have hσx : σ x = x * (x⁻¹ * σ x) := by rw [mul_inv_cancel_left]
    generalize hcdef : x⁻¹ * σ x = c at hσx hcx
    calc σ (σ x) = σ (x * c) := by rw [← hσx]
      _ = σ x * σ c := map_mul σ x c
      _ = x * c * c := by rw [hfix c hcx, ← hσx]
      _ = x := by rw [mul_assoc, mul_self_of_pa_zero hcx, mul_one]
  have : σ ^ 3 = σ := by rw [pow_succ, pow_two, h2, one_mul]
  rw [← this, h3]

end SU

theorem no_s3_aut :
    ¬ ∃ σ τ : MulAut SylSU3_4, σ ≠ 1 ∧ σ ^ 3 = 1 ∧ τ ^ 2 = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  rintro ⟨σ, τ, hσ1, hσ3, hτ2, hτσ⟩
  have hστσ : σ * τ * σ = τ := by
    calc σ * τ * σ = σ * (τ * σ * τ⁻¹) * τ := by group
      _ = σ * σ⁻¹ * τ := by rw [hτσ]
      _ = τ := by group
  have hσ3' : σ * σ * σ = 1 := by rw [← hσ3, pow_succ, sq]
  have hτ2' : τ * τ = 1 := by rw [← hτ2, sq]
  refine F16_no_pair (SU.fbar σ) (SU.fbar τ) (SU.fbar_add σ) (SU.fbar_add τ) (SU.fbar_compat σ)
    (SU.fbar_compat τ) ?_ ?_ ?_ ?_
  · by_contra hne
    push Not at hne
    exact hσ1 (SU.aut_eq_one σ hσ3 hne)
  · intro a
    calc SU.fbar σ (SU.fbar σ (SU.fbar σ a)) = SU.fbar (σ * σ * σ) a := by
          rw [SU.fbar_mul, SU.fbar_mul]
      _ = a := by rw [hσ3', SU.fbar_one]
  · intro a
    calc SU.fbar τ (SU.fbar τ a) = SU.fbar (τ * τ) a := by rw [SU.fbar_mul]
      _ = a := by rw [hτ2', SU.fbar_one]
  · intro a
    calc SU.fbar σ (SU.fbar τ (SU.fbar σ a)) = SU.fbar (σ * τ * σ) a := by
          rw [SU.fbar_mul, SU.fbar_mul]
      _ = SU.fbar τ a := by rw [hστσ]

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open CFSG.GH74.GLS.Bg.TwoGroups

theorem iv2_2_9_no_S3_thm : IV2_2_9_no_S3 := by
  intro T _ _ ⟨φ⟩ H ⟨e⟩
  apply IV229.no_s3_aut
  have hc1 : (finRotate 3 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
  have hc3 : (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 := by decide
  have hs2 : (Equiv.swap (0 : Fin 3) 1) ^ 2 = 1 := by decide
  have hsc : Equiv.swap (0 : Fin 3) 1 * finRotate 3 * (Equiv.swap (0 : Fin 3) 1)⁻¹ =
      (finRotate 3 : Equiv.Perm (Fin 3))⁻¹ := by decide
  let Ψ : Equiv.Perm (Fin 3) →* MulAut SylSU3_4 :=
    (MulAut.congr φ).toMonoidHom.comp (H.subtype.comp e.symm.toMonoidHom)
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have h1 : (MulAut.congr φ) (H.subtype (e.symm x)) = (MulAut.congr φ) (H.subtype (e.symm y)) :=
      hxy
    have h2 := (MulAut.congr φ).injective h1
    have h3 : e.symm x = e.symm y := Subtype.ext h2
    exact e.symm.injective h3
  refine ⟨Ψ (finRotate 3), Ψ (Equiv.swap 0 1), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hc1 (hΨ (h.trans (map_one Ψ).symm))
  · rw [← map_pow, hc3, map_one]
  · rw [← map_pow, hs2, map_one]
  · rw [← map_mul, ← map_inv, ← map_mul, hsc, map_inv]

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
