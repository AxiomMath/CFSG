module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check

theorem noQ16_of_noQ16Check {Y M : Type} [Group Y] [Group M] [DecidableEq M] {ι : Y →* M}
    (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m) {reps : List M}
    (h : Check.noQ16Check L reps = true) : NoQ16 Y := by
  rintro x y ⟨hx4, hx8, hy2, hyx⟩
  have hcov : coverB reps L = true := (Bool.and_eq_true_iff.1 h).1
  have hq : ∀ t ∈ reps, Check.q16At t (centB L t) = true := fun t ht =>
    List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 t ht
  have hz2 : orderOf (x ^ 4) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hx8) hx4
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hι hL hcov hz2
  set x' := g * x * g⁻¹ with hx'
  set y' := g * y * g⁻¹ with hy'
  have hx'4 : x' ^ 4 = r := by rw [hx', conj_pow, hg]
  have hy'2 : y' * y' = r := by
    rw [← hg, ← hy2, hy', ← sq, conj_pow]
  have hyx' : y * x = x⁻¹ * y := by
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x⁻¹ * y := by rw [hyx]
  have hkey : y' * x' = x'⁻¹ * y' := by
    calc y' * x' = g * (y * x) * g⁻¹ := by rw [hx', hy']; group
      _ = g * (x⁻¹ * y) * g⁻¹ := by rw [hyx']
      _ = x'⁻¹ * y' := by rw [hx', hy']; group
  have hx'C : ι x' ∈ centB L (ι r) :=
    (mem_centB hι hL).2 ⟨x', by rw [← hx'4]; exact (Commute.self_pow x' 4).eq, rfl⟩
  have hy'C : ι y' ∈ centB L (ι r) :=
    (mem_centB hι hL).2 ⟨y', by rw [← hy'2]; exact (mul_assoc y' y' y').symm, rfl⟩
  have h2 := hq (ι r) hr
  unfold Check.q16At at h2
  have h3 := List.all_eq_true.1 h2 (ι x')
    (List.mem_filter.2 ⟨hx'C, decide_eq_true (by rw [← map_pow, hx'4])⟩)
  have h4 := List.all_eq_true.1 h3 (ι y')
    (List.mem_filter.2 ⟨hy'C, decide_eq_true (by rw [← map_mul, hy'2])⟩)
  have h5 : ι y' * ι x' = (ι x')⁻¹ * ι y' := by
    rw [← map_inv, ← map_mul, ← map_mul, hkey]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h4
  exact h4 h5

end CFSG.CGT.PushingUpLit.SolKNA.R4
