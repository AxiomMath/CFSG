module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Relations
public import Certificates.Certificate197003

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

set_option linter.unusedSectionVars false


@[expose] def TwinFailY (x y s : HY) : Prop :=
  (∃ g ∈ ({x, y} : Set HY), ∀ k < 4, s * g * s⁻¹ ≠ x ^ k ∧ s * g * s⁻¹ ≠ y * x ^ k) ∧
    ∃ a ∈ ({x, y} : Set HY), ∃ b ∈ ({x, y} : Set HY), a * (s * b * s⁻¹) ≠ (s * b * s⁻¹) * a

private theorem q2_twinFail {x y s : HY} (h : Om2Facts.TwinFail (phi x) (phi y) (phi s)) :
    TwinFailY x y s := by
  have hc : ∀ g : HY, phi (s * g * s⁻¹) = phi s * phi g * (phi s)⁻¹ := fun g => by
    rw [map_mul, map_mul, map_inv]
  have hpair : ∀ g' ∈ ({phi x, phi y} : Set (Equiv.Perm (Fin 480))),
      ∃ g ∈ ({x, y} : Set HY), phi g = g' := by
    rintro g' (rfl | rfl)
    · exact ⟨x, Set.mem_insert _ _, rfl⟩
    · exact ⟨y, Set.mem_insert_of_mem _ rfl, rfl⟩
  obtain ⟨⟨g', hg', hk⟩, a', ha', b', hb', hab⟩ := h
  obtain ⟨g, hg, rfl⟩ := hpair g' hg'
  obtain ⟨a, ha, rfl⟩ := hpair a' ha'
  obtain ⟨b, hb, rfl⟩ := hpair b' hb'
  refine ⟨⟨g, hg, fun k hk4 => ⟨fun e => (hk k hk4).1 ?_, fun e => (hk k hk4).2 ?_⟩⟩,
    a, ha, b, hb, fun e => hab ?_⟩
  · rw [← hc, e, map_pow]
  · rw [← hc, e, map_mul, map_pow]
  · rw [← hc, ← map_mul, e, map_mul]

theorem q8_S0Y {x y : HY} (hx : x ∈ closureY wS0) (hy : y ∈ closureY wS0) (hxx : x * x = t0Y)
    (hyy : y * y = t0Y) (hyx : y * x * y⁻¹ = x⁻¹) :
    (x ∈ R0Y ∧ y ∈ R0Y) ∨ ∃ s ∈ closureY wT, TwinFailY x y s := by
  have hw := wordYOK_of_sub wS0_sub
  have h := Certificates.certificate197003.1 (phi x) ((mem_closureY_iff hw).1 hx) (phi y)
    ((mem_closureY_iff hw).1 hy) (by rw [← map_mul, hxx, phi_t0Y])
    (by rw [← map_mul, hyy, phi_t0Y]) (by rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv])
  rcases h with ⟨h1, h2⟩ | ⟨s, hs, hf⟩
  · exact Or.inl ⟨mem_R0Y_iff.2 h1, mem_R0Y_iff.2 h2⟩
  · obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordYOK_of_sub wT_sub) hs
    exact Or.inr ⟨s', hs', q2_twinFail hf⟩

theorem q8_ScY {x y : HY} (hx : x ∈ closureY wSc) (hy : y ∈ closureY wSc) (hxx : x * x = tcY)
    (hyy : y * y = tcY) (hyx : y * x * y⁻¹ = x⁻¹) : ∃ s ∈ closureY wCc, TwinFailY x y s := by
  have hw := wordYOK_of_sub wSc_sub
  obtain ⟨s, hs, hf⟩ := Certificates.certificate197003.2.1 (phi x)
    ((mem_closureY_iff hw).1 hx) (phi y) ((mem_closureY_iff hw).1 hy) (by rw [← map_mul, hxx, phi_tcY])
    (by rw [← map_mul, hyy, phi_tcY]) (by rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv])
  obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordYOK_of_sub wCc_sub) hs
  exact ⟨s', hs', q2_twinFail hf⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
