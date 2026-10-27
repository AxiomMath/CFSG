module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAS5

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup

section Core

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_fixed_exists (ht : t * t = 1) {B : Type} [Group B] (f : B →* D)
    (hf : Function.Injective f) (hnab : ∃ a b : B, a * b ≠ b * a)
    (hn : ∀ b, ∃ c, t * f b * t⁻¹ = f c) : ∃ b : B, b ≠ 1 ∧ t * f b = f b * t := by
  by_contra hcon
  push Not at hcon
  have hnO : ∀ o ∈ f.range, t * o * t⁻¹ ∈ f.range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := hn b
    exact ⟨c, hc.symm⟩
  have hfix : ∀ o ∈ f.range, t * o = o * t → o = 1 := by
    rintro _ ⟨b, rfl⟩ hb
    by_cases hb1 : b = 1
    · rw [hb1, map_one]
    · exact absurd hb (hcon b hb1)
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  have := (inv_of_centralizer_eq_bot (O := f.range) ht hnO hfix).2 (f a) ⟨a, rfl⟩ (f b) ⟨b, rfl⟩
  exact hf (by rw [map_mul, map_mul]; exact this)

theorem s3a_contra_range (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) {B : Type} [Group B]
    (f : B →* D) (hf : Function.Injective f) (hnab : ∃ a b : B, a * b ≠ b * a)
    (hP : ∀ b : B, b ≠ 1 → ∃ y : B, y * b = b * y ∧ y ≠ 1 ∧ y ≠ b)
    (hn : ∀ b, ∃ c, t * f b * t⁻¹ = f c)
    (hW : ∀ (b : B) (a : ↥(alternatingGroup (Fin 5))), f b * s3a_iota ψ a = s3a_iota ψ a * f b) :
    False := by
  obtain ⟨b, hb1, hbc⟩ := s3a_fixed_exists h.t_sq f hf hnab hn
  have hmemC : ∀ x : D, t * x = x * t → x ∈ centralizer ({t} : Set D) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hx
  have hfb1 : f b ≠ 1 := fun e => hb1 (hf (by rw [e, map_one]))
  have hfbt : f b = t := by
    rcases s3a_cent_iota h ψ (hmemC _ hbc) (hW b) with e | e
    · exact absurd e hfb1
    · exact e
  obtain ⟨y, hy, hy1, hyb⟩ := hP b hb1
  have hfy : t * f y = f y * t := by
    rw [← hfbt, ← map_mul, ← map_mul, hy]
  rcases s3a_cent_iota h ψ (hmemC _ hfy) (hW y) with e | e
  · exact hy1 (hf (by rw [e, map_one]))
  · exact hyb (hf (by rw [e, hfbt]))

end Core

section Prod

theorem s3a_prod_comm_exists : ∀ x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)),
    x ≠ 1 → ∃ y, y * x = x * y ∧ y ≠ 1 ∧ y ≠ x := by
  obtain ⟨c, hc⟩ := s3a_exists_ne_one (A := ↥(alternatingGroup (Fin 5)))
    (by
      have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact s3a_A5_noncomm)
  rintro ⟨a, b⟩ hx
  by_cases ha : a = 1
  · have hb : b ≠ 1 := fun hb => hx (by rw [ha, hb]; rfl)
    refine ⟨(c, 1), ?_, ?_, ?_⟩
    · simp [ha]
    · intro e; exact hc (congrArg Prod.fst e)
    · intro e; apply hc; have := congrArg Prod.fst e; simpa [ha] using this
  · by_cases hb : b = 1
    · refine ⟨(1, c), ?_, ?_, ?_⟩
      · simp [hb]
      · intro e; exact hc (congrArg Prod.snd e)
      · intro e; apply hc; have := congrArg Prod.snd e; simpa [hb] using this
    · refine ⟨(a, 1), ?_, ?_, ?_⟩
      · simp
      · intro e; exact ha (congrArg Prod.fst e)
      · intro e; apply hb; have := congrArg Prod.snd e; simpa using this.symm

theorem s3a_card_A5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

end Prod

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
