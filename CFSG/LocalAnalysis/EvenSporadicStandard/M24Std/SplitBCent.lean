module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import Certificates.Certificate24863

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

theorem eq_one_of_fix_base (z : S24)
    (hz : ∀ i : Fin 24, i.val < 7 → (z : Equiv.Perm (Fin 24)) i = i) : z = 1 := by
  have hV : ValidSchreier m24Certificate := m24Certificate_check
  have h1 : (z : Equiv.Perm (Fin 24)) ∈ m24Certificate.levelSubgroup m24Certificate.baseCount := by
    rw [RawSchreierDatum.mem_levelSubgroup_iff _ hV _ le_rfl]
    refine ⟨by rw [m24Certificate_originalSubgroup]; exact z.2, fun b hb => hz b ?_⟩
    have hb' := List.mem_of_mem_take hb
    have hl : m24Certificate.base.toList = [0, 1, 2, 3, 4, 5, 6] := by decide
    rw [hl] at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [RawSchreierDatum.levelSubgroup_terminal_eq_bot _ hV, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

private theorem apply_comm {x b : S24} (h : x * b = b * x) (p : Fin 24) :
    (x : Equiv.Perm (Fin 24)) ((b : Equiv.Perm (Fin 24)) p) =
      (b : Equiv.Perm (Fin 24)) ((x : Equiv.Perm (Fin 24)) p) := by
  have := congrArg (fun t : S24 => (t : Equiv.Perm (Fin 24)) p) h
  simpa using this

theorem centB0 (x : S24)
    (hx : ∀ b ∈ m24B0l, x * b = b * x) : x ∈ m24B0l := by
  obtain ⟨hcomm, hfree, hcover, hconj⟩ := Certificates.certificate24863
  have hq : ∀ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) ((x : Equiv.Perm (Fin 24)) splitBPt) =
      (x : Equiv.Perm (Fin 24)) splitBPt → b = 1 := by
    intro b hb hbq
    refine hfree b hb ((x : Equiv.Perm (Fin 24)).injective ?_)
    rw [apply_comm (hx b hb), hbq]
  obtain ⟨b₁, hb₁, hb₁p⟩ := hcover _ hq
  obtain ⟨y, hy⟩ : ∃ y : S24, y = b₁⁻¹ * x := ⟨_, rfl⟩
  have hyc : ∀ b ∈ m24B0l, y * b = b * y := by
    intro b hb
    have h1 : b₁⁻¹ * b = b * b₁⁻¹ := (Commute.inv_left (hcomm b₁ hb₁ b hb)).eq
    rw [hy, mul_assoc, hx b hb, ← mul_assoc, h1, mul_assoc]
  have hyp : (y : Equiv.Perm (Fin 24)) splitBPt = splitBPt := by
    rw [hy]
    change ((b₁ : Equiv.Perm (Fin 24))⁻¹ * (x : Equiv.Perm (Fin 24))) splitBPt = splitBPt
    rw [Equiv.Perm.mul_apply, ← hb₁p, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hz : (m24Cj splitBWord)⁻¹ * y * m24Cj splitBWord = 1 := by
    refine eq_one_of_fix_base _ fun i hi => ?_
    obtain ⟨b, hb, hbp⟩ := hconj i hi
    have h1 : (y : Equiv.Perm (Fin 24)) ((m24Cj splitBWord : Equiv.Perm (Fin 24)) i) =
        (m24Cj splitBWord : Equiv.Perm (Fin 24)) i := by
      rw [← hbp, apply_comm (hyc b hb), hyp]
    change ((m24Cj splitBWord : Equiv.Perm (Fin 24))⁻¹ * (y : Equiv.Perm (Fin 24)) *
      (m24Cj splitBWord : Equiv.Perm (Fin 24))) i = i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]
  have hy1 : y = 1 := by
    have : y = m24Cj splitBWord * ((m24Cj splitBWord)⁻¹ * y * m24Cj splitBWord) *
        (m24Cj splitBWord)⁻¹ := by group
    rw [this, hz]
    group
  have hxb : x = b₁ := by
    have : x = b₁ * y := by rw [hy]; group
    rw [this, hy1, mul_one]
  rw [hxb]
  exact hb₁

theorem cent_of_octadType
    {G : Type} [Group G] {L B : Subgroup G} (h : OctadType L B) :
    ∀ l ∈ L, (∀ b ∈ B, l * b = b * l) → l ∈ B := by
  obtain ⟨-, e, he⟩ := h
  intro l hl hcomm
  have key : (e ⟨l, hl⟩ : S24) ∈ m24B0l := by
    refine centB0 _ fun c hc => ?_
    have hxB : ((e.symm c : L) : G) ∈ B := (he (e.symm c)).2 (by simpa using hc)
    have h1 : (⟨l, hl⟩ : L) * e.symm c = e.symm c * ⟨l, hl⟩ := Subtype.ext (hcomm _ hxB)
    simpa using congrArg e h1
  exact (he ⟨l, hl⟩).2 key

end CFSG.EvenSporadicStandard.M24Std
