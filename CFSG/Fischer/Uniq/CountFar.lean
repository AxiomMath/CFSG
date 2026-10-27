module

public import CFSG.Fischer.Uniq.Counting
public import CFSG.Fischer.Uniq.Cover

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem Pair.ncard_farSet (hP : Pair X E) {d : X} (hd : d ∈ E) {k l m : ℕ}
    (hk : (LocalClass E d).ncard = k)
    (hk' : ∀ f ∈ LocalClass E d, (LocalClass E f).ncard = k)
    (hl : ∀ f ∈ LocalClass E d, (LocalClass E d ∩ LocalClass E f).ncard = l)
    (hm : ∀ c ∈ farSet E d, (muSet E d c).ncard = m) :
    (farSet E d).ncard * m = k * (k - 1 - l) := by
  have := Pair.finite hP
  rw [← hk]
  refine ncard_mul_eq_ncard_mul (fun c f => c * f = f * c) (fun c hc => ?_) (fun f hf => ?_)
  · rw [← hm c hc]
    congr 1
    ext f
    constructor
    · rintro ⟨hf, hcf⟩
      refine ⟨hf, hf.1, ?_, hcf.symm⟩
      rintro rfl
      exact hc.2.1 hf.2.2
    · rintro ⟨hf, hfc⟩
      exact ⟨hf, hfc.2.2.symm⟩
  · have h := hk' f hf
    have h2 := hl f hf
    have hd' : d ∉ LocalClass E d ∩ LocalClass E f ∪
        {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c} := by
      rintro (h | h)
      · exact h.1.2.1 rfl
      · exact h.1.2 rfl
    have hdisj : Disjoint (LocalClass E d ∩ LocalClass E f)
        {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c} :=
      Set.disjoint_left.2 fun c hc hc' => hc'.1.2 hc.1.2.2
    have heq : {c | c ∈ farSet E d ∧ c * f = f * c} =
        {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c} := by
      ext c
      constructor
      · rintro ⟨hc, hcf⟩
        exact ⟨⟨hc.1, hc.2.1⟩, hcf⟩
      · rintro ⟨⟨hc, hcd⟩, hcf⟩
        refine ⟨⟨hc, hcd, f, hf, hf.1, ?_, hcf.symm⟩, hcf⟩
        rintro rfl
        exact hcd hf.2.2
    rw [heq]
    rw [localClass_eq_insert hd hf, Set.ncard_insert_of_notMem hd', Set.ncard_union_eq hdisj,
      h2] at h
    omega

end CFSG.Fischer
