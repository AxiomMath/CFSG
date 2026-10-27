module

public import CFSG.Fischer.Uniq.Cover
public import CFSG.Fischer.Uniq.CoverAut

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X} {P : Type} {M : LocalModel P}

theorem Pair.rigidity (hE : Pair X E) {d : X} (hd : d ∈ E) (L : LocalPoints M E d)
    {𝒮 : Set (Set P)} (h : CoverHyp L 𝒮) (hXi : (M.xi 𝒮).Connected)
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) (β : Equiv.Perm E)
    (hβ : ∀ x y : E, (x : X) * y = y * x ↔ ((β x : E) : X) * β y = β y * β x)
    (hβd : (β ⟨d, hd⟩ : X) = d) (hβstar : ∀ f : E, (f : X) ∈ LocalClass E d → (β f : X) = f) :
    (∀ x : E, β x = x) ∨ (∀ x : E, (β x : X) = d * x * d) := by
  have hcd : ∀ x : E, ((β x : E) : X) * d = d * β x ↔ (x : X) * d = d * x := by
    intro x
    have := (hβ x ⟨d, hd⟩).symm
    rwa [show β ⟨d, hd⟩ = ⟨d, hd⟩ from Subtype.ext hβd] at this
  have hmuSet : ∀ x : E, muSet E d (β x : X) = muSet E d x := by
    intro x
    ext s
    constructor
    · rintro ⟨hs, hsx⟩
      set s' : E := ⟨s, hs.1⟩
      have hβs : (β s' : X) = s := hβstar s' hs
      refine ⟨hs, hs.1, fun e => hsx.2.1 ?_, ?_⟩
      · have : s' = x := Subtype.ext e
        rw [← hβs, this]
      · have := (hβ s' x).2
        rw [hβs] at this
        exact this hsx.2.2
    · rintro ⟨hs, hsx⟩
      set s' : E := ⟨s, hs.1⟩
      have hβs : (β s' : X) = s := hβstar s' hs
      refine ⟨hs, hs.1, fun e => hsx.2.1 ?_, ?_⟩
      · have h1 : β s' = β x := Subtype.ext (hβs.trans e)
        exact congrArg (fun y : E => (y : X)) (β.injective h1)
      · have := (hβ s' x).1 hsx.2.2
        rwa [hβs] at this
  have hfar : ∀ c : farSet E d, (β ⟨c, c.2.1⟩ : X) ∈ farSet E d := by
    intro c
    refine ⟨(β _).2, fun e => c.2.2.1 ((hcd ⟨c, c.2.1⟩).1 e), ?_⟩
    rw [hmuSet]
    exact c.2.2.2
  let P' := coverOf hE hd L h
  let φ : farSet E d → farSet E d := fun c => ⟨β ⟨c, c.2.1⟩, hfar c⟩
  let ψ : farSet E d → farSet E d := fun c => ⟨d * c * d, conj_mem_farSet hE hd c.2⟩
  have hφπ : ∀ c : farSet E d, P'.π (φ c) = P'.π c := by
    intro c
    apply Subtype.ext
    show L.muImg (β ⟨c, c.2.1⟩ : X) = L.muImg c
    ext p
    rw [← Equiv.apply_symm_apply L.χ p, L.χ_mem_muImg_iff, L.χ_mem_muImg_iff,
      show (β ⟨c, c.2.1⟩ : X) = (β ⟨c, c.2.1⟩ : E) from rfl, hmuSet]
  have hψπ : ∀ c : farSet E d, P'.π (ψ c) = P'.π c := by
    intro c
    apply Subtype.ext
    exact L.muImg_conj hE hd c.2.1 c.2.2.1
  have hφadj : ∀ c c' : farSet E d, P'.adj.Adj c c' → P'.adj.Adj (φ c) (φ c') := by
    rintro c c' ⟨hne, hc⟩
    refine ⟨fun e => hne ?_, (hβ ⟨c, c.2.1⟩ ⟨c', c'.2.1⟩).1 hc⟩
    exact congrArg (fun y : E => (y : X)) (β.injective (Subtype.ext e))
  have hψadj : ∀ c c' : farSet E d, P'.adj.Adj c c' → P'.adj.Adj (ψ c) (ψ c') := by
    rintro c c' ⟨hne, hc⟩
    refine ⟨fun e => hne ?_, ?_⟩
    · have : (d : X) * c * d = d * c' * d := e
      simpa using this
    · show d * (c : X) * d * (d * c' * d) = d * c' * d * (d * c * d)
      have hdd : d * d = 1 := Pair.mul_self hE hd
      calc d * (c : X) * d * (d * c' * d) = d * (c * c') * d := by
            rw [show d * (c : X) * d * (d * c' * d) = d * c * (d * d) * c' * d by group, hdd]
            group
        _ = d * (c' * c) * d := by rw [hc]
        _ = d * c' * d * (d * c * d) := by
            rw [show d * (c' : X) * d * (d * c * d) = d * c' * (d * d) * c * d by group, hdd]
            group
  have hφinj : Function.Injective φ := fun c c' e => Subtype.ext
    (congrArg (fun y : E => (y : X)) (β.injective (Subtype.ext
      (congrArg (fun y : farSet E d => (y : X)) e))))
  have hψinj : Function.Injective ψ := fun c c' e => Subtype.ext (by
    have : (d : X) * c * d = d * c' * d := congrArg Subtype.val e
    simpa using this)
  have hidπ : ∀ c : farSet E d, P'.π (id c) = P'.π c := fun c => rfl
  have hidadj : ∀ c c' : farSet E d, P'.adj.Adj c c' → P'.adj.Adj (id c) (id c') :=
    fun _ _ h => h
  have hcls : ∀ x : E, (x : X) = d ∨ (x : X) ∈ LocalClass E d ∨ (x : X) ∈ farSet E d := by
    intro x
    by_cases h0 : (x : X) = d
    · exact Or.inl h0
    · by_cases h1 : (x : X) * d = d * x
      · exact Or.inr (Or.inl ⟨x.2, h0, h1⟩)
      · exact Or.inr (Or.inr ⟨x.2, h1, hmu x x.2 h1⟩)
  by_cases hne : (farSet E d).Nonempty
  swap
  · left
    intro x
    apply Subtype.ext
    rcases hcls x with h0 | h1 | h2
    · rw [h0]
      have : x = ⟨d, hd⟩ := Subtype.ext h0
      rw [this]
      exact hβd
    · exact hβstar x h1
    · exact absurd ⟨_, h2⟩ hne
  obtain ⟨c₀, hc₀⟩ := hne
  have hfib := h.fib _ hc₀ _ (hfar ⟨c₀, hc₀⟩) (by
    have := congrArg Subtype.val (hφπ ⟨c₀, hc₀⟩)
    exact this.symm)
  rcases hfib with e | e
  · left
    have hφ := TwoCover.eq_of_eq_at P' P' hXi hφπ hidπ hφadj hidadj hφinj Function.injective_id
      (c₀ := ⟨c₀, hc₀⟩) (Subtype.ext e)
    intro x
    apply Subtype.ext
    rcases hcls x with h0 | h1 | h2
    · rw [h0]
      have : x = ⟨d, hd⟩ := Subtype.ext h0
      rw [this]
      exact hβd
    · exact hβstar x h1
    · have := congrArg (fun f => ((f ⟨x, h2⟩ : farSet E d) : X)) hφ
      exact this
  · right
    have hφ := TwoCover.eq_of_eq_at P' P' hXi hφπ hψπ hφadj hψadj hφinj hψinj
      (c₀ := ⟨c₀, hc₀⟩) (Subtype.ext e)
    intro x
    rcases hcls x with h0 | h1 | h2
    · have : x = ⟨d, hd⟩ := Subtype.ext h0
      rw [this, hβd, mul_assoc, Pair.mul_self hE hd, mul_one]
    · rw [hβstar x h1, ← h1.2.2, mul_assoc, Pair.mul_self hE hd, mul_one]
    · have := congrArg (fun f => ((f ⟨x, h2⟩ : farSet E d) : X)) hφ
      exact this

end CFSG.Fischer
