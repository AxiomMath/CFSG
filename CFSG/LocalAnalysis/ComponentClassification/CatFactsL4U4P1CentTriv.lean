module

public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def centTrivOK (n : Nat) (sift : Table → Bool) (hs : List (Table × Table)) : Bool :=
  hs.length == n && (List.range n).all fun i =>
    let p := hs.getD i default
    permOK n p.1 && permOK n p.2 && sift p.1 && sift p.2 && ap p.1 i == i && ap p.2 i == i &&
      (List.range n).all fun j => j == i || ap p.1 j != j || ap p.2 j != j

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem eq_one_of_centTrivOK (hD : GroupData n P pg gg sift) {hs : List (Table × Table)}
    (h : centTrivOK n sift hs = true) {c : Equiv.Perm (Fin n)}
    (hc : ∀ g ∈ P, c * g = g * c) : c = 1 := by
  simp only [centTrivOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨-, hall⟩ := h
  ext ⟨i, hi⟩
  obtain ⟨⟨⟨⟨⟨⟨hp1, hp2⟩, hs1⟩, hs2⟩, hf1⟩, hf2⟩, honly⟩ := hall i hi
  set p := hs.getD i default
  have hr1 := rep_tp hp1
  have hr2 := rep_tp hp2
  have hm1 := (hD.sift _ _ hr1).1 hs1
  have hm2 := (hD.sift _ _ hr2).1 hs2
  have hap : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → ∀ j : Fin n,
      ap T j = (g j : ℕ) := by
    intro T g hT j
    rw [hT j j.2, idx_of_lt _ j.2]
    rfl
  have hfix : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → ap T i = i →
      g ⟨i, hi⟩ = ⟨i, hi⟩ :=
    fun T g hT h1 => Fin.ext (by rw [← hap T g hT ⟨i, hi⟩]; exact h1)
  set j := c ⟨i, hi⟩
  have hj : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → g ∈ P → ap T i = i →
      ap T j = j := by
    intro T g hT hg h1
    rw [hap T g hT j]
    have h2 := congrArg (fun f : Equiv.Perm (Fin n) => f ⟨i, hi⟩) (hc g hg)
    simp only [Equiv.Perm.mul_apply, hfix T g hT h1] at h2
    rw [← h2]
  have hj1 := hj _ _ hr1 hm1 hf1
  have hj2 := hj _ _ hr2 hm2 hf2
  rcases honly j j.2 with (h3 | h3) | h3
  · rw [Equiv.Perm.one_apply]
    exact h3
  · exact absurd hj1 h3
  · exact absurd hj2 h3

end CFSG.ComponentClassification.HarrisLit.P1
