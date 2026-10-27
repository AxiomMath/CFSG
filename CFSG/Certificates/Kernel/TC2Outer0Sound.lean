module

public import Certificates.Data.Kernel.TC2Outer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2TableSpec

public section

namespace CFSG.KC.TC2Outer

open CFSG.EvenSporadicStandard.Fin76b.TableX

theorem checkSpec0_of_check0 {n : ℕ} {inn : ℕ → Bool} {mul : ℕ → ℕ → ℕ} {tI : ℕ}
    (h : outerCheck0 n inn mul tI = true) : CheckSpec0 n inn mul tI := by
  simp only [outerCheck0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, List.contains_iff_mem, List.mem_range, List.mem_filter] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩ := h
  refine
  { n_eq := h1
    tI_lt := h2
    inn_zero := h3
    inn_t := h4
    roots_ge := h5
    inn_closed := fun a ha hia b hb hib =>
      h6 a (mem_innList.2 ⟨ha, hia⟩) b (mem_innList.2 ⟨hb, hib⟩)
    inv := h7
    t_central := h8
    E_zero := h9
    E_t := h10
    E_roots := h11
    E_mul := h12
    E_inv := h13
    E_prod_roots := fun a ha => or_assoc.1 (h14 a ha)
    E_prod_invol := ?_
    t_invol := h16
    E_nonab := h17
    E_comm := h18
    E_center := ?_
    K_center := ?_
    K_cent := ?_
    sqrt_lt := ?_
    outer_nbr := ?_ }
  · intro a ha
    rcases h15 a ha with (h | h) | ⟨x, ⟨hx, hx2, hx0⟩, y, ⟨hy, hy2, hy0⟩, hxy⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, hx, hx2, hx0, y, hy, hy2, hy0, hxy⟩)
  · intro y hy hc
    rcases h19 y hy with (⟨f, hf, hne⟩ | h0) | ht
    · exact absurd (hc f hf) hne
    · exact Or.inl h0
    · exact Or.inr ht
  · intro y hy hc
    rcases h20 y hy with (⟨f, hf, hne⟩ | h0) | ht
    · exact absurd (hc f (by simpa using hf)) hne
    · exact Or.inl h0
    · exact Or.inr ht
  · intro y hy hc
    rcases h21 y hy with (⟨f, hf, hne⟩ | h0) | ht
    · exact absurd (hc f hf) hne
    · exact Or.inl h0
    · exact Or.inr ht
  · intro c hc hc2 hc0 hct
    rcases h22 c hc with ((hne | h0) | ht) | hlt
    · exact absurd hc2 hne
    · exact absurd h0 hc0
    · exact absurd ht hct
    · exact hlt
  · intro a ha hinn hsq
    rcases h23 a ha with (h | h) | h
    · rw [hinn] at h
      exact absurd h (by decide)
    · exact absurd hsq h
    · exact h

end CFSG.KC.TC2Outer
