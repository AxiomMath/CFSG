module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conf

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open CFSG CFSG.Blueprint CFSG.GH74.GLS

theorem isL2Model_of_hasL2Model {K : Type} [Group K]
    (h : HasL2Model K (fun q => Odd q ∧ 3 < q)) : IsL2Model K := by
  obtain ⟨p, f, hp, hf, ⟨hodd, h3⟩, hL⟩ := h
  rcases hL with ⟨-, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hmod
    exact ⟨F, hF, hFin, ⟨by rw [hcard]; exact hodd, by rw [hcard]; exact h3⟩, ⟨e⟩⟩
  all_goals exact absurd h0 (by norm_num)

end CFSG.GH74.GLS.Stage1.Thm6.Glue
