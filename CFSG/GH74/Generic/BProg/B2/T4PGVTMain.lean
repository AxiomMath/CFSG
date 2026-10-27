module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTOrd
public import CFSG.GH74.Generic.BProg.B2.T4PGVTL3
public import CFSG.GH74.Generic.BProg.B2.T4PGVTL3Out
public import CFSG.GH74.Generic.BProg.B2.T4PGVTU3Out
public import CFSG.GH74.Generic.BProg.B2.T4PGVTSp4
public import CFSG.GH74.Generic.BProg.B2.T4PGVTExc
public import CFSG.GH74.Generic.BProg.B2.T4PGVTG2Three

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

theorem q3_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hodd : Odd f) :
    Q3Empty (fun X _ => LieModel X .PSL 3 p f) := by
  by_cases h5 : 5 ≤ p ^ f
  · exact Q3Empty.of_in_out (q3In_l3 hp hp2 h5 hodd) (q3Out_l3 hp hp2 h5 hodd)
  · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf
      (pow_le_three_of_lt_five hp hp2 h5)
    exact q3_l3three

theorem q3_u3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3Empty (fun X _ => LieModel X .PSU 3 p f) := by
  by_cases h5 : 5 ≤ p ^ f
  · exact Q3Empty.of_in_out (q3In_u3 hp hp2 h5) (q3Out_u3 hp hp2 h5)
  · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf
      (pow_le_three_of_lt_five hp hp2 h5)
    exact q3_u3three

theorem q3_g2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3Empty (fun X _ => LieModel X .G2 0 p f) := by
  refine Q3Empty.of_in_out (q3In_g2 p f hp hp2 hf) ?_
  by_cases hp3 : p = 3
  · subst hp3
    exact q3Out_g2three hf
  · exact q3Out_g2 hp hp2 hp3 hf

theorem q3_d4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3Empty (fun X _ => LieModel X .trialityD4 0 p f) :=
  Q3Empty.of_in_out (q3In_d4 p f hp hp2 hf) (q3Out_d4 hp hp2 hf)

theorem q3Table_holds :
    Q3Table := by
  intro N _ _ H t K hs hGH
  rcases hGH with ⟨n, -, h11, he⟩ | hspor | ⟨p, f, hp, hf, hrow⟩
  · exact (q3_alt n h11 N H t K hs he).elim
  · exfalso
    rcases hspor with h | h | h | h | h | h | h | h | h
    · exact q3_m11 N H t K hs h
    · exact q3_m12 N H t K hs h
    · exact q3_m22 N H t K hs h
    · exact q3_m23 N H t K hs h
    · exact q3_j1 N H t K hs h
    · exact q3_j2 N H t K hs h
    · exact q3_j3 N H t K hs h
    · exact q3_mcl N H t K hs h
    · exact q3_ly N H t K hs h
  · rcases hrow with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, -, hm⟩ | ⟨hp2, -, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨-, hm | hm | hm | hm | hm⟩
    · exact (q3_l2 p f hp hp2 N H t K hs hm).elim
    · by_cases hev : Even f
      · obtain ⟨g, hg⟩ := hev
        refine Or.inr (Or.inl ⟨p, g, hp, hp2, by omega, ?_⟩)
        have : 2 * g = f := by omega
        rwa [this]
      · exact (q3_l3 hp hp2 hf (Nat.not_even_iff_odd.mp hev) N H t K hs hm).elim
    · exact (q3_u3 hp hp2 hf N H t K hs hm).elim
    · exact (q3_sp4 hp hp2 hf N H t K hs hm).elim
    · exact (q3_g2 hp hp2 hf N H t K hs hm).elim
    · exact (q3_d4 hp hp2 hf N H t K hs hm).elim
    · exact Or.inr (Or.inr ⟨p, f, hp, hp2, hf, Or.inl hm⟩)
    · exact Or.inr (Or.inr ⟨p, f, hp, hp2, hf, Or.inr hm⟩)
    · exact Or.inl ⟨p, f, hp, PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inl hmod), hf,
        Or.inl ⟨hmod, hm⟩⟩
    · exact Or.inl ⟨p, f, hp, PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inr hmod), hf,
        Or.inr ⟨hmod, hm⟩⟩
    · exact (q3_ree f N H t K hs hm).elim
    · exact (q3_l28 N H t K hs hm).elim
    · exact (q3_l216 N H t K hs hm).elim
    · exact (q3_l34 N H t K hs hm).elim
    · exact (q3_u34 N H t K hs hm).elim
    · exact (q3_sz8 N H t K hs hm).elim

end CFSG.GH74.Generic.BProg.B2.T4.PGV
