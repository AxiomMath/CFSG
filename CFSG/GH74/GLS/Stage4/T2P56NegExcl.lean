module

public import CFSG.GH74.GLS.Stage4.T2P56Excl

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

theorem eps_eq_neg_one_of_layer {Y : Type} [Group Y] [Finite Y] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (E : Subgroup (Y ⧸ pPrimeCore 2 Y)) [E.Normal]
    (hEodd : Odd E.index) (hE : IsLnEps 3 ↥E ε (p ^ n))
    (hshape : (p ^ n % 4 = 1 ∧ HasSDSylow Y) ∨ (p ^ n % 4 = 3 ∧ HasWreathedSylow Y)) : ε = -1 := by
  rcases hε with h | h
  · exfalso
    subst h
    rcases hshape with ⟨h1, ⟨S, m, hm, ⟨e⟩⟩⟩ | ⟨h3, ⟨S, m, hm, ⟨e⟩⟩⟩
    · obtain ⟨S', ⟨e'⟩⟩ := exists_sylow_of_layer (T := CFSG.Open.SemidihedralGroup m) ⟨S, ⟨e⟩⟩ E hEodd
      have hcong : ((p ^ n : ℕ) : ℤ) ≡ 1 [ZMOD 4] := by
        unfold Int.ModEq; omega
      obtain ⟨m', hm', ⟨e''⟩⟩ := (Proofs2.ivk_4_4b ↥E 1 p n hp hp2 hE S').2 hcong
      exact not_sd_and_wreathed hm hm' ⟨e'⟩ ⟨e''⟩
    · obtain ⟨S', ⟨e'⟩⟩ := exists_sylow_of_layer (T := CFSG.Open.WreathedTwoGroup m) ⟨S, ⟨e⟩⟩ E hEodd
      have hncong : ¬ ((p ^ n : ℕ) : ℤ) ≡ 1 [ZMOD 4] := by
        unfold Int.ModEq; omega
      obtain ⟨m', ⟨hm', ⟨e''⟩⟩⟩ := (Proofs2.ivk_4_4b ↥E 1 p n hp hp2 hE S').1 hncong
      exact not_sd_and_wreathed hm' hm ⟨e''⟩ ⟨e'⟩
  · exact h

end CFSG.GH74.GLS.Stage4.Rest
