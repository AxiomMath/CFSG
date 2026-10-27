module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RQuot
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
public import CFSG.GH74.GLS.IVK.Statements.Sec4b

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Assembly.LowTwoRank

namespace Ivk41R

theorem charP_of_natCard_eq_pow {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ n) : CharP F p := by
  have := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h0
  exact (CharP.charP_iff_prime_eq_zero hp).mpr (pow_eq_zero_iff'.mp h0).1

end Ivk41R

open Ivk41R in
theorem ivk_4_1_R_L3 : IVK_4_1_R_L3 := by
  intro J _ _ p n hp hp2 hJ z hz X hXz hXp hXc
  rcases hJ with (⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h1, -⟩) | (⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h1, -⟩)
  · have hchar : CharP F p := charP_of_natCard_eq_pow hp hcard
    exact rgood_transport (e.trans (specialLinearGroupEquivStatedSL 3 F).symm)
      (fun z' X' hz' hXz' _ hXc' => rgood_sl3 hp hp2 hcard hz' hXz' hXc') hz hXz hXp hXc
  · exact absurd h1 (by norm_num)
  · have hchar : CharP F p := charP_of_natCard_eq_pow hp hcard
    exact rgood_transport (e.trans (Lemma41dL3.projEquiv F).symm)
      (fun z' X' hz' hXz' hXp' hXc' => rgood_projectiveSL3 hp hp2 hcard hz' hXz' hXp' hXc')
      hz hXz hXp hXc
  · exact absurd h1 (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
