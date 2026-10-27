module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem l154_oddInner_of_ambAlt {S : Type} [Group S] (h : catalogIs S l154AmbAlt) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  obtain ⟨i, ⟨hi, hnu⟩, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | sporadic s => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact oddInner_transport e oddInner_alt5
    · exact oddInner_transport e oddInner_alt6
    · exact oddInner_transport e oddInner_alt8
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    rcases ambiguous_two_lie hv hi with ⟨q, rfl, h7⟩ | ⟨q, rfl, h3⟩
    ·
      have hM := CFSG.Models.lieModel_A 1 q hv e
      have hsc : CFSG.Open.StatedClassicalModel S CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
        hM.2.resolve_right (fun h => absurd h.1 (by norm_num))
      have hq7 : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans h7
      haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
      have hF : Nat.card (GaloisField 7 1) = q.p ^ q.exponent := by
        rw [GaloisField.card 7 1 (by norm_num), pow_one, hq7]
      obtain ⟨e7⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated q.p q.exponent
        (F := GaloisField 7 1) q.exponent_pos hF hsc
      exact oddInner_transport e7 oddInner_psl27
    · exact absurd h3 hnu

section Certs


theorem l154_false_of_odd_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {y : Γ} (hK : GLAPComponent p X K) (hchev : IsChevSimple 2 (PSimple p K))
    (hyN : y ∈ Subgroup.normalizer (K : Set Γ)) (hyp : y ^ p = 1) (hF : FieldOn p y K)
    (hodd : ∀ φ : MulAut (PSimple p K), Odd (orderOf φ) → ∃ g : PSimple p K, φ = MulAut.conj g) :
    False := by
  have hα : MI.indAut p K y hyN ^ p = 1 := l154_indAut_pow_eq_one hyN hyp
  have hodd' : Odd (orderOf (MI.indAut p K y hyN)) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨g, hg⟩ := hodd _ hodd'
  have hin : InducesInnerMod p K y :=
    (MI.indAut_mem_inner_iff hp hK hyN).1 ⟨g, hg.symm⟩
  exact (MI.field_nonInnDiag_any hK hF).2 (MI.inner_innDiag_any hK hchev hyN hin)

theorem l154NIDOn_ambAlt : L154NIDOn l154AmbAlt := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_ambAlt hQ)).elim

theorem l154TD4On_ambAlt : L154TD4On l154AmbAlt := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_ambAlt hQ)).elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X
