module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47GraphEnd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem harris47_of
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKG : AutPSL2SylowInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGA : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hT1 : Harris82Theorem1KProper) (hCI : GSLit.ClassicalInvolutionInput)
    (h34 : Harris81Lemma34Input) (h35 : Harris81Lemma35Step)
    (hQ81 : Harris47Q81Input) (hC3 : L4U4InvolutionCentralizerFact)
    (hC5 : L34CoverInvolutionFact) (hC8 : AlternatingCoverInvolutionFact) :
    Harris47Input := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j' J hJ k hk htype
  have hc := harris46c_of hFC hKC hSch h219 hSD X hnonab hK hcat t L p f S w z V i j hs i' j'
  have hd := harris46d_of hFC hKC hSch h219 hSD hGA hGC hCI h34 X hnonab hK hcat t L p f S w z V
    i j hs i' j'
  have he := harris46eOdd_of hFC hKC hSch h219 hSD hGA hGC hCI h34 X hnonab hK hcat t L p f S w z
    V i j hs i' j'
  obtain ⟨hm2, hgraph⟩ := hs.setup.graph_of_lemma47 hnonab hK hcat hSch hFC hKC hKG hGA hT1 hC3
    i' j' hc hd he hJ hk htype
  have hp : p.Prime := hs.standing.config.prime
  have hp2 : p ≠ 2 := hs.standing.config.ne_two
  by_cases hs3 : p ^ k = 3
  ·
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := hs3 ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    have hk1 : k = 1 := by
      by_contra hk1
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hk1
    have hfe : Even f := hs.standing.dihedral.even 3 f hp hp2 hs.standing.config.lieModel
    have hf4 : f = 4 := by
      obtain ⟨m, hm⟩ := hfe
      omega
    exact hQ81 X hnonab hK hcat t L 3 f S w z V i j hs rfl hf4 i' j' J hJ htype
  ·
    have hodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have h3 : 3 ≤ p ^ k := by
      have h3p : 3 ≤ p := by
        have := hp.two_le
        rcases hp.eq_two_or_odd' with h2 | ⟨m, hm⟩ <;> omega
      calc 3 ≤ p := h3p
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have hs5 : 5 ≤ p ^ k := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact hs.setup.false_of_graph hnonab hK hcat hSch hFC hKC hI hKG hGA h219 h35 hC5 hC8 i' j'
      hk hs5 hgraph

end CFSG.ComponentClassification.HarrisLit
