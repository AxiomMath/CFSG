module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
public import Certificates.Certificate12642

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu Subgroup

theorem commute_of_mem_S_of_commute_z
    (k : Fin 3) {g h : GJ}
    (hg : g ∈ SJ k) (hh : h ∈ SJ k) (hgz : g * zJ = zJ * g) : g * h = h * g := by
  obtain ⟨i, hi, hrg⟩ := exists_rep_subOf (by decide) (enumS k.1 k.2).1 hg
  obtain ⟨j, hj, hrh⟩ := exists_rep_subOf (by decide) (enumS k.1 k.2).1 hh
  rw [(enumS k.1 k.2).2] at hi hj
  have hcz : commA (cS k.1).pts[i]! zArr = true :=
    commA_of_commute hrg rep_z (Commute.eq hgz |> fun e => e)
  have h0 := Certificates.certificate12642
  simp only [sCentOK, List.all_eq_true, List.mem_range] at h0
  have h1 := h0 k.1 k.2 i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · rw [hcz] at h1; exact Bool.noConfusion h1
  · have h2 := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
    exact (commute_of_commA hrg hrh h2).eq

theorem inf_centralizer_z_le_centralizer
    {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (hXE : E0 ≤ normalizer (X : Set GJ)) :
    X ⊓ centralizer ({zJ} : Set GJ) ≤ centralizer (X : Set GJ) := by
  obtain ⟨k, hk⟩ := le_S hX2 hXE
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  have := commute_of_mem_S_of_commute_z k (hk hg.1) (hk hh)
    (mem_centralizer_singleton_iff.1 hg.2)
  exact this.symm

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
