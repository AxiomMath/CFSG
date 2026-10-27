module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FCompl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7E

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_inv_of_normalized [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B E U : Subgroup G}
    (hE : Sec7E G t L S z g B E) (hUE : U ≤ E)
    (hHU : ∀ h ∈ MSub S B ⊓ normalizer (E : Set G), ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∀ n ∈ L ⊓ MSub S B, ∀ u ∈ U, ∃ u' ∈ U, ∃ o ∈ oddCoreIn (MSub S B),
      n * u * n⁻¹ = u' * o := by
  intro n hn u hu
  obtain ⟨o, ho, h, hh, rfl⟩ :=
    s7f_frattini h36 h76 hP h77b h78 h710c h710d hE.choice hE.sylow hE.A_le n hn.2
  have hu' : h * u * h⁻¹ ∈ U := hHU h hh u hu
  have hEM : E ≤ MSub S B := fun x hx => (hE.sylow.1 hx).1
  have hu'M : h * u * h⁻¹ ∈ MSub S B := hEM (hUE hu')
  refine ⟨h * u * h⁻¹, hu', (h * u * h⁻¹)⁻¹ * o * (h * u * h⁻¹) * o⁻¹, ?_, by group⟩
  have h1 : (h * u * h⁻¹)⁻¹ * o * (h * u * h⁻¹) ∈ oddCoreIn (MSub S B) := by
    have h2 := conj_mem_oddCoreIn (Subgroup.le_normalizer ((MSub S B).inv_mem hu'M)) ho
    rwa [inv_inv] at h2
  exact (oddCoreIn (MSub S B)).mul_mem h1 ((oddCoreIn (MSub S B)).inv_mem ho)

theorem asc82Final7U_of_sec7 (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) : Asc82Final7U := by
  intro G _ _ t L S z g B E hE
  obtain ⟨φ, -, F⟩ := s7f_frame_of_sec7E h36 h76 hP h77b h78 h710c h710d hE
  obtain ⟨U, hUE, hBU, hcard, hsup, hinf, hHU⟩ := F.exists_compl
  exact ⟨U, hE, hUE, hBU, hcard, hsup, hinf,
    s7f_inv_of_normalized h36 h76 hP h77b h78 h710c h710d hE hUE hHU⟩

theorem asc82Final7E_of_sec7 (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) : Asc82Final7E :=
  asc82Final7E_of (asc82Final7U_of_sec7 h36 h76 hP h77b h78 h710c h710d) h36 h76 hP h77b h78
    h710c h710d

end CFSG.OddStandard.SmallF3.Omega
