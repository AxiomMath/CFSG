module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTLemma
public import Certificates.Certificate442264
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LModel
public import Certificates.Certificate22242

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem asc82FactOm6PA6Bar_of_certs :
    Asc82FactOm6PA6Bar := by
  have : Finite (projectiveSL 4 (ZMod 3)) :=
    Nat.finite_of_card_ne_zero (by rw [card_P]; norm_num)
  intro α _ hα
  exact fbar_of_facts l43Model l43_groupData rfl (extra := [])
    (fun _ hu => absurd hu List.not_mem_nil) (by simp [l43Runs]) l43_cos
    Certificates.certificate22242.2.1 Certificates.certificate22242.2.2
    Certificates.certificate442264 α hα

theorem asc82Lemma63_of_certs
    (h33 : Asc82Lemma33) (h35 : Asc82Lemma35)
    (h36 : Asc82Lemma36) (hsh : Asc82Shapes) (hP : Asc82Tab6P) (hM : Asc82Tab6M)
    (hF : Asc82AutFacts) : Asc82Lemma63 :=
  asc82Lemma63_of_fbar h33 h35 h36 hsh hP hM hF asc82FactOm6PA6Bar_of_certs

end CFSG.OddStandard.SmallF3.Omega
