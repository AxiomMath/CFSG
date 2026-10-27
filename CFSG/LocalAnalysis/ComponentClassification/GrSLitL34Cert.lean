module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate2021

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem twoCentralOK_eq_true :
    twoCentralOK (enumBFS 42 gTabs 241920).tabs
      (centTabs 42 (enumBFS 42 gensS 20160).tabs r₁T) = true :=
  Certificates.certificate2021

theorem tabRep_powTwoTab {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) (k : ℕ) :
    TabRep (powTwoTab t k) (g ^ 2 ^ k) := by
  induction k with
  | zero => simpa [powTwoTab] using ht
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_two]
    exact ih.comp ih

theorem pow_eq_one_of_commute_C₁ {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (hc : ∀ c ∈ C₁, g * c = c * g) : g ^ 2 ^ 8 = 1 := by
  obtain ⟨k, hk, hrep⟩ := enumerates_R.exists_pos hg
  have h := twoCentralOK_eq_true
  simp only [twoCentralOK, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with hk' | hk'
  · have hall : allBelow (centS r₁T).size
        (fun i => comp 42 enumR.tabs[k]! (centS r₁T)[i]! ==
          comp 42 (centS r₁T)[i]! enumR.tabs[k]!) = true := by
      rw [allBelow_eq_true]
      intro i hi
      obtain ⟨a, ha, hrepa⟩ := enumerates_C₁.exists_elt hi
      exact ((hrep.comp hrepa).beq_iff (hrepa.comp hrep)).2 (hc a ha)
    rw [hall] at hk'
    exact Bool.noConfusion hk'
  · exact ((tabRep_powTwoTab hrep 8).beq_iff TabRep.idTab).1 hk'

end CFSG.ComponentClassification.GrSLit
