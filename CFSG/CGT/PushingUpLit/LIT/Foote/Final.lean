module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Statements

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement)
open CFSG.ComponentClassification.Asc76 (Asc76Theorem1)

theorem footeNonsolvableSimple_of_inputs (h3 : Theorem3Statement) (h1 : Asc76Theorem1)
    (h54 : Lemma54) (h55 : Lemma55) (h56 : Lemma56) : FooteNonsolvableSimple := by
  intro G _ _ hsimple _ hchar M X hM hXM hsub hXs hXq huniq
  by_contra hnorm
  have c : CE G M X :=
    { simple := hsimple
      charTwo := hchar
      maxLocal := hM
      le := hXM
      subnormal := hsub
      block := ⟨hXs, hXq⟩
      unique := huniq
      notNormal := hnorm }
  obtain ⟨z₀, hz₀J, hz₀o, hz₀c⟩ := c.exists_involution_center h3 h1
  have hz₀ : ZData X z₀ :=
    { mem := hz₀J
      central := hz₀c
      sq := by
        have : z₀ ^ 2 = 1 := by rw [← hz₀o]; exact pow_orderOf_eq_one z₀
        rwa [pow_two] at this
      ne_one := fun h => by
        rw [h, orderOf_one] at hz₀o
        omega }
  have h2 := h54 G M X z₀ c hz₀
  exact h56 G M X z₀ c hz₀ h2 (h55 G M X z₀ c hz₀ h2)

end CFSG.CGT.PushingUpLit.LIT.Foote
