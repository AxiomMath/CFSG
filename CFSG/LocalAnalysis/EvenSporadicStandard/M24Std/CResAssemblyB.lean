module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEData

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

variable {Y : Type} [Group Y] [Finite Y] {Cc : Type} [Group Cc]

theorem exists_mulEquiv_range (hFT : OddSolv) (hH1 : ElemAbH1) (hH2 : ElemAbH2)
    (hCc : Nat.card (MulAut Cc) ∣ gl12) (ρ : Y →* MulAut Cc) (U : Subgroup Y)
    (hU : commutator U = ⊤) {E : Type} [Group E] [Finite E] (q : U →* E)
    (hq : Function.Surjective q) (hqodd : Odd (Nat.card q.ker))
    (hker : ∀ u : U, ρ u = 1 → q u = 1) (hE : EData E) :
    ∃ e : (ρ.comp U.subtype).range ≃* E,
      ∀ u : U, e ((ρ.comp U.subtype).rangeRestrict u) = q u := by
  set ρU : U →* MulAut Cc := ρ.comp U.subtype with hρU
  set ρU' := ρU.rangeRestrict with hρU'
  have hsurj : Function.Surjective ρU' := MonoidHom.rangeRestrict_surjective ρU
  have hker' : ρU'.ker ≤ q.ker := by
    intro u hu
    have h1 : ρU' u = 1 := hu
    have h2 : ρU u = 1 := congrArg Subtype.val h1
    exact hker u h2
  let q' : ρU.range →* E :=
    ρU'.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨q, hker'⟩
  have hq'ρ : ∀ u, q' (ρU' u) = q u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply ρU' (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨q, hker'⟩ u
  have : Finite ρU.range := Finite.of_surjective ρU' hsurj
  have hq's : Function.Surjective q' := by
    intro x
    obtain ⟨u, hu⟩ := hq x
    exact ⟨ρU' u, by rw [hq'ρ, hu]⟩
  have hodd' : Odd (Nat.card q'.ker) := by
    let f : q.ker →* q'.ker := (ρU'.comp q.ker.subtype).codRestrict q'.ker fun u => by
      show q' (ρU' u) = 1
      rw [hq'ρ]
      exact u.2
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨u, hu⟩ := hsurj y
      have hqu : q u = 1 := by
        rw [← hq'ρ, hu]
        exact y.2
      exact ⟨⟨u, hqu⟩, Subtype.ext hu⟩
    exact Odd.of_dvd_nat hqodd (Subgroup.card_dvd_of_surjective hf)
  have hperf : Group.IsPerfect U := ⟨hU⟩
  have hUt : commutator ρU.range = ⊤ := (Group.IsPerfect.range ρU).commutator_eq_top
  have hN0 : Nat.card ρU.range ∣ gl12 :=
    (Subgroup.card_subgroup_dvd_card ρU.range).trans hCc
  have hker1 := card_ker_eq_one_of_chiefData hFT hH1 hH2 hUt q' hq's hodd' hN0 hE.chief hE.hopf
  have hinj : Function.Injective q' := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hker1
  exact ⟨MulEquiv.ofBijective q' ⟨hinj, hq's⟩, fun u => hq'ρ u⟩

end CFSG.EvenSporadicStandard.M24Std
