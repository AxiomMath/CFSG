module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.LemmaC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.ModelCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Model
public import Certificates.Certificate450070
public import Certificates.Certificate450071
public import Certificates.Certificate450072

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M12Std.PropA

theorem rbcModel_of_certificate
    (b : Bool) : RbcModel (K28 b) D28 pT x28 := by
  obtain ⟨hcomm, hexp, hYD, hnorm, h2⟩ := Certificates.certificate450070 b
  exact ⟨hcomm, hexp, hYD, hnorm, h2, Certificates.certificate450071 b,
    Certificates.certificate450072 b⟩

section Certified


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem rbcFacts_of_outer (h : StdHyp G L) (hL : IsSporadic L .M12) {t x : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hout : ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G))
    (hxL : x ∈ L) (hx2 : orderOf x = 2) (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240) :
    PropA.Facts L t x ∧ RbcFacts L t x := by
  obtain ⟨b, ι, hE⟩ := exists_isEmb h hL ht ht2 hout hxL hx2 hx
    (fun b => (model_of_certificate b).2.1) (model_of_certificate false).2.2
  exact ⟨hE.facts (model_of_certificate b).1, IsEmb.rbcFacts hE (rbcModel_of_certificate b)⟩

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
