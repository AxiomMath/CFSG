module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269GA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3Pick
public import CFSG.ClassicalInvolution.Q3.TL4E3C269BDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.secH_equiv (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ e : ↥(secH R u) ≃* ↥(nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J),
      ∀ h, ((e h : ↥(nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)) : Y) =
        ((h : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) :=
  ⟨(MulEquiv.subgroupCongr (le_antisymm hF.secH_le_nbrGen (hF.nbrGen_le_secH hO))).trans
    (Subgroup.subgroupOfEquivOfLe hF.nbrGen_le_centralizer), fun _ => rfl⟩

theorem E3Frame.le_sup_of_secGen (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hgen : ∀ s : SecQ R u, E3.secT htu ht * s = s * E3.secT htu ht → s ≠ E3.secT htu ht →
      (∃ g : SecQ R u, s = g * E3.secT htu ht * g⁻¹) →
        Subgroup.centralizer ({E3.secT htu ht} : Set (SecQ R u)) ⊔
          Subgroup.centralizer ({s} : Set (SecQ R u)) = ⊤)
    {x : Y} (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)
    (hxt : x * t * x⁻¹ ≠ t) (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
      nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ⊓
          Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.zpowers x ⊔
        oddCoreOf (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J) := by
  obtain ⟨e, he⟩ := hF.secH_equiv hO
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hx
  have hxH : (⟨x, hxC⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u :=
    hF.nbrGen_le_secH hO (Subgroup.mem_subgroupOf.mpr hx)
  have hinj : Function.Injective fun w : ↥(secH R u) =>
      ((w : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) :=
    Subtype.val_injective.comp Subtype.val_injective
  have htt : t * t = 1 := by rw [← pow_two, ← hF.large.datum.order, pow_orderOf_eq_one]
  have key := E3C269G.le_sup_oddCoreOf_of_gen e (t := ⟨⟨t, htu⟩, ht⟩) (x := ⟨⟨x, hxC⟩, hxH⟩)
    (hinj htt) (hinj hcomm) (fun h => hxt (congrArg (fun w : ↥(secH R u) =>
      ((w : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)) h)) hgen
  rwa [he, he] at key

end Cit3


theorem E3Frame.secGen {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {J : Subgroup Y} {u : Y} (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hE4 : SecIdE4Edge)
    (hL2 : E3C269L2) (hF : E3Frame n R S t J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) {Sb : Sylow 2 ↥(secR R u)}
    (hex : TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht))
    (hedge : TightEdgeless (secR R u)) (hμ : ∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W)
    (hnE2 : ¬ TightInO2 (E3.secT htu ht)) (s : SecQ R u)
    (hts : E3.secT htu ht * s = s * E3.secT htu ht) (hne : s ≠ E3.secT htu ht)
    (hconj : ∃ g : SecQ R u, s = g * E3.secT htu ht * g⁻¹) :
    Subgroup.centralizer ({E3.secT htu ht} : Set (SecQ R u)) ⊔
      Subgroup.centralizer ({s} : Set (SecQ R u)) = ⊤ := by
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  have hcR : TightClsR 3 (SecQ R u) (secR R u) Sq (E3.secT htu ht) := tightClsR_three_iff.mpr hc
  have hm : EdgelessMember3 (secR R u) Sq (E3.secT htu ht) := ⟨hd, hcR, hedge⟩
  have key := fun hx => E3C269G.sup_centralizer_of_e3Z2 hT hE3 hL2 hm hμ hnE2 hx hts hne hconj
  rcases TightEx.reduce hd hc hex hnE2 with ⟨-, h3⟩ | ⟨-, hM⟩ | ⟨hZ, h4⟩
  · rcases (tightDichotomy_of hd hc).resolve_left hnE2 with hq | htw
    · rcases hF.plus.thm6 (SecQ R u) hF.card_secQ_lt (secR R u) Sq (E3.secT htu ht) hd hcR
          hnE2 hq hedge with hg | hx
      · exact absurd (acts3_of_good hg) h3
      · exact key (Or.inl ⟨h3, Or.inl hx⟩)
    · exact key (Or.inl ⟨h3, Or.inr htw⟩)
  · exact key (Or.inr hM)
  · exact absurd hedge (hE4 _ _ _ _ hd hc hnE2 hZ h4)

theorem tightE3C269Gen_of {n : ℕ} (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hE4 : SecIdE4Edge)
    (hL2 : E3C269L2) : TightE3C269Gen n :=
  fun _ _ _ _ _ _ _ _ hF htu ht _ hex hedge hμ hnE2 hO _ _ _ _ _ _ _ _ _ _ hx hxt hcomm =>
    hF.le_sup_of_secGen hO htu ht (hF.secGen hT hE3 hE4 hL2 htu ht hex hedge hμ hnE2) hx hxt
      hcomm

end CFSG.ClassicalInvolution.Q3.TL4
