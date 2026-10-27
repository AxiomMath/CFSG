module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrCases
public import CFSG.ClassicalInvolution.Q3.TL4S289Z
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseSec
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open scoped commutatorElement Pointwise

section Defs

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def LinkWR (R : Subgroup Y) (t : Y) : Prop :=
  (∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
      ∃ P : Subgroup ↥(linkGrp R t), P.Normal ∧ IsPGroup 2 ↥P ∧ a ∈ P) ∧
    T3.DStarConnected (linkFam R t)

@[expose] def LinkSR (R : Subgroup Y) (t : Y) : Prop :=
  DEdgeless (linkFam R t) ∧ (∃ M ∈ linkFam R t, (omegaStarNbr (linkFam R t) M).Nonempty) ∧
    ∃ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 ↥R') (z' : ↥(linkGrp R t)),
      R' ∈ linkFam R t ∧ TightDatum R' S' z' ∧ ExitLU R' S' z' ∧
        CoreAssembly.conjClass (tightCore R') = linkFam R t

@[expose] def LinkZR (R : Subgroup Y) (t : Y) : Prop :=
  DEdgeless (linkFam R t) ∧ ExitL2Facts (linkFam R t)

end Defs


section NoCert

theorem exists_star_not_nbr_of_dstarConnected {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (hcon : T3.DStarConnected Φ) (hnc : ¬ DConnected Φ) :
    ∃ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  by_contra hno
  push Not at hno
  apply hnc
  intro K hK J hJ
  have h : Relation.ReflTransGen (dstarAdj Φ) K J := hcon K hK J hJ
  have key : ∀ P, Relation.ReflTransGen (dstarAdj Φ) K P → P ∈ Φ ∧
      Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) K P := by
    intro P hP
    induction hP with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hbΦ, hb⟩ := ih
      refine ⟨hstep.1, hb.tail ⟨hstep.1, ?_⟩⟩
      rcases hstep.2 with h1 | h1
      · exact Or.inl (hno b hbΦ c hstep.1 h1)
      · exact Or.inr (hno c hstep.1 b hbΦ h1)
  exact (key J h).2


end NoCert

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkTrans_of_not_dConnected (h4 : Thm4RBelow r n) (hL : TightLargeHypR r n Y R S t)
    (hnc : ¬ DConnected (linkFam R t)) : LinkTrans R t := by
  have hΦ : TypeRFam r (linkFam R t) := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hO := oddCore_linkGrp_eq_bot hL
  have hn := S289.natCard_linkGrp_lt hL
  intro L hL' L' hL''
  by_contra hno
  exact hnc (dConnected_of_not_conjR h4 hΦ hO hn hL' hL''
    fun ⟨g, _, hg⟩ => hno ⟨g, hg⟩)


end Cit3

section Cert



variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkShape_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (hG : GH74SectionalModels)
    (h6 : ∀ m, TightLargeEdgeSR r m) (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n)
    (hdisc : TightLinkDiscR r n) (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hbad : LinkAlphaBad R t) :
    ¬ DConnected (linkFam R t) ∧ LinkTrans R t ∧ (LinkWR R t ∨ LinkSR R t ∨ LinkZR R t) := by
  classical
  have hΦ : TypeRFam r (linkFam R t) := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hO := oddCore_linkGrp_eq_bot hL
  have hgen : omegaGen (linkFam R t) = ⊤ := omegaGen_linkRestrict
  have hn := S289.natCard_linkGrp_lt hL
  have h4' : Thm4RBelow r n := h4 hL.below hL.tbelow
  have hnc := hdisc Y R S t hL hc hA hbad
  have htr := linkTrans_of_not_dConnected h4' hL hnc
  refine ⟨hnc, htr, ?_⟩
  obtain ⟨J, hJ, -⟩ := hbad
  have hK := subgroupOf_mem_linkRestrict (t := t) hJ
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hK
  have htr' : ∀ L ∈ linkFam R t, ∃ g ∈ omegaGen (linkFam R t),
      conjSub g ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) = L :=
    fun L hL' => by
      obtain ⟨g, hg⟩ := htr _ hK L hL'
      exact ⟨g, by rw [hgen]; exact Subgroup.mem_top g, hg⟩
  obtain ⟨S', hd, hc', hfam⟩ := exists_datumR_of_omegaTransitive (by omega) hΦ hO hgen hK htr' hz'
  by_cases hO2 : TightInO2 z'
  ·
    obtain ⟨P, hPn, hP2, hzP⟩ := hO2
    have hin : ∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
        ∃ P : Subgroup ↥(linkGrp R t), P.Normal ∧ IsPGroup 2 ↥P ∧ a ∈ P := by
      intro M hM a ha
      obtain ⟨g, -, rfl⟩ := htr' M hM
      refine ⟨P, hPn, hP2, ?_⟩
      rw [← (hz'.conj g).eq ha]
      exact hPn.conj_mem z' hzP g
    have hAE : ∀ L ∈ linkFam R t, AEmpty (linkFam R t) L := fun L hL' =>
      aEmpty_of_noTwins hΦ.hyp hL' (hΦ.noTwins L hL')
    exact Or.inl ⟨hin, dstarConnected_of_inO2_four_le hr hΦ hO hAE
      fun L hL' u hu => hin L hL' u hu⟩
  ·
    have hE : TightEdgeless
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) := by
      by_contra hne
      exact hO2 (inO2_of_edge_four_le hr hL.tbelow hNo hn hd hc' hne)
    have hDE : DEdgeless (linkFam R t) := by
      have h := hE
      unfold TightEdgeless at h
      rwa [hfam] at h
    rcases exit_cases hr hL.below hL.tbelow hG h6 hn hΦ hO hK hd hz' hc' hfam hO2 hE with
      ⟨hst, hLU⟩ | hZ2
    · exact Or.inr (Or.inl ⟨hDE, hst, _, S', z', hK, hd, hLU, hfam⟩)
    · exact Or.inr (Or.inr ⟨hDE, hZ2⟩)

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
