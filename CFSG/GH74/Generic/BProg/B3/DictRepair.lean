module

public import CFSG.GH74.Generic.BProg.AssemblyS3
public import CFSG.GH74.Generic.BProg.AssemblyS1
public import CFSG.GH74.Generic.BProg.NS.S1S45

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

@[expose] def NoJPrimeG (G : Type) [Group G] : Prop :=
  ∀ (x' : G) (M' : Subgroup G), IsJ2 x' M' → pRank 2 ↥(CxK x' M') ≤ 1

theorem isJ2Circ_of_noJPrimeG {G : Type} [Group G] {x : G} {M : Subgroup G} (hJ : NoJPrimeG G)
    (h : IsJ2 x M) : IsJ2Circ x M :=
  ⟨h, Or.inr hJ⟩

theorem noJPrimeG_of_liftJ2NS (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS) {G : Type} [Group G] [Finite G]
    (hyp : Hyp2 G) (hNo : NoAltJ2 G) : NoJPrimeG G := by
  intro x' M' hJ
  by_contra hgt
  have hP := hJ' G hyp hNo x' M' hJ (not_le.1 hgt)
  have h1 := (hL1 G hyp.simple hyp.nonab hyp.rank hyp.gen4 hyp.kgh hyp.sylow hyp.generic hyp.noThin x' M' hJ
    hNo hP).2
  omega

structure NbhdDataJ (G : Type) [Group G] (x c : G) (L : Subgroup G) : Prop where
  noAlt : NoAltJ2 G
  ex : ∃ (Iw A : Subgroup G) (y : G) (Lb : Subgroup (CentralizerBar x)),
    IsJ2 x Iw ∧ IsSource2 x Iw A ∧ IsAdmPair x Iw A y Lb ∧ c ∈ closure ({x, y} : Set G) ∧ c ≠ 1 ∧
      L ≤ centralizer ({c} : Set G) ∧
      L ≤ ⨆ g ∈ L, (liftAt x y Lb).map (MulAut.conj g).toMonoidHom

theorem NbhdDataJ.toNbhdData {G : Type} [Group G] {x c : G} {L : Subgroup G} (hJ : NoJPrimeG G)
    (h : NbhdDataJ G x c L) : NbhdData G x c L := by
  obtain ⟨Iw, A, y, Lb, hJ2, hsrc, hadm, hc, hc1, hLC, hgen⟩ := h.ex
  exact ⟨h.noAlt, Iw, A, y, Lb, isJ2Circ_of_noJPrimeG hJ hJ2, hsrc, hadm, hc, hc1, hLC, hgen⟩

theorem nbhdDataJ_of_parts {G : Type} [Group G] {x c y : G} {Iw A : Subgroup G}
    {Lb : Subgroup (CentralizerBar x)} {L B : Subgroup G} (hNo : NoAltJ2 G) (hJ2 : IsJ2 x Iw)
    (hsrc : IsSource2 x Iw A) (hadm : IsAdmPair x Iw A y Lb) (hc : c ∈ closure ({x, y} : Set G))
    (hc1 : c ≠ 1) (hLC : L ≤ centralizer ({c} : Set G)) (hBlift : B ≤ liftAt x y Lb)
    (hgen : L ≤ ⨆ g ∈ L, B.map (MulAut.conj g).toMonoidHom) : NbhdDataJ G x c L := by
  refine ⟨hNo, Iw, A, y, Lb, hJ2, hsrc, hadm, hc, hc1, hLC, hgen.trans (iSup₂_le fun g hg => ?_)⟩
  exact le_iSup₂_of_le g hg (Subgroup.map_mono hBlift)

@[expose] def DictS3J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3.S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S3.OnlyInvX x K →
      ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
        S3.NbrData G t p f x y Iw Iv → S3.imgBar x Iw = K →
          NoAltJ2 G ∧ IsJ2 x Iw ∧
            ∃ A : Subgroup G, IsSource2 x Iw A ∧ IsAdmPair x Iw A y (S3.imgBar x Iv)

theorem dictS3_of_parts (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS) (hD : DictS3J) : DictS3 := by
  intro G _ _ x K hset hmax hthin honly t p f y Iw Iv hnd himg
  have hHyp : Hyp2 G := ⟨hset.simple, hset.nonab, hset.rank, hset.gen4, hset.kgh, hset.sylow,
    ⟨x, hset.inv, K, hset.comp, hset.g2⟩, hthin⟩
  obtain ⟨hNo, hJ2, hA⟩ := hD G x K hset hmax hthin honly t p f y Iw Iv hnd himg
  exact ⟨hNo, isJ2Circ_of_noJPrimeG (noJPrimeG_of_liftJ2NS hL1 hJ' hHyp hNo) hJ2, hA⟩

@[expose] def DictS1HighJ : Prop :=
  S1.S1LiftExactProp →
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1.S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1.S1Front G x K → S1.S1LargeModel K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1.S1Frame x K u hu →
        S1.S1SymFrame x u → ∀ c ∈ S1.symJ (S1.symX x u) 3, orderOf c = 2 →
          (∀ a ∈ S1.symJ (S1.symX x u) 3, a * c = c * a) →
            NbhdDataJ G x c (S1.symJ (S1.symX x u) 0 ⊔ S1.symJ (S1.symX x u) 1)

@[expose] def DictS1ThreeJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1.S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1.S1Front G x K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1.S1Frame x K u hu →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 → S1.S1SymFrameLin x u F →
          S1.S1FrameOddFree x u → ∀ c ∈ S1.symJ3 (S1.symX x u) 3, orderOf c = 2 →
            (∀ a ∈ S1.symJ3 (S1.symX x u) 3, a * c = c * a) →
              NbhdDataJ G x c (S1.symJ3 (S1.symX x u) 0 ⊔ S1.symJ3 (S1.symX x u) 1)

@[expose] def DictS1Q3J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1.S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1.S1Front G x K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1.S1Frame x K u hu →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 → S1.S1SymFrameLin x u F →
          ∀ Fr : S1.Q3FrameB G F, Fr.X = S1.symX x u →
            NbhdDataJ G x (Fr.X 2 * Fr.X 3) Fr.Ablk

theorem dictS1High_of_parts (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hD : DictS1HighJ) :
    DictS1High := by
  intro G _ _ x K hset hmax hthin hfront hbig u hu hf hsym c hcJ hc2 hcc
  have hExact : S1.S1LiftExactProp :=
    S1.s1LiftExact_of_central_schur (s1LiftCentralProp_of_liftJ2NS hL1) (S1.s1SchurOdd_of_griess hGA)
  have h := hD hExact G x K hset hmax hthin hfront hbig u hu hf hsym c hcJ hc2 hcc
  exact h.toNbhdData (noJPrimeG_of_liftJ2NS hL1 hJ' (s1Setup_hyp2 hset hthin) h.noAlt)

theorem dictS1Three_of_parts (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS) (hD : DictS1ThreeJ) :
    DictS1Three := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
  have h := hD G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
  exact h.toNbhdData (noJPrimeG_of_liftJ2NS hL1 hJ' (s1Setup_hyp2 hset hthin) h.noAlt)

theorem dictS1Q3_of_parts (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS) (hD : DictS1Q3J) : DictS1Q3 := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin Fr hFr
  have h := hD G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin Fr hFr
  exact h.toNbhdData (noJPrimeG_of_liftJ2NS hL1 hJ' (s1Setup_hyp2 hset hthin) h.noAlt)

theorem nbrComp_of_programJ (hA : Stage2Allow) (hL1 : B_Gen4_liftJ2NS) (hJ' : JPrimeNS)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (h3 : DictS3J)
    (h1 : DictS1HighJ) (h13 : DictS1ThreeJ) (hq : DictS1Q3J) :
    S3.B_S3_nbrComp ∧ S1.B_S1_nbrComp :=
  ⟨b_S3_nbrComp_of_program hA (dictS3_of_parts hL1 hJ' h3),
    b_S1_nbrComp_of_program hA (dictS1High_of_parts hL1 hJ' hGA h1) (dictS1Three_of_parts hL1 hJ' h13)
      (dictS1Q3_of_parts hL1 hJ' hq)⟩

end CFSG.GH74.Generic.BProg.B3
