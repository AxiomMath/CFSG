module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (SporL3Down IsL3Kind)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (PQ I1419UpSporFact I1419SporIndex)

@[expose] def I1419CoverL3U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → GLAPPrimeCore 3 X = ⊥ →
    catalogIs (X ⧸ Subgroup.center X) l3u3Index → IsL3Kind 2 X

theorem catalogIs_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs X Q) : catalogIs Y Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem glaPPrimeCore_barOf_eq_bot {G : Type} [Group G] [Finite G] (J : Subgroup G) :
    GLAPPrimeCore 3 (barOf 3 J) = ⊥ :=
  CFSG.pPrimeCore_quotient_eq_bot (G := ↥J) Nat.prime_three

theorem spor_of_facts (hSpor : ∀ s : TauCeti.SporadicName, SporL3Down s) (hCover : I1419CoverL3U3) :
    I1419UpSporFact := by
  intro Q _ _ β J hQ hCat _ hβ3 _ hJ hcat
  obtain ⟨β', J', hβ'3, hJ', ⟨eJ⟩⟩ := transfer_pSimple β hβ3 hJ
  obtain ⟨i, hi, ⟨eS⟩⟩ := hCat
  cases i with
  | cyclic _ _ => simp [I1419SporIndex] at hi
  | alternating _ _ => simp [I1419SporIndex] at hi
  | lie _ => simp [I1419SporIndex] at hi
  | sporadic s =>
    have hS : IsSimpleGroup (PQ Q ⧸ Subgroup.center (PQ Q)) := hQ.2
    have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQ Q) hQ
    have hnot := hSpor s (PQ Q ⧸ Subgroup.center (PQ Q)) hS hna ⟨eS⟩ β' hβ'3 J' hJ' 2
    apply hnot
    have hq : CFSG.Open.IsQuasisimple (barOf 3 J') := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ'
    have hcat' : catalogIs (barOf 3 J' ⧸ Subgroup.center (barOf 3 J')) l3u3Index :=
      catalogIs_of_mulEquiv' eJ hcat
    exact hCover (barOf 3 J') hq (glaPPrimeCore_barOf_eq_bot J') hcat'

end CFSG.LocalAnalysis.GLTheoremA.H1419

section SporBM


namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (SporL3Down)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (I1419UpSporFact)

theorem spor_of_BM (hB : SporL3Down TauCeti.SporadicName.B) (hM : SporL3Down TauCeti.SporadicName.M)
    (hCover : I1419CoverL3U3) : I1419UpSporFact :=
  spor_of_facts (CFSG.LocalAnalysis.GLTheoremA.I2018.sporL3Down_all_of_BM hB hM) hCover

end CFSG.LocalAnalysis.GLTheoremA.H1419

end SporBM
end
