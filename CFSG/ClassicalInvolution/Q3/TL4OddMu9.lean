module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP
public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu
public import CFSG.ClassicalInvolution.Q3.TL4OddFrNon

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Orbits

variable {G : Type} [Group G]

theorem hyp51_of_three_vertices {t u w : G} (ht : t * t = 1) (hu : u * u = 1)
    (htu : t * u = u * t) (htw : t * w = w * t)
    (hE : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set G)))
    (h8 : Nat.card ↥(Subgroup.closure ({t, u, w} : Set G)) = 8) {g : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.closure ({t, u, w} : Set G) : Subgroup G) : Set G))
    (hgt : g * t * g⁻¹ = t) (hgu : g * u * g⁻¹ = w) (hgw : g * w * g⁻¹ = u * w)
    (vt : Hyp51At (Subgroup.closure ({t, u, w} : Set G)) t)
    (vu : Hyp51At (Subgroup.closure ({t, u, w} : Set G)) u)
    (vtu : Hyp51At (Subgroup.closure ({t, u, w} : Set G)) (t * u)) :
    Hyp51 (Subgroup.closure ({t, u, w} : Set G)) := by
  set B := Subgroup.closure ({t, u, w} : Set G) with hBdef
  have hw2 : w * w = 1 := by
    rw [← hgu]
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hmv : ∀ {c c' : G}, Hyp51At B c → g * c * g⁻¹ = c' → Hyp51At B c' := by
    intro c c' h e
    have h1 := ExactLayer.hyp51At_of_normalizes hg h
    rwa [e] at h1
  have vw : Hyp51At B w := hmv vu hgu
  have vuw : Hyp51At B (u * w) := hmv vw hgw
  have vtw : Hyp51At B (t * w) := hmv vtu (by
    calc g * (t * u) * g⁻¹ = (g * t * g⁻¹) * (g * u * g⁻¹) := by group
      _ = t * w := by rw [hgt, hgu])
  have vtuw : Hyp51At B (t * u * w) := hmv vtw (by
    calc g * (t * w) * g⁻¹ = (g * t * g⁻¹) * (g * w * g⁻¹) := by group
      _ = t * u * w := by rw [hgt, hgw, mul_assoc])
  refine ⟨hE, h8, fun c hc hc1 => ?_⟩
  have huw : u * w = w * u := DeltaClosure.comm_of_mem_elemAbelian hE
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  rcases mem_closure_three_cases hw2 htw huw hc with h | ⟨e, he, rfl⟩
  · rcases T3CII.closure_pair_cases ht hu htu h with rfl | rfl | rfl | rfl
    · exact absurd rfl hc1
    · exact vt
    · exact vu
    · exact vtu
  · rcases T3CII.closure_pair_cases ht hu htu he with rfl | rfl | rfl | rfl
    · rwa [one_mul]
    · exact vtw
    · exact vuw
    · exact vtuw

end Orbits

section Frames

variable {Y : Type} [Group Y]

structure StarFrameAt (R : Subgroup Y) (t : Y) (J K'' : Subgroup Y) (u w : Y) : Prop where
  memJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  memK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  star : K'' ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) J
  notNbr : K'' ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) J
  invJ : IsUniqueInvolution J u
  invK : IsUniqueInvolution K'' w
  secStar : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∈
    omegaStarNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J)
  secNotNbr : secImg (CoreAssembly.conjClass (tightCore R)) t K'' ∉
    omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J)

end Frames

section Case


variable {Y : Type} [Group Y]

@[expose] def LinkS3S4 (R : Subgroup Y) (t : Y) : Prop :=
  (∀ L ∈ restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)),
    ∀ L' ∈ restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)),
      ∃ g : ↥(omegaGen (coreLinkFam R t)), conjSub g L = L') ∧
    SecIdMuS3S4Id (restrictFamily (coreLinkFam R t) (omegaGen (coreLinkFam R t)))

end Case

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K'' : Subgroup Y} {u w : Y}

theorem StarFrameAt.comm_tu (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen hL.datum.isUniqueInvolution_core hF.memJ
    hF.invJ

theorem StarFrameAt.comm_tw (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    t * w = w * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen hL.datum.isUniqueInvolution_core hF.memK
    hF.invK

theorem StarFrameAt.comm_uw (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    u * w = w * u := by
  have hΩ := hL.datum.hypOmegaGen
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := hF.star
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hwN : w ∈ Subgroup.normalizer (J : Set Y) :=
    hUN (T3.mem_of_isPGroup hF.invK hUK (Sec6Gen.isPGroup_of_mem_USet hΩ hU) (by omega))
  have h1 := hF.invJ.conj_eq (mem_normalizer_iff_conjSub_eq.mp hwN)
  calc u * w = (w * u * w⁻¹) * w := by rw [h1]
    _ = w * u := by group

theorem StarFrameAt.ne_mul (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    w ≠ t * u := by
  intro e
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  obtain ⟨P, hP, hPt⟩ := XMem.exists_sylow (xMem_of_mem_omegaNbr_core hL hF.memK)
  have hu : u = t * w := by
    rw [e, ← mul_assoc, ht.sq, one_mul]
  have hPu : P ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro p hp
    have h1 : p * t = t * p := Subgroup.mem_centralizer_singleton_iff.mp (hPt hp)
    have h2 : p * w * p⁻¹ = w := hF.invK.conj_eq (conjSub_eq_self_of_mem (hP.1 hp))
    have h3 : p * w = w * p := by
      calc p * w = (p * w * p⁻¹) * p := by group
        _ = w * p := by rw [h2]
    rw [Subgroup.mem_centralizer_singleton_iff, hu]
    calc p * (t * w) = (p * t) * w := by group
      _ = (t * p) * w := by rw [h1]
      _ = t * (p * w) := by group
      _ = t * (w * p) := by rw [h3]
      _ = t * w * p := by group
  exact hF.notNbr ⟨hF.memK.1, hF.star.2.1, P, mem_RSet_of_isSylow2In hF.memK.1 hP, hP.1,
    hPu.trans (h.tight J hF.memJ.1 u hF.invJ)⟩

theorem StarFrameAt.not_mem_closure (hL : TightLargeHypR r n Y R S t)
    (hF : StarFrameAt R t J K'' u w) : w ∉ Subgroup.closure ({t, u} : Set Y) := by
  have ht := hL.datum.isUniqueInvolution_core
  intro hmem
  rcases T3CII.closure_pair_cases ht.sq hF.invJ.sq (hF.comm_tu hL) hmem with h | h | h | h
  · exact hF.invK.ne_one h
  · exact hF.memK.2.1 (eq_core_of_isUniqueInvolution hL hF.memK.1 (h ▸ hF.invK))
  · exact hF.star.2.1 (noTwins_of_large hL J hF.memJ.1 K'' ⟨hF.memK.1, u, hF.invJ, h ▸ hF.invK⟩)
  · exact hF.ne_mul hL h

theorem StarFrameAt.isElemAbelian (hL : TightLargeHypR r n Y R S t)
    (hF : StarFrameAt R t J K'' u w) : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set Y)) :=
  T8T.isElemAbelian_closure_three hL.datum.isUniqueInvolution_core.sq hF.invJ.sq hF.invK.sq
    (hF.comm_tu hL) (hF.comm_tw hL) (hF.comm_uw hL)

theorem StarFrameAt.natCard (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    Nat.card ↥(Subgroup.closure ({t, u, w} : Set Y)) = 8 := by
  have ht := hL.datum.isUniqueInvolution_core
  have htu : t ≠ u := fun h =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (h ▸ hF.invJ))
  exact T8T.natCard_closure_three ht.sq hF.invJ.sq hF.invK.sq (hF.comm_tu hL) (hF.comm_tw hL)
    (hF.comm_uw hL) ht.ne_one hF.invJ.ne_one htu hF.invK.ne_one (hF.not_mem_closure hL)

@[expose] def TightStar289ZR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) t

@[expose] def TightStar289TR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) u

@[expose] def TightStar289ZTR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) (t * u)

@[expose] def TightStar289OrbR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        ∃ g ∈ Subgroup.normalizer
            ((Subgroup.closure ({t, u, w} : Set Y) : Subgroup Y) : Set Y),
          g * t * g⁻¹ = t ∧ g * u * g⁻¹ = w ∧ g * w * g⁻¹ = u * w

theorem hyp51_starFrame_of_residuals (hz : TightStar289ZR r n) (ht : TightStar289TR r n)
    (hzt : TightStar289ZTR r n) (ho : TightStar289OrbR r n) (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hcase : LinkS3S4 R t) (hF : StarFrameAt R t J K'' u w) :
    Hyp51 (Subgroup.closure ({t, u, w} : Set Y)) := by
  obtain ⟨g, hg, hgt, hgu, hgw⟩ := ho Y R S t hL hc hA hcase J K'' u w hF
  exact hyp51_of_three_vertices hL.datum.isUniqueInvolution_core.sq hF.invJ.sq (hF.comm_tu hL)
    (hF.comm_tw hL) (hF.isElemAbelian hL) (hF.natCard hL) hg hgt hgu hgw
    (hz Y R S t hL hc hA hcase J K'' u w hF) (ht Y R S t hL hc hA hcase J K'' u w hF)
    (hzt Y R S t hL hc hA hcase J K'' u w hF)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
