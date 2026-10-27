module

public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbitC
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.Blueprint

section Sec

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {u : Y}

theorem E3.secMovedOddFree_of_exLie (hO : classicalInvolutionOddCore (SecQ R u) = ⊥)
    (h : PhilipHall.QuaternionBridge.ExLie (SecQ R u ⧸ Subgroup.center (SecQ R u)))
    (x : SecQ R u) : SecMovedOddFree R u x := by
  have : IsSimpleGroup (SecQ R u ⧸ Subgroup.center (SecQ R u)) := Vtx.isSimpleGroup_of_exLie h
  have hk : IsPGroup 2 ↥(QuotientGroup.mk' (Subgroup.center (SecQ R u))).ker := by
    rw [QuotientGroup.ker_mk']
    exact Vtx.isPGroup_center_of_oddFree hO
  intro L hL hN hmv
  exact (PhilipHall.Frame.TwinCentRes.atMostOne_oddFree_of_surj_simple
    (QuotientGroup.mk' (Subgroup.center (SecQ R u))) (QuotientGroup.mk'_surjective _) hk
    (fun _ => Vtx.autOddFree_of_exLie h) x).2 L hL hN hmv

theorem E3.mem_normalizer_oddCent {a c : Y} (hc : c ∈ Subgroup.centralizer ({a} : Set Y)) :
    c ∈ Subgroup.normalizer (oddCoreImg (Subgroup.centralizer ({a} : Set Y)) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_oddCoreImg (Subgroup.le_normalizer hc) hx, fun hx => ?_⟩
  have h1 := conj_mem_oddCoreImg (Subgroup.le_normalizer (Subgroup.inv_mem _ hc)) hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h1

end Sec

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.eq_top_of_orbGen_le (hF : E3Frame n R S t J u) {H : Subgroup Y}
    (h1 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J ≤ H)
    (h2 : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤ H) : H = ⊤ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hFam := hF.graphFam
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hF.large.cls.2.1
  have hY := hF.lemma1710.generate hgen g (by rw [hgJ]; exact mem_orbOf_self _ _)
  have hπ : conjSub g '' orbOf (TC.nbrAdj Ω) (tightCore R) J =
      orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    have h3 := isMaxOrb_conj hFam hF.maxAdj.2 g
    rw [hgJ] at h3
    exact maxOrb_unique hFam hJn.1 h3 (orbOf_mem_maxOrbs hFam hF.maxAdj.1 hF.maxAdj.2)
  rw [eq_top_iff, ← hY]
  refine iSup₂_le fun M hM => ?_
  rcases hM with hM | hM
  · exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) (tightCore R) J) => N)
      M hM).trans h1
  · rw [hπ] at hM
    exact (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N)
      M hM).trans h2

theorem E3Frame.tightOddCent_of_le (hF : E3Frame n R S t J u)
    (hle : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreImg (Subgroup.centralizer ({u} : Set Y))) : TightOddCent t := by
  obtain ⟨g, -, -, hgt, hgu⟩ := hF.exists_swap'
  have hge : oddCoreImg (Subgroup.centralizer ({u} : Set Y)) ≤
      oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := by
    intro x hx
    have h1 := conj_mem_oddCent g⁻¹ hx
    rw [show g⁻¹ * u * g⁻¹⁻¹ = t by rw [← hgt]; group] at h1
    have h2 := conj_mem_oddCent g (hle h1)
    rwa [hgu, show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at h2
  have heq := le_antisymm hge hle
  have htop : Subgroup.normalizer
      (oddCoreImg (Subgroup.centralizer ({t} : Set Y)) : Set Y) = ⊤ := by
    refine hF.eq_top_of_orbGen_le (fun x hx => ?_) (fun x hx => ?_)
    · exact E3.mem_normalizer_oddCent (hF.orbGen_core_le_centralizer hx)
    · rw [← heq]
      exact E3.mem_normalizer_oddCent (hF.orbGen_J_le_centralizer hx)
  have hO : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨Subgroup.normalizer_eq_top_iff.mp htop, odd_natCard_oddCoreImg _⟩
  rw [hF.large.cls.2.2] at hO
  exact le_bot_iff.mp hO

theorem E3Frame.tightOddCent_of_secMovedOddFree (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hsec : SecMovedOddFree R u (E3.secT htu ht)) : TightOddCent t := by
  have hd := hF.large.datum
  exact hF.tightOddCent_of_le (oddCent_le_oddCent_of_sec htu hd.isUniqueInvolution_core.sq
    (ne_one_of_datum hd) (oddCent_le_centralizer_of_alpha hd (hF.alpha J hF.maxAdj.1.2 u hF.inv))
    ht hsec)

theorem tightE3E4OddCent_proved (n : ℕ) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
      (u : Y), E3Frame n R S t J u →
        (LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .PSp 3 2 1 ∨
          LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .POmegaPlus 4 2 1) →
          TightOddCent t := by
  intro Y _ _ R S t J u hF hM
  obtain ⟨-, -, -, htu, -⟩ := hF.large.datum.edge_involution hF.maxAdj.1.2 hF.inv
  have ht := mem_secH hF.large.datum htu
  obtain ⟨Sq, -, hc⟩ := hF.exists_secCls htu ht
  exact hF.tightOddCent_of_secMovedOddFree htu ht (E3.secMovedOddFree_of_exLie hc.2.2 hM _)

theorem E3Frame.tightE4_secQ (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hZ : Subgroup.center (SecQ R u) ≠ ⊥)
    (hM : PhilipHall.QuaternionBridge.ExLie (SecQ R u ⧸ Subgroup.center (SecQ R u))) :
    TightE4 (SecQ R u) := by
  obtain ⟨Sq, -, hc⟩ := hF.exists_secCls htu ht
  exact PhilipHall.QuaternionBridge.tightE4_of_exLie_quotient
    (Vtx.isPGroup_center_of_oddFree hc.2.2) hZ hM

theorem tightC17_11R_of (hE4O : TightE3E4O n) : TightC17_11R n := by
  have hOC := tightE3E4OddCent_proved (n := n)
  intro Y _ _ R S t J u hF htu ht _ hZ hM
  exact hE4O Y R S t hF.large (hOC Y R S t J u hF (Or.inl hM)) hF.conn hF.sep J
    hF.maxAdj u hF.inv htu ht (hF.tightE4_secQ htu ht hZ (Or.inl hM))

theorem tightC17_11'R_of (hE4O : TightE3E4O n) :
    TightC17_11'R n := by
  have hOC := tightE3E4OddCent_proved (n := n)
  intro Y _ _ R S t J u hF htu ht _ hZ hM
  exact hE4O Y R S t hF.large (hOC Y R S t J u hF (Or.inr hM)) hF.conn hF.sep J
    hF.maxAdj u hF.inv htu ht (hF.tightE4_secQ htu ht hZ (Or.inr hM))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
