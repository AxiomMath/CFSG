module

public import CFSG.ClassicalInvolution.Q3.TL4SepAlpha
public import CFSG.ClassicalInvolution.Q3.TL4SepRestr
public import CFSG.ClassicalInvolution.Q3.TL4SepFamB
public import CFSG.ClassicalInvolution.Q3.TL4SepQuotB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_nbrGen {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K : Subgroup G}
    {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G)) :
    c ∈ Subgroup.normalizer ((nbrGen (nbrAdj Ω) K : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact conj_mem_nbrGen hΩ hc hx
  · have := conj_mem_nbrGen hΩ (Subgroup.inv_mem _ hc) hx
    simpa [mul_assoc] using this

theorem card_lt_of_le_centralizer (hZ : Subgroup.center G = ⊥) {H : Subgroup G} {z : G}
    (hz1 : z ≠ 1) (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) : Nat.card H < Nat.card G := by
  have hCz : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    have hmem : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun y => by
      have hy : y ∈ Subgroup.centralizer ({z} : Set G) := htop ▸ Subgroup.mem_top y
      exact Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  calc Nat.card H ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := Subgroup.card_le_of_le hHz
    _ < Nat.card G := lt_of_le_of_ne (Subgroup.card_le_card_group _)
        (fun h => hCz ((Subgroup.card_eq_iff_eq_top _).mp h))

variable {r : ℕ} {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem nbrGen_le_centralizer_of_alpha (hd : TightDatum R S t)
    (hF : TightFam r G (CoreAssembly.conjClass (tightCore R))) (hα : TightSepAlpha R t) (g : G) :
    nbrGen (nbrAdj (CoreAssembly.conjClass (tightCore R))) (conjSub g (tightCore R)) ≤
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  refine nbrGen_le fun J hJ => ?_
  obtain ⟨u, hu⟩ := hF.inv J hJ.2.1
  obtain ⟨-, -, P, hP, hPJ, hPN⟩ := hJ.2
  exact le_centralizer_of_alpha_sep (hd.isUniqueInvolution_core.conj g) hu (hF.twoGroup J hJ.2.1)
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hd.hypOmegaGen hJ.2.1 hP hPJ) hPN
    (hF.tight J hJ.2.1 u hu) (hα.at_conj hd g hJ.2 hu)

section Cit3


theorem sepHyp_of_thm4R_alpha {n : ℕ} (hL : TightLargeHypR r n G R S t)
    (hα : TightSepAlpha R t) (h4 : Thm4RBelow r n) :
    TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := by
  have hd := hL.datum
  have hF := TightFam.of_datum hd hL.cls.1
  intro K J J' hKJ hKJ' hnot
  obtain ⟨g, rfl⟩ := hKJ.1
  have hz := hd.isUniqueInvolution_core.conj g
  have hHz := nbrGen_le_centralizer_of_alpha hd hF hα g
  set H := nbrGen (nbrAdj (CoreAssembly.conjClass (tightCore R))) (conjSub g (tightCore R))
  have hOH : oddCoreImg H ≤ oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set G)) :=
    TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le H).trans hHz)
      (fun c hc _ ho => conj_mem_oddCoreImg
        (mem_normalizer_nbrGen hd.hypOmegaGen (hF.tight _ hKJ'.1 _ hz hc)) ho)
      (odd_natCard_oddCoreImg H)
  have hJH : J ≤ H := le_nbrGen hKJ
  have hJ'H : J' ≤ H := le_nbrGen hKJ'
  have hJm : J.subgroupOf H ∈ restrictFamily (CoreAssembly.conjClass (tightCore R)) H :=
    ⟨J, hKJ.2.1, hJH, rfl⟩
  have hJ'm : J'.subgroupOf H ∈ restrictFamily (CoreAssembly.conjClass (tightCore R)) H :=
    ⟨J', hKJ'.2.1, hJ'H, rfl⟩
  have hFH := hF.restrict H
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
  have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n := by
    rw [← hL.card]
    exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans_lt
      (card_lt_of_le_centralizer hL.center hz.ne_one hHz)
  have hc : Commutes ((J.subgroupOf H).map f) ((J'.subgroupOf H).map f) := by
    refine h4 _ hlt _ (hFH.t4Hyp_quot (three_le_of_quat hd hL.cls.1)) _ ⟨_, hJm, rfl⟩ _
      ⟨_, hJ'm, rfl⟩ ?_
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← AscQuot.map_conjSub] at hx
    obtain ⟨m, -, hm⟩ := hFH.exists_conj_of_map_eq
      (CFSG.ComponentClassification.OddCore.odd_card ↥H) (hFH.conjInvariant x _ hJm) hJ'm hx
    rw [← conjSub_mul] at hm
    obtain ⟨y, hyH, hy⟩ := exists_conjSub_of_restrict hJH hJ'H ⟨_, hm⟩
    exact hnot ⟨y, hyH, hy⟩
  obtain ⟨u, hu⟩ := hF.inv J hKJ.2.1
  have hON := oddCoreImg_le_normalizer_of_alpha hz.ne_one (hF.tight J hKJ.2.1 u hu)
    (hα.at_conj hd g hKJ.2 hu)
  have hJ'N : J' ≤ Subgroup.normalizer (J : Set G) := by
    intro s hs
    have h1 := hc _ ⟨⟨u, hJH hu.mem⟩, Subgroup.mem_subgroupOf.mpr hu.mem, rfl⟩ _
      ⟨⟨s, hJ'H hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have h2 : f ⟨u, hJH hu.mem⟩ = f (⟨s, hJ'H hs⟩ * ⟨u, hJH hu.mem⟩ * ⟨s, hJ'H hs⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have hn : u⁻¹ * (s * u * s⁻¹) ∈ oddCoreImg H := ⟨_, QuotientGroup.eq.mp h2, rfl⟩
    exact hF.mem_normalizer_of_conj_eq_mul hKJ.2.1 hu
      (mul_inv_cancel_left u (s * u * s⁻¹)).symm
      ((odd_natCard_oddCoreImg H).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hn)) (hON (hOH hn))
  obtain ⟨P, hP, hPJ', -⟩ := exists_mem_RSet_ge hKJ'.2.1 IsPGroup.of_bot bot_le
  exact ⟨hKJ.2.1, hKJ'.2.1, fun h => hnot (by rw [h]; exact mem_orbOf_self _ J), P, hP,
    hPJ'.1, hPJ'.1.trans hJ'N⟩

theorem tightSepLeafRα_of_thm4R {n : ℕ} (h4 : Thm4RBelow r n) : TightSepLeafRα r n :=
  fun _ _ _ _ _ _ hL hα => sepHyp_of_thm4R_alpha hL hα h4

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
