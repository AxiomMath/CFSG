module

public import CFSG.ClassicalInvolution.SmallCases.G2SGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_oddCore_of_sq {Y : Type} [Group Y] [Finite Y] {c : Y}
    (hc : c ∈ classicalInvolutionOddCore Y) (h : c * c = 1) : c = 1 := by
  have h2 : orderOf (⟨c, hc⟩ : classicalInvolutionOddCore Y) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h))
  have h3 := orderOf_dvd_natCard (⟨c, hc⟩ : classicalInvolutionOddCore Y)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h4)
  · rw [h4] at h3
    exact absurd (even_iff_two_dvd.mpr h3)
      (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))

theorem commute_of_mk_commute {Ω : Set (Subgroup G)} {x : G} (hP1 : LocalOddCentral Ω {x})
    {u v : G} (hu : u ∈ locLayer Ω x) (hv : v ∈ locLayer Ω x) (hu2 : u * u = 1)
    (hv2 : v * v = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩) :
    u * v = v * u := by
  set a : ↥(locLayer Ω x) := ⟨u, hu⟩ with ha
  set b : ↥(locLayer Ω x) := ⟨v, hv⟩ with hb
  have haa : a * a = 1 := Subtype.ext hu2
  have hbb : b * b = 1 := Subtype.ext hv2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) (a * b) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) (b * a) := by
    rw [map_mul, map_mul]
    exact h
  have hcO : (b * a)⁻¹ * (a * b) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    QuotientGroup.eq.mp hmk.symm
  set c := (b * a)⁻¹ * (a * b) with hc
  have hcc : c = a * b * a * b := by
    rw [hc, mul_inv_rev, hai, hbi]
    group
  have hcent : a * c = c * a := Subgroup.mem_center_iff.mp (hP1 hcO) a
  have hcc1 : c * c = 1 := by
    have h1 : a * c * a⁻¹ = c⁻¹ := by
      rw [hcc, hai]
      calc a * (a * b * a * b) * a = (a * a) * b * a * b * a := by group
        _ = b * a * b * a := by rw [haa, one_mul]
        _ = (a * b * a * b)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hai, hbi]
          group
    rw [hcent, mul_inv_cancel_right] at h1
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel c
  have h1 : c = 1 := eq_one_of_mem_oddCore_of_sq hcO hcc1
  have h2 : (b * a)⁻¹ * (a * b) = 1 := h1
  exact congrArg Subtype.val (inv_mul_eq_one.mp h2).symm

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem layer_le_normalizer (C : Ctx p f Ω L w) :
    centralizingLayer Ω {w} ≤ Subgroup.normalizer (L : Set G) := by
  rw [C.layer_eq]
  refine sup_le Subgroup.le_normalizer (iSup₂_le fun N hN n hn => ?_)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_eq_of_mem_of_commutes hn hN.2.2.symm)

theorem conjSub_eq_of_mem_layer (C : Ctx p f Ω L w) {y : G} (hy : y ∈ centralizingLayer Ω {w}) :
    conjSub y L = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (C.layer_le_normalizer hy)

theorem conj_mem_nbhd (C : Ctx p f Ω L w) {y : G} (hy : y ∈ centralizingLayer Ω {w})
    {N : Subgroup G} (hN : N ∈ nbhd Ω L) : conjSub y N ∈ nbhd Ω L := by
  refine ⟨C.inClass.conjInvariant y N hN.1, fun e => hN.2.1 ?_, ?_⟩
  · have h := congrArg (conjSub y⁻¹) e
    rwa [conjSub_inv_conjSub, C.conjSub_eq_of_mem_layer (Subgroup.inv_mem _ hy)] at h
  · have := hN.2.2.conjSub y
    rwa [C.conjSub_eq_of_mem_layer hy] at this

theorem nbhd_nonempty (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4) : (nbhd Ω L).Nonempty := by
  obtain ⟨R₀, hR₀, hmem⟩ := D.meets i₁
  obtain ⟨M, hM, hMR⟩ := mem_locFamily_iff.mp hmem
  have hM' : M ∈ insert L (nbhd Ω L) := C.omega_eq ▸ hM
  rcases hM' with rfl | hM'
  · exfalso
    obtain ⟨i₀, hi₀t, -, hi₀⟩ := locImg_eq_range_of_involution C.mfz D C.mem_centralizingMembers
      C.cls
    have hle : locImg Ω w M ≤ (D.hom i₁).range := hMR ▸ Subgroup.map_le_range _ _
    have hle0 : locImg Ω w M ≤ (D.hom i₀).range := hi₀ ▸ le_rfl
    have := eq_of_locImg_le_range C.inClass C.exact D hM hle0 hle
    subst this
    rcases htag with h | h <;> rw [h] at hi₀t <;> exact absurd hi₀t (by decide)
  · exact ⟨M, hM'⟩

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
