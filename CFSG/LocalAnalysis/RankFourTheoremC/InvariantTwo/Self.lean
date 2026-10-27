module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_2Self
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.inf_centralizer_le_self (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D := by
  classical
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hCM : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have hCp : ∀ y ∈ centralizer (D : Set G), y ^ p = 1 → y ∈ D := fun y hyC hyp =>
    hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCM hyC hyp
  have hDC : D ≤ centralizer (D : Set G) := le_centralizer_iff_isMulCommutative.mpr hDab
  have hCN : centralizer (D : Set G) ≤ normalizer (D : Set G) := centralizer_le_normalizer _
  set S : Subgroup G := (P : Subgroup G) ⊓ centralizer (D : Set G)
  set T : Subgroup G := (P : Subgroup G) ⊓ normalizer (D : Set G)
  have hDS : D ≤ S := le_inf hDP hDC
  have hST : S ≤ T := inf_le_inf_left _ hCN
  have hSp : IsPGroup p S := P.isPGroup'.to_inf_left
  have hSD : ∀ y ∈ S, y ^ p = 1 → y ∈ D := fun y hy hyp => hCp y hy.2 hyp
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer (D : Set G)) := by
    have hN := hS.isSylowOf_normalizer_inf hD1 hp hext hPD hDab hCM hzD hz1 hzc hN₀M
    have hC := hN.inf_of_le_normalizer hCN
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D)
    rwa [inf_assoc, inf_eq_right.mpr hCN] at hC
  by_contra hSnD
  obtain ⟨s, hsS, hsD⟩ := IsConcreteLE.not_le_iff_exists.mp hSnD
  obtain ⟨y, hyD, hy1, hyW⟩ := exists_ne_one_mem_inf_pPowerSubgroup hSp hSD hsS hsD
  have hDW : D ≤ pPowerSubgroup p S := by
    have hN := normalizer_le_normalizer_inf_pPowerSubgroup hsyl hDS hDe.2 hSD
    exact (le_of_normalizer_le_of_exists_conj inf_le_left ⟨y, ⟨hyD, hyW⟩, hy1⟩ hN
      fun d hd hd1 =>
        hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCM hzD hz1 hzc hN₀M hd hd1).trans
      inf_le_right
  obtain ⟨g, hgP, hgD, hD'T, hTD'⟩ := exists_conj_normalizer_inf hprime P hDP hPD
  set D' : Subgroup G := D.map (MulAut.conj g).toMonoidHom
  have hD'ne : D' ≠ D := fun h => hgD (mem_normalizer_iff_map_conj_eq.mpr h)
  have hD'card : Nat.card D' = Nat.card D := card_map_of_injective (MulAut.conj g).injective
  have hD'e : ∀ w ∈ D', w ^ p = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    change (g * d * g⁻¹) ^ p = 1
    rw [conj_pow, hDe.2 d hd, mul_one, mul_inv_cancel]
  obtain ⟨u, huD', huC⟩ : ∃ u ∈ D', u ∉ centralizer (D : Set G) := by
    by_contra hall
    push Not at hall
    exact hD'ne (Subgroup.eq_of_le_of_card_ge
      (fun w hw => hCp w (hall w hw) (hD'e w hw)) hD'card.ge)
  have huT : u ∈ T := hD'T huD'
  have huN : u ∈ normalizer (D : Set G) := huT.2
  have hupow : ∀ s ∈ S, u * s ^ p = s ^ p * u := by
    intro s hs
    have hsC : s ∈ centralizer (D : Set G) := hs.2
    have hsT : s ∈ T := hST hs
    have haS : u⁻¹ * s * u ∈ S := by
      have hsP : s ∈ (P : Subgroup G) := hs.1
      have huP : u ∈ (P : Subgroup G) := huT.1
      have haP : u⁻¹ * s * u ∈ (P : Subgroup G) := mul_mem (mul_mem (inv_mem huP) hsP) huP
      refine ⟨haP, ?_⟩
      · show u⁻¹ * s * u ∈ centralizer (D : Set G)
        rw [mem_centralizer_iff]
        intro h hh
        have hh' : u * h * u⁻¹ ∈ D := (mem_normalizer_iff.mp huN h).mp hh
        have := mem_centralizer_iff.mp hsC _ hh'
        calc h * (u⁻¹ * s * u) = u⁻¹ * ((u * h * u⁻¹) * s) * u := by group
          _ = u⁻¹ * (s * (u * h * u⁻¹)) * u := by rw [this]
          _ = (u⁻¹ * s * u) * h := by group
    have hcS : s⁻¹ * (u⁻¹ * s * u) ∈ S := mul_mem (inv_mem hs) haS
    have hcD' : s⁻¹ * (u⁻¹ * s * u) ∈ D' := by
      have h1 : s⁻¹ * u * s⁻¹⁻¹ ∈ D' := (mem_normalizer_iff.mp (hTD' (inv_mem hsT)) u).mp huD'
      have h2 := inv_mem h1
      have h3 := mul_mem h2 huD'
      rwa [show (s⁻¹ * u * s⁻¹⁻¹)⁻¹ * u = s⁻¹ * (u⁻¹ * s * u) by group] at h3
    have hcD : s⁻¹ * (u⁻¹ * s * u) ∈ D := hCp _ hcS.2 (hD'e _ hcD')
    have hcomm : s * (s⁻¹ * (u⁻¹ * s * u)) = (s⁻¹ * (u⁻¹ * s * u)) * s :=
      (mem_centralizer_iff.mp hsC _ hcD).symm
    have hcp : (s⁻¹ * (u⁻¹ * s * u)) ^ p = 1 := hD'e _ hcD'
    have hpow : (u⁻¹ * s * u) ^ p = s ^ p := by
      have e : u⁻¹ * s * u = s * (s⁻¹ * (u⁻¹ * s * u)) := by group
      rw [e, Commute.mul_pow hcomm, hcp, mul_one]
    have hconjp : (u⁻¹ * s * u) ^ p = u⁻¹ * s ^ p * u := by
      have := conj_pow (a := u⁻¹) (b := s) (i := p)
      simpa using this
    have hfix : u⁻¹ * s ^ p * u = s ^ p := hconjp.symm.trans hpow
    have h1 : u * (u⁻¹ * s ^ p * u) = s ^ p * u := by group
    rw [hfix] at h1
    exact h1
  have hcentr : pPowerSubgroup p S ≤ centralizer ({u} : Set G) := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hupow s hs
  apply huC
  rw [mem_centralizer_iff]
  intro d hd
  exact (mem_centralizer_iff.mp (hcentr (hDW hd)) u (Set.mem_singleton u)).symm

end CFSG.LocalAnalysis.RankFourTheoremC
