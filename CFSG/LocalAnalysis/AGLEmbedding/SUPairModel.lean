module

public import CFSG.LocalAnalysis.AGLEmbedding.SUPairInvolution
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.CTP.StrongPClassification
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import Certificates.Certificate43

public section

namespace CFSG.AGLEmbedding.SUPair

open Subgroup CFSG.ComponentClassification.AS76b

theorem map_oUpperTwo {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B) (X : Subgroup A) :
    (oUpperTwo X).map f = oUpperTwo (X.map f) := by
  rw [oUpperTwo, oUpperTwo, MonoidHom.map_closure]
  apply le_antisymm
  · refine closure_mono ?_
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    exact ⟨mem_map_of_mem f hx, ho.of_dvd_nat (orderOf_map_dvd f x)⟩
  · refine (closure_le _).mpr ?_
    rintro y ⟨⟨x, hx, rfl⟩, ho⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : (2 ^ a).Coprime (orderOf (f x)) :=
      Nat.Coprime.pow_left a (Odd.coprime_two_right ho).symm
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have h1 : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hxm ▸ dvd_mul_right _ _), hxm,
        Nat.mul_div_cancel_left m (by positivity)]
    refine subset_closure ⟨(x ^ 2 ^ a) ^ c, ⟨X.pow_mem (X.pow_mem hx _) _, ?_⟩, ?_⟩
    · exact (h1 ▸ hm).of_dvd_nat (orderOf_pow_dvd c)
    · rw [map_pow, map_pow, hc]

variable {Y : Type} [Group Y] [Finite Y]

theorem Heis27.of_card {A Z : Subgroup Y} (hA : Nat.card A = 27) (hZA : Z ≤ A)
    (hZ3 : Nat.card Z = 3) (hZc : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hcube : ∀ a ∈ A, a ^ 3 = 1) (hnab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) : Heis27 A Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup ↥A := center ↥A with hC
  set Zs : Subgroup ↥A := Z.subgroupOf A with hZs
  have hZsC : Zs ≤ C := by
    intro z hz
    rw [mem_center_iff]
    intro g
    have := hZc z (mem_subgroupOf.mp hz) g g.2
    exact Subtype.ext this.symm
  have hZscard : Nat.card Zs = 3 := by
    rw [hZs, Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hZ3]
  have hnab' : ¬ ∀ a b : ↥A, a * b = b * a := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact hab (congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩))
  have hquot : Nat.card ↥A = Nat.card (↥A ⧸ C) * Nat.card C :=
    card_eq_card_quotient_mul_card_subgroup C
  have hCcard : Nat.card C = 3 := by
    have hdvd : Nat.card C ∣ 27 := hA ▸ card_subgroup_dvd_card C
    have h3 : 3 ∣ Nat.card C := hZscard ▸ card_dvd_of_le hZsC
    have hne27 : Nat.card C ≠ 27 := by
      intro h27
      apply hnab'
      have hCtop : C = ⊤ := (card_eq_iff_eq_top C).mp (by rw [h27, hA])
      intro a b
      have : a ∈ C := hCtop ▸ mem_top a
      exact ((mem_center_iff.mp this) b).symm
    have hne9 : Nat.card C ≠ 9 := by
      intro h9
      apply hnab'
      have hq3 : Nat.card (↥A ⧸ C) = 3 := by
        rw [hA, h9] at hquot
        omega
      haveI : IsCyclic (↥A ⧸ C) := isCyclic_of_prime_card hq3
      exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' C)
        (by rw [QuotientGroup.ker_mk'])
    have : Nat.card C ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h
    · rw [h] at h3
      norm_num at h3
    · exact h
    · exact absurd h hne9
    · exact absurd h hne27
  have hCeq : C = Zs := (eq_of_le_of_card_ge hZsC (by rw [hCcard, hZscard])).symm
  refine ⟨hA, hZA, hZ3, hZc, ?_, ?_, hcube, hnab⟩
  · intro a ha b hb
    have hq9 : Nat.card (↥A ⧸ C) = 3 ^ 2 := by
      rw [hA, hCcard] at hquot
      omega
    have hcomm := IsPGroup.commutative_of_card_eq_prime_sq hq9
    have h1 : QuotientGroup.mk' C (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm (QuotientGroup.mk' C ⟨a, ha⟩) (QuotientGroup.mk' C ⟨b, hb⟩)]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    rw [hCeq, hZs, mem_subgroupOf] at h2
    simpa using h2
  · intro c hc hcen
    have h1 : (⟨c, hc⟩ : ↥A) ∈ C := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hcen g g.2).symm
    rw [hCeq, hZs, mem_subgroupOf] at h1
    exact h1

private theorem sq_conj_S {H : Type*} [Group H] {S D F : H} (hFS : F * S = D * F)
    (hFD : F * D = S ^ 2 * F) (hS : S ^ 3 = 1) : F ^ 2 * S * (F ^ 2)⁻¹ = S⁻¹ := by
  have h1 : F * S * F⁻¹ = D := by rw [hFS]; group
  have h2 : F * D * F⁻¹ = S ^ 2 := by rw [hFD]; group
  have hS2 : S ^ 2 = S⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hS]
  calc F ^ 2 * S * (F ^ 2)⁻¹ = F * (F * S * F⁻¹) * F⁻¹ := by rw [sq]; group
    _ = S⁻¹ := by rw [h1, h2, hS2]

private theorem sq_conj_D {H : Type*} [Group H] {S D F : H} (hFS : F * S = D * F)
    (hFD : F * D = S ^ 2 * F) (hD : D ^ 3 = 1) : F ^ 2 * D * (F ^ 2)⁻¹ = D⁻¹ := by
  have h1 : F * S * F⁻¹ = D := by rw [hFS]; group
  have h2 : F * D * F⁻¹ = S ^ 2 := by rw [hFD]; group
  have hD2 : D ^ 2 = D⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hD]
  calc F ^ 2 * D * (F ^ 2)⁻¹ = F * (F * D * F⁻¹) * F⁻¹ := by rw [sq]; group
    _ = F * S ^ 2 * F⁻¹ := by rw [h2]
    _ = (F * S * F⁻¹) ^ 2 := by rw [conj_pow]
    _ = D⁻¹ := by rw [h1, hD2]

open CFSG.GH74.QTGen4.Leaves.F112 CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape in
theorem exists_data_of_su {T : Subgroup Y}
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥T ≃* ↥(CFSG.Open.StatedSU 3 2 K))) :
    ∃ s d z f : Y, s ∈ T ∧ d ∈ T ∧ f ∈ T ∧ f ^ 4 = 1 ∧
      f ^ 2 * s * (f ^ 2)⁻¹ = s⁻¹ ∧ f ^ 2 * d * (f ^ 2)⁻¹ = d⁻¹ ∧
      (∀ x ∈ T, z * x = x * z) ∧ Heis27 (oUpperTwo T) (zpowers z) ∧
      s ∈ oUpperTwo T ∧ d ∈ oUpperTwo T ∧ s * d ≠ d * s := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK4, ⟨e⟩⟩ := h
  obtain ⟨ω, hω, h2⟩ := exists_omega hK4
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  have hZ1 := sZ_ne_one o
  have hFS := sF_mul_sS o
  have hFD := sF_mul_sD o
  have hF4 := sF_four o
  have hF2 := sF_sq_ne_one o
  have hcard : Nat.card (SUg K) = 216 := card_SUg hK4
  set ι : SUg K →* Y := T.subtype.comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := T.subtype_injective.comp e.symm.injective
  have hιT : ∀ x : SUg K, ι x ∈ T := fun x => (e.symm x).2
  have hιsurj : ∀ x ∈ T, ∃ y, ι y = x := fun x hx =>
    ⟨e ⟨x, hx⟩, by simp [hι]⟩
  have hord : orderOf (OmegaData.sF o) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := OmegaData.sF o) (by simpa using hF2)
      (by simpa using hF4)
    simpa using this
  haveI := heisSubgroup_normal hcard hrel hZ1 (hrel.F_mem_normalizer hFS hFD) hord
  have hO : oUpperTwo (⊤ : Subgroup (SUg K)) = heisSubgroup hrel := by
    apply le_antisymm
    · exact (closure_le _).mpr fun x hx => odd_mem_heisSubgroup hcard hrel hZ1 hx.2
    · intro x hx
      refine subset_closure ⟨mem_top x, ?_⟩
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hrel.cube_of_mem hx)
      exact (by decide : Odd 3).of_dvd_nat hdvd
  have hTmap : (⊤ : Subgroup (SUg K)).map ι = T := by
    apply le_antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact hιT x
    · intro x hx
      obtain ⟨y, rfl⟩ := hιsurj x hx
      exact mem_map_of_mem ι (mem_top y)
  have hOT : oUpperTwo T = (heisSubgroup hrel).map ι := by
    rw [← hO, map_oUpperTwo, hTmap]
  have hOcard : Nat.card (oUpperTwo T) = 27 := by
    rw [hOT, card_map_of_injective hιinj, card_heisSubgroup hcard hrel hZ1]
  set s := ι (OmegaData.sS o)
  set d := ι (OmegaData.sD o)
  set z := ι (sZ o)
  set f := ι (OmegaData.sF o)
  have hsO : s ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.S_mem
  have hdO : d ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.D_mem
  have hzO : z ∈ oUpperTwo T := hOT ▸ mem_map_of_mem ι hrel.Z_mem
  have hzc : ∀ x ∈ T, z * x = x * z := by
    intro x hx
    obtain ⟨y, rfl⟩ := hιsurj x hx
    rw [← map_mul, ← map_mul, sZ_central o y]
  have hsd : s * d ≠ d * s := by
    intro h
    apply hrel.S_mul_D_ne hZ1
    apply hιinj
    rw [map_mul, map_mul]
    exact h
  have hz3 : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sZ_cube o, map_one]
    · intro h
      apply hZ1
      apply hιinj
      rw [map_one]
      exact h
  refine ⟨s, d, z, f, hιT _, hιT _, hιT _, by rw [← map_pow, hF4, map_one], ?_, ?_, hzc, ?_,
    hsO, hdO, hsd⟩
  · rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, sq_conj_S hFS hFD (OmegaData.sS_cube o),
      map_inv]
  · rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, sq_conj_D hFS hFD (OmegaData.sD_cube o),
      map_inv]
  · refine Heis27.of_card hOcard (zpowers_le.mpr hzO) (by rw [Nat.card_zpowers, hz3]) ?_ ?_
      ⟨s, hsO, d, hdO, hsd⟩
    · intro w hw a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      have ha' : a ∈ T := oUpperTwo_le_self' ha
      exact ((Commute.zpow_left (hzc a ha') k : Commute (z ^ k) a)).eq
    · intro a ha
      rw [hOT] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      rw [← map_pow, hrel.cube_of_mem hx, map_one]
  where
    oUpperTwo_le_self' {X : Subgroup Y} {a : Y} (ha : a ∈ oUpperTwo X) : a ∈ X :=
      (closure_le _).mpr (fun _ hx => hx.1) ha

end CFSG.AGLEmbedding.SUPair
