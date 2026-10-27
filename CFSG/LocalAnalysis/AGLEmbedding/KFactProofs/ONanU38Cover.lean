module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Vec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem card_scalars : Nat.card (unitaryScalars hU 3) = 3 := by
  have hF : Nat.card GF64 = (2 ^ 3) ^ 2 := by rw [GF64.card_eq]; norm_num
  rw [unitaryScalars_eq hU (by norm_num)]
  have := (CFSG.LinearGroups.unitary_scalar_kernel (K := GF64) (p := 2) (f := 3) Nat.prime_two
    hF (n := 3) (by norm_num)).2.2
  rw [this]
  norm_num

theorem card_PSU : Nat.card (unitaryPSU hU 3) = 5515776 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars hU 3)
  rw [card_SU, card_scalars] at h
  have h2 : Nat.card (unitaryPSU hU 3) * 3 = 16547328 := h.symm
  omega

theorem commutator_mul_center {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h1 : z * b = b * z := (Subgroup.mem_center_iff.1 hz b).symm
  have h2 : z * b * z⁻¹ = b := by rw [h1]; group
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * z * b * (z⁻¹ * a⁻¹) * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

theorem commutator_mul_center_mul_center {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_center hz, ← commutatorElement_inv, commutator_mul_center hw,
    commutatorElement_inv]

section Cover


theorem card_hopf_psu : Nat.card (CFSG.Open.griessHopfMultiplier (unitaryPSU hU 3)) = 3 := by
  have hF : Nat.card GF64 = (2 ^ 3) ^ 2 := by rw [GF64.card_eq]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (F := GF64) (p := 2) (f := 3) hF (by norm_num) (n := 3) (by norm_num) (by decide)
    (by norm_num)
  have e' := (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
    (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3))).trans e
  rw [Nat.card_congr e'.toEquiv]
  simp

theorem card_center_dvd_three {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (e1 : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3) : Nat.card (Subgroup.center K) ∣ 3 := by
  have := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e1
  rwa [card_hopf_psu] at this

theorem exists_equiv_psu {K : Type} [Group K] (e1 : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3)
    (hZ : Subgroup.center K = ⊥) : Nonempty (K ≃* unitaryPSU hU 3) :=
  ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e1⟩

theorem exists_equiv_su {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (e1 : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3) (hZ : Nat.card (Subgroup.center K) = 3) :
    ∃ f : SU ≃* K, ∀ c ∈ Subgroup.center K, ∃ z ∈ unitaryScalars hU 3, f z = c := by
  classical
  have hF : Nat.card GF64 = (2 ^ 3) ^ 2 := by rw [GF64.card_eq]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : K →* unitaryPSU hU 3 := e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    with hqdef
  have hq : Function.Surjective q := e1.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : ∀ k, q k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    change e1 (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ _
    rw [map_eq_one_iff _ e1.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set π0 : SU →* unitaryPSU hU 3 := unitaryProj hU 3 with hπ0
  let P : Subgroup (K × SU) :=
    MonoidHom.eqLocus (q.comp (MonoidHom.fst K SU)) (π0.comp (MonoidHom.snd K SU))
  have hP : ∀ x : P, q (x : K × SU).1 = π0 (x : K × SU).2 := fun x => x.2
  let p2 : P →* SU := (MonoidHom.snd K SU).comp P.subtype
  have hp2 : Function.Surjective p2 := by
    intro g
    obtain ⟨k, hk⟩ := hq (π0 g)
    exact ⟨⟨(k, g), hk⟩, rfl⟩
  have hcen : p2.ker ≤ Subgroup.center P := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (x : K × SU).2 = 1 := hx
    have hxq : (x : K × SU).1 ∈ Subgroup.center K := by
      rw [← hqker, hP x, hx1, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.1 hxq (y : K × SU).1)
    · simp [hx1]
  have hn : (3 : ℕ) ≤ 3 := le_rfl
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
    (F := GF64) (p := 2) (f := 3) hF (by norm_num) (n := 3) hn (by decide) (by norm_num)
    (E := P) (π := p2) hp2 hcen
  let f : SU →* K := (MonoidHom.fst K SU).comp (P.subtype.comp s)
  have hf : ∀ g, q (f g) = π0 g := by
    intro g
    have h1 := hP (s g)
    have h2 : (s g : K × SU).2 = g := hs g
    rw [h2] at h1
    exact h1
  have hdecomp : ∀ k : K, ∃ g : SU, ∃ z ∈ Subgroup.center K, k = f g * z := by
    intro k
    obtain ⟨g, hg⟩ := unitaryProj_surjective hU 3 (q k)
    refine ⟨g, (f g)⁻¹ * k, ?_, by group⟩
    rw [← hqker, map_mul, map_inv, hf, hg, inv_mul_cancel]
  have hsurj : Function.Surjective f := by
    have hcomm : commutator K ≤ f.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨g₁, z₁, hz₁, rfl⟩ := hdecomp a
      obtain ⟨g₂, z₂, hz₂, rfl⟩ := hdecomp b
      rw [commutator_mul_center_mul_center hz₁ hz₂, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have htop : f.range = ⊤ := top_le_iff.1 (by
      rw [← hperf.commutator_eq_top]
      exact hcomm)
    exact MonoidHom.range_eq_top.1 htop
  have hcardK : Nat.card K = Nat.card SU := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [hZ, Nat.card_congr e1.toEquiv, card_PSU] at h
    rw [h, card_SU]
  have hbij : Function.Bijective f :=
    Function.Surjective.bijective_of_nat_card_le hsurj (by rw [hcardK])
  refine ⟨MulEquiv.ofBijective f hbij, fun c hc => ?_⟩
  obtain ⟨g, hg⟩ := hsurj c
  refine ⟨g, ?_, hg⟩
  rw [← ker_unitaryProj hU 3, MonoidHom.mem_ker, ← hf, hg, hqker]
  exact hc

end Cover

end CFSG.AGLEmbedding.ChevOuter.U38
