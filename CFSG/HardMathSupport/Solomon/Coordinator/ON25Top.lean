module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Final
public import CFSG.HardMathSupport.Solomon.Coordinator.C25ON
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONMult
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Defs
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

section


theorem onGeneration_of_mult (hMult : CFSG.EvenSporadicStandard.Induction.ONMultThree) :
    ONGeneration := by
  intro Y _ _ hY hiso B hBel hB27
  obtain ⟨iso⟩ := hiso
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hq' : CFSG.IsQuasisimple Y :=
    ⟨⟨hY.1⟩, hY.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hY⟩
  have hd := hMult Y hq' ⟨iso.trans b'.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · have hcen : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    let e1 : Y ⧸ (⊥ : Subgroup Y) ≃* Y := QuotientGroup.quotientBot
    let e2 : Y ⧸ Subgroup.center Y ≃* Y ⧸ (⊥ : Subgroup Y) := QuotientGroup.quotientMulEquivOfEq hcen
    have f : Y ≃* PON.Group :=
      ((e2.trans e1).symm.trans (iso.trans b'.symm)).trans nonempty_equiv_PON.some
    exact on25_gen_simple hY hcen f B hBel hB27
  · have hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover Y CFSG.Blueprint.NativeSporadic.ON :=
      ⟨h3, ⟨iso.trans b'.symm⟩⟩
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model ⟨hY.1⟩ hT
    exact on25_gen_cover hY e B hBel hB27

theorem input23_25_2Facts_on1_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], UniquenessMaximal.IsHatON Y → ∀ B₀ : Subgroup Y,
      IsElemAbelian 3 B₀ → Nat.card B₀ = 27 → ⊤ ≤ gammaLBelow B₀ (⊤ : Subgroup Y) := by
  intro Y _ _ hH B₀ hB₀ h27
  obtain ⟨hperf, hZ, ⟨iso⟩⟩ := hH
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := by
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
      CFSG.Sporadic.ON.isSimpleGroup_ON
    exact (iso.trans b'.symm).isSimpleGroup
  have hY : CFSG.Open.IsQuasisimple Y := ⟨hperf, hsimple⟩
  have hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover Y CFSG.Blueprint.NativeSporadic.ON :=
    ⟨hZ, ⟨iso.trans b'.symm⟩⟩
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model ⟨hperf⟩ hT
  have hcenE : (Subgroup.center Y).map e.toMonoidHom = center GM := Subgroup.map_center_eq e
  have hcomm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcentral : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Y := fun x hx y hy => by
    rw [hcomm x hx y hy]
    simp
  have hE : CFSG.RankThree.PartTwo.Late.IsE27 (B₀.map e.toMonoidHom) := by
    refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      show e x * e y = e y * e x
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      show (e x) ^ 3 = 1
      rw [← map_pow, hB₀.2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective e.injective, h27]
  have hcov := on25_gen_cover_of_E27 hY e B₀ hcentral hE le_rfl
  obtain ⟨c, hcB, hcz⟩ := on25_E27_contains_z hE
  have hcc : c ∈ Subgroup.center Y := by
    have : e c ∈ (Subgroup.center Y).map e.toMonoidHom := by
      rw [hcenE]
      show e c ∈ center GM
      rw [show e c = zG from hcz, center_GM]
      exact mem_zpowers zG
    obtain ⟨c', hc', hcc'⟩ := this
    exact (e.injective hcc' ▸ hc' : c ∈ Subgroup.center Y)
  have hc1 : c ≠ 1 := fun h => relG.x1 (by rw [← show e c = zG from hcz, h, map_one])
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hB₀.2 c hcB) hc1
  have hZc : Subgroup.center Y = zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcc)
      (by rw [hZ, Nat.card_zpowers, hc3])).symm
  have hpr3 : CFSG.pRank 3 ↥B₀ = 3 := c25_pRank_eq hB₀ (by rw [h27]; norm_num)
  refine hcov.trans (iSup₂_le fun b hb => iSup_le fun hbc => ?_)
  set E : Subgroup Y := zpowers c ⊔ zpowers b with hEdef
  have hEB : E ≤ B₀ := sup_le (Subgroup.zpowers_le.2 hcB) (Subgroup.zpowers_le.2 hb)
  have hE9 : Nat.card E = 9 := by
    refine CFSG.RankThree.PartTwo.Sec4.card_zpowers_sup_zpowers (hB₀.2 b hb) hc3 ?_ ?_
    · rw [← hZc]; exact hbc
    · exact Subgroup.mem_center_iff.1 hcc b
  have hEel : IsElemAbelian 3 E := LocalBalance.Lemma54Ns.isElemAbelian_of_le' hB₀ hEB
  have hpr2 : CFSG.pRank 3 ↥E = 2 := c25_pRank_eq hEel (by rw [hE9]; norm_num)
  have hC : (⊤ : Subgroup Y) ⊓ Subgroup.centralizer (E : Set Y) =
      Subgroup.centralizer ({b} : Set Y) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.mem_top, true_and]
    constructor
    · intro h
      exact (h b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))).symm
    · intro h y hy
      have hEle : E ≤ Subgroup.centralizer ({x} : Set Y) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.1 hcc x).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact h.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hEle hy)
  have hrk : pRank 3 B₀ - 1 ≤ pRank 3 E := by
    show CFSG.pRank 3 ↥B₀ - 1 ≤ CFSG.pRank 3 ↥E
    rw [hpr3, hpr2]
  unfold gammaLBelow
  rw [← hC]
  exact le_iSup₂_of_le E ⟨hEB, hrk⟩ le_rfl

theorem input23_25_2Facts_holds : Input23_25_2Facts := ⟨input23_25_2Facts_on1_holds⟩

end

end CFSG.HardMathSupport.Solomon.Coordinator
