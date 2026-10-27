module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b8
public import CFSG.ClassicalInvolution.Q3.TL4OddBadW
public import CFSG.ClassicalInvolution.Q3.TL4ConnBend
public import CFSG.ClassicalInvolution.Q3.Q3AMDB04
public import CFSG.Holt.PointHullTwoGroupBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem exists_gens_of_card_le_two_pow {F : Type} [Group F] [Finite F] {k : ℕ}
    (h : Nat.card F ≤ 2 ^ k) : ∃ s : Finset F, s.card ≤ k ∧ Subgroup.closure (s : Set F) = ⊤ := by
  classical
  have key : ∀ m : ℕ, ∃ s : Finset F, s.card ≤ m ∧
      (Subgroup.closure (s : Set F) = ⊤ ∨ 2 ^ m ≤ Nat.card (Subgroup.closure (s : Set F))) := by
    intro m
    induction m with
    | zero => exact ⟨∅, by simp, Or.inr (by rw [pow_zero]; exact Nat.card_pos)⟩
    | succ m ih =>
      obtain ⟨s, hs, hs' | hs'⟩ := ih
      · exact ⟨s, hs.trans m.le_succ, Or.inl hs'⟩
      by_cases htop : Subgroup.closure (s : Set F) = ⊤
      · exact ⟨s, hs.trans m.le_succ, Or.inl htop⟩
      obtain ⟨g, hg⟩ : ∃ g, g ∉ Subgroup.closure (s : Set F) := by
        by_contra hcon
        push Not at hcon
        exact htop (eq_top_iff.mpr fun x _ => hcon x)
      refine ⟨insert g s, (Finset.card_insert_le g s).trans (Nat.succ_le_succ hs), Or.inr ?_⟩
      have hle : Subgroup.closure (s : Set F) ≤
          Subgroup.closure ((insert g s : Finset F) : Set F) := by
        apply Subgroup.closure_mono
        rw [Finset.coe_insert]
        exact Set.subset_insert g _
      have hgmem : g ∈ Subgroup.closure ((insert g s : Finset F) : Set F) :=
        Subgroup.subset_closure (by simp)
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
      have hc1 : c ≠ 1 := by
        rintro rfl
        rw [mul_one] at hc
        have heq := Subgroup.eq_of_le_of_card_ge hle hc.le
        rw [← heq] at hgmem
        exact hg hgmem
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact (Nat.card_pos (α := Subgroup.closure ((insert g s : Finset F) : Set F))).ne' hc
      rw [hc, pow_succ]
      exact Nat.mul_le_mul hs' (by omega)
  obtain ⟨s, hs, hs' | hs'⟩ := key k
  · exact ⟨s, hs, hs'⟩
  · exact ⟨s, hs, Subgroup.eq_top_of_card_eq _
      (le_antisymm (Subgroup.card_le_card_group _) (h.trans hs'))⟩

theorem isBenderGroup_or_fourGenerated {L : Type} [Group L] [Finite L]
    (h : goldschmidtSimpleType L) : fusionIsBenderGroup L ∨ TwoSubgroupsFourGenerated L := by
  rcases CFSG.Holt.PointHull.fusionIsBenderGroup_or_card_dvd h with hB | ⟨k, hk, hdvd⟩
  · exact Or.inl hB
  · refine Or.inr fun P hP => ?_
    have h8 : Nat.card P ≤ 2 ^ 3 :=
      Nat.le_of_dvd (by norm_num) (CFSG.Holt.PointHull.card_dvd_eight_of_isPGroup hk hdvd hP)
    obtain ⟨s, hs, hcl⟩ := exists_gens_of_card_le_two_pow h8
    refine ⟨s.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_⟩
    · rw [Finset.card_map]
      omega
    · have e := MonoidHom.map_closure P.subtype (s : Set P)
      rw [hcl, Subgroup.map_top, Subgroup.range_subtype] at e
      rw [Finset.coe_map]
      exact e.symm

private theorem bender_of_fusionIsBenderGroup {X : Type} [Group X]
    (h : fusionIsBenderGroup X) : CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · exact .isPSU3 f hf
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 f).symm))
  · exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a).symm))

private theorem genFittingFStar_le_of_normal_of_ne_bot {Y : Type} [Group Y]
    (hs : IsSimpleGroup ↥(genFittingFStar Y))
    (hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥) {N : Subgroup Y}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : genFittingFStar Y ≤ N := by
  have hFn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hNF : (N.subgroupOf (genFittingFStar Y)).Normal := Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (genFittingFStar Y)) with h | h
  · exfalso
    apply hN1
    have hd : Disjoint N (genFittingFStar Y) := Subgroup.subgroupOf_eq_bot.mp h
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot, ← Subgroup.mem_bot, ← hC, Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have := hN.conj_mem x⁻¹ (N.inv_mem hx) y
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact N.mul_mem hx this
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ genFittingFStar Y :=
      (genFittingFStar Y).mul_mem (hFn.conj_mem y hy x) ((genFittingFStar Y).inv_mem hy)
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.mp hd h1 h2
    calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
      _ = x * y := by rw [h3, inv_one, one_mul]
  · exact Subgroup.subgroupOf_eq_top.mp h

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_bot_of_stronglyClosed_of_large (hgold : CFSG.Goldschmidt.TopStatement)
    (hL : TightLargeHypR r n Y R S t) (T : Sylow 2 Y) {A : Subgroup Y}
    (hAT : A ≤ (T : Subgroup Y)) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set Y) (T : Subgroup Y)) : A = ⊥ := by
  by_contra hA1
  obtain ⟨hFs, hFnab, hFc⟩ := TL4.TightLargeHypR.isSimpleGroup_genFittingFStar hL
  set F : Subgroup Y := genFittingFStar Y with hFdef
  have hFn : F.Normal := genFittingFStar_normal Y
  set M : Subgroup Y := Subgroup.normalClosure (A : Set Y) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hFM : F ≤ M := genFittingFStar_le_of_normal_of_ne_bot hFs hFc hMn fun h => hA1 (by
    rw [eq_bot_iff, ← h]
    exact hAM)
  have hOM : CFSG.oddCore ↥M = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.normal_intersection Y M
    have hO : componentClassificationOddCore Y = ⊥ := hL.cls.2.2
    rw [hO, inf_bot_eq] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  obtain ⟨-, -, hcomp⟩ := CFSG.ComponentClassification.AschbacherTheorem3.goldschmidt_subgroup
    hgold T hAT hAab hcl rfl hOM
  set K : Subgroup ↥M := F.subgroupOf M with hKdef
  have hKn : K.Normal := Subgroup.normal_subgroupOf
  let e : ↥K ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFM
  have hKs : IsSimpleGroup ↥K := e.isSimpleGroup
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hFnab
    refine ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, h']
  have hcK : IsComponentOf K ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤),
      CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hKnab⟩
  have hZ : Subgroup.center ↥K = ⊥ := CFSG.Holt.PointHull.center_eq_bot_of_isSimpleGroup hKnab
  have htype : goldschmidtSimpleType ↥F :=
    CFSG.ComponentClassification.AschbacherTheorem3.goldschmidtSimpleType_of_mulEquiv
      (e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)
      (hcomp K hcK)
  rcases isBenderGroup_or_fourGenerated htype with hB | h4
  · exact TL4.tightBenderEndR Y R S t hL.datum (bender_of_fusionIsBenderGroup hB) hFc
  · exact hL.large h4

theorem Tri.of_tight (hL : TightLargeHypR r n Y R S t)
    (hall : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J)
    {J M : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u)
    (hB2 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t M) :
    Tri r (CoreAssembly.conjClass (tightCore R)) (tightCore R) J M t u where
  fam := (TightLargeHypR.typeRFam hL)
  trans := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    exact ⟨g' * g⁻¹, by rw [← conjSub_mul, inv_mul_cancel_right]⟩
  mem := CoreAssembly.mem_conjClass_self _
  inv_K := hL.datum.isUniqueInvolution_core
  adj_J := hJ
  inv_J := hu
  adj_M := hM
  adj_MJ := hMJ
  h2 := fun J' hJ' K' hK' hK'J' u' z' hu' hz' => hall J' hJ' K' hK' hK'J' u' z' hu' hz'
  h7 := by
    intro L hL'
    rcases hB2 L hL' with e | e
    · obtain ⟨ν, hν, hLν⟩ := exists_conj_of_secImg_eq (TightLargeHypR.typeRFam hL)
        (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hL') e.symm
      exact ⟨(ν : Y), Subgroup.mem_map.mpr ⟨ν, hν, rfl⟩, Or.inl hLν⟩
    · obtain ⟨ν, hν, hLν⟩ := exists_conj_of_secImg_eq (TightLargeHypR.typeRFam hL)
        (xMem_of_mem_omegaNbr_core hL hM) (xMem_of_mem_omegaNbr_core hL hL') e.symm
      exact ⟨(ν : Y), Subgroup.mem_map.mpr ⟨ν, hν, rfl⟩, Or.inr hLν⟩

theorem false_of_B2b' (hgold : CFSG.Goldschmidt.TopStatement) (hQ : QuatAutFacts r)
    (hL : TightLargeHypR r n Y R S t)
    (hall : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J)
    {J M : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u)
    (hB2 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t M)
    (hrig : RigidEdge (tightCore R) J t u) : False := by
  have h := Tri.of_tight hL hall hJ hM hMJ hu hB2
  obtain ⟨S₀, hES, hcl⟩ := h.stronglyClosed hQ hrig
  have hab : IsMulCommutative (Subgroup.closure ({t, u} : Set Y)) :=
    Q3AM.isMulCommutative_closure_pair h.comm_tu
  have hbot := eq_bot_of_stronglyClosed_of_large hgold hL S₀ hES hab hcl
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  rw [hbot, Subgroup.mem_bot] at htE
  exact h.inv_K.ne_one htE

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
