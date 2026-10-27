module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT0
public import CFSG.CGT.PushingUpLit.SolKNA.QuatSporadic
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieRanges
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem le_tightCore_of_isPGroup {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P) :
    P ≤ tightCore P := fun _ hx =>
  Subgroup.subset_closure ⟨hx, hP.to_le (Subgroup.zpowers_le.2 hx)⟩

theorem lt3_tightDatum {G : Type} [Group G] [Finite G] {K : Subgroup G} {t : G}
    (ht2 : orderOf t = 2) (htP : t ∈ pCoreOf 2 K) (hPq : IsQuaternionTwoGroup (pCoreOf 2 K))
    (hPC : pCoreOf 2 K ≤ Subgroup.centralizer ({t} : Set G))
    (hPn : ((pCoreOf 2 K).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    ∃ SP : Sylow 2 ↥(pCoreOf 2 K), TightDatum (pCoreOf 2 K) SP t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  obtain ⟨n, hn, ⟨e⟩⟩ := hPq
  obtain ⟨SP, hSP⟩ : ∃ SP : Sylow 2 ↥(pCoreOf 2 K), (SP : Subgroup ↥(pCoreOf 2 K)) = ⊤ := by
    have hTop : IsPGroup 2 (⊤ : Subgroup ↥(pCoreOf 2 K)) :=
      hP2.of_equiv Subgroup.topEquiv.symm
    obtain ⟨S', hS'⟩ := hTop.exists_le_sylow
    exact ⟨S', top_le_iff.mp hS'⟩
  refine ⟨SP, ⟨⟨n, hn, ⟨(MulEquiv.subgroupCongr hSP).trans (Subgroup.topEquiv.trans e)⟩⟩, ?_, ht2,
    hPC, hPn, hP2.to_quotient _⟩⟩
  rw [hSP, Subgroup.map_top, Subgroup.range_subtype]
  exact htP

theorem eq_top_of_isSubnormal_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    {A K : Subgroup G} (h : CFSG.Open.IsSubnormal A K) : K = ⊤ → A ≠ ⊥ → A = ⊤ := by
  induction h with
  | refl H => intro hK _; exact hK
  | @step H M K' hHM hN hMK ih =>
    intro hK hA
    have hM : M ≠ ⊥ := fun hM => hA (le_bot_iff.mp (hM ▸ hHM))
    have hMtop : M = ⊤ := ih hK hM
    subst hMtop
    have hHn : H.Normal := ⟨fun n hn g => by
      have := hN.conj_mem ⟨n, trivial⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨g, trivial⟩
      exact Subgroup.mem_subgroupOf.mp this⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · exact absurd h hA
    · exact h

section Large

theorem large_of_component {G : Type} [Group G] [Finite G] {K : Subgroup G} (hK : STSetting G K)
    (R₀ : Sylow 2 K) (hq : IsQuaternionTwoGroup (sylowImg R₀)) (hT : Lie3Table)
    (hP : Pos3Table) (c : CompData) (hc : c.Valid) (ψ : c.G →* G)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _) (L : Subgroup G)
    (hLfund : ∃ R ∈ c.fund, L = R.map ψ) (hPL : pCoreOf 2 K ≤ L) : MTOutcome G K R₀ := by
  have : IsSimpleGroup G := hK.simple
  rcases hc with ⟨τ, n, hFT, hadm, rfl⟩ | rfl | rfl
  · obtain ⟨R, hR, rfl⟩ := hLfund
    have hsv := hT τ n hFT hadm G ψ hsurj hker R hR K hK R₀ hq hPL
    obtain ⟨hqs, hmodel⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero τ n 3 1
      Nat.prime_three hFT hadm
    have hperf : commutator (modelUniv τ n 3 1 Nat.prime_three).K = ⊤ := hqs.1
    have hZ := center_eq_map_center_of_central_kernel ψ hsurj hker hperf
    let e := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ hsurj hker hZ
    have hmodelG : CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) τ n 3 1 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel
    have hZG : Subgroup.center G = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot G hK.nonab
    let e₂ : G ⧸ Subgroup.center G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hZG).trans QuotientGroup.quotientBot
    have hLie : CFSG.Blueprint.LieModel G τ n 3 1 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e₂ hmodelG
    rcases hsv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · have hQ8 := hP G .PSL 3 (Or.inl ⟨rfl, rfl⟩) hLie (sylowImg R₀) hq
      exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inl
        (statedClassical_of_lieModel_ne_zero (by norm_num) hLie)⟩))
    · have hQ8 := hP G .PSU 3 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hLie (sylowImg R₀) hq
      exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inl
        (statedClassical_of_lieModel_ne_zero (by norm_num) hLie))⟩))
    · have hn : n = 0 := hadm.2.2.1
      subst hn
      have hQ8 := hP G .G2 0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hLie (sylowImg R₀) hq
      exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inr (Or.inl hLie))⟩))
  · exfalso
    have hcard : Nat.card G ≤ Nat.card SL(2, ZMod 3) := Nat.card_le_card_of_surjective ψ hsurj
    rw [natCard_sl2Three] at hcard
    have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty ‹IsSimpleGroup G›
      hK.nonab
    omega
  · have hM := m11Facts
    have hsimpleM : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := hM.1
    have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      let _ : CommGroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
        { (inferInstance : Group ↥CFSG.Blueprint.NativeSporadic.M11) with mul_comm := hcon }
      have := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
      rw [hM.2] at this
      exact absurd this (by norm_num)
    have hc : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact le_bot_iff.mp (hker.trans hc.le)
    let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* G := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
    have hQ8 : Nonempty (↥(sylowImg R₀) ≃* QuaternionGroup 2) :=
      nonempty_equiv_quaternionGroup_two_of_perm hq (Ω := Fin 11) (by simp)
        ((CFSG.Blueprint.NativeSporadic.M11).subtype.comp e.symm.toMonoidHom)
        (Subtype.val_injective.comp e.symm.injective)
    exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm⟩)))⟩))

theorem qlLarge_of_lift (hCIT : CIT3Inductive) (hLift : TightLiftSimple) (hT : Lie3Table)
    (hP : Pos3Table) : QLLarge := by
  intro G _ _ K hK R₀ hq _ hnG
  have : IsSimpleGroup G := hK.simple
  obtain ⟨t, ht2, htP, hPq, -, hPC, hPn, -⟩ := lt3_datum hK R₀ hq
  obtain ⟨SP, hD⟩ := lt3_tightDatum ht2 htP hPq hPC hPn
  obtain ⟨L, hL1, hL2⟩ := hLift G hK.nonab hnG (pCoreOf 2 K) SP t hD
  have hPL : pCoreOf 2 K ≤ L :=
    (le_tightCore_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans hL1
  have htL : t ∈ L := hL2.mem
  have hLne : L ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.mem_bot] at htL
    rw [htL, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hcl : subnormalClosure L = ⊤ :=
    eq_top_of_isSubnormal_of_simple (isSubnormal_subnormalClosure L) rfl
      (fun h => hLne (le_bot_iff.mp (h ▸ le_subnormalClosure L)))
  have hO : CFSG.Open.classicalInvolutionOddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.classicalInvolutionOddCore G)
      with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card ↥(CFSG.Open.classicalInvolutionOddCore G)) :=
        CFSG.ComponentClassification.OddCore.odd_card G
      rw [h, Subgroup.card_top] at hodd
      have h2dvd : 2 ∣ Nat.card G := ht2 ▸ orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hΛ := inClass3_conjugates_of_closure hL2 hcl
  have hLΛ : L ∈ Set.range (fun g : G => conjSub g L) := ⟨1, conjSub_one L⟩
  obtain ⟨ι, hι, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree hO (hCIT G _ hΛ)
  obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hLΛ
  have hLrange : L ≤ (D.hom i).range := hLR.le.trans (Subgroup.map_le_range _ _)
  have := D.range_normal i
  have hsub : CFSG.Open.IsSubnormal (D.hom i).range ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hcl]
    exact subnormalClosure_le hLrange hsub
  exact large_of_component hK R₀ hq hT hP (D.kind i) (D.valid i) (D.hom i) hsurj
    (D.ker_le_center i) L ⟨R, hR, hLR⟩ hPL

end Large

end CFSG.CGT.PushingUpLit.SolKNA
