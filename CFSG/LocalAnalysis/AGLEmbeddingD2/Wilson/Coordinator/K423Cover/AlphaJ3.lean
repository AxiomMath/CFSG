module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.RigidOuter
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Open (GLAPPrimeCore GLAPPrimeCoreOf)
open Subgroup

theorem aschbacherSolvableCore_le_GLAPPrimeCore (H : Type*) [Group H] [Finite H] :
    aschbacherSolvableCore 3 H ≤ GLAPPrimeCore 3 H := by
  obtain ⟨-, hchar, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have : (aschbacherSolvableCore 3 H).Characteristic := hchar
  refine le_sSup ⟨inferInstance, ?_⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3

theorem aschbacherSolvableCore_eq_bot_of_GLAPPrimeCoreOf {G : Type*} [Group G] [Finite G]
    {C : Subgroup G} (h : GLAPPrimeCoreOf 3 C = ⊥) : aschbacherSolvableCore 3 C = ⊥ := by
  have h' : GLAPPrimeCore 3 C = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h
  exact le_bot_iff.mp (h' ▸ aschbacherSolvableCore_le_GLAPPrimeCore C)

theorem exists_pow_eq_one_of_mem_center_of_GLAPPrimeCore {C : Type*} [Group C] [Finite C]
    (h : GLAPPrimeCore 3 C = ⊥) {g : C} (hg : g ∈ center C) : ∃ k : ℕ, g ^ 3 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  refine ⟨k, ?_⟩
  set h' := g ^ 3 ^ k with hh'
  have hh'm : h' ^ m = 1 := by
    rw [hh', ← pow_mul, ← hkm, pow_orderOf_eq_one]
  have hcen : h' ∈ center C := pow_mem hg _
  have hnorm : (zpowers h').Normal := by
    constructor
    intro n hn x
    have hnc : n ∈ center C := (zpowers_le.mpr hcen) hn
    rw [(Subgroup.mem_center_iff.mp hnc x), mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 3 (Nat.card (zpowers h')) := by
    rw [Nat.card_zpowers]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hm ?_
    exact h3.trans (orderOf_dvd_of_pow_eq_one hh'm)
  have hle : zpowers h' ≤ GLAPPrimeCore 3 C := le_sSup ⟨hnorm, hcop⟩
  rw [h] at hle
  exact (Subgroup.mem_bot.mp (hle (mem_zpowers h')))

theorem alphaNine_J3 :
    Census.Karpilovsky.Coordinator.Cover423.AlphaNine (Blueprint.NativeSporadic.Carrier .J3) := by
  intro D hD hD9
  have : Finite Blueprint.NativeSporadic.J3 := CFSG.Sporadic.J3.fam_j3_simplicity.1
  have : Finite (Blueprint.NativeSporadic.Carrier .J3) := CFSG.Sporadic.J3.fam_j3_simplicity.1
  have hJ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hO := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_J3 _ hJ
  have hNO := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.noOuterFixesCentralizer_J3 _ hJ
  have hZ : center (Blueprint.NativeSporadic.Carrier .J3) = ⊥ := Item426.center_J3_McL_ON.1
  have hOut : ∀ σ : MulAut (Blueprint.NativeSporadic.Carrier .J3), ∃ k : ℕ,
      σ ^ (2 ^ k) ∈ (MulAut.conj : Blueprint.NativeSporadic.Carrier .J3 →*
        MulAut (Blueprint.NativeSporadic.Carrier .J3)).range := by
    intro σ
    refine ⟨1, ?_⟩
    set x : CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Blueprint.NativeSporadic.Carrier .J3) := QuotientGroup.mk σ with hx
    have hc : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Blueprint.NativeSporadic.Carrier .J3)) ≤ 2 := card_outer_J3
    have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Blueprint.NativeSporadic.Carrier .J3)) := Nat.card_pos
    have hdvd : orderOf x ∣ 2 := by
      have h1 := orderOf_dvd_natCard x
      rcases (show Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (Blueprint.NativeSporadic.Carrier .J3)) = 1 ∨
          Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
            (Blueprint.NativeSporadic.Carrier .J3)) = 2 by omega) with h | h
      · rw [h] at h1
        exact h1.trans (one_dvd 2)
      · rwa [h] at h1
    have h2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [hx, ← QuotientGroup.mk_pow] at h2
    rw [pow_one]
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD9
    omega
  have hord : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (hD.2 b hb) hb1
  refine Res423Three.alphaVanishes_of_rigid hZ hD1
    (fun b hb hb1 => aschbacherSolvableCore_eq_bot_of_GLAPPrimeCoreOf (hO b (hord b hb hb1)))
    (fun b hb hb1 σ hσ hfix => ?_)
  have hb3 := hord b hb hb1
  refine Census.Karpilovsky.Proving.eq_one_of_fix_of_outer hZ hOut (centralizer ({b} : Set _))
    ?_ ?_ σ hσ hfix
  · intro g hg
    have hbC : b ∈ centralizer ({b} : Set (Blueprint.NativeSporadic.Carrier .J3)) :=
      mem_centralizer_singleton_iff.mpr rfl
    have hgC : g ∈ centralizer ({b} : Set (Blueprint.NativeSporadic.Carrier .J3)) :=
      mem_centralizer_singleton_iff.mpr (hg b hbC)
    have hcen : (⟨g, hgC⟩ : centralizer ({b} : Set (Blueprint.NativeSporadic.Carrier .J3))) ∈
        center (centralizer ({b} : Set (Blueprint.NativeSporadic.Carrier .J3))) := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hg c c.2).symm
    have hcore : GLAPPrimeCore 3 (centralizer ({b} : Set (Blueprint.NativeSporadic.Carrier .J3))) =
        ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp (hO b hb3)
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_center_of_GLAPPrimeCore hcore hcen
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro τ hτ2 hτo hall
    obtain ⟨t, ht1, ht2⟩ := hNO τ hτ2 hτo b hb3
    exact ht2 (hall t (mem_centralizer_singleton_iff.mpr ht1.symm))

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
