module

public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharAlmostSimple
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LargeExtraspecial.S14 (conjOuter ker_conjOuter)

section General

variable {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]

theorem card_map_conjOuter_mul_card_inf (hC : Subgroup.centralizer (K : Set Y) ≤ K)
    (E : Subgroup Y) :
    Nat.card (E.map (conjOuter K)) * Nat.card (K ⊓ E : Subgroup Y) = Nat.card E := by
  have h := Subgroup.relIndex_ker E (conjOuter K)
  rw [ker_conjOuter K hC] at h
  rw [← h]
  exact Subgroup.relIndex_mul_card K E

theorem le_of_coprime_card_outer (hC : Subgroup.centralizer (K : Set Y) ≤ K) {E : Subgroup Y}
    (h : Nat.Coprime (Nat.card E) (Nat.card (Outer K))) : E ≤ K := by
  have h1 : Nat.card (E.map (conjOuter K)) = 1 :=
    Nat.eq_one_of_dvd_coprimes h
      (Dvd.intro _ (card_map_conjOuter_mul_card_inf hC E))
      (Subgroup.card_subgroup_dvd_card _)
  intro x hx
  have hx' : conjOuter K x ∈ E.map (conjOuter K) := ⟨x, hx, rfl⟩
  rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hx'
  rw [← ker_conjOuter K hC]
  exact hx'

theorem false_of_cube {p : ℕ} [Fact p.Prime] (hC : Subgroup.centralizer (K : Set Y) ≤ K)
    (hK : RankLE1 p K) (hO : RankLE1 p (Outer K)) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 3) : False := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : Nat.card (E.map (conjOuter K)) ≤ p := hO _ (hE.map _)
  have h2 : Nat.card (K ⊓ E : Subgroup Y) ≤ p := by
    have := hK ((K ⊓ E).subgroupOf K) ((hE.mono inf_le_right).subgroupOf K)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ E ≤ K)).toEquiv] at this
  have h3 := Nat.mul_le_mul h1 h2
  rw [card_map_conjOuter_mul_card_inf hC E, hc] at h3
  nlinarith [Nat.mul_pos (by omega : 0 < p) (by omega : 0 < p)]

theorem false_of_cube_of_equiv {p : ℕ} [Fact p.Prime] {S : Type*} [Group S] (hS : RankLE1 p S)
    (hO : RankLE1 p (Outer S)) (hC : Subgroup.centralizer (K : Set Y) ≤ K) (e : K ≃* S)
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) : False :=
  false_of_cube hC (RankLE1.of_mulEquiv e.symm hS) (RankLE1.of_mulEquiv (equivalence e).symm hO)
    hE hc

end General

theorem rankLE1_of_isCyclic {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [IsCyclic G] :
    RankLE1 p G :=
  rankLE1_of_elemAbelian_cyclic hp fun _ _ => inferInstance

theorem rankLE1_of_no_plane {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (h : ∀ A : Subgroup G, IsElemAbelian p A → Nat.card A = p ^ 2 → False) : RankLE1 p G := by
  intro F hF
  by_contra hlt
  push Not at hlt
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h0 : Nat.card F ≠ 0 := by omega
  have : Finite F := Nat.finite_of_card_ne_zero h0
  obtain ⟨n, hn⟩ := hF.isPGroup.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [← hn, pow_one] at this
    omega
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p (n := 2)
    (by rw [hn]; exact pow_dvd_pow p hn2)
  exact h (A₀.map F.subtype) (hF.mono (Subgroup.map_subtype_le A₀))
    (by rw [Subgroup.card_map_of_injective F.subtype_injective, hA₀])

section Suzuki

theorem rankLE1_cat_suzuki {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    RankLE1 p (Cat ⟨.suzuki m, hv⟩) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := suzukiModel_cat hv
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : Cat ⟨.suzuki m, hv⟩ ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have : Finite (Cat ⟨.suzuki m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  refine rankLE1_of_elemAbelian_cyclic hp fun A hA => ?_
  obtain ⟨n, hn⟩ := hA.isPGroup.exists_card_eq
  have hodd : Odd (Nat.card A) := by
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic A
    hodd hA.1
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic a ha hF'
      e')

theorem kFactSeitzOuterCubeRankTwoAt_suzuki
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    KFactSeitzOuterCubeRankTwoAt ⟨.suzuki m, hv⟩ := by
  intro p _ hp2 Y _ _ K hKn hC he _ _ _ E hE hc
  have : K.Normal := hKn
  obtain ⟨e⟩ := he
  have : IsCyclic (Outer (Cat ⟨.suzuki m, hv⟩)) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 (2 * m + 1)
      (suzukiModel_cat hv)).1.1
  exact (false_of_cube_of_equiv (rankLE1_cat_suzuki hv Fact.out hp2) (rankLE1_of_isCyclic Fact.out)
    (hC.le.trans bot_le) e hE hc).elim

end Suzuki

section Ree


theorem kFactSeitzOuterCubeRankTwoAt_reeG2 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    KFactSeitzOuterCubeRankTwoAt ⟨.reeG2 m, hv⟩ := by
  intro p _ hp2 Y _ _ K hKn hC he hpd _ _ E hE hc
  have : K.Normal := hKn
  obtain ⟨e⟩ := he
  have hp : p.Prime := Fact.out
  have hp3 : 3 < p := by
    have h3 : p ≠ 3 := by simpa using hpd
    have := hp.two_le
    omega
  obtain ⟨X, _, _, _, hm1, hX, ⟨e'⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
      (K := Cat ⟨.reeG2 m, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have : IsCyclic (Outer (Cat ⟨.reeG2 m, hv⟩)) :=
    (MulEquiv.isCyclic (equivalence e')).2
      (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.isCyclic_outer_reeG2 hm1 hX)
  have hS : RankLE1 p (Cat ⟨.reeG2 m, hv⟩) :=
    rankLE1_of_no_plane fun F hF hFc => no_plane_cat_reeG2 hv hp hp3 F hF hFc
  exact (false_of_cube_of_equiv hS (rankLE1_of_isCyclic hp) (hC.le.trans bot_le) e hE hc).elim

end Ree

section Tits


theorem kFactSeitzOuterCubeRankTwoAt_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    KFactSeitzOuterCubeRankTwoAt ⟨.tits, hv⟩ := by
  intro p _ hp2 Y _ _ K hKn hC he _ _ hno E hE hc
  have : K.Normal := hKn
  obtain ⟨e⟩ := he
  have hOut : Nat.card (Outer K) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact (card_cat_tits_outer hv).2
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (Outer K)) := by
    rw [hc, hOut]
    exact Nat.Coprime.pow_left 3 ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  exact (hno ⟨E, le_of_coprime_card_outer (hC.le.trans bot_le) hcop, hE, hc⟩).elim

end Tits

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
