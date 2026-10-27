module

public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.LocalAnalysis.GLTheoremB.Statements

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem le_glbCore_three_of_coprime_invariant {G : Type*} [Group G] [Finite G] {p n : ℕ}
    (hp : p.Prime) {B Y : Subgroup G} (hB : IsElemAbelian p B) (hcard : Nat.card B = p ^ n)
    (hn : 4 ≤ n) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ p ∣ Nat.card Y) :
    Y ≤ GLBCore p 3 B := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine (le_iSup_inf_centralizer_hyperplane hB hBY hY).trans
    (iSup₂_le fun K hK => inf_le_right.trans ?_)
  have hKB : K ≤ B := hK.1
  have hKcard : Nat.card K = p ^ k := card_eq_of_index_eq hp hKB hK.2 hcard
  have hKel : IsElemAbelian p K := isElemAbelian_mono hB hKB
  have h3 : 3 ≤ pRank p K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact (Subgroup.centralizer_le_normalizer _).trans
    (le_sSup ⟨K, hKB, h3, rfl⟩ : Subgroup.normalizer (K : Set G) ≤ GLBCore p 3 B)

theorem normalizer_le_glbCore_three {G : Type*} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    (h3 : 3 ≤ pRank p B) : Subgroup.normalizer (B : Set G) ≤ GLBCore p 3 B :=
  le_sSup ⟨B, le_rfl, h3, rfl⟩

theorem exists_glaIsMaxTwoLocal_ge {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsTwoLocal H) : ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧ H ≤ M := by
  obtain ⟨M, hHM, hM⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hH
  exact ⟨M, ⟨hM.1, fun K hK hMK => le_antisymm (hM.2 hK hMK) hMK⟩, hHM⟩

theorem theoremOne_iff : TheoremOne ↔ ∀ (G : Type) [Group G] [Finite G] (m p : ℕ),
    GLStanding G m p → ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M : Subgroup G,
      IsPreUniquenessTwoLocal p B M := by
  constructor
  · intro h G _ _ m p hS
    obtain ⟨hs, hnab, hK, hC, he, hm, hq, hp, hr, hd⟩ := hS
    obtain ⟨B, hB, M, hM1, hM2, hM3⟩ := h G hnab hK hC he m hm hq p hp hr hd
    exact ⟨B, hB, M, hM1, hM2, hM3⟩
  · intro h G _ _ _ hnab hK hC he m hm hq p hp hr hd
    obtain ⟨B, hB, M, hM⟩ := h G m p ⟨inferInstance, hnab, hK, hC, he, hm, hq, hp, hr, hd⟩
    exact ⟨B, hB, M, hM.1, hM.2.1, hM.2.2⟩

theorem exists_isBZeroMax_of_not_glaDeltaZero {G : Type*} [Group G] [Finite G] {p : ℕ}
    (h : ¬ GLADeltaZero G p) : ∃ B : Subgroup G, IsBZeroMax p B := by
  by_contra hno
  apply h
  unfold GLADeltaZero
  intro B hB D hDB hDel hDcard
  have hDpl : IsPPlane p D := ⟨hDel, hDcard⟩
  refine ⟨fun h5 => ?_, fun h3 => ?_⟩
  · by_contra hodd
    have hEven : Even (Nat.card (GLADelta p D)) := Nat.not_odd_iff_even.mp hodd
    have hBZ : IsBZeroMax p B :=
      ⟨hB, D, hDB, hDpl, fun _ => hEven, fun h3 => absurd h3 (by omega)⟩
    exact hno ⟨B, hBZ⟩
  · by_contra hodd
    have hEven : Even (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G)) :=
      Nat.not_odd_iff_even.mp hodd
    have hBZ : IsBZeroMax p B :=
      ⟨hB, D, hDB, hDpl, fun h => absurd h (by omega), fun _ => hEven⟩
    exact hno ⟨B, hBZ⟩

theorem commutator_glaDelta_le {G : Type*} [Group G] {p : ℕ} {B D : Subgroup G}
    (hB : IsElemAbelian p B) (hDB : D ≤ B) : ⁅GLADelta p D, B⁆ ≤ GLADelta p D := by
  have key : ∀ b ∈ B, ∀ x ∈ GLADelta p D, b * x * b⁻¹ ∈ GLADelta p D := by
    intro b hb x hx
    simp only [GLADelta, Subgroup.mem_iInf] at hx ⊢
    intro d hd hd1
    have hbC : b ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hb (hDB hd))
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_glaPPrimeCoreOf p _ hbC) x).mp (hx d hd hd1)
  refine Subgroup.commutator_le.mpr fun x hx b hb => ?_
  show x * b * x⁻¹ * b⁻¹ ∈ GLADelta p D
  have hcomm : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
  rw [hcomm]
  exact (GLADelta p D).mul_mem hx (key b hb x⁻¹ ((GLADelta p D).inv_mem hx))

theorem isBOneMax_of_isBZeroMax {G : Type*} [Group G] [Finite G] {p : ℕ} (hp3 : 3 ≤ p)
    {B : Subgroup G} (h : IsBZeroMax p B) : IsBOneMax p B := by
  obtain ⟨hB, D, hDB, hDpl, h3, h3'⟩ := h
  refine ⟨hB, D, hDB, hDpl, ?_⟩
  rcases Nat.lt_or_ge 3 p with hlt | hle
  · exact h3 hlt
  · have hp : p = 3 := by omega
    have hcomm : ⁅GLADelta p D, B⁆ ≤ GLADelta p D := commutator_glaDelta_le hB.1 hDB
    have hdvd : Nat.card (⁅GLADelta p D, B⁆ : Subgroup G) ∣ Nat.card (GLADelta p D) :=
      Subgroup.card_dvd_of_le hcomm
    exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp (h3' hp)).trans hdvd)

theorem glaPPrimeCoreOf_top_eq_bot {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {p : ℕ}
    (hp : p.Prime) (hpG : p ∣ Nat.card G) : GLAPPrimeCoreOf p (⊤ : Subgroup G) = ⊥ := by
  have key : ∀ N : Subgroup (⊤ : Subgroup G), N.Normal → Nat.Coprime p (Nat.card N) → N = ⊥ := by
    intro N hN hcop
    let f : (⊤ : Subgroup G) →* G := (⊤ : Subgroup G).subtype
    have hcardN : Nat.card (N.map f) = Nat.card N := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have hNG : (N.map f).Normal := by
      refine ⟨?_⟩
      rintro _ ⟨n, hn, rfl⟩ g
      exact ⟨⟨g, Subgroup.mem_top g⟩ * n * ⟨g, Subgroup.mem_top g⟩⁻¹,
        hN.conj_mem n hn _, rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
    · exact Subgroup.card_eq_one.mp (by rw [← hcardN, h, Subgroup.card_bot])
    · exfalso
      have hcG : Nat.Coprime p (Nat.card G) := by
        rw [← Subgroup.card_top (G := G), ← h, hcardN]
        exact hcop
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcG) hpG
  have hcore : GLAPPrimeCore p (⊤ : Subgroup G) = ⊥ :=
    le_bot_iff.mp (sSup_le fun N hN => le_of_eq (key N hN.1 hN.2))
  rw [GLAPPrimeCoreOf, hcore, Subgroup.map_bot]

theorem ne_top_of_even_card_glaPPrimeCoreOf {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} (hp : p.Prime) (hpG : p ∣ Nat.card G) {M : Subgroup G}
    (h : Even (Nat.card (GLAPPrimeCoreOf p M))) : M ≠ ⊤ := by
  intro hM
  rw [hM, glaPPrimeCoreOf_top_eq_bot hp hpG, Subgroup.card_bot] at h
  exact Nat.not_even_one h

theorem isTwoLocal_normalizer_pCoreOf_two {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (h : pCoreOf 2 M ≠ ⊥) : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) ∧
      M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨⟨pCoreOf 2 M, h, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M⟩

end CFSG.HardMathSupport.Solomon.Proving

end
