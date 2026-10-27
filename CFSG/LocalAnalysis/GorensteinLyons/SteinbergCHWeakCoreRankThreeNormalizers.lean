module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBYDeltaWeakCore

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

namespace SteinbergCH

theorem le_pRank_of_relIndex_eq [Finite G] {p : ℕ} (hp : p.Prime) {E D : Subgroup G}
    (hE : IsElemAbelian p E) {k : ℕ} (hEk : k + 1 ≤ CFSG.Open.pRank p E) (hDE : D ≤ E)
    (hDidx : D.relIndex E = p) : k ≤ CFSG.Open.pRank p D := by
  have := Fact.mk hp
  have hp1 := hp.one_lt
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian' hE).exists_card_eq
  obtain ⟨E', hE'E, -, hE'card⟩ := CFSG.SectionRank.exists_pRank hp1 E
  have hrank : CFSG.Open.pRank p E ≤ n := by
    have h1 := card_le_of_le hE'E
    rw [hE'card, hn] at h1
    exact (Nat.pow_le_pow_iff_right hp1).mp h1
  have hDcard : Nat.card D = p ^ (n - 1) := by
    have h1 := relIndex_mul_card D E
    rw [inf_eq_left.mpr hDE, hDidx, hn] at h1
    have h2 : p ^ n = p * p ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have h1 := CFSG.SectionRank.le_pRank hp1 le_rfl (isElemAbelian_of_le_elem hDE hE) hDcard
  omega

theorem centralizer_singleton_le_normalizer_zpowers (f : G) :
    centralizer ({f} : Set G) ≤ normalizer (zpowers f : Set G) := by
  rw [← centralizer_closure, ← zpowers_eq_closure]
  exact centralizer_le_normalizer _

theorem rank_three_normalizer_intersection [Finite G] (hchar : IsCharacteristicPType G 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B W : Subgroup G} (hBel : IsElemAbelian p B)
    (hDW : ∀ D : Subgroup G, D ≤ B → 2 ≤ CFSG.Open.pRank p D → normalizer (D : Set G) ≤ W)
    {E U : Subgroup G} (hEB : E ≤ B) (hE3 : 3 ≤ CFSG.Open.pRank p E) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : E ≤ normalizer (U : Set G)) :
    E ≤ W ⊓ normalizer (U : Set G) ∧
      U ≤ CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ∧
      CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ≤
        CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ normalizer (U : Set G)) ∧
      CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ≠ ⊥ ∧
      IsCharacteristicP 2 (W ⊓ normalizer (U : Set G) : Subgroup G) ∧
      ∀ R : Subgroup G, R ≤ W → (R.subgroupOf W).Normal → Odd (Nat.card R) →
        R ⊓ (W ⊓ normalizer (U : Set G)) = ⊥ ∧ R ⊓ normalizer (U : Set G) = ⊥ := by
  classical
  have := Fact.mk Nat.prime_two
  have hp1 := hp.one_lt
  have hY : IsPLocal 2 (normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  have hEel : IsElemAbelian p E := isElemAbelian_of_le_elem hEB hBel
  have hEW : E ≤ W := le_normalizer.trans (hDW E hEB (by omega))
  have hEne : E ≠ ⊥ := by
    intro h
    obtain ⟨E', hE'E, -, hE'card⟩ := CFSG.SectionRank.exists_pRank hp1 E
    rw [h, le_bot_iff] at hE'E
    rw [hE'E, card_bot] at hE'card
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p E ≠ 0) hp1
    omega
  have hQW : CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ≤ W := by
    refine le_of_forall_hyperplane_centralizer_le hp hEel hEne
      (hEU.trans (le_normalizer_inSubgroup_pCore 2 _))
      (DeltaWeakCore.not_dvd_card_of_isPGroup_two hp hp2 (isPGroup_inSubgroup_pCore 2 _))
      fun D hDE hDidx => ?_
    have hD2 : 2 ≤ CFSG.Open.pRank p D := le_pRank_of_relIndex_eq hp hEel hE3 hDE hDidx
    exact inf_le_right.trans ((centralizer_le_normalizer _).trans (hDW D (hDE.trans hEB) hD2))
  obtain ⟨hle, hcharL⟩ := DeltaWeakCore.le_inSubgroup_pCore_and_isCharacteristicP (hchar _ hY)
    (inf_le_right : W ⊓ normalizer (U : Set G) ≤ _) (le_inf hQW (map_subtype_le _))
  refine ⟨le_inf hEW hEU, le_inSubgroup_pCore_of_normal le_normalizer normal_in_normalizer hU2,
    hle, inSubgroup_pCore_ne_bot_of_isPLocal hY, hcharL, fun R hRW hRn hRodd => ?_⟩
  have hRO : R ⊓ CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ normalizer (U : Set G)) = ⊥ := by
    obtain ⟨m, hm⟩ := (isPGroup_inSubgroup_pCore 2 (W ⊓ normalizer (U : Set G))).exists_card_eq
    refine (disjoint_of_coprime_natCard ?_).eq_bot
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hRodd)
  have hKC : R ⊓ (W ⊓ normalizer (U : Set G)) ≤
      centralizer (CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ normalizer (U : Set G)) : Set G) := by
    intro k hk
    obtain ⟨hkR, hkL⟩ := mem_inf.mp hk
    rw [mem_centralizer_iff]
    intro x hx
    have hxL : x ∈ W ⊓ normalizer (U : Set G) := map_subtype_le _ hx
    have h1 : k * x * k⁻¹ * x⁻¹ ∈ R := by
      have h2 : x * k⁻¹ * x⁻¹ ∈ R :=
        (normal_subgroupOf_iff hRW).mp hRn _ _ (inv_mem hkR) (mem_inf.mp hxL).1
      have h3 := mul_mem hkR h2
      rwa [← mul_assoc, ← mul_assoc] at h3
    have h2 : k * x * k⁻¹ * x⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ normalizer (U : Set G)) :=
      mul_mem ((mem_normalizer_iff.mp (le_normalizer_inSubgroup_pCore 2 _ hkL) x).mp hx)
        (inv_mem hx)
    have h3 : k * x * k⁻¹ * x⁻¹ ∈
        R ⊓ CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ normalizer (U : Set G)) := ⟨h1, h2⟩
    rw [hRO, mem_bot] at h3
    calc x * k = (k * x * k⁻¹ * x⁻¹)⁻¹ * (k * x) := by group
      _ = k * x := by rw [h3, inv_one, one_mul]
  have hKO := le_inSubgroup_pCore_of_le_centralizer hcharL inf_le_right hKC
  have hK : R ⊓ (W ⊓ normalizer (U : Set G)) = ⊥ :=
    eq_bot_iff.mpr fun k hk => by
      rw [← hRO]
      exact mem_inf.mpr ⟨(mem_inf.mp hk).1, hKO hk⟩
  refine ⟨hK, ?_⟩
  rw [← hK, ← inf_assoc, inf_of_le_left hRW]

end SteinbergCH

open SteinbergCH

theorem actual_weak_core_rank_three_normalizer_intersections [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) {B D₀ S₀ : Subgroup G}
    (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀ : IsElemAbelian p D₀)
    (hD₀card : Nat.card D₀ = p ^ 2) (hW : IsDeltaSeedWitness p B D₀ S₀) {S : Subgroup G}
    (hS : Maximal (· ∈ deltaSeededFamily p B S₀) S) {A H Q R : Subgroup G}
    (hA : A = B ⊓ centralizer (S : Set G)) (hH : H = normalizer (S : Set G))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) H) (hR : R = Q ⊓ centralizer (S : Set G))
    {F : Subgroup G → Subgroup G} (hF : ∀ D : Subgroup G, F D = Q ⊓ centralizer (D : Set G))
    {L : Set (Subgroup G)} (hL : L = {D | D ≤ A ∧ Nat.card D = p ∧ S < F D})
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalsContaining (H : Set G))
    (P : Sylow p G) (hBP : B ≤ (P : Subgroup G)) :
    (∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E → ∀ U : Subgroup G, U ≠ ⊥ →
      IsPGroup 2 U → E ≤ normalizer (U : Set G) →
      E ≤ GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G) ∧
      U ≤ CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ∧
      CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ≤
        CFSG.inSubgroup (CFSG.pCore 2)
          (GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G)) ∧
      CFSG.inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) ≠ ⊥ ∧
      IsCharacteristicP 2
        (GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G) : Subgroup G) ∧
      ∀ N : Subgroup G, N ≤ GLAWeakCore p (P : Subgroup G) →
        (N.subgroupOf (GLAWeakCore p (P : Subgroup G))).Normal → Odd (Nat.card N) →
        N ⊓ (GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G)) = ⊥ ∧
          N ⊓ normalizer (U : Set G) = ⊥) ∧
    ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E → ∀ f : G, orderOf f = 2 →
      E ≤ centralizer ({f} : Set G) → ∀ N : Subgroup G, N ≤ GLAWeakCore p (P : Subgroup G) →
        (N.subgroupOf (GLAWeakCore p (P : Subgroup G))).Normal → Odd (Nat.card N) →
        N ⊓ centralizer ({f} : Set G) = ⊥ := by
  have hpp : p.Prime := hp.1
  obtain ⟨-, -, -, hDW, -⟩ := delta_weak_core_contains_local_two_cores hnab hchar hp hfail hB
    hD₀B hD₀ hD₀card hW hS hA hH hQ hR hF hL hM P hBP
  have hmain := fun {E U : Subgroup G} (hEB : E ≤ B) (hE3 : 3 ≤ CFSG.Open.pRank p E)
      (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hEU : E ≤ normalizer (U : Set G)) =>
    rank_three_normalizer_intersection hchar hpp hp.2.1 hB.1 hDW hEB hE3 hU1 hU2 hEU
  refine ⟨fun E hEB hE3 U hU1 hU2 hEU => hmain hEB hE3 hU1 hU2 hEU, ?_⟩
  intro E hEB hE3 f hf hEf N hNW hNn hNodd
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hf
    exact absurd hf (by norm_num)
  have hU1 : zpowers f ≠ ⊥ := fun h => hf1 (zpowers_eq_bot.mp h)
  have hU2 : IsPGroup 2 (zpowers f) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hf, pow_one])
  have hCN := centralizer_singleton_le_normalizer_zpowers f
  have h1 := ((hmain hEB hE3 hU1 hU2 (hEf.trans hCN)).2.2.2.2.2 N hNW hNn hNodd).2
  exact le_bot_iff.mp (h1 ▸ inf_le_inf_left N hCN)

end CFSG.LocalAnalysis.GorensteinLyons
