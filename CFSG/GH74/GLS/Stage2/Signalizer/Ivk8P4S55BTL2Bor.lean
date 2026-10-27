module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Par
public import CFSG.LieType.SteinbergBRPrimeLinearTwoSylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.L2V

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.OuterAutomorphisms

theorem perfect_eq_bot_of_le_normalizer {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (h : Blueprint.LieModel Y .PSL 2 p f) {W : Subgroup Y} (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W)
    {X : Subgroup Y} (hX : ⁅X, X⁆ = X) (hXW : X ≤ normalizer (W : Set Y)) : X = ⊥ := by
  classical
  obtain ⟨S, M, hMtop, hNM, hSM⟩ := Ivk8.l2_borelTitsConcl hp h W hW hWp
  obtain ⟨-, hf, -, -, -⟩ := ComponentClassification.AutL2Facts.lieModel_psl2_data h
  obtain ⟨K, _, hKfin, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := Ivk8.charP_of_card_eq_pow hp hf hcard
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  let φ : Y →* LinearFlag.projectiveSL 2 K := e.toMonoidHom
  have hbij : Function.Bijective φ := e.bijective
  let T : Sylow p (LinearFlag.projectiveSL 2 K) := Sylow.mapSurjective (f := φ) hbij.2 S
  have hT : (T : Subgroup (LinearFlag.projectiveSL 2 K)) = (S : Subgroup Y).map φ := rfl
  have hNT : normalizer ((T : Subgroup (LinearFlag.projectiveSL 2 K)) : Set _) ≤ M.map φ := by
    rw [hT, ← Subgroup.map_normalizer_eq_of_bijective _ hbij]
    exact Subgroup.map_mono hSM
  have hM'top : M.map φ ≠ ⊤ := by
    intro htop
    apply hMtop
    rw [eq_top_iff]
    intro y _
    have hy : φ y ∈ M.map φ := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmy⟩ := hy
    exact (hbij.1 hmy) ▸ hm
  obtain ⟨M₁, hM₁, hM'le⟩ := (eq_top_or_exists_le_coatom (M.map φ)).resolve_left hM'top
  have hmem : M₁ ∈ LinearFlag.maximalParabolics (LinearFlag.projectiveSL 2 K) p :=
    ⟨hM₁, _, ⟨T, rfl⟩, hNT.trans hM'le⟩
  rw [(LinearFlag.maximal_parabolics p (by norm_num : 1 ≤ 2)).1] at hmem
  obtain ⟨W₀, ⟨hW0, hWtop⟩, rfl⟩ := hmem
  have hlt : Module.finrank K W₀ < 2 := by
    have := Submodule.finrank_lt (hWtop.ne)
    rwa [Module.finrank_fin_fun] at this
  have hpos : Module.finrank K W₀ ≠ 0 := fun h0 => hW0.ne' (Submodule.finrank_eq_zero.mp h0)
  have hrank : Module.finrank K W₀ = 1 := by omega
  have hsol : Group.IsSolvable (LinearFlag.projStabilizer W₀) := by
    have := LieType.SteinbergBR.isSolvable_stabilizer_line hp hcard hrank
    exact Group.isSolvable_of_surjective ((LinearFlag.proj 2 K).subgroupMap_surjective _)
  have hle : X.map φ ≤ LinearFlag.projStabilizer W₀ :=
    (Subgroup.map_mono (hXW.trans hNM)).trans hM'le
  have : Group.IsSolvable (X.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hXφ : X.map φ = ⊥ :=
    LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable (by rw [← Subgroup.map_commutator, hX])
  exact (Subgroup.map_eq_bot_iff_of_injective X hbij.1).mp hXφ

theorem perfect_eq_bot_of_card_prime {Y : Type} [Group Y] {X : Subgroup Y} (hX : ⁅X, X⁆ = X)
    {r : ℕ} (hr : r.Prime) (hXr : Nat.card X = r) : X = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hXr]; exact hr.ne_zero)
  have hP : IsPGroup r ↥X := IsPGroup.of_card (n := 1) (by rw [hXr, pow_one])
  have : Group.IsNilpotent ↥X := hP.isNilpotent
  exact LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hX

theorem perfect_eq_bot_of_card_dvd_six {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}
    (hX : ⁅X, X⁆ = X) (h6 : Nat.card X ∣ 6) : X = ⊥ := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hle : Nat.card X ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases hc : Nat.card X
  · exact Subgroup.card_eq_one.mp hc
  · exact perfect_eq_bot_of_card_prime hX Nat.prime_two hc
  · exact perfect_eq_bot_of_card_prime hX Nat.prime_three hc
  · norm_num at h6
  · norm_num at h6
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hc]; norm_num)
    set N : Subgroup ↥X := zpowers x with hN
    have hNc : Nat.card N = 3 := by rw [hN, Nat.card_zpowers, hx]
    have hidx : N.index = 2 := by
      have e := N.card_mul_index
      rw [hNc, hc] at e
      omega
    have hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have : Group.IsNilpotent ↥N := (IsPGroup.of_card (p := 3) (n := 1)
      (by rw [hNc, pow_one])).isNilpotent
    have : Group.IsNilpotent (↥X ⧸ N) := (IsPGroup.of_card (p := 2) (n := 1)
      (by rw [← Subgroup.index, hidx, pow_one])).isNilpotent
    have : Group.IsSolvable ↥X := Group.isSolvable_of_ker_le_range N.subtype
      (QuotientGroup.mk' N) fun y hy => ⟨⟨y, by rwa [QuotientGroup.ker_mk'] at hy⟩, rfl⟩
    have h1 := LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hX
    rw [h1, Subgroup.card_bot] at hc
    omega

theorem perfect_eq_bot_of_sixty {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : Nat.card Y = 60) {W : Subgroup Y} (hW : W ≠ ⊥) (hW3 : IsPGroup 3 ↥W)
    {X : Subgroup Y} (hX : ⁅X, X⁆ = X) (hXW : X ≤ normalizer (W : Set Y)) : X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW3
  have hkd : 3 ^ k ∣ 60 := hk ▸ hY ▸ card_subgroup_dvd_card W
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hW (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    have hk2 : k < 2 := by
      by_contra h2
      have := (pow_dvd_pow 3 (not_lt.mp h2)).trans hkd
      norm_num at this
    omega
  subst hk1
  have hfac : (Nat.card Y).factorization 3 = 1 := by
    rw [hY, show (60 : ℕ) = 3 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let P : Sylow 3 Y := Sylow.ofCard W (by rw [hk, hfac])
  obtain ⟨n, hn⟩ : ∃ n, (normalizer (W : Set Y)).index = n := ⟨_, rfl⟩
  have hcardS : Nat.card (Sylow 3 Y) = n := (Sylow.card_eq_index_normalizer P).trans hn
  have hmod : n % 3 = 1 % 3 := hcardS ▸ card_sylow_modEq_one 3 Y
  have hWidx : W.index = 20 := by
    have e := W.card_mul_index
    rw [hk, hY] at e
    omega
  have hndvd : n ∣ 20 := hn ▸ hWidx ▸ Subgroup.index_dvd_of_le le_normalizer
  have hn1 : n ≠ 1 := by
    rintro rfl
    have htop : normalizer (W : Set Y) = ⊤ := Subgroup.index_eq_one.mp hn
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW h
    · rw [h, card_top, hY] at hk
      norm_num at hk
  have hn4 : n ≠ 4 := by
    rintro rfl
    have hcore := (normalizer (W : Set Y)).index_normalCore_dvd_factorial_index
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalizer (W : Set Y)).normalCore with h | h
    · rw [h, index_bot, hY, hn] at hcore
      norm_num [Nat.factorial] at hcore
    · have htop : normalizer (W : Set Y) = ⊤ := top_le_iff.mp (h ▸ normalCore_le _)
      rw [htop, index_top] at hn
      omega
  have hn10 : n = 10 := by
    have hn20 : n ≤ 20 := Nat.le_of_dvd (by norm_num) hndvd
    interval_cases n <;> omega
  have hN6 : Nat.card (normalizer (W : Set Y)) = 6 := by
    have e := (normalizer (W : Set Y)).card_mul_index
    rw [hn, hn10, hY] at e
    omega
  exact perfect_eq_bot_of_card_dvd_six hX (hN6 ▸ Subgroup.card_dvd_of_le hXW)

theorem mem_inner_of_pow_three {Y : Type} [Group Y] (hO : Nat.card (Outer Y) ∣ 2)
    {α : MulAut Y} (h3 : α ^ 3 = 1) : α ∈ inner Y := by
  have h1 : ((α : Outer Y)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
  have h2 : ((α : Outer Y)) ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := hO
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  have h : ((α : Outer Y)) = 1 := by
    calc ((α : Outer Y)) = ((α : Outer Y)) ^ 3 * (((α : Outer Y)) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h1, h2, inv_one, mul_one]
  exact (QuotientGroup.eq_one_iff (N := inner Y) α).mp h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.L2V
