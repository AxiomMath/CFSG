module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup MulAction Equiv Equiv.Perm CFSG.Assembly.LowTwoRank
open scoped Pointwise



theorem exists_threeCycle_of_sylow {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : 3 ≤ Fintype.card Ω)
    (G : Subgroup (Perm Ω)) (P : Sylow 3 (Perm Ω)) (hP : (P : Subgroup (Perm Ω)) ≤ G) :
    ∃ g ∈ G, IsThreeCycle g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp (by omega : 2 < Fintype.card Ω)
  set c3 : Perm Ω := swap a b * swap a c with hc3
  have hcyc : IsThreeCycle c3 := isThreeCycle_swap_mul_swap_same hab hac hbc
  have hord : orderOf c3 = 3 := hcyc.orderOf
  have hpg : IsPGroup 3 (zpowers c3) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord]; norm_num
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm Ω) P Q
  have hc3Q : c3 ∈ (Q : Subgroup (Perm Ω)) := hQ (mem_zpowers c3)
  rw [← hg] at hc3Q
  rw [Sylow.smul_def] at hc3Q
  change c3 ∈ (MulAut.conj g • (P : Subgroup (Perm Ω))) at hc3Q
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hc3Q
  obtain ⟨s, hs, hsg⟩ := hc3Q
  refine ⟨s, hP hs, ?_⟩
  have hsc : s = g⁻¹ * c3 * g := by
    simp only [MulAut.smul_def, MulAut.conj_apply] at hsg
    rw [← hsg]; group
  rw [hsc]
  have : IsThreeCycle (g⁻¹ * c3 * g⁻¹⁻¹) := by
    unfold IsThreeCycle
    rw [cycleType_conj]
    exact hcyc
  simpa using this


theorem fac3 (a b : ℕ) (hb : ¬ 3 ∣ b) : (3 ^ a * b).factorization 3 = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero 3)
  rw [Nat.factorization_def _ Nat.prime_three, padicValNat.mul (pow_ne_zero a (by norm_num)) hb0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hb, add_zero]

theorem fac3_25920 : (25920 : ℕ).factorization 3 = 4 := by
  have e : (25920 : ℕ) = 3 ^ 4 * 320 := by norm_num
  rw [e]; exact fac3 4 320 (by norm_num)

theorem fac3_fact9 : (Nat.factorial 9).factorization 3 = 4 := by
  have e : Nat.factorial 9 = 3 ^ 4 * 4480 := by decide
  rw [e]; exact fac3 4 4480 (by norm_num)

theorem fac3_fact10 : (Nat.factorial 10).factorization 3 = 4 := by
  have e : Nat.factorial 10 = 3 ^ 4 * 44800 := by decide
  rw [e]; exact fac3 4 44800 (by norm_num)

theorem fac3_fact11 : (Nat.factorial 11).factorization 3 = 4 := by
  have e : Nat.factorial 11 = 3 ^ 4 * 492800 := by decide
  rw [e]; exact fac3 4 492800 (by norm_num)

theorem no_small_index_of_card_25920 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 25920) (M : Subgroup Y) (hM : M ≠ ⊤) : 11 < M.index := by
  classical
  obtain ⟨M1, hM1, hMM1⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  have hidx : M1.index ≤ M.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hMM1)
  suffices h : 11 < M1.index from lt_of_lt_of_le h hidx
  by_contra hle
  push Not at hle
  have hM1top : M1 ≠ ⊤ := hM1.1
  have hm1 : M1.index ≠ 1 := fun h => hM1top (Subgroup.index_eq_one.mp h)
  have hm0 : M1.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  let Ω := Y ⧸ M1
  have : Fintype Ω := Fintype.ofFinite Ω
  have hΩ' : Nat.card Ω = M1.index := rfl
  have hΩcard : Fintype.card Ω = M1.index := by rw [← hΩ', Nat.card_eq_fintype_card]
  have hnt : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hpre : IsPreprimitive Y Ω := by
    rw [← isCoatom_stabilizer_iff_preprimitive Y ((1 : Y) : Ω), MulAction.stabilizer_quotient]
    exact hM1
  let φ : Y →* Perm Ω := MulAction.toPermHom Y Ω
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker φ) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
      obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y a b
      have hyk : y ∈ MonoidHom.ker φ := h ▸ mem_top y
      have h1 : φ y = 1 := hyk
      have h2 : y • a = a := by
        have := congrArg (fun f : Perm Ω => f a) h1
        simpa [φ] using this
      exact hab (h2.symm.trans hy)
  let R : Subgroup (Perm Ω) := φ.range
  have hRcard : Nat.card R = 25920 := by
    rw [← hcard]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hprimR : IsPreprimitive R Ω := by
    have := hpre
    exact IsPreprimitive.of_surjective (M := Y) (N := R) (α := Ω) (β := Ω) (φ := φ.rangeRestrict)
      (f := ⟨id, fun y a => rfl⟩) Function.surjective_id
  have hdvd : 25920 ∣ (M1.index).factorial := by
    have h1 : Nat.card R ∣ Nat.card (Perm Ω) := Subgroup.card_subgroup_dvd_card R
    rw [hRcard, Nat.card_perm, hΩ'] at h1
    exact h1
  have hmain : 9 ≤ M1.index → False := by
    intro h9
    have hv : (Nat.factorial M1.index).factorization 3 = 4 := by
      generalize M1.index = m at hle h9
      interval_cases m
      · exact fac3_fact9
      · exact fac3_fact10
      · exact fac3_fact11
    obtain ⟨P⟩ : Nonempty (Sylow 3 R) := inferInstance
    have hPcard : Nat.card (P : Subgroup R) = 3 ^ 4 := by
      rw [P.card_eq_multiplicity, hRcard, fac3_25920]
    let P' : Subgroup (Perm Ω) := (P : Subgroup R).map R.subtype
    have hP'card : Nat.card P' = 3 ^ ((Nat.card (Perm Ω)).factorization 3) := by
      rw [Nat.card_perm, hΩ', hv]
      rw [Subgroup.card_map_of_injective R.subtype_injective, hPcard]
    let Q : Sylow 3 (Perm Ω) := Sylow.ofCard P' hP'card
    have hQle : (Q : Subgroup (Perm Ω)) ≤ R := Subgroup.map_subtype_le _
    obtain ⟨g, hg, h3⟩ := exists_threeCycle_of_sylow (by omega) R Q hQle
    have hA : alternatingGroup Ω ≤ R :=
      alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprimR h3 hg
    have hle2 : Nat.card (alternatingGroup Ω) ≤ 25920 := hRcard ▸ Subgroup.card_le_of_le hA
    have h2 : 2 * Nat.card (alternatingGroup Ω) = Nat.card (Perm Ω) := two_mul_nat_card_alternatingGroup
    rw [Nat.card_perm, hΩ'] at h2
    have : (Nat.factorial 9) ≤ Nat.factorial M1.index := Nat.factorial_le h9
    have h9' : Nat.factorial 9 = 362880 := by decide
    omega
  by_cases h9 : 9 ≤ M1.index
  · exact hmain h9
  · push Not at h9
    generalize M1.index = m at hdvd hm0 hm1 h9
    interval_cases m
    all_goals first | exact absurd rfl hm1 | exact absurd rfl hm0 | (revert hdvd; decide)


theorem minIndexU42 : MinIndexU42 := by
  intro Y _ hY M hM
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hY
  have hF3 : Nat.card F = 3 ^ 1 := hcard
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inr (Or.inl ⟨by simpa using hF3, le_refl 2⟩))
  have hY' : IsSimpleGroup Y := e.isSimpleGroup_congr.mpr hsimpleP
  have hfin : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hord : Nat.card Y = 25920 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.ClassicalInvolution.card_statedProj_statedSp_eq_ordBC Nat.prime_three (by norm_num) hcard
        (by norm_num)]
    decide
  exact no_small_index_of_card_25920 hord M hM

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
