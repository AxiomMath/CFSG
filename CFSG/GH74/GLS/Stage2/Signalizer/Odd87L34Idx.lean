module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion

public section

open Subgroup MulAction Equiv Equiv.Perm

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem no_small_index_of_card_20160 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 20160)
    (hnA : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      IsEmpty (Y ≃* alternatingGroup Ω))
    (M : Subgroup Y) (hM : M ≠ ⊤) : 11 < M.index := by
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
  have hRcard : Nat.card R = 20160 := by
    rw [← hcard]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hprimR : IsPreprimitive R Ω := by
    have := hpre
    exact IsPreprimitive.of_surjective (M := Y) (N := R) (α := Ω) (β := Ω) (φ := φ.rangeRestrict)
      (f := ⟨id, fun y a => rfl⟩) Function.surjective_id
  have hdvd : 20160 ∣ (M1.index).factorial := by
    have h1 : Nat.card R ∣ Nat.card (Perm Ω) := Subgroup.card_subgroup_dvd_card R
    rw [hRcard, Nat.card_perm, hΩ'] at h1
    exact h1
  have hm8 : 8 ≤ M1.index := by
    by_contra h8
    push Not at h8
    generalize M1.index = m at hdvd hm0 hm1 h8
    interval_cases m
    all_goals first | exact absurd rfl hm1 | exact absurd rfl hm0 | (revert hdvd; decide)
  have hJordan : ∀ p : ℕ, p.Prime → p ∣ 20160 → 2 * p > M1.index → p + 3 ≤ M1.index →
      alternatingGroup Ω ≤ R := by
    intro p hp hpd hlarge hsmall
    have : Fact p.Prime := ⟨hp⟩
    have hd : p ∣ Nat.card R := by rw [hRcard]; exact hpd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := R) p hd
    have hg : orderOf (u : Perm Ω) = p := (Subgroup.orderOf_coe u).trans hu
    have hc : (u : Perm Ω).IsCycle := Equiv.Perm.isCycle_of_prime_order
      (by rw [hg]; exact hp) (by
        have hs' := Finset.card_le_univ (u : Perm Ω).support
        rw [hg]; omega)
    have hs : (u : Perm Ω).support.card = p := hc.orderOf.symm.trans hg
    exact CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
      hprimR hp (by rw [hΩ']; omega) hc hs u.property
  have hAle : alternatingGroup Ω ≤ R := by
    by_cases h10 : 10 ≤ M1.index
    · exact hJordan 7 (by decide) (by norm_num) (by omega) (by omega)
    · exact hJordan 5 (by decide) (by norm_num) (by omega) (by omega)
  have hle2 : Nat.card (alternatingGroup Ω) ≤ 20160 := hRcard ▸ Subgroup.card_le_of_le hAle
  have h2 : 2 * Nat.card (alternatingGroup Ω) = Nat.card (Perm Ω) := two_mul_nat_card_alternatingGroup
  rw [Nat.card_perm, hΩ'] at h2
  have hm8' : M1.index = 8 := by
    by_contra hne
    have h9 : 9 ≤ M1.index := by omega
    have : Nat.factorial 9 ≤ Nat.factorial M1.index := Nat.factorial_le h9
    have h9' : Nat.factorial 9 = 362880 := by decide
    omega
  have hAeq : alternatingGroup Ω = R := by
    apply Subgroup.eq_of_le_of_card_ge hAle
    rw [hRcard]
    rw [hm8'] at h2
    have h8' : Nat.factorial 8 = 40320 := by decide
    omega
  have hΩ8 : 5 ≤ Fintype.card Ω := by rw [hΩcard]; omega
  exact (hnA Ω hΩ8).false
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hAeq.symm))

theorem isSimpleGroup_of_lieModel_l34 {Y : Type} [Group Y] (h : CFSG.Blueprint.LieModel Y .PSL 3 2 2) :
    IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ (h.statedClassicalModel (by decide))).2

theorem minIndexL34 : MinIndexL34 := by
  intro Y _ _ hY M hM
  have hs := isSimpleGroup_of_lieModel_l34 hY
  obtain ⟨hcard, -, hnA⟩ := CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated Y
    (CFSG.GH74.Generic.stated_of_lieModel_PSL hY)
  exact no_small_index_of_card_20160 hcard (fun Ω _ _ h5 => hnA Ω h5) M hM

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
