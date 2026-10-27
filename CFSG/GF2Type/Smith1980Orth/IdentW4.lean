module

public import CFSG.GF2Type.Smith1980Orth.Ident
public import CFSG.GF2Type.Smith1980Orth.TriD4Rank
public import CFSG.LargeExtraspecial.S10Iso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open CFSG.Blueprint Module

private theorem omegaOdd_two_true : omegaOdd true 2 = 9 := by decide

private theorem omegaOdd_two_false : omegaOdd false 2 = 15 := by decide

private theorem psl_numeric_two {n e i : ℕ} {b : Bool} (hn : 3 ≤ n) (he : e ≤ 1)
    (hi : i % 4 = 3)
    (h : 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) =
      2 ^ ((2 + 1) * (2 + 2) + e) * (3 * omegaOdd b 2 * i)) : False := by
  obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj (odd_prod_two_pow_sub_one n)
    (odd_three_mul_omegaOdd_mul b (by norm_num) hi) h
  have hev : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  rw [Nat.even_iff] at hev
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · interval_cases n <;> omega
  · have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul h6 (by omega)
    omega

private theorem pomega_numeric_two {n e i : ℕ} {b b' : Bool} (hn : 4 ≤ n) (he : e ≤ 1)
    (hi : i % 4 = 3)
    (h : 2 ^ (n * (n - 1)) * omegaOdd b' n =
      2 ^ ((2 + 1) * (2 + 2) + e) * (3 * omegaOdd b 2 * i)) :
    n = 4 ∧ e = 0 ∧ b' = b := by
  obtain ⟨hexp, hU⟩ := two_pow_mul_odd_inj (odd_omegaOdd b' (by omega))
    (odd_three_mul_omegaOdd_mul b (by norm_num) hi) h
  have hn4 : n = 4 := by
    by_contra hne
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  subst hn4
  refine ⟨rfl, by omega, ?_⟩
  have h1 : omegaOdd true 4 = 42525 := by decide
  have h2 : omegaOdd false 4 = 48195 := by decide
  cases b <;> cases b'
  · rfl
  · exfalso
    rw [h1, omegaOdd_two_false] at hU
    omega
  · exfalso
    rw [h2, omegaOdd_two_true] at hU
    omega
  · rfl

private theorem not_card_of_not_dvd {c y e : ℕ} (hc : c = 2 ^ ((2 + 1) * (2 + 2) + e) * y)
    (hnd : ¬ 2 ^ 12 ∣ c) : False := by
  refine hnd ?_
  rw [hc]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) y

private theorem outcome_orthogonal_two {G : Type} [Group G] [Finite G] (hFI : DW.DW2FieldInput)
    {D : Set G} (hD : DW.IsTransClass34 D) (hOut : Timmesfeld.Outcome G) {e i : ℕ} (b : Bool)
    (he : e ≤ 1) (hi : i % 4 = 3)
    (hcard : Nat.card G = 2 ^ ((2 + 1) * (2 + 2) + e) * (3 * omegaOdd b 2 * i)) :
    ((b = true → LieModel G .POmegaPlus 4 2 1) ∧ (b = false → LieModel G .POmegaMinus 4 2 1)) ∨
      (b = true ∧ e = 0 ∧ LieModel G .trialityD4 0 2 1) := by
  have hodd : Odd (3 * omegaOdd b 2 * i) := odd_three_mul_omegaOdd_mul b (by norm_num) hi
  rcases hOut with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    exfalso
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSL n f (by omega) (Or.inl ⟨rfl, hn⟩) h D hD
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).1 rfl, ordA_two (by omega)] at hcard
    exact psl_numeric_two hn he hi hcard
  ·
    exfalso
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSp n f (by omega) (Or.inr (Or.inl ⟨rfl, hn⟩)) h D hD
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at hcard
    obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordBC (n := n) (le_refl 1)).two
    rw [hr'] at hcard
    have := (two_pow_mul_odd_inj hr hodd hcard).1
    exact psp_numeric (m := 2) (n := n) he (by omega)
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaPlus n f (by omega) (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩))) h D
        hD).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl, ordD_two (by omega)] at hcard
    obtain ⟨rfl, -, rfl⟩ := pomega_numeric_two (by omega) he hi hcard
    exact Or.inl ⟨fun _ => h, fun hb => by simp at hb⟩
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaMinus n f (by omega) (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩))) h D
        hD).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl,
      ordTwistedD_two (by omega)] at hcard
    obtain ⟨rfl, -, rfl⟩ := pomega_numeric_two (by omega) he hi hcard
    exact Or.inl ⟨fun hb => by simp at hb, fun _ => h⟩
  ·
    exact (hFI G .G2 0 f hf (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))) h D hD).elim
  ·
    have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain rfl : f = 1 := by
      by_contra hne
      refine hFI G t 0 f (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))) h D hD
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      tauto
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel hct h
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have hm' : Nat.card G = ordTrialityD4 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      have hval : ordTrialityD4 (2 ^ 1) = 2 ^ 12 * 51597 := by decide
      rw [hm', hval] at hcard
      obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (by decide : Odd 51597) hodd hcard
      cases b
      · exfalso
        rw [omegaOdd_two_false] at h2
        omega
      · exact Or.inr ⟨rfl, by omega, h⟩
    ·
      exfalso
      have hm' : Nat.card G = ordF4 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordF4 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      omega
    ·
      exfalso
      have hm' : Nat.card G = ordE6 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      omega
    ·
      exfalso
      have hm' : Nat.card G = ordTwistedE6 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordTwistedE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      omega
    ·
      exfalso
      have hm' : Nat.card G = ordE7 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE7 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      omega
    ·
      exfalso
      have hm' : Nat.card G = ordE8 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE8 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      omega
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have h6048 : Nat.card G = 6048 := by
      rw [Nat.card_congr e'.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
        Nat.prime_three le_rfl hK (by norm_num)]
      decide
    exact not_card_of_not_dvd (h6048.symm.trans hcard) (by norm_num)
  ·
    exfalso
    obtain ⟨e'⟩ := h
    have h360 : Nat.card G = 360 := by
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    exact not_card_of_not_dvd (h360.symm.trans hcard) (by norm_num)
  ·
    exfalso
    obtain ⟨e'⟩ := h
    have hJ : Nat.card G = 604800 := (Nat.card_congr e'.toEquiv).trans Sporadic.J2.card_J2
    exact not_card_of_not_dvd (hJ.symm.trans hcard) (by norm_num)

private theorem perm_cube : ∀ σ : Equiv.Perm (Fin 3), σ ^ 27 = 1 → σ ^ 3 = 1 := by
  decide +kernel

private theorem perm_comm :
    ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ ^ 3 = 1 → σ * τ = τ * σ := by
  decide +kernel

private theorem gm_cube : ∀ γ : S10.Gm, γ ^ 27 = 1 → γ ^ 3 = 1 := by
  decide +kernel

private theorem gm_comm : ∀ γ δ : S10.Gm, γ ^ 3 = 1 → δ ^ 3 = 1 → γ * δ = δ * γ := by
  decide +kernel

private theorem triple_cube_comm (a b : Equiv.Perm (Fin 3) × S10.Gm) (ha : a ^ 27 = 1)
    (hb : b ^ 27 = 1) : a ^ 3 = 1 ∧ a * b = b * a := by
  have ha1 : a.1 ^ 27 = 1 := by simpa using congrArg Prod.fst ha
  have ha2 : a.2 ^ 27 = 1 := by simpa using congrArg Prod.snd ha
  have hb1 : b.1 ^ 27 = 1 := by simpa using congrArg Prod.fst hb
  have hb2 : b.2 ^ 27 = 1 := by simpa using congrArg Prod.snd hb
  have ha1' := perm_cube a.1 ha1
  have ha2' := gm_cube a.2 ha2
  have hb1' := perm_cube b.1 hb1
  have hb2' := gm_cube b.2 hb2
  exact ⟨Prod.ext (by simpa using ha1') (by simpa using ha2'),
    Prod.ext (perm_comm _ _ ha1' hb1') (gm_comm _ _ ha2' hb2')⟩

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem exists_commutative_exponent_three (O : OrthData S) (hw : S.width = 4)
    (hp : timmesfeldPlusType O.q) (hfac : (Nat.card G).factorization 2 = 12) :
    ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      Nat.card E = 27 := by
  have hm2 : S.width / 2 = 2 := by omega
  obtain ⟨e⟩ : Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega O.q) := by
    rcases O.iso with h | h
    · exact h
    · exfalso
      have h13 := O.factorization_card.2 h
      rw [hfac, hm2] at h13
      omega
  have hQ := O.polarBilin_nondegenerate
  have h4 : finrank (ZMod 2) (Fin S.width → ZMod 2) = 4 := by rw [O.finrank_eq]; omega
  have hP : S10.PlusType4 O.q := by
    obtain ⟨W, hW, hWs⟩ := hp
    exact ⟨W, by omega, hWs⟩
  obtain ⟨φ, hφ⟩ := S10.exists_isometry_M2 h4 hQ hP
  have hrange := S10.range_psi hφ hQ
  let e₂ : S10.Gm ≃* timmesfeldOmega O.q :=
    (MonoidHom.ofInjective (S10.psi_injective (φ := φ))).trans
      (MulEquiv.subgroupCongr (hrange.trans (S7.timmesfeldOmega_eq O.q hQ).symm))
  have hΩ36 : Nat.card (timmesfeldOmega O.q) = 36 := by
    rw [← Nat.card_congr e₂.toEquiv]
    exact S10.card_Gm
  have hcardM : Nat.card S.M = 2 ^ 12 * 3 ^ 3 := by
    have h := (O.card_M).1 ⟨e⟩
    rw [hΩ36, hw] at h
    exact h.trans (by norm_num)
  let Ψ : S.Mbar ≃* Equiv.Perm (Fin 3) × S10.Gm :=
    e.trans (MulEquiv.prodCongr (MulEquiv.refl _) e₂.symm)
  let π : S.M →* Equiv.Perm (Fin 3) × S10.Gm :=
    Ψ.toMonoidHom.comp (S.ρ.rangeRestrict : S.M →* S.Mbar)
  have hker : ∀ x : S.M, π x = 1 → x ∈ S.Q := by
    intro x hx
    have h1 : (S.ρ.rangeRestrict : S.M →* S.Mbar) x = 1 := (Ψ.map_eq_one_iff).1 hx
    exact S.mem_Q_of_ρ_eq_one (congrArg Subtype.val h1)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 S.M))
  have h3 : (Nat.card S.M).factorization 3 = 3 := by
    rw [hcardM, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hT27 : Nat.card (T : Subgroup S.M) = 27 := by
    have h := Sylow.card_eq_multiplicity T
    rw [h3] at h
    exact h.trans (by norm_num)
  have hdisj : Disjoint (T : Subgroup S.M) S.Q :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ T.isPGroup' S.extraspecial.1
  have hTinj : ∀ a ∈ (T : Subgroup S.M), ∀ b ∈ (T : Subgroup S.M), π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ (T : Subgroup S.M) := mul_mem (inv_mem ha) hb
    have h2 : a⁻¹ * b ∈ S.Q := hker _ (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    exact inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hdisj h1 h2)
  have h27 : ∀ a ∈ (T : Subgroup S.M), a ^ 27 = 1 := by
    intro a ha
    have h := pow_card_eq_one' (G := (T : Subgroup S.M)) (x := ⟨a, ha⟩)
    rw [hT27] at h
    simpa using congrArg Subtype.val h
  have hπ27 : ∀ a ∈ (T : Subgroup S.M), π a ^ 27 = 1 := fun a ha => by
    rw [← map_pow, h27 a ha, map_one]
  have hcube : ∀ a ∈ (T : Subgroup S.M), a ^ 3 = 1 := fun a ha => by
    refine hTinj _ (pow_mem ha 3) 1 (one_mem _) ?_
    rw [map_pow, map_one]
    exact (triple_cube_comm (π a) (π a) (hπ27 a ha) (hπ27 a ha)).1
  have hcomm : ∀ a ∈ (T : Subgroup S.M), ∀ b ∈ (T : Subgroup S.M), a * b = b * a := by
    intro a ha b hb
    refine hTinj _ (mul_mem ha hb) _ (mul_mem hb ha) ?_
    rw [map_mul, map_mul]
    exact (triple_cube_comm (π a) (π b) (hπ27 a ha) (hπ27 b hb)).2
  refine ⟨(T : Subgroup S.M).map S.M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa using congrArg Subtype.val (hcomm a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg Subtype.val (hcube a ha)
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective S.M), hT27]

theorem identW4Input : IdentW4Input := by
  intro G _ _ _ S O hw hD hnd hidx
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  have hOut := Timmesfeld.outcome (S14.hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩)
  have hD34 := isTransClass34_of_threeFourPlusClass hD
  have hm2 : S.width / 2 = 2 := by omega
  by_cases hp : timmesfeldPlusType O.q
  · obtain ⟨e, i, he, hi, hcard⟩ := O.card_G_eq hidx true (iff_of_true rfl hp)
    rw [hm2] at hcard
    rcases outcome_orthogonal_two DW.dw2FieldInput hD34 hOut true he hi hcard with
      ⟨h1, -⟩ | ⟨-, he0, hT⟩
    · exact ⟨fun _ => h1 rfl, fun h => absurd hp h⟩
    · exfalso
      subst he0
      have hfac : (Nat.card G).factorization 2 = 12 := by
        rw [hcard]
        exact S14.factorization_two_pow_mul_odd
          (odd_three_mul_omegaOdd_mul true (by norm_num) hi)
      obtain ⟨E, hcomm, h3, hE⟩ := exists_commutative_exponent_three O hw hp hfac
      exact not_lieModel_trialityD4_of_elementary E hcomm h3 hE hT
  · obtain ⟨e, i, he, hi, hcard⟩ := O.card_G_eq hidx false (iff_of_false (by simp) hp)
    rw [hm2] at hcard
    rcases outcome_orthogonal_two DW.dw2FieldInput hD34 hOut false he hi hcard with
      ⟨-, h2⟩ | ⟨h, -, -⟩
    · exact ⟨fun h => absurd h hp, fun _ => h2 rfl⟩
    · exact absurd h (by simp)

end CFSG.GF2Type.Smith1980Orth
