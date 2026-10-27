module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256m

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple ambiguousChev)

section GF4Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.Assembly.LowTwoRank
open CFSG.StandardType.ChevTwo (blueprintLieModel_of_modelsLieModel untwistedChevalleyModel_of_bridge
  twistedChevalleyModel_of_bridge)

theorem even_exponent_of_card_eq_four_pow {q : PrimePower} (hp : q.p = 2) {k : ℕ} (hk : q.card = 4 ^ k) :
    Even q.exponent := by
  have hc := PrimePower.card_def q
  rw [hp] at hc
  have h1 : 2 ^ q.exponent = 2 ^ (2 * k) := by
    rw [← hc, hk, pow_mul]
    norm_num
  exact ⟨k, by have := Nat.pow_right_injective (le_refl 2) h1; omega⟩

theorem two_pow_odd_ne_four_pow {m k : ℕ} (h : 2 ^ (2 * m + 1) = 4 ^ k) : False := by
  have h1 : 2 ^ (2 * m + 1) = 2 ^ (2 * k) := by
    rw [h, pow_mul]
    norm_num
  have := Nat.pow_right_injective (le_refl 2) h1
  omega


theorem exists_lieModel_two_even_of_gf4 {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (hk : ∃ k : ℕ, 1 ≤ k ∧ Inputs256c.defField d.1 = 4 ^ k)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f ∧ Even f ∧
      ¬ (t = .PSL ∧ n = 2 ∧ f = 2) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨k, hk1, hkq⟩ := hk
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hdup := ((LieTypeIndex.valid_iff _).mp hv).2
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    refine ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h,
      even_exponent_of_card_eq_four_pow hp hq4, ?_⟩
    rintro ⟨-, hr1, he2⟩
    apply hdup
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    refine Or.inl ⟨by omega, Or.inl ?_⟩
    rw [PrimePower.card_def, hp, he2]
    norm_num
  | twistedA r q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent := by
      simp [ValidLieTypeIndex.fieldExponent]
    rw [hc, hfe] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h,
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h,
        even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h,
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h,
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.E6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e6 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.E7, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e7 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.E8, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e8 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.F4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.f4 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    exact ⟨.G2, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩, untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.twistedE6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    have hq4 : q.card = 4 ^ k := hkq
    exact ⟨.trialityD4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩),
      even_exponent_of_card_eq_four_pow hp hq4, by simp⟩
  | suzuki m => exact (two_pow_odd_ne_four_pow (m := m) hkq).elim
  | reeG2 m => exact absurd hd (by simp)
  | reeF4 a => exact (two_pow_odd_ne_four_pow (m := a) hkq).elim
  | tits =>
    exfalso
    have h2 : (2 : ℕ) = 4 ^ k := hkq
    have h4 : 4 ≤ 4 ^ k := Nat.le_self_pow (by omega) 4
    omega

end GF4Model

section Chev3

open CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank

theorem evenLieOrder_ne_three_sixty_of_even {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hf : Even f) : CFSG.SeitzReduction.F4Pilot.evenLieOrder t n f ≠ 360 := by
  have hf1 : 1 ≤ f := hadm.2.1
  have h45 : Odd 45 := by decide
  have hN : ∀ N : ℕ, f * N ≠ 3 := fun N h => by
    have h2 : Even (f * N) := hf.mul_right N
    rw [h] at h2
    exact absurd h2 (by decide)
  rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num]
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    show CFSG.Open.ordA (n - 1) (2 ^ f) ≠ _
    exact (CFSG.Timmesfeld.Orders.profile_ordA (n := n - 1) (by omega) hf1).ne_of_ne h45 (hN _)
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    show CFSG.Open.ordTwistedA (n - 1) (2 ^ f) ≠ _
    exact (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := n - 1) (by omega) hf1).ne_of_ne h45 (hN _)
  | PSp =>
    show CFSG.Open.ordBC n (2 ^ f) ≠ _
    exact (CFSG.Timmesfeld.Orders.profile_ordBC hf1).ne_of_ne h45 (hN _)
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordD n (2 ^ f) ≠ _
    exact (CFSG.Timmesfeld.Orders.profile_ordD (by omega) hf1).ne_of_ne h45 (hN _)
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordTwistedD n (2 ^ f) ≠ _
    exact (CFSG.Timmesfeld.Orders.profile_ordTwistedD (by omega) hf1).ne_of_ne h45 (hN _)
  | G2 => exact (CFSG.Timmesfeld.Orders.profile_ordG2 hf1).ne_of_ne h45 (hN _)
  | F4 => exact (CFSG.Timmesfeld.Orders.profile_ordF4 hf1).ne_of_ne h45 (hN _)
  | E6 => exact (CFSG.Timmesfeld.Orders.profile_ordE6 hf1).ne_of_ne h45 (hN _)
  | E7 => exact (CFSG.Timmesfeld.Orders.profile_ordE7 hf1).ne_of_ne h45 (hN _)
  | E8 => exact (CFSG.Timmesfeld.Orders.profile_ordE8 hf1).ne_of_ne h45 (hN _)
  | twistedE6 => exact (CFSG.Timmesfeld.Orders.profile_ordTwistedE6 hf1).ne_of_ne h45 (hN _)
  | trialityD4 => exact (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf1).ne_of_ne h45 (hN _)
  | twistedB2 => exact absurd hf (Nat.not_even_iff_odd.2 hadm.2.2.2.2.1)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 => exact absurd hf (Nat.not_even_iff_odd.2 hadm.2.2.2.2.1)
  | Tits => exact absurd hf (by rw [hadm.2.2.2.2]; decide)


theorem not_isChevSimple_three_of_lieModel_even {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hM : CFSG.Blueprint.LieModel X t n 2 f) (hf : Even f) (h22 : ¬ (t = .PSL ∧ n = 2 ∧ f = 2)) :
    ¬ IsChevSimple 3 X := by
  have hadm := CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hM
  intro h3
  rcases h3 with ⟨i, hi, ⟨e3⟩⟩ | ⟨i, hi, ⟨e3⟩⟩
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = 3 := hi
      have hodd := CFSG.LocalAnalysis.GLTheoremA.small_odd_lie Nat.prime_three (by norm_num) hd e3
      rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hM hodd with
        ⟨h1, h2, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
      · exact h22 ⟨h1, h2, h3⟩
      · exact absurd (h3 ▸ hf) (by decide)
      · exact absurd (h3 ▸ hf) (by decide)
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating m hm =>
      have hm6 : m = 6 := by
        rcases hi with ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · norm_num at h
        · norm_num at h
        · exact h
        · norm_num at h
      subst hm6
      have h360 : Nat.card X = 360 := by
        rw [Nat.card_congr e3.toEquiv]
        show Nat.card (alternatingGroup (Fin 6)) = 360
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        rfl
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at h360
      exact evenLieOrder_ne_three_sixty_of_even hadm hf h360
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      rcases CFSG.LocalAnalysis.GLTheoremA.small_amb_lie (r := 3) (by norm_num) hv hi with
        ⟨q, rfl, hq8, -⟩ | ⟨q, rfl, hq2, -⟩
      · obtain ⟨hp2, he3⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 3)
          Nat.prime_two (by norm_num) (hq8.trans (by norm_num))
        have hMq := CFSG.Models.lieModel_A 1 q hv e3
        rw [hp2, he3] at hMq
        have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
          (by simp [CFSG.Blueprint.classicalTags]) hMq
        have hc := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hB
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at hc
        obtain ⟨-, -, hf3⟩ := CFSG.SeitzReduction.RankOne.evenLieOrder_eq_ordA_one hadm (by norm_num) hc
        exact absurd (hf3 ▸ hf) (by decide)
      · obtain ⟨hp2, he1⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 1)
          Nat.prime_two (by norm_num) (hq2.trans (by norm_num))
        have hMq := CFSG.Models.lieModel_twistedA 3 q hv e3
        have hc2 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 2 := by
          simp [ValidLieTypeIndex.characteristic, hp2]
        have hf1 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 1 := by
          simp [ValidLieTypeIndex.fieldExponent, he1]
        rw [hc2, hf1] at hMq
        have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
          (by simp [CFSG.Blueprint.classicalTags]) hMq
        have hc := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hB
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at hc
        obtain ⟨-, -, hg1⟩ := CFSG.SeitzReduction.UnitaryPilot.evenLieOrder_eq_ordTwistedA (m := 4) (f := 1)
          hadm (by norm_num) le_rfl hc
        exact absurd (hg1 ▸ hf) (by decide)

theorem not_isChevSimple_three_of_isGF4Type {X : Type} [Group X] (h : IsGF4Type X) : ¬ IsChevSimple 3 X := by
  obtain ⟨d', hd2, hk, ⟨e⟩⟩ := h
  obtain ⟨t, n, f, hM, hf, h22⟩ := exists_lieModel_two_even_of_gf4 d' hd2 hk e
  exact not_isChevSimple_three_of_lieModel_even hM hf h22

end Chev3

section Linear

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem isGF4Comp_map {S T : Type} [Group S] [Group T] (e : S ≃* T) (β : MulAut S) {J : Subgroup S}
    (hJ : IsGF4Comp β J) : IsGF4Comp (MulAut.congr e β) (J.map (e : S →* T)) := by
  obtain ⟨hsn, hq, h3, ht⟩ := hJ
  set e₁ : J ≃* J.map (e : S →* T) := Subgroup.equivMapOfInjective J (e : S →* T) e.injective
  have e₂ : (J ⧸ Subgroup.center J) ≃* (J.map (e : S →* T) ⧸ Subgroup.center (J.map (e : S →* T))) :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  refine ⟨?_, hq.of_mulEquiv e₁.symm, ?_, ?_⟩
  · rw [Inputs256e.fixSubgroup_congr]
    exact hsn.map (e : S →* T)
  · rw [← Nat.card_congr e₂.toEquiv]
    exact h3
  · rcases ht with ⟨⟨f⟩⟩ | hg
    · exact Or.inl ⟨e₂.symm.trans f⟩
    · exact Or.inr (hg.of_mulEquiv e₂.symm)

theorem gf4Gen_of_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (β : MulAut S)
    (h : ∀ t : T, MulAut.congr e β t = t → (∃ n : ℕ, t ^ 2 ^ n = 1) →
      t ∈ ⨆ (J : Subgroup T) (_ : IsGF4Comp (MulAut.congr e β) J), J) :
    ∀ s : S, β s = s → (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ ⨆ (J : Subgroup S) (_ : IsGF4Comp β J), J := by
  intro s hs ⟨n, hn⟩
  have hfix : MulAut.congr e β (e s) = e s := by
    show e (β (e.symm (e s))) = e s
    rw [e.symm_apply_apply, hs]
  have hmem := h (e s) hfix ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hβ : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext x
    simp [MulAut.congr]
  have hle : (⨆ (J : Subgroup T) (_ : IsGF4Comp (MulAut.congr e β) J), J).map (e.symm : T →* S) ≤
      ⨆ (J : Subgroup S) (_ : IsGF4Comp β J), J := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hJ => ?_
    have h1 := isGF4Comp_map e.symm (MulAut.congr e β) hJ
    rw [hβ] at h1
    exact le_iSup₂_of_le (f := fun (J : Subgroup S) (_ : IsGF4Comp β J) => J) _ h1 le_rfl
  have := hle (Subgroup.mem_map_of_mem (e.symm : T →* S) hmem)
  simpa using this

theorem gf4Gen_of_centralQuotient {X T : Type} [Group X] [Finite X] [Group T] (π : X →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) (hcop : Nat.Coprime (Nat.card π.ker) 2)
    (α : MulAut X) (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.Open.IsQuasisimple (F i))
    (hFt : ∀ i, 3 ∣ Nat.card (F i ⧸ Subgroup.center (F i)) ∧
      (MovingAround.IsAltType 5 (F i ⧸ Subgroup.center (F i)) ∨ IsGF4Type (F i ⧸ Subgroup.center (F i))))
    (hgen : ∀ x ∈ fixSubgroup α, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ ⨆ i, F i) :
    ∀ s : T, β s = s → (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ ⨆ (J : Subgroup T) (_ : IsGF4Comp β J), J := by
  intro s hs ⟨n, hn⟩
  obtain ⟨x, hx, hxn⟩ := Inputs256e.exists_pow_lift π hπ hcop hn
  have hzk : x⁻¹ * α x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hx, hs, inv_mul_cancel]
  have hcomm : Commute x (α x) := by
    have hz : Commute x (x⁻¹ * α x) := Subgroup.mem_center_iff.1 (hker hzk) x
    have e : α x = x * (x⁻¹ * α x) := by group
    rw [e]
    exact (Commute.refl x).mul_right hz
  have hzq : (x⁻¹ * α x) ^ 2 ^ n = 1 := by
    rw [(hcomm.inv_left).mul_pow, inv_pow, hxn, ← map_pow, hxn, map_one, inv_one, one_mul]
  have hαx : α x = x := by
    have h1 := Inputs256e.eq_one_of_mem_of_coprime hcop hzk hzq
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hxF : x ∈ ⨆ i, F i := hgen x hαx ⟨n, hxn⟩
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  have hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπ
  have hFS : ∀ i, IsGF4Comp β ((F i).map π) := by
    intro i
    obtain ⟨hq, ⟨e⟩⟩ := Inputs256e.centralImage_facts π hker (hFq i)
    obtain ⟨h3, ht⟩ := hFt i
    refine ⟨IsSubnormal.step (Subgroup.map_mono (hFα i)) (Inputs256e.normal_map_subgroupOf_map π (hFn i))
      (IsSubnormal.step hNC hNn (IsSubnormal.refl _)), hq, ?_, ?_⟩
    · rw [← Nat.card_congr e.toEquiv]
      exact h3
    · rcases ht with ⟨⟨f⟩⟩ | hg
      · exact Or.inl ⟨e.symm.trans f⟩
      · exact Or.inr (hg.of_mulEquiv e.symm)
  have hle : (⨆ i, F i).map π ≤ ⨆ (J : Subgroup T) (_ : IsGF4Comp β J), J := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun i => le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : IsGF4Comp β J) => J) _
      (hFS i) le_rfl
  rw [← hx]
  exact hle (Subgroup.mem_map_of_mem π hxF)

theorem three_dvd_orderPSL_four_pow {j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m) :
    3 ∣ ((4 ^ j) ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, ((4 ^ j) ^ i - 1)) / m.gcd (4 ^ j - 1) := by
  have h3 : 3 ∣ 4 ^ j - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 j
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ?_ _
  rcases Nat.lt_or_ge m 3 with h | h
  · obtain rfl : m = 2 := by omega
    have hodd : Odd (4 ^ j - 1) := by
      have he : Even (4 ^ j) := (by decide : Even 4).pow_of_ne_zero (by omega)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) he odd_one
    have hg : Nat.gcd 2 (4 ^ j - 1) = 1 := Nat.coprime_two_left.mpr hodd
    rw [hg, one_mul, Finset.Icc_self, Finset.prod_singleton]
    exact h3.trans (Nat.sub_one_dvd_pow_sub_one _ 2)
  · have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 m := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      omega
    have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun i => (4 ^ j) ^ i - 1) h23
    rw [Finset.prod_pair (by norm_num)] at hprod
    refine (?_ : Nat.gcd m (4 ^ j - 1) * 3 ∣ ((4 ^ j) ^ 2 - 1) * ((4 ^ j) ^ 3 - 1)).trans hprod
    rw [mul_comm ((4 ^ j) ^ 2 - 1)]
    exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 3))
      (h3.trans (Nat.sub_one_dvd_pow_sub_one _ 2))

theorem sl_gf4_facts {E : Type} [Field E] [Finite E] {j : ℕ} (hj : 1 ≤ j) (hEc : Nat.card E = 4 ^ j)
    {m : ℕ} (hm : 2 ≤ m) {F : Type} [Group F] (e : Matrix.SpecialLinearGroup (Fin m) E ≃* F) :
    3 ∣ Nat.card (F ⧸ Subgroup.center F) ∧
      (MovingAround.IsAltType 5 (F ⧸ Subgroup.center F) ∨ IsGF4Type (F ⧸ Subgroup.center F)) := by
  have e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin m) E ≃* (F ⧸ Subgroup.center F) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr e₂.toEquiv,
      CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear E m (by omega), hEc]
    exact three_dvd_orderPSL_four_pow hj hm
  · by_cases h24 : m = 2 ∧ j = 1
    · obtain ⟨rfl, rfl⟩ := h24
      left
      haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hEc]; norm_num)
      have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) = 60 := by
        rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear E 2 (by norm_num), hEc]
        norm_num [Finset.Icc_self]
      obtain ⟨f⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard
      exact ⟨e₂.symm.trans f⟩
    · right
      obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
      let Q : TauCeti.PrimePower := ⟨2, 2 * j, Nat.prime_two, by omega⟩
      have hQc : Q.card = 4 ^ j := by
        rw [TauCeti.PrimePower.card_def]
        show 2 ^ (2 * j) = 4 ^ j
        rw [pow_mul]
        norm_num
      have h4j : 4 ≤ 4 ^ j := Nat.le_self_pow (by omega) 4
      have h4j' : ∀ c : ℕ, c < 4 → 4 ^ j ≠ c := fun c hc h => by omega
      have hodd : ∀ c : ℕ, Odd c → 4 ^ j ≠ c := fun c hc h => by
        have he : Even (4 ^ j) := (by decide : Even 4).pow_of_ne_zero (by omega)
        rw [h] at he
        exact (Nat.not_even_iff_odd.2 hc) he
      have hv : (TauCeti.LieTypeIndex.A r Q).Valid := by
        refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
        · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
          exact ⟨by omega, fun _ => hQc ▸ h4j⟩
        intro hdup
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
        simp only [hQc] at hdup
        revert hdup
        rintro (⟨hr, h4 | h5 | h9⟩ | ⟨-, h2⟩ | ⟨-, h2⟩)
        · apply h24
          refine ⟨by omega, ?_⟩
          have h1 : 4 ^ j = 4 ^ 1 := by rw [h4, pow_one]
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h1
        · exact hodd 5 (by decide) h5
        · exact hodd 9 (by decide) h9
        · exact h4j' 2 (by norm_num) h2
        · exact h4j' 2 (by norm_num) h2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hK : Nat.card E = 2 ^ (2 * j) := by
        rw [hEc, pow_mul]
        norm_num
      let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField E 2 (2 * j) (by omega) hK
      let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin (r + 1))
      haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
      let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r Q hv
      exact ⟨⟨TauCeti.LieTypeIndex.A r Q, hv⟩, TauCeti.LieTypeIndex.characteristic_A r Q, ⟨j, hj, hQc⟩,
        ⟨e₂.symm.trans (eP.trans eC.symm)⟩⟩

theorem exists_card_eq_four_pow_of_algebra {k E : Type} [Field k] [Finite k] [Field E] [Algebra k E]
    [Module.Finite k E] (hk4 : Nat.card k = 4) : ∃ j : ℕ, 1 ≤ j ∧ Nat.card E = 4 ^ j := by
  refine ⟨Module.finrank k E, ?_, by rw [Module.natCard_eq_pow_finrank (K := k), hk4]⟩
  by_contra h0
  have hc := Module.natCard_eq_pow_finrank (K := k) (V := E)
  rw [show Module.finrank k E = 0 by omega, pow_zero] at hc
  haveI : Finite E := Module.finite_of_finite k
  have := Finite.one_lt_card (α := E)
  omega

variable {k : Type} [Field k] [Finite k]

theorem mem_iSup_specialFactor_of_gf4 (hk : ringChar k = 2) (hk4 : Nat.card k = 4) {n : ℕ}
    {A : GL (Fin n) k} (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) {j : ℕ} (hg : g ^ 2 ^ j = 1) :
    (g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      ⨆ h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h},
        specialFactor A h.1.1 := by
  refine mem_iSup_specialFactor_of_blockDetHom_eq_one hsq g ?_
  have hu : blockDetHom hsq g ^ 2 ^ j = 1 := by rw [← map_pow, hg, map_one]
  refine Prod.ext (funext fun b => ?_) (funext fun b => ?_)
  · have : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    have : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
    have hchar : ringChar (AdjoinRoot (b : k[X])) = 2 := by
      rw [← Algebra.ringChar_eq k (AdjoinRoot (b : k[X])), hk]
    refine Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units Nat.prime_two hchar) (n := j) ?_
    have := congrArg (fun u => u.1 b) hu
    simp only [Prod.pow_fst, Pi.pow_apply, Prod.fst_one, Pi.one_apply] at this
    exact this
  · have : Fact (Irreducible (b.1 : k[X])) := ⟨irreducible_of_mem_primaryFactors b.1.2⟩
    have : Finite (AdjoinRoot (b.1 : k[X])) := Module.finite_of_finite k
    have hchar : ringChar (AdjoinRoot (b.1 : k[X])) = 2 := by
      rw [← Algebra.ringChar_eq k (AdjoinRoot (b.1 : k[X])), hk]
    have hle : primaryMultiplicity (glA A : Module.End k (Fin n → k)) (b.1 : k[X]) ≤ 1 := by
      have h4 : 4 ≤ Nat.card (AdjoinRoot (b.1 : k[X])) := by
        obtain ⟨i, hi, hc⟩ := exists_card_eq_four_pow_of_algebra (k := k) (E := AdjoinRoot (b.1 : k[X])) hk4
        rw [hc]
        exact Nat.le_self_pow (by omega) 4
      have hb := b.2
      unfold IsGoodFactor at hb
      omega
    haveI : Finite (blockGL (glA A : Module.End k (Fin n → k)) (b.1 : k[X])) :=
      Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h0 => by
        have := Inputs256e.coprime_card_gl_of_finrank_le_one (W := primaryComponent (glA A :
          Module.End k (Fin n → k)) (b.1 : k[X])) Nat.prime_two hchar hle
        rw [blockGL] at h0
        rw [h0] at this
        exact Nat.prime_two.one_lt.ne' (Nat.coprime_zero_left _ |>.1 this))).ne'
    refine Inputs256e.eq_one_of_coprime_card
      (Inputs256e.coprime_card_gl_of_finrank_le_one Nat.prime_two hchar hle) (n := j) ?_
    have := congrArg (fun u => u.2 b) hu
    simp only [Prod.pow_snd, Pi.pow_apply, Prod.snd_one, Pi.one_apply] at this
    exact this

theorem gf4Gen_conjAut (hk : ringChar k = 2) (hk4 : Nat.card k = 4) {n : ℕ} {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∀ s : LinearFlag.projectiveSL n k, LinearFlag.conjAut n k A s = s → (∃ m : ℕ, s ^ 2 ^ m = 1) →
      s ∈ ⨆ (J : Subgroup (LinearFlag.projectiveSL n k)) (_ : IsGF4Comp (LinearFlag.conjAut n k A) J), J := by
  have hpk : ((3 : ℕ) : k) ≠ 0 :=
    Inputs256e.natCast_ne_zero_of_ne Nat.prime_two Nat.prime_three (by norm_num) hk
  have hsq := squarefree_minpoly_glA hpk hA
  obtain ⟨hker, hcop⟩ := Inputs256e.proj_ker_facts (k := k) Nat.prime_two hk n
  refine gf4Gen_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) hker hcop
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => open_isQuasisimple (isQuasisimple_specialFactor hsq h.1.2 h.2)) (fun h => ?_)
    (fun x hx ⟨j, hj⟩ => mem_iSup_specialFactor_of_gf4 hk hk4 hsq ⟨x, hx⟩ (j := j) (Subtype.ext hj))
  have : Fact (Irreducible (h.1.1 : k[X])) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  have : Finite (AdjoinRoot (h.1.1 : k[X])) := Module.finite_of_finite k
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq h.1.2
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) (h.1.1 : k[X]) := by
    rcases h.2 with h3 | ⟨h2, -⟩ <;> omega
  obtain ⟨j, hj, hc⟩ := exists_card_eq_four_pow_of_algebra (k := k) (E := AdjoinRoot (h.1.1 : k[X])) hk4
  exact sl_gf4_facts hj hc hm e

theorem gf4Gen_projectiveSL (hk : ringChar k = 2) (hk4 : Nat.card k = 4) {n : ℕ} (hn : 3 ≤ n)
    (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : orderOf β = 3) :
    ∀ s : LinearFlag.projectiveSL n k, β s = s → (∃ m : ℕ, s ^ 2 ^ m = 1) →
      s ∈ ⨆ (J : Subgroup (LinearFlag.projectiveSL n k)) (_ : IsGF4Comp β J), J := by
  haveI : CharP k 2 := hk ▸ ringChar.charP k
  have hK : Nat.card k = 2 ^ 2 := by rw [hk4]; norm_num
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two
    (by norm_num : 1 ≤ 2) hn hK
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n k
  · have hrange : LinearFlag.linearAutGroup n k = (LinearFlag.conjAut n k).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ 3 ∈ (LinearFlag.conjAut n k).ker := by rw [MonoidHom.mem_ker, map_pow, hβ3]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact gf4Gen_conjAut hk hk4 hc.symm
  · exfalso
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn (by decide : Odd 3) hβ3
    have hmem : LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ ∈ LinearFlag.semilinearAutGroup n k :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup (LinearFlag.conjAut_mem_linearAutGroup A))
        (Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩))
    obtain ⟨h32, -⟩ := hdesc.2.2.2.2.2.2.2 3 Nat.prime_three (by norm_num) _ hmem hlin hβ
    norm_num at h32

theorem gf4CompsOn_linear :
    GF4CompsOn fun d => ∃ r : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .A r q ∧ q.card = 4 := by
  rintro S _ _ ⟨d, hv⟩ ⟨r, q, hdq, hq4⟩ ⟨eS⟩ β hβ
  simp only at hdq
  subst hdq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  have hr2 : 2 ≤ r := by
    have hs := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    rw [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hs
    by_contra h
    have hr1 : r = 1 := by have := hs.1.1; omega
    exact hs.2 (Or.inl ⟨hr1, Or.inl hq4⟩)
  let e : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    eS.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p, hp2]
  have hk4 : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2, he2]
    norm_num
  have hβ' : orderOf (MulAut.congr e β) = 3 := by
    rw [MulEquiv.orderOf_eq, hβ]
  exact gf4Gen_of_congr e β (gf4Gen_projectiveSL hchar hk4 (by omega) _ hβ')

end Linear

section Rest

@[expose] def Chev2GF4Rest : Prop :=
  Gen2313On (fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧ ¬ EvenScope d.1 ∧
    ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q) ∧
  GF4CompsOn (fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧
    (¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q) ∧ ¬ ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .A r q) ∧
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, IsSporType s S → ∀ α : MulAut S, α ^ 3 = 1 →
    ∀ I : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
      ¬ IsGF4Type (PSimple 3 I)

theorem chev2GF4_of_rest
    (h : Chev2GF4Rest) :
    Inputs256c.Chev2GF4 := by
  have hC : GF4CompsOn fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q := by
    refine (GF4CompsOn.or gf4CompsOn_linear h.2.1).mono fun d hd => ?_
    by_cases hA : ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .A r q
    · obtain ⟨r, q, hrq⟩ := hA
      have h4 : Inputs256c.defField d.1 = 4 := hd.2.1
      rw [hrq] at h4
      exact Or.inl ⟨r, q, hrq, h4⟩
    · exact Or.inr ⟨hd.1, hd.2.1, hd.2.2, hA⟩
  exact chev2GF4_of_pump h.1 hC fun _ _ hJ H _ _ hH _ hP =>
    good2319_of_pumpup_gf4 (CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds 3) (fun _ _ hX => not_isChevSimple_three_of_isGF4Type hX) h.2.2
      hJ H hH hP

end Rest

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m

end
