module

public import CFSG.GH74.Generic.S45.LEvenBender
public import CFSG.LocalAnalysis.SteinbergBTEvenHigherLinearFixedNoSL2
public import CFSG.LocalAnalysis.SteinbergBTEvenHigherUnitaryFixedNoSL2
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIEvenClassicalBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ClassicalGroups.UnitaryFlag

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {S : Type} [Group S]

theorem conj_inj_of_center_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut S => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem congr_conj {M : Type} [Group M] (Φ : S ≃* M) (s : S) :
    (MulAut.congr Φ) (MulAut.conj s) = MulAut.conj (Φ s) := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem even_apply {M : Type} [Group M] (hZ : Subgroup.center S = ⊥) (Φ : S ≃* M)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) :
    ∃ (L' : Subgroup (MulAut S)) (φ : ↥(inner S) ≃* M) (ρ : MulAut S →* MulAut M),
      CFSG.Assembly.IsComponentOf L' (inner S ⊓ Subgroup.centralizer ({ya} : Set (MulAut S))) ∧
      (∀ x : ↥L', orderOf x ≠ 4) ∧ 3 ∣ Nat.card ↥L' ∧ Nat.card ↥L' * 2 = q * (q ^ 2 - 1) ∧
      Function.Injective ρ ∧ (∀ w : ↥(inner S), ρ w = MulAut.conj (φ w)) ∧ Nonempty (↥Lb ≃* ↥L') := by
  obtain ⟨L', hL', ⟨e⟩⟩ := exists_component_conj hZ ya hQ.le hQ.sub hQ.simple hQ.nonab
  have hι : Function.Injective (MulAut.conj : S →* MulAut S) := conj_inj_of_center_bot hZ
  let eI : S ≃* ↥(inner S) := MonoidHom.ofInjective hι
  refine ⟨L', eI.symm.trans Φ, (MulAut.congr Φ).toMonoidHom, hL', ?_, ?_, ?_,
    (MulAut.congr Φ).injective, ?_, ⟨e⟩⟩
  · intro x hx4
    apply hQ.no4 (e.symm x : S) (e.symm x).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx4]
  · rw [← Nat.card_congr e.toEquiv]
    exact three_dvd_of_card hQ.card
  · rw [← Nat.card_congr e.toEquiv]
    exact hQ.card
  · intro w
    obtain ⟨s, rfl⟩ := eI.surjective w
    have h1 : ((eI s : ↥(inner S)) : MulAut S) = MulAut.conj s := rfl
    show (MulAut.congr Φ) ((eI s : ↥(inner S)) : MulAut S) = MulAut.conj ((eI.symm.trans Φ) (eI s))
    rw [h1, congr_conj]
    simp

theorem center_eq_bot_of_equiv {M : Type} [Group M] (hZ : Subgroup.center S = ⊥) (Φ : S ≃* M) :
    Subgroup.center M = ⊥ := by
  rw [← Subgroup.map_center_eq Φ, hZ, Subgroup.map_bot]

theorem finite_mulAut [Finite S] : Finite (MulAut S) :=
  Finite.of_injective (fun β : MulAut S => (β : S → S)) DFunLike.coe_injective

theorem orderOf_eq_two_of_qdata {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) :
    orderOf ya = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hQ.sq) hQ.ne


theorem linear_ge4_false [Finite S] {n e : ℕ} {K : Type} [Field K] (hn : 4 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (hZ : Subgroup.center S = ⊥) (Φ : S ≃* projectiveSL n K)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) : False := by
  obtain ⟨L', φ, ρ, hL', h4, -, -, hinj, hρW, -⟩ := even_apply hZ Φ hQ
  have : Finite (MulAut S) := finite_mulAut
  exact CFSG.LocalAnalysis.SteinbergBT.linear_fixed_false (orderOf_eq_two_of_qdata hQ) hL' hn he
    hK φ hinj hρW (center_eq_bot_of_equiv hZ Φ) h4

theorem unitary_ge4_false [Finite S] {e n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 e K) (hn : 4 ≤ n) (hZ : Subgroup.center S = ⊥)
    (Φ : S ≃* unitaryPSU h n) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) :
    False := by
  obtain ⟨L', φ, ρ, hL', h4, -, -, hinj, hρW, -⟩ := even_apply hZ Φ hQ
  have : Finite (MulAut S) := finite_mulAut
  exact CFSG.LocalAnalysis.SteinbergBT.unitary_fixed_false h hn (orderOf_eq_two_of_qdata hQ) hL' φ
    hinj hρW h4

theorem sp_false [Finite S] {r e : ℕ} {K : Type} [Field K]
    (hr : 2 ≤ r) (he : 1 ≤ e) (hre : ¬ (r = 2 ∧ e = 1)) (hK : Nat.card K = 2 ^ e)
    (hZ : Subgroup.center S = ⊥) (Φ : S ≃* StatedProj (StatedSp r K)) {ya : MulAut S}
    {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) : False := by
  obtain ⟨L', φ, ρ, hL', h4, h3, -, hinj, hρW, -⟩ := even_apply hZ Φ hQ
  have : Finite (MulAut S) := finite_mulAut
  exact CFSG.LocalAnalysis.SteinbergBT.sp_fixed_false (orderOf_eq_two_of_qdata hQ) hL' hr he hre hK
    φ hinj hρW (center_eq_bot_of_equiv hZ Φ) h4 h3


theorem centralizer_inner_bot (hZ : Subgroup.center S = ⊥) :
    Subgroup.centralizer ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  rw [Subgroup.mem_bot]
  ext v
  have h1 : MulAut.conj (φ v) = MulAut.conj v := by
    ext w
    have h2 := congrArg (fun ψ : MulAut S => ψ (φ.symm w)) (hφ (MulAut.conj v) ⟨v, rfl⟩)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h2
    simpa [MulAut.conj_apply] using h2.symm
  simpa using conj_inj_of_center_bot hZ h1

theorem assembly_subnormal_of_normal {A : Type*} [Group A] {L N C : Subgroup A}
    (hLN : CFSG.Assembly.IsSubnormal L N) (hNC : N ≤ C) (hn : (N.subgroupOf C).Normal) :
    CFSG.Assembly.IsSubnormal L C :=
  hLN.trans (.step hNC hn (.refl C))

theorem isComponentOf_centralizer {L' : Subgroup (MulAut S)} {ya : MulAut S}
    (hL' : CFSG.Assembly.IsComponentOf L' (inner S ⊓ Subgroup.centralizer ({ya} : Set (MulAut S)))) :
    CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({ya} : Set (MulAut S))) := by
  refine ⟨hL'.1.trans inf_le_right, ?_, hL'.2.2⟩
  refine assembly_subnormal_of_normal hL'.2.1 inf_le_right ?_
  rw [Subgroup.inf_subgroupOf_right]
  infer_instance


theorem false_of_card_dvd_168 {N q : ℕ} (hN : N ∣ 168) (hq5 : 5 ≤ q) (hq8 : q % 8 = 3 ∨ q % 8 = 5)
    (h : N * 2 = q * (q ^ 2 - 1)) : False := by
  have hN168 : N ≤ 168 := Nat.le_of_dvd (by norm_num) hN
  have hq7 : q ≤ 7 := by
    by_contra hgt
    push Not at hgt
    have h1 : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 8 * (8 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  interval_cases q
  · have : N = 60 := by norm_num at h; omega
    subst this
    norm_num at hN
  · omega
  · omega

theorem no_solution_40320 {q : ℕ} (h : q * (q ^ 2 - 1) = 40320) : False := by
  rcases lt_or_ge q 35 with hlt | hge
  · have h1 : q ^ 2 ≤ 34 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : q * (q ^ 2 - 1) ≤ 34 * (34 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  · have h1 : 35 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h2 : 35 * (35 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right h1 1)
    omega

theorem psl3_selector [Finite S] (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    {e : ℕ} {K : Type} [Field K] (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (hZ : Subgroup.center S = ⊥) (Φ : S ≃* projectiveSL 3 K) {ya : MulAut S} {Lb : Subgroup S}
    {q : ℕ} (hQ : QData S ya Lb q)
    (hWaltP : ∀ m : ℕ, 5 ≤ m → IsEmpty (projectiveSL 3 K ≃* alternatingGroup (Fin m))) :
    e = 2 ∧ q = 5 := by
  obtain ⟨L', φ, ρ, hL', h4, h3, hcard, hinj, hρW, ⟨eL⟩⟩ := even_apply hZ Φ hQ
  have : Finite (MulAut S) := finite_mulAut
  have hLc := isComponentOf_centralizer hL'
  have hLW : L' ≤ inner S := hL'.1.trans inf_le_left
  let eI : S ≃* ↥(inner S) := MonoidHom.ofInjective (conj_inj_of_center_bot hZ)
  have hWs : IsSimpleGroup ↥(inner S) := eI.symm.isSimpleGroup
  have hWnab : ∃ x y : ↥(inner S), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eI a, eI b, fun h => hab (eI.injective (by rw [map_mul, map_mul, h]))⟩
  have hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (↥(inner S) ≃* alternatingGroup (Fin m)) := fun m hm =>
    ⟨fun ε => (hWaltP m hm).false (φ.symm.trans ε)⟩
  obtain ⟨p, f, hp, hf, hpq, hLie⟩ := hQ.model (fun x => x = q) rfl
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    rw [hpq] at h2
    exact (Nat.not_even_iff_odd.2 hQ.odd) h2
  have hLstated : StatedClassicalModel ↥Lb .PSL 2 p f := LQ.stated_of_lieModel_PSL hLie
  have hL's : IsSimpleGroup ↥L' := by
    have : IsSimpleGroup ↥Lb := hQ.simple
    exact eL.symm.isSimpleGroup
  have hL'nab : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQ.nonab
    exact ⟨eL a, eL b, fun h => hab (eL.injective (by rw [map_mul, map_mul, h]))⟩
  have hcen : Subgroup.center ↥L' = ⊥ := center_eq_bot_of_simple_nonab hL's hL'nab
  let eq' : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥Lb :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans eL.symm
  have hsrc : StatedClassicalModel (↥L' ⧸ Subgroup.center ↥L') .PSL 2 p f ∨
      Nonempty (↥L' ⧸ Subgroup.center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥L' ⧸ Subgroup.center ↥L') .PSL 3 2 2 :=
    Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eq'.symm hLstated)
  obtain ⟨ρ', -, -, -, -, -, -, c, hrows⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector
      hWs hWnab (centralizer_inner_bot hZ) (orderOf_eq_two_of_qdata hQ) hLW hLc hp hp2 hf hsrc hWalt
      (n := 3) le_rfl (by omega) hK φ
  rcases hrows with ⟨σ, hrowsF, -⟩ | ⟨-, -, -, -, -, -, hrowsG⟩
  · rcases hrowsF with ⟨-, he2, hp7, hf1, -⟩ | ⟨-, he4, -, hL34, -⟩
    · exfalso
      have hq7 : q = 7 := by rw [← hpq, hp7, hf1]; norm_num
      have := hQ.mod8
      omega
    · exfalso
      have hcardL := (CFSG.Timmesfeld.card_statedClassicalModel_two hL34).1 rfl
      have h20160 : Nat.card ↥L' = 20160 := by
        rw [hcardL]
        decide +kernel
      apply no_solution_40320 (q := q)
      rw [← hcard, h20160]
  · rcases hrowsG with ⟨-, he2, hp5, hf1, -⟩ | ⟨hn5, -⟩
    · refine ⟨he2, ?_⟩
      rw [← hpq, hp5, hf1]
      norm_num
    · omega


open CFSG.ComponentClassification.OutcomeLocal (no_component_of_even_classical_model)

theorem psl3_outcome [Finite S] (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) {e : ℕ} (hstated : StatedClassicalModel S .PSL 3 2 e)
    (hZ : Subgroup.center S = ⊥) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) :
    e = 2 ∧ q = 5 := by
  obtain ⟨⟨-, he, hn, -, -⟩, K, hKf, hKfin, hK, ⟨eT⟩⟩ := id hstated
  let Φ : S ≃* projectiveSL 3 K :=
    eT.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  have hCharP : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two he hK
  by_cases he1 : e = 1
  · exfalso
    subst he1
    have hcardS := (CFSG.Timmesfeld.card_statedClassicalModel_two hstated).1 rfl
    have h168 : Nat.card S = 168 := by
      rw [hcardS]
      decide +kernel
    have hdvd : Nat.card ↥Lb ∣ 168 := h168 ▸ Subgroup.card_subgroup_dvd_card Lb
    exact false_of_card_dvd_168 hdvd hQ.q5 hQ.mod8 hQ.card
  · have he2 : 2 ≤ e := by omega
    by_cases he2' : e = 2
    · subst he2'
      refine psl3_selector hSs hSnab he2 hK hZ Φ hQ ?_
      intro m hm
      have hX : StatedClassicalModel (projectiveSL 3 K) .PSL 3 2 2 :=
        CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv Φ hstated
      exact (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated
        (projectiveSL 3 K) hX).2.2 (Fin m) (by simpa using hm)
    · refine psl3_selector hSs hSnab he2 hK hZ Φ hQ ?_
      intro m hm
      exact CFSG.QuasithinUnique.Id2519.projectiveSL_three_not_alternating (by omega) hK m hm


theorem classical_outcome [Finite S]
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) (hmodel : StatedClassicalModel S t n 2 f)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) :
    q = 5 ∧ ya ∉ inner S ∧ (StatedClassicalModel S .PSL 3 2 2 ∨ StatedClassicalModel S .PSU 3 2 2 ∨
      StatedClassicalModel S .PSL 2 2 4) := by
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hSs hSnab
  have hout : ya ∉ inner S := fun hin => false_of_inner_component hZ (fun u hu B =>
    no_component_of_even_classical_model (by tauto) hmodel u hu B) hQ hin
  rcases ht with rfl | rfl | rfl
  ·
    obtain ⟨⟨-, hf, hn, hne2, -⟩, K, hKf, hKfin, hK, ⟨eT⟩⟩ := id hmodel
    by_cases hn2 : n = 2
    · subst hn2
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1 : f = 1 := by omega
        subst hf1
        exact hne2 (by norm_num)
      obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hf2
        (Or.inl ⟨by decide, hmodel⟩)
      obtain ⟨hf4, hq5⟩ := l2even_outer hf2 e hQ hout
      subst hf4
      exact ⟨hq5, hout, Or.inr (Or.inr hmodel)⟩
    · by_cases hn3 : n = 3
      · subst hn3
        obtain ⟨hf2, hq5⟩ := psl3_outcome hSs hSnab hmodel hZ hQ
        subst hf2
        exact ⟨hq5, hout, Or.inl hmodel⟩
      · exfalso
        let Φ : S ≃* projectiveSL n K :=
          eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
            (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
        exact linear_ge4_false (by omega) hf hK hZ Φ hQ
  ·
    obtain ⟨⟨-, hf, hn, hq⟩, K, hKf, hKfin, hK, ⟨eT⟩⟩ := id hmodel
    have hUF : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    by_cases hn3 : n = 3
    · subst hn3
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1 : f = 1 := by omega
        subst hf1
        exact hq (by norm_num)
      obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hf2 (Or.inl ⟨by decide, hmodel⟩)
      have hmodel' : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
          CFSG.Models.benderPSU3Model_eq_psu3 f
      obtain ⟨hf2', hq5⟩ := u3even_outer hf2 (e.trans (MulEquiv.subgroupCongr hmodel'.symm)) hQ hout
      subst hf2'
      exact ⟨hq5, hout, Or.inr (Or.inl hmodel)⟩
    · exfalso
      let Φ : S ≃* unitaryPSU hUF n := eT.trans (unitaryPSUEquiv hUF (by omega)).symm
      exact unitary_ge4_false hUF (by omega) hZ Φ hQ
  ·
    obtain ⟨⟨-, hf, hn, hne⟩, K, hKf, hKfin, hK, ⟨eT⟩⟩ := id hmodel
    exfalso
    exact sp_false hn hf (fun ⟨h1, h2⟩ => hne (by rw [h1, h2]; norm_num)) hK hZ eT hQ

end CFSG.GH74.Generic.S45
