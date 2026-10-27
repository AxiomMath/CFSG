module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapCT
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e8PilotSwapUniqueNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

theorem ordE8_sq_eq (x : ℕ) (hx : 1 ≤ x) :
    ordE8 (x ^ 2) = ordE8 x * (x ^ 120 * (x ^ 30 + 1) * (x ^ 24 + 1) * (x ^ 20 + 1) *
      (x ^ 18 + 1) * (x ^ 14 + 1) * (x ^ 12 + 1) * (x ^ 8 + 1) * (x ^ 2 + 1)) := by
  have h : ∀ k, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ hx
  have h' : ∀ k, 1 ≤ (x ^ 2) ^ k := fun k => Nat.one_le_pow _ _ (h 2)
  unfold ordE8
  zify [h 30, h 24, h 20, h 18, h 14, h 12, h 8, h 2, h' 30, h' 24, h' 20, h' 18, h' 14, h' 12,
    h' 8, h' 2]
  ring

theorem not_sq_ordE8_dvd_ordE8_sq {e : ℕ} (he : 1 ≤ e) :
    ¬ ordE8 (2 ^ e) ^ 2 ∣ ordE8 ((2 ^ e) ^ 2) := by
  intro h
  set x := 2 ^ e with hxdef
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  set R := x ^ 120 * (x ^ 30 + 1) * (x ^ 24 + 1) * (x ^ 20 + 1) * (x ^ 18 + 1) * (x ^ 14 + 1) *
    (x ^ 12 + 1) * (x ^ 8 + 1) * (x ^ 2 + 1) with hRdef
  rw [ordE8_sq_eq x hx1, sq] at h
  have hpos : 0 < ordE8 x := by
    have hk : ∀ k, 0 < k → 1 ≤ x ^ k - 1 := fun k hk => by
      have : 2 ≤ x ^ k := le_trans hx2 (Nat.le_self_pow (by omega) x)
      omega
    unfold ordE8
    have := hk 30 (by norm_num)
    have := hk 24 (by norm_num)
    have := hk 20 (by norm_num)
    have := hk 18 (by norm_num)
    have := hk 14 (by norm_num)
    have := hk 12 (by norm_num)
    have := hk 8 (by norm_num)
    have := hk 2 (by norm_num)
    positivity
  have hdvd : ordE8 x ∣ R := Nat.dvd_of_mul_dvd_mul_left hpos h
  have hx3 : ((x : ℕ) : ZMod 3) ^ 2 = 1 := by
    rw [hxdef, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul]
    have : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide
    rw [this, one_pow]
  have h3 : 3 ∣ ordE8 x := by
    have hsq : 3 ∣ x ^ 2 - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx1), Nat.cast_pow,
        Nat.cast_one, hx3, sub_self]
    unfold ordE8
    exact Dvd.dvd.mul_left hsq _
  have hR : ¬ 3 ∣ R := by
    rw [← ZMod.natCast_eq_zero_iff, hRdef]
    have hp : ∀ k : ℕ, ((x : ℕ) : ZMod 3) ^ (2 * k) = 1 := fun k => by
      rw [pow_mul, hx3, one_pow]
    push_cast
    rw [show (120 : ℕ) = 2 * 60 by norm_num, show (30 : ℕ) = 2 * 15 by norm_num,
      show (24 : ℕ) = 2 * 12 by norm_num, show (20 : ℕ) = 2 * 10 by norm_num,
      show (18 : ℕ) = 2 * 9 by norm_num, show (14 : ℕ) = 2 * 7 by norm_num,
      show (12 : ℕ) = 2 * 6 by norm_num, show (8 : ℕ) = 2 * 4 by norm_num, hp, hp, hp, hp, hp, hp,
      hp, hp, hx3]
    decide
  exact hR (h3.trans hdvd)

theorem pow_dvd_ordE8 (q : ℕ) : q ^ 120 ∣ ordE8 q := by
  unfold ordE8
  simp only [mul_assoc]
  exact Dvd.intro _ rfl

section Standard


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inf_eq_bot_of_le_centralizer_E8 {M₁ M₂ : Subgroup G} {K₁ : Type} [Field K₁]
    (e₁ : M₁ ≃* adjointGroup .E8 K₁) (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) : M₁ ⊓ M₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hcen : (⟨x, (mem_inf.1 hx).1⟩ : M₁) ∈ center M₁ := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext ((mem_centralizer_iff.1 (h₁₂ (mem_inf.1 hx).2)) y y.2)
  have h1 : e₁ ⟨x, (mem_inf.1 hx).1⟩ ∈ center (adjointGroup .E8 K₁) :=
    (MulEquivClass.apply_mem_center_iff e₁).2 hcen
  rw [center_adjointGroup_eq_bot_field, mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact mem_bot.2 (congrArg Subtype.val h1)

theorem inf_centralizer_eq_of_swap_E8 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M₁ M₂ : Subgroup G} {K₁ : Type}
    [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f) (e₁ : M₁ ≃* adjointGroup .E8 K₁)
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) :
    (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₁
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨φ, hφinj, hφ⟩ := F4Pilot.exists_injective_eq_range_of_swap h₁₂
    (inf_eq_bot_of_le_centralizer_E8 e₁ h₁₂) ht2 hswap
  have hOut := isSolvable_outer_of_mulEquiv_E8 e
  have : Group.IsPerfect (adjointGroup .E8 K₁) := CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 K₁
  have hrange : (φ.comp e₁.symm.toMonoidHom).range = φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e₁.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e₁ x, by simp⟩
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [← hrange]
    exact F4Pilot.commutator_monoidHom_range_eq_of_isPerfect _
  rw [hφ]
  refine Subgroup.eq_of_le_of_card_ge
    (std_perfect_le hset hOut htC ht hperf (hφ ▸ inf_le_right)) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr e₁.toEquiv,
    Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK, hK₁]

theorem exists_le_inf_centralizer_of_inner_E8 {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {f : ℕ} {K₁ : Type} [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f) (eM : M ≃* adjointGroup .E8 K₁)
    (hin : ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹) :
    ∃ X : Subgroup G, X ≤ M ⊓ centralizer ({t} : Set G) ∧ 2 ^ (72 * f) ∣ Nat.card X := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₁
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₁
  obtain ⟨m₀, hm₀M, hm₀⟩ := hin
  obtain ⟨w, hwM, hw2, hwC⟩ := E6Pilot.exists_involution_centralizer_le_of_inner_of_center_eq_bot
    ht eM (center_adjointGroup_eq_bot_field _ K₁)
    (E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E8) (Pi.single (0 : Fin 8) 1)) hm₀M hm₀
  have hw' : orderOf (eM ⟨w, hwM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
  set φ : adjointGroup .E8 K₁ →* G := M.subtype.comp eM.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := M.subtype_injective.comp eM.symm.injective
  have hφw : φ (eM ⟨w, hwM⟩) = w := by simp [hφ]
  refine ⟨(centralizer ({eM ⟨w, hwM⟩} : Set (adjointGroup .E8 K₁))).map φ, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine mem_inf.2 ⟨(eM.symm p).2, ?_⟩
    have hpw := mem_centralizer_singleton_iff.1 hp
    have hpw' : φ p * w = w * φ p := by
      rw [← hφw, ← map_mul, ← map_mul, hpw]
    exact mem_centralizer_singleton_iff.2 (hwC _ (eM.symm p).2 hpw')
  · rw [card_map_of_injective hφinj]
    exact two_pow_dvd_card_centralizer_E8 hK₁ hw'

theorem perfect_card_inf_centralizer_of_outer_E8 {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    {f : ℕ} (hf : 1 ≤ f) {K₁ : Type} [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f)
    (eM : M ≃* adjointGroup .E8 K₁) (htM : t ∈ normalizer (M : Set G))
    (hout : ¬ ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹) :
    ∃ e' : ℕ, 1 ≤ e' ∧ f = 2 * e' ∧
      ⁅M ⊓ centralizer ({t} : Set G), M ⊓ centralizer ({t} : Set G)⁆ =
        M ⊓ centralizer ({t} : Set G) ∧
      Nat.card (M ⊓ centralizer ({t} : Set G) : Subgroup G) = ordE8 (2 ^ e') := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₁
  set β : MulAut M := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  set α : MulAut (adjointGroup .E8 K₁) := (eM.symm.trans β).trans eM with hαdef
  have hα2 : α ^ 2 = 1 := (F4Pilot.pow_two_conj_eq_one_iff eM β).2
    (E6Pilot.normalizerMonoidHom_sq_eq_one_of_orderOf ht htM)
  have hβo : β ∉ (MulAut.conj : M →* MulAut M).range := by
    rintro ⟨m, hm⟩
    refine hout ⟨m, m.2, fun x hx => ?_⟩
    have h := congrArg (fun γ : MulAut M => ((γ ⟨x, hx⟩ : M) : G)) hm
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hαo : α ∉ (MulAut.conj : adjointGroup .E8 K₁ →* MulAut (adjointGroup .E8 K₁)).range :=
    fun h => hβo ((F4Pilot.conj_mem_range_conj_iff eM β).1 h)
  obtain ⟨-, Θ, -, -, hker, hinv⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form
    hf K₁ hK₁ .E8 (Or.inr rfl)
  have hΘ1 : Θ α ≠ 1 := fun h1 => hαo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨e', he'⟩, hσc⟩ := (hinv α hα2).resolve_left hΘ1
  have hfe : f = 2 * e' := by omega
  have he1 : 1 ≤ e' := by omega
  have hK₁' : Nat.card K₁ = 2 ^ (2 * e') := by rw [hK₁, hfe]
  have hσ : ∀ c, Θ α c = c ^ 2 ^ e' := fun c => by rw [hσc, show f / 2 = e' by omega]
  obtain ⟨ψ₀, hψ₀⟩ :=
    exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inr rfl) he1 K₁ hK₁' (Θ α) hσ hα2 hαo
  set φM : adjointGroup .E8 K₁ →* G := M.subtype.comp eM.symm.toMonoidHom with hφM
  have hφinj : Function.Injective φM := M.subtype_injective.comp eM.symm.injective
  have hCM : M ⊓ centralizer ({t} : Set G) = (E6Pilot.fixSubgroup α).map φM :=
    E6Pilot.inf_centralizer_eq_map_fixSubgroup eM htM
  have hfix : (E6Pilot.fixSubgroup (entrywiseAdjointAut .E8 (Θ α))).map ψ₀⁻¹.toMonoidHom =
      E6Pilot.fixSubgroup α := by
    rw [E6Pilot.map_fixSubgroup_conj, ← hψ₀]
    congr 1
    group
  obtain ⟨hperf, hcard⟩ := fixSubgroup_entrywiseAdjointAut_facts_E8 he1 hK₁' (Θ α) hσ
  refine ⟨e', he1, hfe, ?_, ?_⟩
  · rw [hCM, ← map_commutator, ← hfix, ← map_commutator, hperf]
  · rw [hCM, card_map_of_injective hφinj, ← hfix, card_map_of_injective ψ₀⁻¹.injective, hcard]

theorem swap_and_inf_centralizer_eq_of_mem_normalizer_E8 (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {M₁ M₂ : Subgroup G} {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (hK₁ : Nat.card K₁ = 2 ^ f) (hK₂ : Nat.card K₂ = 2 ^ f)
    (e₁ : M₁ ≃* adjointGroup .E8 K₁) (e₂ : M₂ ≃* adjointGroup .E8 K₂)
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (htM : t ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) :
    M₁.map (MulAut.conj t).toMonoidHom = M₂ ∧ (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₁
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hs₁ : IsSimpleGroup M₁ := by
    have := isSimpleGroup_adjointGroup_E8 K₁
    exact e₁.isSimpleGroup
  have hs₂ : IsSimpleGroup M₂ := by
    have := isSimpleGroup_adjointGroup_E8 K₂
    exact e₂.isSimpleGroup
  have hna₁ := exists_mul_ne_mul_of_mulEquiv_adjointGroup_E8 e₁
  have hna₂ := exists_mul_ne_mul_of_mulEquiv_adjointGroup_E8 e₂
  have h₂₁ : M₁ ≤ centralizer (M₂ : Set G) := le_centralizer_iff.1 h₁₂
  rcases F4Pilot.map_conj_eq_or_eq_of_isSimpleGroup h₁₂ hs₁ hs₂ hna₁ htM with h | h
  · exfalso
    have htM₁ : t ∈ normalizer (M₁ : Set G) := F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 h
    have htM' : t ∈ normalizer ((M₂ ⊔ M₁ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact htM
    have htM₂ : t ∈ normalizer (M₂ : Set G) := by
      rcases F4Pilot.map_conj_eq_or_eq_of_isSimpleGroup h₂₁ hs₂ hs₁ hna₂ htM' with h' | h'
      · exact F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 h'
      · exact absurd (F4Pilot.map_conj_toMonoidHom_inj.1 (h.trans h'.symm))
          (F4Pilot.ne_of_le_centralizer_of_exists_ne h₁₂ hna₁)
    have hdisj := inf_eq_bot_of_le_centralizer_E8 e₁ h₁₂
    have key : ∀ {M : Subgroup G} {K' : Type} [Field K'], Nat.card K' = 2 ^ f →
        (M ≃* adjointGroup .E8 K') → t ∈ normalizer (M : Set G) →
        ∃ X : Subgroup G, X ≤ M ⊓ centralizer ({t} : Set G) ∧ 2 ^ (60 * f) ∣ Nat.card X ∧
          ((2 ^ (72 * f) ∣ Nat.card X) ∨
            (∃ e', f = 2 * e' ∧ 1 ≤ e' ∧ ⁅X, X⁆ = X ∧ Nat.card X = ordE8 (2 ^ e'))) := by
      intro M K' _ hK' eM htMM
      by_cases hin : ∃ m ∈ M, ∀ x ∈ M, t * x * t⁻¹ = m * x * m⁻¹
      · obtain ⟨X, hX, hXc⟩ := exists_le_inf_centralizer_of_inner_E8 ht hK' eM hin
        exact ⟨X, hX, (pow_dvd_pow 2 (by omega)).trans hXc, .inl hXc⟩
      · obtain ⟨e', he1, hfe, hperf, hcard⟩ :=
          perfect_card_inf_centralizer_of_outer_E8 ht hf hK' eM htMM hin
        refine ⟨M ⊓ centralizer ({t} : Set G), le_rfl, ?_, .inr ⟨e', hfe, he1, hperf, hcard⟩⟩
        rw [hcard, hfe, show 60 * (2 * e') = e' * 120 by ring, pow_mul]
        exact pow_dvd_ordE8 _
    obtain ⟨X₁, hX₁, hX₁60, hX₁'⟩ := key hK₁ e₁ htM₁
    obtain ⟨X₂, hX₂, hX₂60, hX₂'⟩ := key hK₂ e₂ htM₂
    have hX₁M : X₁ ≤ M₁ := hX₁.trans inf_le_left
    have hX₂M : X₂ ≤ M₂ := hX₂.trans inf_le_left
    have h12 : X₂ ≤ centralizer (X₁ : Set G) := fun y hy =>
      (Subgroup.centralizer_le fun x hx => hX₁M hx) (h₁₂ (hX₂M hy))
    have hd12 : X₁ ⊓ X₂ = ⊥ := le_bot_iff.1 ((inf_le_inf hX₁M hX₂M).trans hdisj.le)
    have hcard12 := F4Pilot.card_sup_eq_mul_of_le_centralizer h12 hd12
    have hXt : X₁ ⊔ X₂ ≤ centralizer ({t} : Set G) :=
      sup_le (hX₁.trans inf_le_right) (hX₂.trans inf_le_right)
    have hb := factorization_card_le_of_le_centralizer_E8 hset.standard hK e ht hKt hXt
    have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
    have hpos : Nat.card (X₁ ⊔ X₂ : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    have hbig : ∀ a b : ℕ, 2 ^ a ∣ Nat.card X₁ → 2 ^ b ∣ Nat.card X₂ →
        a + b ≤ 120 * f + 1 + f.factorization 2 := by
      intro a b ha hb'
      have hdvd : 2 ^ (a + b) ∣ Nat.card (X₁ ⊔ X₂ : Subgroup G) := by
        rw [hcard12, pow_add]
        exact mul_dvd_mul ha hb'
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 hdvd
      omega
    rcases hX₁' with h1 | ⟨e₁', hfe₁, he₁, hperf₁, hcard₁⟩
    · have := hbig _ _ h1 hX₂60
      omega
    rcases hX₂' with h2 | ⟨e₂', hfe₂, -, hperf₂, hcard₂⟩
    · have := hbig _ _ hX₁60 h2
      omega
    have hee : e₂' = e₁' := by omega
    rw [hee] at hcard₂
    have hOut := isSolvable_outer_of_mulEquiv_E8 e
    have hPL : X₁ ⊔ X₂ ≤ L := std_perfect_le hset hOut htC ht
      (F4Pilot.commutator_sup_eq_sup_of_perfect hperf₁ hperf₂) hXt
    have hdvd := Subgroup.card_dvd_of_le hPL
    rw [hcard12, hcard₁, hcard₂, Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK, hfe₁,
      show (2 : ℕ) ^ (2 * e₁') = (2 ^ e₁') ^ 2 by rw [← pow_mul, mul_comm], ← sq] at hdvd
    exact not_sq_ordE8_dvd_ordE8_sq he₁ hdvd
  · exact ⟨h, inf_centralizer_eq_of_swap_E8 hset hK e htC ht hK₁ e₁ h₁₂ h⟩

end Standard

section Step3


variable {K : Type} [Field K]

theorem commutator_levi_eq_E8 [Finite K] (hq : 4 ≤ Nat.card K) (J : Finset (Fin (Tag.rank .E8))) :
    ⁅CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J,
        CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J⁆ =
      CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J := by
  apply Subgroup.map_injective (adjointGroup .E8 K).subtype_injective
  rw [Subgroup.map_commutator, map_subtype_levi_adjDatumE8]
  exact commutator_rootSpan_amalgamRoots_eq_E8 (F4Pilot.three_le_natCard_top_units hq) J

theorem levi_le_centralizer_leviTorus_E8 (J : Finset (Fin (Tag.rank .E8))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J ≤
      centralizer (((leviTorus K J).subgroupOf (adjointGroup .E8 K) :
        Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro d hd
  have hxR : ((x : adjointGroup .E8 K) : ModGL .E8 K) ∈ rootSpan .E8 K (amalgamRoots J) :=
    mem_subgroupOf.1 ((levi_adjDatumE8_eq (K := K) J).le hx)
  have h1 : ((x : adjointGroup .E8 K) : ModGL .E8 K) ∈
      centralizer (leviTorus K J : Set (ModGL .E8 K)) :=
    (mem_inf.1 (rootSpan_amalgamRoots_le_inf_centralizer (T := leviTorus K J) le_rfl hxR)).2
  exact Subtype.ext (mem_centralizer_iff.1 h1 _ (mem_subgroupOf.1 hd))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_perfectCore_of_swap_E8 [Finite K] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .E8 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1)
    {M₁ M₂ : Subgroup G} (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) (hdisj : M₁ ⊓ M₂ = ⊥)
    (htN : t ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G))
    (hC : (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L) :
    M₁ ⊔ M₂ ≤ ⨆ i : Fin (Tag.rank .E8),
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G)) := by
  have hcomm : M₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (M₁ : Set G) := hswap ▸ h₁₂
  have hdisj' : M₁ ⊓ M₁.map (MulAut.conj t).toMonoidHom = ⊥ := hswap ▸ hdisj
  have hδinj := F4Pilot.swapDiagHom_injective hcomm hdisj'
  have hδL : (F4Pilot.swapDiagHom hcomm).range = L := by
    rw [F4Pilot.range_swapDiagHom hcomm ht2 hdisj', hswap, hC]
  set E : M₁ ≃* L := (MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr hδL) with hE
  have hEδ : ∀ x : M₁, ((E x : L) : G) = F4Pilot.swapDiagHom hcomm x := fun x => rfl
  set Φ₁ : adjointGroup .E8 K →* G := M₁.subtype.comp (E.trans e).symm.toMonoidHom with hΦ₁
  have hΦ₁mem : ∀ y, Φ₁ y ∈ M₁ := fun y => ((E.trans e).symm y).2
  have hkey : ∀ y : adjointGroup .E8 K,
      F4Pilot.swapDiagHom hcomm ((E.trans e).symm y) = ((e.symm y : L) : G) := by
    intro y
    rw [MulEquiv.symm_trans_apply, ← hEδ, MulEquiv.apply_symm_apply]
  set P : Subgroup G := ⨆ i : Fin (Tag.rank .E8),
    perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G)) with hP
  have hpiece : ∀ i : Fin (Tag.rank .E8),
      CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} ≤ P.comap Φ₁ := by
    intro i
    set S := CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} with hS
    have hSperf : ⁅S.map Φ₁, S.map Φ₁⁆ = S.map Φ₁ := by
      rw [← map_commutator, commutator_levi_eq_E8 hq]
    have hSle : S.map Φ₁ ≤
        (M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_inf.2 ⟨mem_sup_left (hΦ₁mem y), mem_centralizer_iff.2 fun τ hτ => ?_⟩
      obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hτ
      rw [← hkey d, F4Pilot.swapDiagHom_apply]
      have hyd : d * y = y * d :=
        mem_centralizer_iff.1 (levi_le_centralizer_leviTorus_E8 {i} hy) d (mem_subgroupOf.2 hdT)
      have h1 : Φ₁ d * Φ₁ y = Φ₁ y * Φ₁ d := by rw [← map_mul, ← map_mul, hyd]
      have hdM₂ : t * Φ₁ d * t⁻¹ ∈ M₂ := by
        rw [← hswap]
        exact ⟨_, hΦ₁mem d, rfl⟩
      have h2 : Φ₁ y * (t * Φ₁ d * t⁻¹) = (t * Φ₁ d * t⁻¹) * Φ₁ y :=
        mem_centralizer_iff.1 (h₁₂ hdM₂) _ (hΦ₁mem y)
      change Φ₁ d * (t * Φ₁ d * t⁻¹) * Φ₁ y = Φ₁ y * (Φ₁ d * (t * Φ₁ d * t⁻¹))
      calc Φ₁ d * (t * Φ₁ d * t⁻¹) * Φ₁ y = Φ₁ d * ((t * Φ₁ d * t⁻¹) * Φ₁ y) := by group
        _ = Φ₁ d * (Φ₁ y * (t * Φ₁ d * t⁻¹)) := by rw [h2]
        _ = (Φ₁ d * Φ₁ y) * (t * Φ₁ d * t⁻¹) := by group
        _ = (Φ₁ y * Φ₁ d) * (t * Φ₁ d * t⁻¹) := by rw [h1]
        _ = Φ₁ y * (Φ₁ d * (t * Φ₁ d * t⁻¹)) := by group
    intro y hy
    exact le_iSup (fun i : Fin (Tag.rank .E8) =>
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G))) i
      (CFSG.Quasithin.le_perfectCore_of_perfect hSle hSperf ⟨y, hy, rfl⟩)
  have htop : ⊤ ≤ P.comap Φ₁ := top_le_of_forall_levi_singleton_le_E8 hpiece
  have hM₁ : M₁ ≤ P := by
    intro x hx
    have h1 : Φ₁ ((E.trans e) ⟨x, hx⟩) = x := by
      simp only [hΦ₁, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, coe_subtype]
    rw [← h1]
    exact htop (mem_top _)
  have htP : ∀ i : Fin (Tag.rank .E8),
      (perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G))).map
        (MulAut.conj t).toMonoidHom =
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K {i}) : Set G)) := by
    intro i
    refine F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _
        (inf_normalizer_le_normalizer_inf ⟨htN, le_normalizer ?_⟩))
    exact centralizer_le (SetLike.coe_subset_coe.2 (E6Pilot.modelToG_le e _)) htC
  have hM₂ : M₂ ≤ P := by
    calc M₂ = M₁.map (MulAut.conj t).toMonoidHom := hswap.symm
      _ ≤ P.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hM₁
      _ = P := by rw [hP, Subgroup.map_iSup]; exact iSup_congr htP
  exact sup_le hM₁ hM₂

theorem unique_of_swap_E8 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₁ : Subgroup G} {K₁ : Type} [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f)
    (e₁ : G₁ ≃* adjointGroup .E8 K₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hJ : ∀ i : Fin (Tag.rank .E8), pieceCore e {i} ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₁
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have e₂ : G₁.map (MulAut.conj t).toMonoidHom ≃* adjointGroup .E8 K₁ :=
    (G₁.equivMapOfInjective _ (MulAut.conj t).injective).symm.trans e₁
  refine F4Pilot.unique_of_forall_conjugate_generation
    (J := fun i : Fin (Tag.rank .E8) => modelToG e (leviTorus K {i})) hJ fun h htM => ?_
  rw [F4Pilot.conjugate_sup_eq_sup_conjugate] at htM ⊢
  have e₁' := (F4Pilot.conjugateSymmEquiv G₁ h).trans e₁
  have e₂' := (F4Pilot.conjugateSymmEquiv (G₁.map (MulAut.conj t).toMonoidHom) h).trans e₂
  have h₁₂' := F4Pilot.conjugate_le_centralizer_conjugate_of_le h₁₂ h
  obtain ⟨hswap, hC⟩ := swap_and_inf_centralizer_eq_of_mem_normalizer_E8 hset hK e htC ht hKt
    hK₁ hK₁ e₁' e₂' h₁₂' htM
  have hdisj := inf_eq_bot_of_le_centralizer_E8 e₁' h₁₂'
  exact le_iSup_perfectCore_of_swap_E8 hq e htC ht2 h₁₂' hswap hdisj htM hC

end Step3

section Input


theorem e8SwapRowUniqueInput_holds : E8SwapRowUniqueInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ G₁ ⟨e₁⟩ h₁₂ hsup g hg
  have hJ : ∀ i : Fin (Tag.rank .E8),
      pieceCore e {i} ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := fun i => by
    rw [hsup]
    exact pieceCore_le_pieceSup ⟨{i}, by simp⟩
  have h := unique_of_swap_E8 hw.standard hf hw.card_eq e hw.mem_centralizer hw.orderOf_eq
    (hw.inf_eq e) hw.card_eq e₁ h₁₂ hJ g
  rw [hsup] at h
  exact h hg

end Input

end CFSG.SeitzReduction.E8Pilot
