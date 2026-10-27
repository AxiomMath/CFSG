module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267CenterMultiplier
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
import CFSG.Adapters.TauCetiLieModels
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)


section Multiplier

theorem exceptionalOrders_dvd_sq (t : StatedLieTag) (n ℓ f : ℕ) :
    (exceptionalOrders t n ℓ f).1 ∣ ℓ ^ 2 ∧ (exceptionalOrders t n ℓ f).2 ∣ ℓ ^ 2 := by
  unfold exceptionalOrders
  split <;> norm_num

theorem card_multiplier_eq {X : Type} [Group X] {t : StatedLieTag} {n ℓ f : ℕ}
    (e : CFSG.Open.griessHopfMultiplier X ≃*
      CFSG.Blueprint.Multiplier.generic t n ℓ f × CFSG.Blueprint.Multiplier.exceptional t n ℓ f) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) =
      (genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2 *
        ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2) := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem not_dvd_card_multiplier (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    {t : StatedLieTag} {n ℓ f : ℕ} (h : StatedClassicalModel X t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hA : t = .PSL → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hU : t = .PSU → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  have hℓ : ℓ.Prime := h.1.1
  obtain ⟨-, ⟨e⟩⟩ := hGA X t n ℓ f (CFSG.Models.lieModel_of_statedClassicalModel h)
  rw [card_multiplier_eq e]
  have h4 : ∀ m : ℕ, m ∣ 4 → ¬ p ∣ m := fun m hm hpm => by
    have h4' : p ∣ 2 ^ 2 := hpm.trans hm
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4'))
  have hsq : ∀ m : ℕ, m ∣ ℓ ^ 2 → ¬ p ∣ m := fun m hm hpm =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hpm.trans hm)))
  obtain ⟨he1, he2⟩ := exceptionalOrders_dvd_sq t n ℓ f
  have hexc : ¬ p ∣ (exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2 := by
    rw [hp.dvd_mul, not_or]
    exact ⟨hsq _ he1, hsq _ he2⟩
  have hgen : ¬ p ∣ (genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2 := by
    rw [hp.dvd_mul, not_or]
    obtain ⟨-, hmodel⟩ := h
    cases t with
    | PSL =>
      exact ⟨by simpa [genericOrders] using hA rfl, by simp [genericOrders, hp.ne_one]⟩
    | PSU =>
      exact ⟨by simpa [genericOrders] using hU rfl, by simp [genericOrders, hp.ne_one]⟩
    | PSp =>
      refine ⟨h4 _ ?_, by simp [genericOrders, hp.ne_one]⟩
      simp only [genericOrders]
      exact (Nat.gcd_dvd_left _ _).trans (by norm_num)
    | POmegaOdd =>
      exact ⟨h4 _ (by simp [genericOrders]), by simp [genericOrders, hp.ne_one]⟩
    | POmegaPlus =>
      simp only [genericOrders]
      split_ifs
      · exact ⟨by simp [hp.ne_one], by simp [hp.ne_one]⟩
      · exact ⟨h4 _ (by norm_num), h4 _ (by norm_num)⟩
      · exact ⟨h4 _ (Nat.gcd_dvd_left _ _), by simp [hp.ne_one]⟩
    | POmegaMinus =>
      exact ⟨h4 _ (by simp only [genericOrders]; exact Nat.gcd_dvd_left _ _),
        by simp [genericOrders, hp.ne_one]⟩
    | _ => exact hmodel.elim
  rw [hp.dvd_mul, not_or]
  exact ⟨hgen, hexc⟩

theorem center_eq_bot_of_classical (hGA : GriessAllModelsStatement) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) {t : StatedLieTag} {n ℓ f : ℕ}
    (h : StatedClassicalModel (PSimple p S) t n ℓ f) (hpℓ : p ≠ ℓ)
    (hA : t = .PSL → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hU : t = .PSU → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : Subgroup.center ↥S = ⊥ :=
  S267.BadExc.center_eq_bot_of_multiplier hp hperf hcore (MulEquiv.refl _)
    (not_dvd_card_multiplier hGA h hp hp2 hpℓ hA hU)

end Multiplier

section Cover

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_cover_of_center_eq_bot (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {H : Subgroup (GL ι K)} (e : PSimple p S ≃* StatedProj H) :
    ∃ φ : ↥H →* Ω, φ.range = S ∧ φ.ker = (StatedScalars ι K).subgroupOf H := by
  set ε : StatedProj H ≃* ↥S :=
    e.symm.trans ((S267.BadExc.psimpleEquivCenterQuotOfCore hcore).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)) with hε
  refine ⟨S.subtype.comp (ε.toMonoidHom.comp (QuotientGroup.mk' _)), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (ε.surjective.comp (QuotientGroup.mk'_surjective _)), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · ext h
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
    constructor
    · intro h1
      have h2 : ε (QuotientGroup.mk' _ h) = 1 := Subtype.ext h1
      rw [map_eq_one_iff _ ε.injective] at h2
      rwa [← QuotientGroup.ker_mk' ((StatedScalars ι K).subgroupOf H), MonoidHom.mem_ker]
    · intro h1
      rw [← QuotientGroup.ker_mk' ((StatedScalars ι K).subgroupOf H), MonoidHom.mem_ker] at h1
      change ((ε (QuotientGroup.mk' _ h) : ↥S) : Ω) = 1
      rw [h1, map_one]
      rfl

theorem exists_cover_of_odd_splitting [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥) {H : Subgroup (GL ι K)}
    (e : PSimple p S ≃* StatedProj H)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → ∃ s : ↥H →* E, ∀ g, π (s g) = g) :
    ∃ φ : ↥H →* Ω, φ.range = S ∧ φ.ker ≤ (StatedScalars ι K).subgroupOf H := by
  haveI : Group.IsPerfect ↥S := ⟨S267.perfect_of_commutator_self_eq hperf⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥S)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
        hp hcore)
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨φ, hφs, hφk, -⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting hodd
    ((S267.BadExc.psimpleEquivCenterQuotOfCore hcore).symm.trans e) hsplit
  refine ⟨S.subtype.comp φ, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφs, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro h hh
    apply hφk
    rw [MonoidHom.mem_ker] at hh ⊢
    exact Subtype.ext hh

end Cover

section Action

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

@[expose] noncomputable def coverEquiv {H : Type*} [Group H] (φ : H →* Ω) (hφS : φ.range = S) :
    H ⧸ φ.ker ≃* ↥S :=
  (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφS)

theorem coverEquiv_mk {H : Type*} [Group H] (φ : H →* Ω) (hφS : φ.range = S) (h : H) :
    ((coverEquiv φ hφS (QuotientGroup.mk h) : ↥S) : Ω) = φ h :=
  rfl

variable [S.Normal]

@[expose] noncomputable def transAut {X : Type*} [Group X] (e : X ≃* ↥S) (x : Ω) : MulAut X :=
  (e.trans (MulAut.conjNormal x)).trans e.symm

theorem transAut_spec {X : Type*} [Group X] (e : X ≃* ↥S) (x : Ω) (g : X) :
    ((e (transAut e x g) : ↥S) : Ω) = x * e g * x⁻¹ := by
  simp only [transAut, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]

theorem transAut_conj {X : Type*} [Group X] (e : X ≃* ↥S) (x : Ω) (g : X) :
    x * (S.subtype.comp e.toMonoidHom) g * x⁻¹ =
      (S.subtype.comp e.toMonoidHom) (transAut e x g) :=
  (transAut_spec e x g).symm

end Action

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def conjOn {H : Subgroup (GL ι K)} {y : GL ι K}
    (hy : y ∈ Subgroup.normalizer (H : Set (GL ι K))) : MulAut ↥H where
  toFun h := ⟨y * h * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy h).1 h.2⟩
  invFun h := ⟨y⁻¹ * h * y, by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) h).1 h.2
    simpa using this⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjOn {H : Subgroup (GL ι K)} {y : GL ι K}
    (hy : y ∈ Subgroup.normalizer (H : Set (GL ι K))) (h : ↥H) :
    ((conjOn hy h : ↥H) : GL ι K) = y * h * y⁻¹ :=
  rfl

@[expose] noncomputable def quotAut {H : Type*} [Group H] (K₀ : Subgroup H) [K₀.Normal]
    (β : MulAut H) (hβ : K₀.map β.toMonoidHom = K₀) : MulAut (H ⧸ K₀) :=
  QuotientGroup.congr K₀ K₀ β hβ

theorem quotAut_mk {H : Type*} [Group H] (K₀ : Subgroup H) [K₀.Normal] (β : MulAut H)
    (hβ : K₀.map β.toMonoidHom = K₀) (h : H) :
    quotAut K₀ β hβ (QuotientGroup.mk h) = QuotientGroup.mk (β h) :=
  rfl

theorem map_conjOn_eq_of_le_scalars {H : Subgroup (GL ι K)} {y : GL ι K}
    (hy : y ∈ Subgroup.normalizer (H : Set (GL ι K))) {K₀ : Subgroup ↥H}
    (hK₀ : K₀ ≤ (StatedScalars ι K).subgroupOf H) :
    K₀.map (conjOn hy).toMonoidHom = K₀ := by
  have hfix : ∀ k ∈ K₀, conjOn hy k = k := by
    intro k hk
    apply Subtype.ext
    rw [coe_conjOn]
    have hc : (k : GL ι K) ∈ Subgroup.center (GL ι K) := by
      have h1 := Subgroup.mem_subgroupOf.1 (hK₀ hk)
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    rw [Subgroup.mem_center_iff.1 hc y, mul_inv_cancel_right]
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hfix k' hk']
    exact hk'
  · intro hk
    exact ⟨k, hk, hfix k hk⟩

theorem transAut_coverEquiv_eq_quotAut {Ω : Type} [Group Ω] {S : Subgroup Ω} [S.Normal]
    {H : Subgroup (GL ι K)} (φ : ↥H →* Ω) (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars ι K).subgroupOf H) {y : GL ι K}
    (hy : y ∈ Subgroup.normalizer (H : Set (GL ι K))) {x : Ω}
    (hxy : ∀ h : ↥H, φ (conjOn hy h) = x * φ h * x⁻¹) :
    transAut (coverEquiv φ hφS) x =
      quotAut φ.ker (conjOn hy) (map_conjOn_eq_of_le_scalars hy hφk) := by
  refine MulEquiv.ext fun g => ?_
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  apply (coverEquiv φ hφS).injective
  apply Subtype.ext
  rw [transAut_spec, quotAut_mk, coverEquiv_mk, coverEquiv_mk, hxy]

end Matrix

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
