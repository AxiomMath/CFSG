module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)

open CFSG.LieType.Ree

theorem l154_inner_of_induced {P T : Type*} [Group P] [Group T] (e₀ : P ≃* T ⧸ Subgroup.center T)
    (hZ : Subgroup.center T = ⊥) (ψ : MulAut T) (α : MulAut P)
    (hα : ∀ s, e₀ (α s) = onCenterQuotient ψ (e₀ s))
    (hinn : α ∈ (MulAut.conj : P →* MulAut P).range) :
    ∃ j : T, ∀ t : T, ψ t = j * t * j⁻¹ := by
  obtain ⟨u, hu⟩ := hinn
  obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (e₀ u)
  refine ⟨j, fun t => ?_⟩
  have h1 := hα (e₀.symm (QuotientGroup.mk t))
  have h2 : α (e₀.symm (QuotientGroup.mk t)) = u * e₀.symm (QuotientGroup.mk t) * u⁻¹ := by
    rw [← hu, MulAut.conj_apply]
  rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hj] at h1
  have h3 : onCenterQuotient ψ (QuotientGroup.mk t) = QuotientGroup.mk (ψ t) :=
    onCenterQuotient_apply_mk ψ t
  rw [h3] at h1
  have h4 : (QuotientGroup.mk (ψ t) : T ⧸ Subgroup.center T) = QuotientGroup.mk (j * t * j⁻¹) := by
    rw [← h1]
    rfl
  rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h4
  exact h4

theorem l154_twist_by_inner {Γ : Type*} [Group Γ] {p : ℕ} {φ : MulAut Γ} (hφp : φ ^ p = 1)
    {T : Subgroup Γ} (hZ : Subgroup.center ↥T = ⊥) {j : Γ} (hjT : j ∈ T)
    (hφT : ∀ t ∈ T, φ t = j * t * j⁻¹) :
    φ j = j ∧ (MulAut.conj j⁻¹ * φ) ^ p = 1 ∧ ∀ t ∈ T, (MulAut.conj j⁻¹ * φ) t = t := by
  have hφj : φ j = j := by
    rw [hφT j hjT]
    group
  have hiter : ∀ (k : ℕ) (t : Γ), t ∈ T → (φ ^ k) t = j ^ k * t * (j ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      have h1 : φ t ∈ T := by
        rw [hφT t ht]
        exact T.mul_mem (T.mul_mem hjT ht) (T.inv_mem hjT)
      rw [pow_succ, MulAut.mul_apply, ih (φ t) h1, hφT t ht]
      group
  have hjp : j ^ p = 1 := by
    have hmem : (⟨j ^ p, T.pow_mem hjT p⟩ : ↥T) ∈ Subgroup.center ↥T := by
      rw [Subgroup.mem_center_iff]
      intro t
      have h1 := hiter p t.1 t.2
      rw [hφp, MulAut.one_apply] at h1
      apply Subtype.ext
      show (t : Γ) * j ^ p = j ^ p * t
      calc (t : Γ) * j ^ p = (j ^ p * t * (j ^ p)⁻¹) * j ^ p := by rw [← h1]
        _ = j ^ p * t := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hcomm : Commute (MulAut.conj j⁻¹ : MulAut Γ) φ := by
    refine MulEquiv.ext fun z => ?_
    show j⁻¹ * φ z * j⁻¹⁻¹ = φ (j⁻¹ * z * j⁻¹⁻¹)
    simp only [map_mul, map_inv, hφj]
  refine ⟨hφj, ?_, fun t ht => ?_⟩
  · rw [hcomm.mul_pow, ← map_pow, inv_pow, hjp, inv_one, map_one, one_mul, hφp]
  · simp only [MulAut.mul_apply, MulAut.conj_apply, hφT t ht]
    group

section Fixed


theorem l154_ree_fixed_card {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hσ : orderOf σ = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧
      Nat.card ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (ReeTag.F4.reeGammaFieldAut K a σ)) = l154ReeOrd (2 ^ (2 * b + 1)) := by
  obtain ⟨b, hbc, hkc, -⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  obtain ⟨b', hk'c, hch, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_fieldAut_equiv hK hp hp2 σ
      hσ
  have hb : b' = b := by
    have h1 : 2 ^ (2 * b' + 1) = 2 ^ (2 * b + 1) := hk'c.symm.trans hkc
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb
  refine ⟨b', hbc, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b' _
    hk'c).1

end Fixed

section Lang


theorem l154_ree_lang_conj {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    {φ : MulAut (ReeTag.F4.reeGamma K a)} (hφp : φ ^ p = 1) (hφout : ∀ g, φ ≠ MulAut.conj g)
    (j : ReeTag.F4.reeGamma K a) (hψp : (MulAut.conj j⁻¹ * φ) ^ p = 1) :
    ∃ (σ : K ≃+* K) (g : ReeTag.F4.reeGamma K a), orderOf σ = p ∧
      MulAut.conj j⁻¹ * φ =
        MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a σ * (MulAut.conj g)⁻¹ := by
  classical
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hφ1 : φ ≠ 1 := fun h => hφout 1 (by rw [h, map_one])
  obtain ⟨g, σ, hσ, hg⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd ha hK hp φ
      ⟨orderOf_eq_prime hφp hφ1, hφout⟩
  obtain ⟨σh, hσh⟩ : ∃ σh : MulAut (ReeTag.F4.reeGamma K a),
      σh = ReeTag.F4.reeGammaFieldAut K a σ := ⟨_, rfl⟩
  rw [← hσh, ← map_inv] at hg
  have hψ : (MulAut.conj j⁻¹ * φ : MulAut (ReeTag.F4.reeGamma K a)) =
      MulAut.conj (j⁻¹ * g * σh g⁻¹) * σh := by
    rw [hg]
    refine MulEquiv.ext fun z => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  obtain ⟨g', hg'⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp σ hσ
    (MulAut.conj j⁻¹ * φ) hψp ⟨_, hσh ▸ hψ⟩
  exact ⟨σ, g', hσ, hg'⟩

end Lang

section Descent


theorem l154_ree_descent {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {φ : MulAut (ReeTag.F4.reeGamma K a)} (hφp : φ ^ p = 1)
    (hφout : ∀ g, φ ≠ MulAut.conj g) {T : Subgroup (ReeTag.F4.reeGamma K a)}
    (hZ : Subgroup.center ↥T = ⊥) {j : ReeTag.F4.reeGamma K a} (hjT : j ∈ T)
    (hφT : ∀ t ∈ T, φ t = j * t * j⁻¹) (hdvd : 2 ^ (2 * a + 1) - 1 ∣ Nat.card ↥T) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hψp, hψT⟩ := l154_twist_by_inner hφp hZ hjT hφT
  obtain ⟨σ, g', hσ, hg'⟩ := l154_ree_lang_conj ha hK hp hφp hφout j hψp
  obtain ⟨σh, hσh⟩ : ∃ σh : MulAut (ReeTag.F4.reeGamma K a),
      σh = ReeTag.F4.reeGammaFieldAut K a σ := ⟨_, rfl⟩
  rw [← hσh, ← map_inv] at hg'
  have hfix : ∀ t ∈ T, σh (g'⁻¹ * t * g') = g'⁻¹ * t * g' := by
    intro t ht
    have h1 := hψT t ht
    rw [hg'] at h1
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [inv_inv] at h1
    calc σh (g'⁻¹ * t * g') = g'⁻¹ * (g' * σh (g'⁻¹ * t * g') * g'⁻¹) * g' := by group
      _ = g'⁻¹ * t * g' := by rw [h1]
  have hle : T.map (MulAut.conj g'⁻¹).toMonoidHom ≤
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup σh := by
    rintro _ ⟨t, ht, rfl⟩
    show σh (g'⁻¹ * t * g'⁻¹⁻¹) = g'⁻¹ * t * g'⁻¹⁻¹
    rw [inv_inv]
    exact hfix t ht
  have hcard : Nat.card ↥T ∣
      Nat.card ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup σh) := by
    have h1 : Nat.card ↥(T.map (MulAut.conj g'⁻¹).toMonoidHom) = Nat.card ↥T :=
      Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨b, hb, hcb⟩ := l154_ree_fixed_card hK hp hp2 σ hσ
  rw [← hσh] at hcb
  apply l154_ree_arith hp hp5 (m := 2 * b + 1) (by omega)
  have e : 2 ^ (p * (2 * b + 1)) = 2 ^ (2 * a + 1) := by rw [mul_comm, hb]
  rw [e, ← hcb]
  exact hdvd.trans hcard

end Descent

section Main


theorem l154_false_of_ree_innDiag_ge5 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hc : IsChevSimple 2 (PSimple p S)) (hQ : catalogIs (PSimple p S) l154ExcRee)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hxy : x * y = y * x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x)
    (hInnJ : InnDiagOn p (Subgroup.zpowers y) J) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨a, K, _, _, _, θ, s, φ, ha, hK, hs, hφp, hφout, -, hindx, hindy⟩ :=
    l154_ree_setup hp hp2 hSn hqS hSp hc hQ hxp hyp hxy hInn hF hcm
  have hxN := l154_mem_normalizer_of_normal hSn x
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hTc := l154_JImage_glaPComponent hp hxp hxN hJ θ (MulAut.conj s) hindx
  obtain ⟨hqT, hZT, hdvd, hty⟩ := l154_ree_layer ha hK hp (by omega) hs hTc
  obtain ⟨ψJ, e₀, hψ, he₀⟩ := l154_JImage_equiv hp hSp hJ hJS hJy θ φ hindy hqT
  have hperf : commutator (PQuot p J) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hJ).1
  have hMJ : LargeEvenMarking (PQuot p J) fun lab _ _ _ _ _ => ¬ L154OutdiagCfg p lab := by
    rcases hty with h | h
    · obtain ⟨e⟩ := h
      exact CFSG.StandardType.Canonical.largeEvenMarking_mono
        (fun lab _ _ _ _ _ h => l154_notCfg_of_markTag_markRank hp hp2 h.1 h.2.1)
        (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf
          ((l154_lieModel_psl_two ha hK e).of_mulEquiv e₀.symm))
    · obtain ⟨e⟩ := h
      exact CFSG.StandardType.Canonical.largeEvenMarking_mono
        (fun lab _ _ _ _ _ h => l154_notCfg_of_markTag h.1 (Or.inr rfl))
        (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf
          ((l154_lieModel_twistedB2 ha hK hZT e).of_mulEquiv e₀.symm))
  have hin : MI.indAut p J y hJy ∈ OuterAutomorphisms.inner (PSimple p J) :=
    l154_inner_of_innDiagOn_nonCfg hp hp2 hJy hyp hInnJ hMJ
  obtain ⟨j, hj⟩ := l154_inner_of_induced e₀ hZT ψJ (MI.indAut p J y hJy) he₀ hin
  refine l154_ree_descent ha hK hp hp5 hφp hφout hZT j.2 (fun t ht => ?_) hdvd
  have h1 := hj ⟨t, ht⟩
  have h2 := congrArg Subtype.val h1
  rw [hψ ⟨t, ht⟩] at h2
  exact h2

end Main

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
