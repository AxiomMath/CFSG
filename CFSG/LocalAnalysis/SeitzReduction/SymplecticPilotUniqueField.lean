module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective)

section Induced

variable {G : Type*} [Group G] {X : Type*} [Group X]

theorem exists_mulAut_of_mem_normalizer_range {Ψ : X →* G} (hinj : Function.Injective Ψ)
    {t : G} (htN : t ∈ normalizer (Ψ.range : Set G)) :
    ∃ β : MulAut X, ∀ x, t * Ψ x * t⁻¹ = Ψ (β x) := by
  set E : X ≃* Ψ.range := MonoidHom.ofInjective hinj with hE
  refine ⟨F4Pilot.normalizerMulAut E.symm ⟨t, htN⟩, fun x => ?_⟩
  have h := F4Pilot.coe_symm_normalizerMulAut_apply E.symm ⟨t, htN⟩ x
  rw [MulEquiv.symm_symm] at h
  rw [← MonoidHom.ofInjective_apply hinj, ← MonoidHom.ofInjective_apply hinj]
  exact h.symm

theorem mul_self_eq_one_of_conj_eq {Ψ : X →* G} (hinj : Function.Injective Ψ) {t : G}
    (htt : t * t = 1) {β : MulAut X} (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x)) : β * β = 1 := by
  refine MulEquiv.ext fun x => hinj ?_
  rw [MulAut.mul_apply, MulAut.one_apply, ← hβ, ← hβ]
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [ht]
  calc t * (t * Ψ x * t) * t = (t * t) * Ψ x * (t * t) := by group
    _ = Ψ x := by rw [htt, one_mul, mul_one]

theorem range_inf_centralizer_eq_map {Ψ : X →* G} (hinj : Function.Injective Ψ) {t : G}
    {β : MulAut X} (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x)) :
    Ψ.range ⊓ centralizer ({t} : Set G) = (fixedSubgroup β).map Ψ := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hxt⟩
    refine ⟨x, ?_, rfl⟩
    change β x = x
    apply hinj
    rw [← hβ]
    have h := mem_centralizer_singleton_iff.1 hxt
    calc t * Ψ x * t⁻¹ = Ψ x * t * t⁻¹ := by rw [h]
      _ = Ψ x := by group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hx' : β x = x := hx
    show Ψ x ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h := hβ x
    rw [hx'] at h
    calc Ψ x * t = t * Ψ x * t⁻¹ * t := by rw [h]
      _ = t * Ψ x := by group

end Induced

section Generation

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

omit [Field K] in
theorem statedSpMap_eq_spFieldMap [Field K] (ι : K →+* F) (x : StatedSp n K) :
    statedSpMap ι n x = spFieldMap n ι x :=
  rfl

theorem statedSpMap_mem_leviTorusSp (ι : K →+* F) {J : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ leviTorusSp K J) : statedSpMap ι n x ∈ leviTorusSp F J := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [statedSpMap_eq_spFieldMap, spFieldMap_diagSp]
  refine ⟨liftParam ι t, fun j hj => ⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · simp only [liftParam, (ht j hj).1 h]
  · simp only [liftParam, (ht j hj).2 h, map_one]

variable {G : Type*} [Group G] {L : Subgroup G}

theorem range_le_spGlobal_of_comp_statedSpMap [Finite F] (hF : 4 ≤ Nat.card F) (hn : 1 ≤ n)
    (e : L ≃* StatedSp n K) (ι : K →+* F) {Φ : StatedSp n F →* G}
    (hΦ : ∀ x, Φ (statedSpMap ι n x) = ((e.symm x : L) : G)) : Φ.range ≤ spGlobal e := by
  rw [MonoidHom.range_eq_map, ← iSup_simpleRootSL2_eq_top hn, Subgroup.map_iSup]
  refine iSup_mono fun j => ?_
  have hperf : ⁅(simpleRootSL2 F j).map Φ, (simpleRootSL2 F j).map Φ⁆ =
      (simpleRootSL2 F j).map Φ := by
    rw [← map_commutator, commutator_simpleRootSL2_eq_of_four_le hF j]
  refine F4Pilot.le_centralizerPerfectCore hperf ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hy
  have hxF : statedSpMap ι n x ∈ leviTorusSp F ({j} : Finset (Fin n)) :=
    statedSpMap_mem_leviTorusSp ι hx
  have hcomm : statedSpMap ι n x * a = a * statedSpMap ι n x :=
    mem_centralizer_iff.1 (simpleRootSL2_le_centralizer_leviTorusSp
      (Finset.mem_singleton_self j) ha) _ hxF
  rw [← hΦ, ← map_mul, ← map_mul, hcomm]

end Generation

section Conjugate

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fixedSubgroup_conj_eq_centralizer {X : Type*} [Group X] (s : X) :
    fixedSubgroup (MulAut.conj s) = centralizer ({s} : Set X) := by
  ext y
  rw [mem_centralizer_singleton_iff]
  change s * y * s⁻¹ = y ↔ y * s = s * y
  constructor
  · intro h
    calc y * s = s * y * s⁻¹ * s := by rw [h]
      _ = s * y := by group
  · intro h
    rw [← h]
    group

theorem not_mem_range_conj_of_fieldRow (hL : CFSG.Open.standardComponentIsStandard L) {n f : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = Nat.card K ^ 2) {Ψ : StatedSp n F →* G}
    (hinj : Function.Injective Ψ) {β : MulAut (StatedSp n F)}
    (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x)) :
    β ∉ (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range := by
  rintro ⟨s, rfl⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hββ := mul_self_eq_one_of_conj_eq hinj htt hβ
  have hss : s * s = 1 := by
    have h1 : MulAut.conj (s * s) = 1 := by rw [map_mul]; exact hββ
    have h2 : s * s ∈ center (StatedSp n F) := by
      rw [mem_center_iff]
      intro y
      have h3 := DFunLike.congr_fun h1 y
      rw [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (s * s) = (s * s) * y * (s * s)⁻¹ * (s * s) := by rw [h3]
        _ = (s * s) * y := by group
    rwa [center_statedSp_eq_bot, mem_bot] at h2
  have hdvd := pow_dvd_card_centralizer_statedSp (F := F) hss
  rw [← fixedSubgroup_conj_eq_centralizer] at hdvd
  have hXt : (fixedSubgroup (MulAut.conj s)).map Ψ ≤ centralizer ({t} : Set G) := by
    rw [← range_inf_centralizer_eq_map hinj hβ]
    exact inf_le_right
  have hv := factorization_card_le_of_le_centralizer_sp hL hn hK e ht hKt hXt
  rw [card_map_of_injective hinj] at hv
  have hpow : Nat.card F ^ (n * (n + 1) / 2) = 2 ^ (f * (n * (n + 1))) := by
    rw [hF, hK, ← pow_mul, ← pow_mul]
    congr 1
    have h2 : n * (n + 1) / 2 * 2 = n * (n + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
    calc f * (2 * (n * (n + 1) / 2)) = f * (n * (n + 1) / 2 * 2) := by ring
      _ = f * (n * (n + 1)) := by rw [h2]
  rw [hpow] at hdvd
  have hv2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hf1 : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have h3 : f * (n * (n + 1)) = f * n ^ 2 + f * n := by ring
  have h4 : 2 * f ≤ f * n := by nlinarith
  omega

theorem exists_comp_statedSpMap_eq (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Ψ : StatedSp n F →* G} (hinj : Function.Injective Ψ) {β : MulAut (StatedSp n F)}
    (hβ : ∀ x, t * Ψ x * t⁻¹ = Ψ (β x))
    (hβi : β ∉ (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range) :
    ∃ Φ : StatedSp n F →* G, Φ.range = Ψ.range ∧
      ∀ x, Φ (statedSpMap ι n x) = ((e.symm x : L) : G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hββ := mul_self_eq_one_of_conj_eq hinj htt hβ
  obtain ⟨y, hy⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_mul_conj_inv hn hσ hββ hβi
  set Ψ₁ : StatedSp n F →* G := Ψ.comp (MulAut.conj y).toMonoidHom with hΨ₁
  have hinj₁ : Function.Injective Ψ₁ := hinj.comp (MulAut.conj y).injective
  have hrange₁ : Ψ₁.range = Ψ.range := by
    rw [hΨ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj y).surjective,
      ← MonoidHom.range_eq_map]
  have hσΨ₁ : ∀ x, t * Ψ₁ x * t⁻¹ = Ψ₁ (fieldSp n F σ x) := by
    intro x
    simp only [hΨ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hβ, hy]
    congr 1
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    group
  have hC : Ψ.range ⊓ centralizer ({t} : Set G) = (Ψ₁.comp (statedSpMap ι n)).range := by
    rw [← hrange₁, range_inf_centralizer_eq_map hinj₁ hσΨ₁,
      show fixedSubgroup (fieldSp n F σ) = (statedSpMap ι n).range from
        F4Pilot.eqLocus_fieldSp_eq_range ι hfix, MonoidHom.range_comp]
  have hinjι : Function.Injective (Ψ₁.comp (statedSpMap ι n)) :=
    hinj₁.comp (statedSpMap_injective ι n)
  have : Group.IsPerfect (StatedSp n K) := isPerfect_statedSp_of_charTwo hn
  have hperf : ⁅(Ψ₁.comp (statedSpMap ι n)).range, (Ψ₁.comp (statedSpMap ι n)).range⁆ =
      (Ψ₁.comp (statedSpMap ι n)).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hle : (Ψ₁.comp (statedSpMap ι n)).range ≤ L :=
    std_perfect_le hset hOut htC ht hperf (by rw [← hC]; exact inf_le_right)
  have hcard : Nat.card L ≤ Nat.card (Ψ₁.comp (statedSpMap ι n)).range := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hinjι).toEquiv]
  have hL : (Ψ₁.comp (statedSpMap ι n)).range = L := Subgroup.eq_of_le_of_card_ge hle hcard
  set E : StatedSp n K ≃* L :=
    (MonoidHom.ofInjective hinjι).trans (MulEquiv.subgroupCongr hL) with hE
  set γ : MulAut (StatedSp n K) := e.symm.trans E.symm with hγdef
  have hγ : ∀ x, Ψ₁ (statedSpMap ι n (γ x)) = ((e.symm x : L) : G) := by
    intro x
    have h1 : E (γ x) = e.symm x := E.apply_symm_apply _
    exact congrArg Subtype.val h1
  obtain ⟨γ', hγ'⟩ := F4Pilot.exists_mulAut_statedSpMap_comm ι hn γ
  refine ⟨Ψ₁.comp γ'.toMonoidHom, ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 γ'.surjective, ← MonoidHom.range_eq_map,
      hrange₁]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hγ', hγ]

end Conjugate

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conjugate_eq_of_spFieldRow (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {F : Type} [Field F]
    [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = spGlobal e) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate (spGlobal e) h : Set G)) :
    CFSG.conjugate (spGlobal e) h = spGlobal e := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hF : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    nlinarith
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  set Ψ : StatedSp n F →* G := (MulAut.conj h⁻¹).toMonoidHom.comp ψ with hΨ
  have hinjΨ : Function.Injective Ψ := (MulAut.conj h⁻¹).injective.comp hinj
  have hrangeΨ : Ψ.range = CFSG.conjugate (spGlobal e) h := by
    rw [hΨ, MonoidHom.range_comp, hrange]
    rfl
  obtain ⟨β, hβ⟩ := exists_mulAut_of_mem_normalizer_range hinjΨ (hrangeΨ ▸ htM)
  have hβi := not_mem_range_conj_of_fieldRow hset.standardSetting.standard hn hKc e ht hKt hF
    hinjΨ hβ
  obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_statedSpMap_eq hset.standardSetting hOut hn e htC ht ι hσ
    hfix hinjΨ hβ hβi
  have hle : CFSG.conjugate (spGlobal e) h ≤ spGlobal e := by
    rw [← hrangeΨ, ← hΦr]
    exact range_le_spGlobal_of_comp_statedSpMap hF4 (by omega) e ι hΦ
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

theorem unique_of_spFieldRow (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {F : Type} [Field F]
    [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = spGlobal e) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G) :=
  F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_spFieldRow hset hn hKc hf e ht hKt ι hσ hfix hinj hrange h htM

theorem spFieldRowUniqueInput_holds : SpFieldRowUniqueInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt F _ _ ι σ hσ hfix ψ hinj hrange _ _
  exact unique_of_spFieldRow hset (by omega) hKc hf e ht hKt ι hσ hfix hinj hrange

end Unique

end CFSG.SeitzReduction.SymplecticPilot
