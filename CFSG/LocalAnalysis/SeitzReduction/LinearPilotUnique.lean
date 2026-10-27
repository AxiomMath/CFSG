module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGen
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

section Fixed

variable {X Y : Type*} [Group X] [Group Y]

theorem fixedSubgroup_congr_eq_map (φ : X ≃* Y) (α : MulAut X) :
    fixedSubgroup (MulAut.congr φ α) = (fixedSubgroup α).map φ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  change φ (α (φ.symm (φ x))) = φ x ↔ α x = x
  rw [MulEquiv.symm_apply_apply, φ.injective.eq_iff]

theorem card_fixedSubgroup_congr (φ : X ≃* Y) (α : MulAut X) :
    Nat.card (fixedSubgroup (MulAut.congr φ α)) = Nat.card (fixedSubgroup α) := by
  rw [fixedSubgroup_congr_eq_map, card_map_of_injective φ.injective]

theorem card_perfectCore_fixedSubgroup_congr [Finite X] [Finite Y] (φ : X ≃* Y)
    (α : MulAut X) :
    Nat.card (perfectCore (fixedSubgroup (MulAut.congr φ α))) =
      Nat.card (perfectCore (fixedSubgroup α)) := by
  rw [fixedSubgroup_congr_eq_map, ← CFSG.Quasithin.map_perfectCore,
    card_map_of_injective φ.injective]

theorem card_fixedSubgroup_centerQuotientAut_dvd [Finite X] (α : MulAut X) :
    Nat.card (fixedSubgroup (centerQuotientAut α)) ∣ Nat.card (fixedSubgroup α) := by
  set Z := center X with hZ
  set π := QuotientGroup.mk' Z with hπ
  set T := (fixedSubgroup (centerQuotientAut α)).comap π with hT
  have hmemT : ∀ x : X, x ∈ T ↔ α x * x⁻¹ ∈ Z := by
    intro x
    rw [hT, mem_comap]
    change centerQuotientAut α (π x) = π x ↔ _
    rw [hπ, F4Pilot.centerQuotientAut_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    constructor
    · intro h
      have h1 := Z.inv_mem h
      rw [mul_inv_rev, inv_inv] at h1
      exact (center X).normal_of_characteristic.mem_comm h1
    · intro h
      have h1 := (center X).normal_of_characteristic.mem_comm h
      have h2 := Z.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at h2
  have hTcard : Nat.card T = Nat.card Z * Nat.card (fixedSubgroup (centerQuotientAut α)) := by
    have hidx : T.index = (fixedSubgroup (centerQuotientAut α)).index :=
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)
    have h1 := T.card_mul_index
    have h2 := (fixedSubgroup (centerQuotientAut α)).card_mul_index
    have h3 : Nat.card X = Nat.card Z * Nat.card (X ⧸ Z) := by
      rw [Z.card_eq_card_quotient_mul_card_subgroup, mul_comm]
    have hpos : 0 < (fixedSubgroup (centerQuotientAut α)).index := Nat.pos_of_ne_zero
      (index_ne_zero_of_finite)
    rw [hidx] at h1
    rw [← h2] at h3
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, h3, mul_assoc]
  let φ : T →* Z :=
    { toFun := fun x => ⟨α x * (x : X)⁻¹, (hmemT x).1 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := mem_center_iff.mp ((hmemT y).1 y.2)
        change α ((x : X) * y) * ((x : X) * y)⁻¹ = α x * (x : X)⁻¹ * (α y * (y : X)⁻¹)
        rw [map_mul, mul_inv_rev]
        calc α (x : X) * α (y : X) * ((y : X)⁻¹ * (x : X)⁻¹)
            = α (x : X) * (α (y : X) * (y : X)⁻¹) * (x : X)⁻¹ := by group
          _ = α (x : X) * ((x : X)⁻¹ * (α (y : X) * (y : X)⁻¹)) := by
              rw [mul_assoc, hy]
          _ = α (x : X) * (x : X)⁻¹ * (α (y : X) * (y : X)⁻¹) := by group }
  have hker : Nat.card φ.ker = Nat.card (fixedSubgroup α) := by
    have hle : fixedSubgroup α ≤ T := fun x hx => by
      rw [hmemT]
      have hx' : α x = x := hx
      rw [hx', mul_inv_cancel]
      exact one_mem _
    refine Nat.card_congr ⟨fun x => ⟨(x : T), ?_⟩, fun x => ⟨⟨x, hle x.2⟩, ?_⟩, ?_, ?_⟩
    · have h := MonoidHom.mem_ker.mp x.2
      have h' : α ((x : T) : X) * ((x : T) : X)⁻¹ = 1 := congrArg Subtype.val h
      exact mul_inv_eq_one.mp h'
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change α (x : X) * (x : X)⁻¹ = 1
      have hx' : α (x : X) = x := x.2
      rw [hx', mul_inv_cancel]
    · intro x
      rfl
    · intro x
      rfl
  have hfac := card_ker_mul_card_range φ
  rw [hker, hTcard] at hfac
  obtain ⟨d, hd⟩ := Subgroup.card_subgroup_dvd_card φ.range
  refine ⟨d, ?_⟩
  have hr : 0 < Nat.card φ.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hr
  rw [mul_comm (Nat.card φ.range), hfac, hd]
  ring

end Fixed

section Order

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_centralizer_dvd_two_mul_card_mulAut (hL : CFSG.Open.standardComponentIsStandard L)
    {n : ℕ} {K : Type*} [Field K] (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Nat.card (centralizer ({t} : Set G)) ∣
      2 * Nat.card (MulAut (LinearFlag.projectiveSL n K)) := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  set φ := (normalizerAut e).comp (inclusion hCtN) with hφ
  have hker : Nat.card φ.ker = 2 := by
    rw [hφ, ker_normalizerAut_comp_inclusion e hCtN hKt]
    have hle : zpowers t ≤ centralizer ({t} : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ht]
  rw [← card_ker_mul_card_range φ, hker]
  exact Nat.mul_dvd_mul_left 2 (Subgroup.card_subgroup_dvd_card _)

end Order

@[expose] def FieldCoreTypeDet (n : ℕ) (K F : Type*) [Field K] [Field F] : Prop :=
  ∀ θ : MulAut (LinearFlag.projectiveSL n F), θ * θ = 1 →
    Nat.card (fixedSubgroup θ) ∣ 2 * Nat.card (MulAut (LinearFlag.projectiveSL n K)) →
    Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card (LinearFlag.projectiveSL n K) →
    Nat.card (LinearFlag.projectiveSL n K) ≤ Nat.card (perfectCore (fixedSubgroup θ))

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_of_mem_normalizer_of_fieldCoreTypeDet (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K F : Type*} [Field K] [Field F] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : FieldCoreTypeDet n K F) {M : Subgroup G}
    (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL n F) (htM : t ∈ normalizer (M : Set G)) :
    L ≤ M := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  set τ := M.normalizerMonoidHom ⟨t, htM⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one M htM (by rw [← ht]; exact pow_orderOf_eq_one t)
  set θ := MulAut.congr ψ₀ (centerQuotientAut τ) with hθ
  have hθ2 : θ * θ = 1 := by
    rw [hθ, ← map_mul, ← centerQuotientAut_mul, hτ2, centerQuotientAut_one, map_one]
  set P := perfectCore (M ⊓ centralizer ({t} : Set G)) with hP
  have hPL : P ≤ L := std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hfixτ : (fixedSubgroup τ).map M.subtype = M ⊓ centralizer ({t} : Set G) := by
    rw [hτ, F4Pilot.fixedSubgroup_normalizerMonoidHom, subgroupOf_map_subtype, inf_comm]
  have hcardfixτ : Nat.card (fixedSubgroup τ) = Nat.card (M ⊓ centralizer ({t} : Set G) :
      Subgroup G) := by
    rw [← hfixτ, card_map_of_injective M.subtype_injective]
  have hcardP : Nat.card (perfectCore (fixedSubgroup τ)) = Nat.card P := by
    rw [hP, ← hfixτ, ← CFSG.Quasithin.map_perfectCore, card_map_of_injective M.subtype_injective]
  have h1 : Nat.card (fixedSubgroup θ) ∣ 2 * Nat.card (MulAut (LinearFlag.projectiveSL n K)) := by
    rw [hθ, card_fixedSubgroup_congr]
    refine (card_fixedSubgroup_centerQuotientAut_dvd τ).trans ?_
    rw [hcardfixτ]
    exact (Subgroup.card_dvd_of_le inf_le_right).trans
      (card_centralizer_dvd_two_mul_card_mulAut hset.standard e ht hKt)
  have h2 : Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card P := by
    rw [hθ, card_perfectCore_fixedSubgroup_congr, perfectCore_fixedSubgroup_centerQuotientAut,
      ← hcardP]
    exact Subgroup.card_map_dvd _ (QuotientGroup.mk' (center M))
  have hPLcard : Nat.card P ∣ Nat.card (LinearFlag.projectiveSL n K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le hPL
  have h3 := hTD θ hθ2 h1 (h2.trans hPLcard)
  have h4 : Nat.card L ≤ Nat.card P := by
    rw [Nat.card_congr e.toEquiv]
    exact h3.trans (Nat.le_of_dvd Nat.card_pos h2)
  have hPeq : P = L := Subgroup.eq_of_le_of_card_ge hPL h4
  rw [← hPeq]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

end Reduction

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem unique_of_fieldCoreTypeDet (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : FieldCoreTypeDet (m + 1) K F) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hq : CFSG.IsQuasisimple G₀) (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  have : Group.IsPerfect G₀ := hq.1
  exact F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_le hset hOut hm ι hσ1 hσσ hfix e (mem_centralizer_of_inf_eq_zpowers hKt) ht
      hG₀ ψ h htM (le_of_mem_normalizer_of_fieldCoreTypeDet hset hOut e ht hKt hTD
        ((conjugateQuotientCenterEquiv G₀ h).symm.trans ψ) htM)

end Unique

end CFSG.SeitzReduction.LinearPilot
