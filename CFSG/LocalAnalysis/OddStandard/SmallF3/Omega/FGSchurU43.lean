module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.Open.GriessAllModelsStatement
import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.GH74.Generic.GKFBridge
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier

theorem fg_index_two_unique {A : Type} [CommGroup A] [Finite A]
    (h : Nat.card {a : A // a ^ 2 = 1} = 2) {N₁ N₂ : Subgroup A}
    (h1 : N₁.index = 2) (h2 : N₂.index = 2) : N₁ = N₂ := by
  have hker : Nat.card (powMonoidHom 2 : A →* A).ker = 2 := by
    refine Eq.trans ?_ h
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [MonoidHom.mem_ker])
  have hrange := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : A →* A)
  rw [hker] at hrange
  have hsq : ∀ N : Subgroup A, N.index = 2 → (powMonoidHom 2 : A →* A).range = N := by
    intro N hN
    have hmem : ∀ a : A, a ^ 2 ∈ N := by
      intro a
      have h1 : (QuotientGroup.mk a : A ⧸ N) ^ Nat.card (A ⧸ N) = 1 := pow_card_eq_one'
      have h2 : Nat.card (A ⧸ N) = 2 := hN
      rw [h2, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hle : (powMonoidHom 2 : A →* A).range ≤ N := by
      rintro _ ⟨a, rfl⟩
      exact hmem a
    have hcard := Subgroup.card_mul_index N
    rw [hN] at hcard
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    omega
  rw [← hsq N₁ h1, ← hsq N₂ h2]

theorem fg_nonempty_mulEquiv_of_central_covers {S E₁ E₂ : Type} [Group S] [Finite S]
    [Group.IsPerfect S] [Group E₁] [Finite E₁] [Group.IsPerfect E₁] [Group E₂] [Finite E₂]
    [Group.IsPerfect E₂] (p₁ : E₁ →* S) (hp₁ : Function.Surjective p₁)
    (hc₁ : p₁.ker ≤ center E₁) (hk₁ : Nat.card p₁.ker = 2) (p₂ : E₂ →* S)
    (hp₂ : Function.Surjective p₂) (hc₂ : p₂.ker ≤ center E₂) (hk₂ : Nat.card p₂.ker = 2)
    (hM : ∀ N₁ N₂ : Subgroup (hopfMultiplier S), N₁.index = 2 → N₂.index = 2 → N₁ = N₂) :
    Nonempty (E₁ ≃* E₂) := by
  obtain ⟨-, h₁, hc₁', -, hs₁, -, e₁, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier p₁ hp₁ hc₁
  obtain ⟨-, h₂, hc₂', -, hs₂, -, e₂, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier p₂ hp₂ hc₂
  have hi₁ : (h₁.comp (hopfMultiplier S).subtype).ker.index = 2 := by
    rw [← hk₁]
    exact Nat.card_congr e₁.toEquiv
  have hi₂ : (h₂.comp (hopfMultiplier S).subtype).ker.index = 2 := by
    rw [← hk₂]
    exact Nat.card_congr e₂.toEquiv
  have hN := hM _ _ hi₁ hi₂
  have hker : ∀ {E : Type} [Group E] (p : E →* S) (h : HopfCover S →* E),
      p.comp h = hopfCoverMap S → ∀ x : HopfCover S, h x = 1 → x ∈ hopfMultiplier S := by
    intro E _ p h hp x hx
    change hopfCoverMap S x = 1
    rw [← hp, MonoidHom.comp_apply, hx, map_one]
  have key : ∀ x : HopfCover S, x ∈ hopfMultiplier S → (h₁ x = 1 ↔ h₂ x = 1) := by
    intro x hx
    have := Subgroup.ext_iff.mp hN ⟨x, hx⟩
    simpa [MonoidHom.mem_ker] using this
  have hkerEq : h₁.ker = h₂.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      exact (key x (hker p₁ h₁ hc₁' x h1)).mp h1
    · intro h1
      exact (key x (hker p₂ h₂ hc₂' x h1)).mpr h1
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective h₁ hs₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
      (QuotientGroup.quotientKerEquivOfSurjective h₂ hs₂))⟩

theorem fg_card_sq_u43 (a b c d : ℕ) (ha : a = 4) (hb : b = 1) (hc : c = 3) (hd : d = 3) :
    Finite ((Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d))) ∧
    Nat.card {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ 2 = 1} = 2 := by
  subst ha hb hc hd
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem fg_hopf_index_two_unique_u43 (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type}
    [Group S] (hS : CFSG.Models.LieModel S .PSU 4 3 1) :
    ∀ N₁ N₂ : Subgroup (hopfMultiplier S), N₁.index = 2 → N₂.index = 2 → N₁ = N₂ := by
  obtain ⟨-, ⟨e⟩⟩ := hGA S .PSU 4 3 1 hS
  let e' : hopfMultiplier S ≃* generic .PSU 4 3 1 × exceptional .PSU 4 3 1 :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).symm.trans e
  have hg : (genericOrders .PSU 4 3 1).1 = 4 := by
    have h : genericOrders .PSU 4 3 1 = (Nat.gcd 4 (3 ^ 1 + 1), 1) := by
      unfold genericOrders; rfl
    rw [h]
    norm_num
  have hg' : (genericOrders .PSU 4 3 1).2 = 1 := by
    have h : genericOrders .PSU 4 3 1 = (Nat.gcd 4 (3 ^ 1 + 1), 1) := by
      unfold genericOrders; rfl
    rw [h]
  have he : exceptionalOrders .PSU 4 3 1 = (3, 3) := rfl
  obtain ⟨hfin, hcard⟩ := fg_card_sq_u43 (genericOrders .PSU 4 3 1).1
    (genericOrders .PSU 4 3 1).2 (exceptionalOrders .PSU 4 3 1).1
    (exceptionalOrders .PSU 4 3 1).2 hg hg' (by rw [he]) (by rw [he])
  intro N₁ N₂ h1 h2
  let f : hopfMultiplier S →* generic .PSU 4 3 1 × exceptional .PSU 4 3 1 := e'
  have key := fg_index_two_unique (A := generic .PSU 4 3 1 × exceptional .PSU 4 3 1) hcard
    (N₁ := N₁.map f) (N₂ := N₂.map f)
    (by rw [Subgroup.index_map_equiv]; exact h1) (by rw [Subgroup.index_map_equiv]; exact h2)
  exact Subgroup.map_injective e'.injective key

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fg_finite_omegaGroup (hQ : Q.Nondegenerate) : Finite (omegaGroup hQ) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ he => LinearEquiv.ext (congrFun he))
  haveI : Finite (OGroup Q) :=
    Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective
  infer_instance

private theorem fg_ker_omegaToProj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    (omegaToProj hQ).ker ≤ center (omegaGroup hQ) ∧ Nat.card (omegaToProj hQ).ker = 2 := by
  haveI := fg_finite_omegaGroup hQ
  have hpi : piOrth Q ∈ omegaGroup hQ := ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs
  let p : omegaGroup hQ := ⟨piOrth Q, hpi⟩
  have hp2 : p * p = 1 := Subtype.ext (by
    change piOrth Q * piOrth Q = 1
    exact piOrth_mul_self)
  have hp1 : p ≠ 1 := fun h =>
    piOrth_ne_one (by omega) (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h)
  have hpker : p ∈ (omegaToProj hQ).ker := by
    rw [MonoidHom.mem_ker]
    exact (omegaToProj_eq_one_iff hQ p).mpr (Or.inr rfl)
  have hle : (omegaToProj hQ).ker ≤ center (omegaGroup hQ) := fun m hm =>
    Subgroup.mem_center_iff.mpr (fun g =>
      omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g)
  refine ⟨hle, ?_⟩
  have hzle : Subgroup.zpowers p ≤ (omegaToProj hQ).ker := Subgroup.zpowers_le.mpr hpker
  have hzcard : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hp2) hp1
  have h1 : Nat.card (omegaToProj hQ).ker ≤ 2 := by
    rw [← natCard_center_omegaGroup_six_minus hQ hdim hs]
    exact Subgroup.card_le_of_le hle
  have h2 : 2 ≤ Nat.card (omegaToProj hQ).ker := by
    rw [← hzcard]
    exact Nat.card_le_card_of_injective
      (fun x : Subgroup.zpowers p => (⟨(x : omegaGroup hQ), hzle x.2⟩ : (omegaToProj hQ).ker))
      (fun x y h => Subtype.ext
        (congrArg (fun z : (omegaToProj hQ).ker => (z : omegaGroup hQ)) h))
  omega

theorem fg_asc82SchurU43_of_index_two_unique
    (hM : ∀ {S : Type} [Group S], CFSG.Blueprint.LieModel S .PSU 4 3 1 →
      ∀ N₁ N₂ : Subgroup (hopfMultiplier S), N₁.index = 2 → N₂.index = 2 → N₁ = N₂) :
    Asc82SchurU43 := by
  intro Y _ _ hY hT
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := isOmegaStar_of_lieModel_psu hT.2
  letI := i1
  letI := i2
  letI := i3
  haveI := fg_finite_omegaGroup hQ
  haveI : Finite ↥(omegaProj hQ) :=
    Finite.of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)
  haveI : Group.IsPerfect (omegaGroup hQ) := (isQuasisimple_omegaGroup_six_minus hQ hdim hs).1
  haveI : Group.IsPerfect ↥(omegaProj hQ) :=
    Group.IsPerfect.ofSurjective (omegaToProj_surjective hQ)
  let p₁ : Y →* ↥(omegaProj hQ) := e.toMonoidHom.comp (QuotientGroup.mk' (center Y))
  have hp₁ : Function.Surjective p₁ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₁ : p₁.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨hc₂, hk₂⟩ := fg_ker_omegaToProj hQ hdim hs
  obtain ⟨f⟩ := fg_nonempty_mulEquiv_of_central_covers p₁ hp₁ hker₁.le
    (by rw [hker₁]; exact hT.1) (omegaToProj hQ) (omegaToProj_surjective hQ) hc₂ hk₂
    (hM (CFSG.Blueprint.LieModel.of_mulEquiv e hT.2))
  exact ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨f⟩⟩

theorem fg_asc82SchurU43 (hGA : CFSG.Open.GriessAllModelsStatement) : Asc82SchurU43 :=
  fg_asc82SchurU43_of_index_two_unique fun hS =>
    fg_hopf_index_two_unique_u43 hGA
      (CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hS)

end CFSG.OddStandard.SmallF3.Omega
