module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Representations.TypePFittingInducedWitness
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
public import CFSG.FeitThompson.Representations.OddDiagonalGroupFixedMovingDualOrbits
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
public import CFSG.FeitThompson.Representations.FixedFreeKernelMovingCharacterPair
public import Mathlib.Tactic.Monotonicity.Lemmas

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep03
  (IsAmbient IsPConfigSetup cent conjSub hallCoreIn fittingIn)
open CFSG.FeitThompson.Prep05
  (IsMinimalSimpleOdd hallCoreOf fittingOf centralizerIn indBetween extendZero IsConjModule
    IsInvariantSubmodule IsIrreducibleLinear)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u v

variable {G : Type*} [Group G]

namespace NoFittingInducedWitness

theorem hallCoreIn_eq_hallCoreOf (M : Subgroup G) : hallCoreIn M = hallCoreOf M := (rfl)

theorem fittingIn_eq_fittingOf [Finite G] (M : Subgroup G) : fittingIn M = fittingOf M := (rfl)

theorem cent_eq_centralizerIn (X Y : Subgroup G) :
    cent X (Y : Set G) = centralizerIn X Y := (rfl)

@[expose] noncomputable def fittingEquiv [Finite G] (M : Subgroup G) :
    ↥(fittingRaw ↥M) ≃* ↥(fittingOf M) :=
  (fittingRaw ↥M).equivMapOfInjective M.subtype (Subgroup.subtype_injective M)

theorem fittingEquiv_coe [Finite G] (M : Subgroup G) (x : ↥(fittingRaw ↥M)) :
    ((fittingEquiv M x : ↥(fittingOf M)) : G) = ((x : ↥M) : G) := (rfl)

theorem mem_fittingOf_iff [Finite G] (M : Subgroup G) (z : ↥M) :
    ((z : G) ∈ fittingOf M) ↔ z ∈ fittingRaw ↥M := by
  rw [CFSG.FeitThompson.Prep05.fittingOf_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective M)).1 (by simpa using h)
  · simpa using Subgroup.mem_map_of_mem (M.subtype) h

theorem indBetween_eq_indClassFun_of_map [Fintype G] (L : Subgroup G) (K : Subgroup ↥L)
    (N : Subgroup G) (e : ↥K ≃* ↥N) (he : ∀ x : ↥K, ((e x : ↥N) : G) = ((x : ↥L) : G))
    (hmem : ∀ z : ↥L, ((z : G) ∈ N) ↔ z ∈ K) (θ : ↥N → ℂ) :
    indBetween N L θ = indClassFun K (θ ∘ e) := by
  classical
  have hNK : N.subgroupOf L = K := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact hmem z
  funext y
  rw [CFSG.FeitThompson.indBetween_eq_indClassFun_extendZero,
    indClassFun_apply, indClassFun_apply]
  have hcard : Nat.card ↥(N.subgroupOf L) = Nat.card ↥K := by rw [hNK]
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hz : (t⁻¹ * y * t : ↥L) ∈ K
  · have hz' : (t⁻¹ * y * t : ↥L) ∈ N.subgroupOf L := by rw [hNK]; exact hz
    rw [dif_pos hz, dif_pos hz']
    have hzN : ((t⁻¹ * y * t : ↥L) : G) ∈ N := (hmem _).2 hz
    rw [show extendZero θ (((⟨(t⁻¹ * y * t : ↥L), hz'⟩ : ↥(N.subgroupOf L)) : ↥L) : G)
        = θ ⟨((t⁻¹ * y * t : ↥L) : G), hzN⟩ from
      CFSG.FeitThompson.extendZero_coe θ ⟨_, hzN⟩]
    exact congrArg θ (Subtype.ext (he ⟨_, hz⟩).symm)
  · have hz' : (t⁻¹ * y * t : ↥L) ∉ N.subgroupOf L := by rw [hNK]; exact hz
    rw [dif_neg hz, dif_neg hz']

theorem indBetween_fittingOf [Fintype G] (M : Subgroup G) (θ : ↥(fittingOf M) → ℂ) :
    indBetween (fittingOf M) M θ = indClassFun (fittingRaw ↥M) (θ ∘ fittingEquiv M) :=
  indBetween_eq_indClassFun_of_map M (fittingRaw ↥M) (fittingOf M) (fittingEquiv M)
    (fittingEquiv_coe M) (mem_fittingOf_iff M) θ

theorem centralizerIn_eq_bot_of_no_witness
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Fintype G]
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1) :
    centralizerIn U (hallCoreOf M) = ⊥ := by
  by_contra hne
  obtain ⟨ψ, hψirr, hψ1, β, -, -, lam, -, hlam, hlamirr, -, -, hker⟩ :=
    FNI_type_p_fitting_induced_witness h₁ G hG M U W₁ W₂ hM hc (Nat.card ↥W₁)
      ((centralizerIn U (hallCoreOf M)).relIndex U) rfl rfl hne
  refine hno ⟨ψ ∘ fittingEquiv M, FrobeniusInduction.mem_Irr_comp_mulEquiv hψirr (fittingEquiv M),
    by simpa using hψ1, ?_, ?_⟩
  · rw [← indBetween_fittingOf, ← hlam]; exact hlamirr
  · rw [← indBetween_fittingOf, ← hlam]; exact hker

theorem fittingOf_eq_hallCoreOf_of_centralizerIn_eq_bot
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hC : centralizerIn U (hallCoreOf M) = ⊥) :
    fittingOf M = hallCoreOf M := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFdir, -, -, -⟩ :=
    h₁ G hG M U W₁ W₂ hM hc (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have h := hFdir.sup_eq
  rw [hC, sup_bot_eq] at h
  exact h.symm

section Diagonal

open Module

variable {p q : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem pow_apply_mod {b : V ≃ₗ[ZMod p] V} (hbq : b ^ q = 1) (n : ℕ) :
    (b : V ≃ₗ[ZMod p] V) ^ n = b ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, hbq, one_pow, one_mul]

theorem val_finRotate_pow [NeZero q] (n : ℕ) (i : Fin q) :
    (((finRotate q) ^ n) i).val = (i.val + n) % q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  induction n generalizing i with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, finRotate_apply, ih (i + 1), Fin.val_add]
    have h1 : (1 : Fin q).val = 1 % q := rfl
    have hone : (1 % q) ≡ 1 [MOD q] := Nat.mod_mod _ _
    rw [h1]
    calc ((i.val + 1 % q) % q + n) % q
        = (i.val + 1 % q + n) % q := by rw [Nat.mod_add_mod]
      _ = (i.val + 1 + n) % q := Nat.ModEq.add_right n (Nat.ModEq.add_left _ hone)
      _ = (i.val + (n + 1)) % q := by ring_nf

theorem pow_smul_mem_line {b : V ≃ₗ[ZMod p] V} {L : Fin q → Submodule (ZMod p) V}
    (hLb : ∀ i, (L i).map (b : V →ₗ[ZMod p] V) = L (finRotate q i))
    {i₀ : Fin q} {v₀ : V} (hv₀ : v₀ ∈ L i₀) (n : ℕ) :
    (b ^ n) v₀ ∈ L (((finRotate q) ^ n) i₀) := by
  induction n with
  | zero => simpa using hv₀
  | succ n ih =>
    have hb : (b ^ (n + 1)) v₀ = b ((b ^ n) v₀) := by rw [pow_succ']; rfl
    rw [hb, pow_succ', Equiv.Perm.mul_apply, ← hLb (((finRotate q) ^ n) i₀)]
    exact ⟨_, ih, rfl⟩

theorem exists_rotBasis [NeZero q] [FiniteDimensional (ZMod p) V]
    {b : V ≃ₗ[ZMod p] V} (hbq : b ^ q = 1)
    {L : Fin q → Submodule (ZMod p) V}
    (hLrank : ∀ i, finrank (ZMod p) ↥(L i) = 1)
    (hLind : iSupIndep L) (hLsup : (⨆ i, L i) = ⊤)
    (hLb : ∀ i, (L i).map (b : V →ₗ[ZMod p] V) = L (finRotate q i)) :
    ∃ e : Basis (ZMod q) (ZMod p) V, shift e = b ∧ ∀ i : ZMod q, ∃ j : Fin q, e i ∈ L j := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hL0 : L (0 : Fin q) ≠ ⊥ := by
    intro h
    have := hLrank (0 : Fin q)
    rw [h] at this
    simp at this
  obtain ⟨v₀, hv₀mem, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  set w : ZMod q → V := fun i => (b ^ i.val) v₀ with hw
  set j : ZMod q → Fin q := fun i => ((finRotate q) ^ i.val) (0 : Fin q) with hj
  have hjval : ∀ i : ZMod q, (j i).val = i.val := by
    intro i
    rw [hj, val_finRotate_pow]
    simpa using Nat.mod_eq_of_lt (ZMod.val_lt i)
  have hjinj : Function.Injective j := fun a c hac =>
    ZMod.val_injective q (by rw [← hjval a, ← hjval c, hac])
  have hwmem : ∀ i, w i ∈ (L ∘ j) i := fun i => pow_smul_mem_line hLb hv₀mem i.val
  have hwne : ∀ i, w i ≠ 0 := fun i h =>
    hv₀ne ((LinearEquiv.map_eq_zero_iff (b ^ i.val)).1 h)
  have hli : LinearIndependent (ZMod p) w :=
    iSupIndep.linearIndependent (L ∘ j) (hLind.comp hjinj) hwmem hwne
  have hjsurj : Function.Surjective j :=
    ((Fintype.bijective_iff_injective_and_card j).2 ⟨hjinj, by simp⟩).2
  have hspan : (⊤ : Submodule (ZMod p) V) ≤ Submodule.span (ZMod p) (Set.range w) := by
    rw [← hLsup]
    refine iSup_le fun k => ?_
    obtain ⟨i, rfl⟩ := hjsurj k
    have hle : (ZMod p ∙ w i) ≤ L (j i) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (hwmem i)
    have heq : (ZMod p ∙ w i) = L (j i) :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton (hwne i), hLrank])
    rw [← heq]
    exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Basis.mk hli hspan, ?_, fun i => ⟨j i, by rw [Basis.mk_apply]; exact hwmem i⟩⟩
  refine LinearEquiv.toLinearMap_injective ((Basis.mk hli hspan).ext fun i => ?_)
  show shift (Basis.mk hli hspan) ((Basis.mk hli hspan) i) = b ((Basis.mk hli hspan) i)
  rw [shift_basis, Basis.mk_apply, Basis.mk_apply, hw]
  show (b ^ (i + 1).val) v₀ = b ((b ^ i.val) v₀)
  have hval : (i + 1).val % q = (i.val + 1) % q := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod]
    exact Nat.ModEq.add_left _ (Nat.mod_mod _ _)
  calc (b ^ (i + 1).val) v₀
      = (b ^ ((i + 1).val % q)) v₀ := by rw [← pow_apply_mod hbq]
    _ = (b ^ ((i.val + 1) % q)) v₀ := by rw [hval]
    _ = (b ^ (i.val + 1)) v₀ := by rw [← pow_apply_mod hbq]
    _ = b ((b ^ i.val) v₀) := by rw [pow_succ']; rfl

theorem exists_dual_trivialStabilizer [NeZero q] [FiniteDimensional (ZMod p) V]
    (hq : q.Prime) (hp : Odd p)
    {D : Subgroup (V ≃ₗ[ZMod p] V)} (hDodd : Odd (Nat.card ↥D)) (hqD : ¬ q ∣ Nat.card ↥D)
    {b : V ≃ₗ[ZMod p] V} (hbq : b ^ q = 1)
    (hbD : ∀ d : V ≃ₗ[ZMod p] V, b * d * b⁻¹ ∈ D ↔ d ∈ D)
    (hcent : ∀ d ∈ D, d * b = b * d → d = 1)
    {L : Fin q → Submodule (ZMod p) V}
    (hLrank : ∀ i, finrank (ZMod p) ↥(L i) = 1)
    (hLind : iSupIndep L) (hLsup : (⨆ i, L i) = ⊤)
    (hLb : ∀ i, (L i).map (b : V →ₗ[ZMod p] V) = L (finRotate q i))
    (hdiag : ∀ g ∈ D, ∃ c : Fin q → ZMod p, ∀ i, ∀ v ∈ L i, g v = c i • v) :
    ∃ ℓ : Module.Dual (ZMod p) V, ℓ ≠ 0 ∧
      ∀ d ∈ D, ∀ n : ℕ, (d * b ^ n) • ℓ = ℓ → d = 1 ∧ (b : V ≃ₗ[ZMod p] V) ^ n = 1 := by
  classical
  obtain ⟨e, hshift, hmem⟩ := exists_rotBasis hbq hLrank hLind hLsup hLb
  have hD : D ≤ diagAutSubgroup e := by
    intro g hg
    obtain ⟨c, hc⟩ := hdiag g hg
    refine mem_diagAutSubgroup_iff.2 fun i => ?_
    obtain ⟨j, hj⟩ := hmem i
    exact ⟨c j, hc j _ hj⟩
  have hconj : ∀ d : V ≃ₗ[ZMod p] V, shift e * d * (shift e)⁻¹ ∈ D ↔ d ∈ D := by
    rw [hshift]; exact hbD
  have hcent' : ∀ d : ↥D, (d : V ≃ₗ[ZMod p] V) * shift e = shift e * d → d = 1 := by
    intro d hd
    rw [hshift] at hd
    exact Subtype.ext (hcent (d : V ≃ₗ[ZMod p] V) d.2 hd)
  obtain ⟨-, ℓ₁, hℓ₁⟩ :=
    exists_fixed_and_moving_fullSupportDual e hD hconj hq hqD hcent' hp hDodd
  have hne : (ℓ₁ : Module.Dual (ZMod p) V) ≠ 0 := by
    intro h
    exact (mem_fullSupportDual.1 ℓ₁.2) 0 (by rw [h]; rfl)
  refine ⟨(ℓ₁ : Module.Dual (ZMod p) V), hne, ?_⟩
  intro d hd n hfix
  set hbsm := shiftDualPerm_smul e hD hconj with hbsmdef
  have hstep : ((shiftDualPerm e hD) ^ n) ℓ₁ = (⟨d, hd⟩ : ↥D)⁻¹ • ℓ₁ := by
    refine Subtype.ext ?_
    rw [coe_shiftDualPerm_pow, coe_smul_fullSupportDual]
    have hdb : (d * (shift e) ^ n) • (ℓ₁ : Module.Dual (ZMod p) V) = ℓ₁ := by
      rw [hshift]; exact hfix
    rw [mul_smul] at hdb
    calc ((shift e) ^ n) • (ℓ₁ : Module.Dual (ZMod p) V)
        = d⁻¹ • (d • (((shift e) ^ n) • (ℓ₁ : Module.Dual (ZMod p) V))) := by
          rw [← mul_smul, inv_mul_cancel, one_smul]
      _ = d⁻¹ • (ℓ₁ : Module.Dual (ZMod p) V) := by rw [hdb]
  have hper : Function.IsPeriodicPt
      (CoprimeFreeAction.orbitQuotientPerm hbsm) n (Quotient.mk'' ℓ₁) := by
    have h1 : ((CoprimeFreeAction.orbitQuotientPerm hbsm) ^ n) (Quotient.mk'' ℓ₁)
        = Quotient.mk'' (((shiftDualPerm e hD) ^ n) ℓ₁) :=
      CoprimeFreeAction.orbitQuotientPerm_pow_mk hbsm n ℓ₁
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow, h1, hstep]
    exact Quotient.sound' (MulAction.mem_orbit _ _)
  have hqmin : Function.minimalPeriod
      (CoprimeFreeAction.orbitQuotientPerm hbsm) (Quotient.mk'' ℓ₁) = q := by
    have hpq : Function.IsPeriodicPt
        (CoprimeFreeAction.orbitQuotientPerm hbsm) q (Quotient.mk'' ℓ₁) := by
      rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow,
        CoprimeFreeAction.orbitQuotientPerm_pow_eq_one hbsm (shiftDualPerm_pow_eq_one e hD)]
      rfl
    have : Fact q.Prime := ⟨hq⟩
    exact Function.minimalPeriod_eq_prime hpq hℓ₁
  obtain ⟨m, rfl⟩ : q ∣ n := hqmin ▸ hper.minimalPeriod_dvd
  have hbn : (b : V ≃ₗ[ZMod p] V) ^ (q * m) = 1 := by rw [pow_mul, hbq, one_pow]
  refine ⟨?_, hbn⟩
  rw [hbn, mul_one] at hfix
  have hfix' : (⟨d, hd⟩ : ↥D) • ℓ₁ = ℓ₁ :=
    Subtype.ext (by rw [coe_smul_fullSupportDual]; exact hfix)
  exact congrArg Subtype.val (eq_one_of_smul_eq_self _ _ hfix')

end Diagonal

noncomputable def hallChar {G : Type*} [Group G] {M : Subgroup G} {p : ℕ} [NeZero p]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hHM : hallCoreOf M ≤ M)
    (e : ↥(hallCoreOf M) ≃* Multiplicative V) (ℓ : Module.Dual (ZMod p) V) :
    ↥((hallCoreOf M).subgroupOf M) →* ℂˣ :=
  (FixedFreeImage.dualChar ℓ).comp
    ((e : ↥(hallCoreOf M) →* Multiplicative V).comp
      ((subgroupOfEquivOfLe hHM : ↥((hallCoreOf M).subgroupOf M) ≃* ↥(hallCoreOf M)) :
        ↥((hallCoreOf M).subgroupOf M) →* ↥(hallCoreOf M)))

theorem hallChar_apply {G : Type*} [Group G] {M : Subgroup G} {p : ℕ} [NeZero p]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hHM : hallCoreOf M ≤ M)
    (e : ↥(hallCoreOf M) ≃* Multiplicative V) (ℓ : Module.Dual (ZMod p) V)
    (x : ↥((hallCoreOf M).subgroupOf M)) :
    hallChar hHM e ℓ x = FixedFreeImage.dualChar ℓ (e (subgroupOfEquivOfLe hHM x)) := (rfl)

theorem exists_hallChar_ne_one {G : Type*} [Group G] {M : Subgroup G} {p : ℕ} [NeZero p]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hHM : hallCoreOf M ≤ M)
    (e : ↥(hallCoreOf M) ≃* Multiplicative V) {ℓ : Module.Dual (ZMod p) V} (hℓ : ℓ ≠ 0) :
    ∃ x : ↥((hallCoreOf M).subgroupOf M), hallChar hHM e ℓ x ≠ 1 := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  refine ⟨(subgroupOfEquivOfLe hHM).symm (e.symm (Multiplicative.ofAdd v)), ?_⟩
  rw [hallChar_apply]
  simp only [MulEquiv.apply_symm_apply]
  exact fun hc => hv ((FixedFreeImage.dualChar_eq_one_iff ℓ v).1 hc)

theorem smul_dual_eq_of_mem_inertiaGroup {G : Type*} [Group G] {M : Subgroup G} {p : ℕ}
    [Fact p.Prime] [NeZero p] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hHM : hallCoreOf M ≤ M)
    [((hallCoreOf M).subgroupOf M).Normal]
    {e : ↥(hallCoreOf M) ≃* Multiplicative V} {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}
    (hρ : IsConjModule p (hallCoreOf M) M V e ρ)
    (ℓ : Module.Dual (ZMod p) V) {t : ↥M}
    (ht : t ∈ inertiaGroup ((hallCoreOf M).subgroupOf M)
      (fun x => (hallChar hHM e ℓ x : ℂ))) :
    ρ t • ℓ = ℓ := by
  have hfun : ∀ n : ↥((hallCoreOf M).subgroupOf M),
      (hallChar hHM e ℓ (MulAut.conjNormal t⁻¹ n) : ℂ) = (hallChar hHM e ℓ n : ℂ) :=
    fun n => by
      have h := congrFun (mem_inertiaGroup.1 ht) n
      rwa [NormalInduction.conjClassFun_apply] at h
  refine LinearMap.ext fun v => ?_
  set h : ↥(hallCoreOf M) := e.symm (Multiplicative.ofAdd v) with hh
  set n : ↥((hallCoreOf M).subgroupOf M) := (subgroupOfEquivOfLe hHM).symm h with hn
  have hev : e h = Multiplicative.ofAdd v := by rw [hh, MulEquiv.apply_symm_apply]
  have hcoe : ((subgroupOfEquivOfLe hHM (MulAut.conjNormal t⁻¹ n) : ↥(hallCoreOf M)) : G)
      = (t : G)⁻¹ * (h : G) * (t : G) := by
    show (((MulAut.conjNormal t⁻¹ n : ↥((hallCoreOf M).subgroupOf M)) : ↥M) : G) = _
    rw [NormalInduction.coe_conjNormal_inv]
    rfl
  have hmem : (t : G)⁻¹ * (h : G) * (t : G) ∈ hallCoreOf M := by
    rw [← hcoe]
    exact (subgroupOfEquivOfLe hHM (MulAut.conjNormal t⁻¹ n)).2
  have hconj : e (subgroupOfEquivOfLe hHM (MulAut.conjNormal t⁻¹ n))
      = Multiplicative.ofAdd (ρ t⁻¹ v) := by
    have h1 : subgroupOfEquivOfLe hHM (MulAut.conjNormal t⁻¹ n)
        = ⟨(t : G)⁻¹ * (h : G) * (t : G), hmem⟩ := Subtype.ext hcoe
    rw [h1, hρ.conj_inv_eq t h hmem, hev]
    rfl
  have hval := hfun n
  rw [hallChar_apply, hallChar_apply, hconj, hn, MulEquiv.apply_symm_apply, hev,
    FixedFreeImage.dualChar_apply, FixedFreeImage.dualChar_apply] at hval
  have hz : ℓ (ρ t⁻¹ v) = ℓ v :=
    FixedFreeImage.zmodCharUnit_ofAdd_inj (Units.ext hval)
  show ℓ ((ρ t).symm v) = ℓ v
  have hsymm : (ρ t).symm v = ρ t⁻¹ v := by
    rw [map_inv]
    rfl
  rw [hsymm, hz]

private theorem isIrreducibleLinear_of_no_witness
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (hM : IsPConfigSetup G M U W₁ W₂)
    (hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1)
    (hF : fittingIn M = hallCoreIn M)
    {p : ℕ} (hp : p = Nat.card ↥W₂)
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V]
    (e : ↥(hallCoreOf M) ≃* Multiplicative V) {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}
    (hρ : IsConjModule p (hallCoreOf M) M V e ρ) :
    IsIrreducibleLinear ((U.subgroupOf M).map ρ) := by
  classical
  have hG : IsMinimalSimpleOdd G :=
    ⟨hM.ambient.odd_natCard, hM.ambient.isSimpleGroup, hM.ambient.not_isMulCommutative,
      hM.ambient.forall_isSolvable⟩
  obtain ⟨hDne, hDab, hDcard, huodd, huq, hBcard, hDB, hfixB, hirrDB, hxor, huN⟩ :=
    FNI_type_p_core_linear_alternative h₁ G hG M U W₁ W₂ hM.isCoatom hM.config
      p (Nat.card ↥W₁) ((centralizerIn U (hallCoreOf M)).relIndex U)
      ((p ^ Nat.card ↥W₁ - 1) / (p - 1)) hp rfl rfl rfl V e ρ hρ
      ((U.subgroupOf M).map ρ) ((W₁.subgroupOf M).map ρ) rfl rfl
  rcases hxor with ⟨hdiag, -⟩ | ⟨hfield, -⟩
  ·
    exfalso
    obtain ⟨-, L, hLinv, hLrank, hLind, hLsup, ⟨b, hbB, hLb⟩, -, hdiagscal⟩ := hdiag
    obtain ⟨-, hpp, hqp, hop, -, -, -, -, hsemiM, hsemiUW, -, -, -, hHcard, -, -, -, -, -, -, -,
      -, -, -⟩ := h₁ G hG M U W₁ W₂ hM.isCoatom hM.config p (Nat.card ↥W₁) hp rfl
    have : Fact p.Prime := ⟨hpp⟩
    have : NeZero p := ⟨hpp.pos.ne'⟩
    have : NeZero (Nat.card ↥W₁) := ⟨hqp.pos.ne'⟩
    have hHM : hallCoreOf M ≤ M := hsemiM.left_le
    have hbne : b ≠ 1 := by
      intro hb1
      have h0 : L 0 = L (finRotate (Nat.card ↥W₁) 0) := by
        have := hLb 0
        rwa [hb1, show ((1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = LinearMap.id from rfl,
          Submodule.map_id] at this
      have hne : (0 : Fin (Nat.card ↥W₁)) ≠ finRotate (Nat.card ↥W₁) 0 := by
        intro hcon
        have hval := val_finRotate_pow (q := Nat.card ↥W₁) 1 (0 : Fin (Nat.card ↥W₁))
        rw [pow_one, ← hcon] at hval
        simp at hval
        rw [← Nat.card_eq_fintype_card] at hval
        exact hqp.ne_one hval
      have hbot : L 0 ⊓ L (finRotate (Nat.card ↥W₁) 0) = ⊥ :=
        disjoint_iff.1 (hLind.pairwiseDisjoint hne)
      rw [← h0, inf_idem] at hbot
      have := hLrank 0
      rw [hbot] at this
      simp at this
    have : Finite V := Finite.of_equiv _ e.toEquiv
    have : Finite (V ≃ₗ[ZMod p] V) :=
      Finite.of_injective (fun f : V ≃ₗ[ZMod p] V => (f : V → V)) fun _ _ h =>
        LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => congrFun h v)
    have hqD : ¬ Nat.card ↥W₁ ∣ Nat.card ↥(Subgroup.map ρ (U.subgroupOf M)) := by
      rw [hDcard]
      exact fun hdvd => hqp.ne_one (huq.symm.eq_one_of_dvd hdvd)
    have hbq : b ^ Nat.card ↥W₁ = 1 := by
      have hb := pow_card_eq_one' (G := ↥(Subgroup.map ρ (W₁.subgroupOf M))) (x := ⟨b, hbB⟩)
      rw [hBcard] at hb
      exact congrArg Subtype.val hb
    have hBgen : Subgroup.zpowers b = Subgroup.map ρ (W₁.subgroupOf M) := by
      have hle : Subgroup.zpowers b ≤ Subgroup.map ρ (W₁.subgroupOf M) :=
        (Subgroup.zpowers_le).2 hbB
      have horder : orderOf b = Nat.card ↥W₁ := by
        have hdvd : orderOf b ∣ Nat.card ↥W₁ := orderOf_dvd_of_pow_eq_one hbq
        rcases (Nat.Prime.eq_one_or_self_of_dvd hqp _ hdvd) with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hbne
        · exact h
      have hcard : Nat.card ↥(Subgroup.map ρ (W₁.subgroupOf M)) ≤ Nat.card ↥(Subgroup.zpowers b) := by
        rw [hBcard, Nat.card_zpowers, horder]
      exact Subgroup.eq_of_le_of_card_ge hle hcard
    have hcent : ∀ d ∈ Subgroup.map ρ (U.subgroupOf M), d * b = b * d → d = 1 := by
      intro d hd hdb
      have hmem : d ∈ Subgroup.map ρ (U.subgroupOf M) ⊓
          centralizer ((Subgroup.map ρ (W₁.subgroupOf M) : Subgroup (V ≃ₗ[ZMod p] V)) :
            Set (V ≃ₗ[ZMod p] V)) := by
        refine ⟨hd, ?_⟩
        rw [← hBgen]
        intro x hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact (Commute.zpow_left (Commute.symm hdb) n)
      rw [hDB] at hmem
      simpa using hmem
    obtain ⟨wb, hwbmem, hwb⟩ := Subgroup.mem_map.1 hbB
    have hUnorm : ∀ x : ↥M, x ∈ U.subgroupOf M → ∀ w : ↥M, w ∈ W₁.subgroupOf M →
        w * x * w⁻¹ ∈ U.subgroupOf M := by
      intro x hx w hw
      have hwn := hsemiUW.right_le_normalizer (Subgroup.mem_subgroupOf.1 hw)
      have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.1 hx
      have hconj := (Subgroup.mem_normalizer_iff.1 hwn (x : G)).1 hxU
      rw [Subgroup.mem_subgroupOf]
      simpa using hconj
    have hbD : ∀ d : V ≃ₗ[ZMod p] V,
        b * d * b⁻¹ ∈ Subgroup.map ρ (U.subgroupOf M) ↔ d ∈ Subgroup.map ρ (U.subgroupOf M) := by
      intro d
      constructor
      · rintro ⟨x, hx, hxd⟩
        refine ⟨wb⁻¹ * x * wb, ?_, ?_⟩
        · simpa using hUnorm x hx wb⁻¹ (inv_mem hwbmem)
        · rw [map_mul, map_mul, map_inv, hwb, hxd]
          group
      · rintro ⟨x, hx, rfl⟩
        refine ⟨wb * x * wb⁻¹, hUnorm x hx wb hwbmem, ?_⟩
        rw [map_mul, map_mul, map_inv, hwb]
    have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
    obtain ⟨ℓ, hℓne, hℓstab⟩ := exists_dual_trivialStabilizer hqp hop
      (D := Subgroup.map ρ (U.subgroupOf M)) (by rw [hDcard]; exact huodd) hqD hbq hbD hcent
      hLrank hLind hLsup hLb (fun g hg => (hdiagscal g hg).imp fun c hc => hc.1)
    have hHab : ∀ x y : ↥(hallCoreOf M), x * y = y * x := fun x y =>
      e.injective (by rw [map_mul, map_mul, mul_comm])
    have hrhoH : ∀ x : ↥M, (x : G) ∈ hallCoreOf M → ρ x = 1 := by
      intro x hx
      refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => ?_)
      have hmem : (x : G) * ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) * (x : G)⁻¹
          ∈ hallCoreOf M :=
        (hallCoreOf M).mul_mem
          ((hallCoreOf M).mul_mem hx (e.symm (Multiplicative.ofAdd v)).2) (inv_mem hx)
      have hcomm : (x : G) * ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G)
          = ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) * (x : G) :=
        congrArg Subtype.val (hHab ⟨(x : G), hx⟩ (e.symm (Multiplicative.ofAdd v)))
      have hval : (x : G) * ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) * (x : G)⁻¹
          = ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have heq : (⟨(x : G) * ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) * (x : G)⁻¹,
          hmem⟩ : ↥(hallCoreOf M)) = e.symm (Multiplicative.ofAdd v) := Subtype.ext hval
      have hconj := hρ.conj_eq x (e.symm (Multiplicative.ofAdd v)) hmem
      have hkey : e (e.symm (Multiplicative.ofAdd v))
          = Multiplicative.ofAdd
            (ρ x (Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd v))))) :=
        (congrArg e heq).symm.trans hconj
      rw [MulEquiv.apply_symm_apply] at hkey
      exact (congrArg Multiplicative.toAdd hkey).symm
    have hC : centralizerIn U (hallCoreOf M) = ⊥ :=
      centralizerIn_eq_bot_of_no_witness h₁ hG hM.isCoatom hM.config hno
    have hinjOn : ∀ K : Subgroup G, K ≤ M →
        Nat.card ↥K = Nat.card ↥(Subgroup.map ρ (K.subgroupOf M)) →
        ∀ x : ↥M, x ∈ K.subgroupOf M → ρ x = 1 → x = 1 := by
      intro K hKM hcard x hx hx1
      have hcard' : Nat.card ↥(K.subgroupOf M) = Nat.card ↥(Subgroup.map ρ (K.subgroupOf M)) := by
        rw [← hcard, Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
      set f : ↥(K.subgroupOf M) → ↥(Subgroup.map ρ (K.subgroupOf M)) :=
        fun z => ⟨ρ (z : ↥M), Subgroup.mem_map_of_mem _ z.2⟩ with hf
      have hsurj : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
        exact ⟨⟨z, hz⟩, rfl⟩
      have hbij : Function.Bijective f := (Nat.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard'⟩
      have hfx : f ⟨x, hx⟩ = f 1 := by
        refine Subtype.ext ?_
        simpa [hf] using hx1
      exact congrArg Subtype.val (hbij.1 hfx)
    have hUM : U ≤ M := le_trans hsemiUW.left_le hsemiM.right_le
    have hW₁M : W₁ ≤ M := le_trans hsemiUW.right_le hsemiM.right_le
    have hinjU : ∀ x : ↥M, x ∈ U.subgroupOf M → ρ x = 1 → x = 1 :=
      hinjOn U hUM (by rw [hDcard, hC, Subgroup.relIndex_bot_left])
    have hinjW : ∀ x : ↥M, x ∈ W₁.subgroupOf M → ρ x = 1 → x = 1 :=
      hinjOn W₁ hW₁M hBcard.symm
    have hNnorm : ((hallCoreOf M).subgroupOf M).Normal := hsemiM.normal_subgroupOf
    have hinert : inertiaGroup ((hallCoreOf M).subgroupOf M)
        (fun x => (hallChar hHM e ℓ x : ℂ)) ≤ (hallCoreOf M).subgroupOf M := by
      intro t ht
      have hstab := smul_dual_eq_of_mem_inertiaGroup hHM hρ ℓ ht
      obtain ⟨a, ha, y, hy, hty⟩ := hsemiM.exists_mul t.2
      obtain ⟨uu, huu, w, hw, hyw⟩ := hsemiUW.exists_mul hy
      have hUmem : (⟨uu, hUM huu⟩ : ↥M) ∈ U.subgroupOf M := Subgroup.mem_subgroupOf.2 huu
      have hWmem : (⟨w, hW₁M hw⟩ : ↥M) ∈ W₁.subgroupOf M := Subgroup.mem_subgroupOf.2 hw
      have hdecomp : t = (⟨a, hHM ha⟩ : ↥M) * ⟨uu, hUM huu⟩ * ⟨w, hW₁M hw⟩ := by
        refine Subtype.ext ?_
        rw [hty, hyw]
        simp [mul_assoc]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, b ^ n = ρ ⟨w, hW₁M hw⟩ :=
        (mem_powers_iff_mem_zpowers).2 (by rw [hBgen]; exact Subgroup.mem_map_of_mem _ hWmem)
      have hρt : ρ t = ρ ⟨uu, hUM huu⟩ * b ^ n := by
        rw [hdecomp, map_mul, map_mul, hrhoH _ ha, one_mul, hn]
      have hfixℓ : (ρ (⟨uu, hUM huu⟩ : ↥M) * b ^ n) • ℓ = ℓ := by rw [← hρt]; exact hstab
      obtain ⟨hd1, hb1⟩ := hℓstab _ (Subgroup.mem_map_of_mem _ hUmem) n hfixℓ
      have huu1 : uu = 1 := congrArg Subtype.val (hinjU _ hUmem hd1)
      have hw1 : w = 1 := congrArg Subtype.val (hinjW _ hWmem (by rw [← hn]; exact hb1))
      have hta : (t : G) = a := by rw [hty, hyw, huu1, hw1]; simp
      rw [Subgroup.mem_subgroupOf, hta]
      exact ha
    have hFsub : fittingOf M = hallCoreOf M := hF
    have hsub : fittingRaw ↥M = (hallCoreOf M).subgroupOf M := by
      ext z
      rw [Subgroup.mem_subgroupOf, ← mem_fittingOf_iff, hFsub]
    rw [hsub] at hno
    obtain ⟨x₀, hx₀⟩ := exists_hallChar_ne_one hHM e hℓne
    refine hno ⟨fun x => (hallChar hHM e ℓ x : ℂ),
      SolvableNormalLayer.coe_monoidHom_units_mem_Irr _, by simp,
      indClassFun_coe_mem_Irr_of_inertiaGroup_le _ hinert, ?_⟩
    intro hall
    have hmem : ∀ x : ↥M, x⁻¹ * ((x₀ : ↥M)) * x ∈ (hallCoreOf M).subgroupOf M := fun x => by
      simpa [mul_assoc] using hNnorm.conj_mem _ x₀.2 x⁻¹
    have hne := indClassFun_apply_ne_index_of_apply_ne_one (hallChar hHM e ℓ) hmem
      (by simpa using hx₀)
    have hone : indClassFun ((hallCoreOf M).subgroupOf M)
        (fun x => (hallChar hHM e ℓ x : ℂ)) 1
        = (((hallCoreOf M).subgroupOf M).index : ℂ) := by
      rw [indClassFun_one]
      simp only [map_one, Units.val_one, mul_one]
      have hne0 : (Nat.card ↥((hallCoreOf M).subgroupOf M) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 Nat.card_pos.ne'
      rw [div_eq_iff hne0, ← Nat.cast_mul, Subgroup.index_mul_card]
    exact hne ((hall (x₀ : ↥M) (Subgroup.mem_subgroupOf.1 x₀.2)).trans hone)
  · exact hfield.1

theorem isInternalSemidirectProduct_subgroupOf {G : Type*} [Group G] {M X A B : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct X A B) (hX : X ≤ M) :
    FreeCore.IsInternalSemidirectProduct (X.subgroupOf M) (A.subgroupOf M) (B.subgroupOf M) where
  sup_eq := by
    rw [← Subgroup.subgroupOf_sup (h.left_le.trans hX) (h.right_le.trans hX), h.sup_eq]
  le_normalizer := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hn := h.le_normalizer hx
    refine Subgroup.mem_normalizer_iff.2 fun n => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.1 hn (n : G)
  disjoint := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxB
    exact Subtype.ext (Subgroup.disjoint_def.1 h.disjoint
      (Subgroup.mem_subgroupOf.1 hxA) (Subgroup.mem_subgroupOf.1 hxB))

private theorem order_equation_aux
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (hM : IsPConfigSetup G M U W₁ W₂)
    (hC : cent U (hallCoreIn M : Set G) = ⊥)
    (hF : fittingIn M = hallCoreIn M)
    (hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1)
    {p q u : ℕ} (hp : p = Nat.card ↥W₂) (hq : q = Nat.card ↥W₁)
    (hu : u = (cent U (hallCoreIn M : Set G)).relIndex U) :
    u * (p - 1) = p ^ q - 1 := by
  classical
  have hG : IsMinimalSimpleOdd G :=
    ⟨hM.ambient.odd_natCard, hM.ambient.isSimpleGroup, hM.ambient.not_isMulCommutative,
      hM.ambient.forall_isSolvable⟩
  obtain ⟨-, hpp, hqp, -, -, -, -, -, hsemiM, hsemiUW, -, hfreeUW, ⟨V, _, _, -, ⟨e⟩⟩, hHcard,
    -, hCHW, -, -, -, -, -, -, -, -⟩ := h₁ G hG M U W₁ W₂ hM.isCoatom hM.config p q hp hq
  have hC' : centralizerIn U (hallCoreOf M) = ⊥ := hC
  have hUcard : u = Nat.card ↥U := by rw [hu, hC, Subgroup.relIndex_bot_left]
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hHle : hallCoreOf M ≤ M := hsemiM.left_le
  have hUM : U ≤ M := hM.config.le_M_E
  have hW₁M : W₁ ≤ M := hM.config.le_M_W₁
  have hW₂M : W₂ ≤ M := hM.config.le_M_W₂
  have hρ : IsConjModule p (hallCoreOf M) M V e (conjLinear p hHM e) :=
    isConjModule_conjLinear p hHM e
  obtain ⟨-, -, -, -, huq, -, -, -, -, hxor, -⟩ :=
    FNI_type_p_core_linear_alternative h₁ G hG M U W₁ W₂ hM.isCoatom hM.config
      p q ((centralizerIn U (hallCoreOf M)).relIndex U)
      ((p ^ q - 1) / (p - 1)) hp hq rfl rfl V e (conjLinear p hHM e) hρ
      ((U.subgroupOf M).map (conjLinear p hHM e)) ((W₁.subgroupOf M).map (conjLinear p hHM e))
      rfl rfl
  have hirr := isIrreducibleLinear_of_no_witness h₁ hM hno hF hp e hρ
  obtain ⟨⟨hnirr, -⟩, -⟩ | ⟨⟨-, E, _, _, -, φ, -, ⟨S, -, hS⟩, -, -, -, -⟩, -⟩ := hxor
  · exact absurd hirr hnirr
  have hU' : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have hqU : ¬ q ∣ Nat.card ↥(U.subgroupOf M) := by
    rw [hC', Subgroup.relIndex_bot_left] at huq
    rw [hU']
    exact fun hdvd => hqp.ne_one (huq.symm.eq_one_of_dvd hdvd)
  obtain ⟨b, hbW, hb1⟩ : ∃ b ∈ W₁, b ≠ 1 := by
    have := hM.config.ne_bot_W₁
    rw [Subgroup.ne_bot_iff_exists_ne_one] at this
    obtain ⟨⟨b, hb⟩, hb1⟩ := this
    exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
  have hordb : orderOf b = q := by
    have hdvd : orderOf b ∣ q := hq ▸ Subgroup.orderOf_dvd_natCard W₁ hbW
    rcases hqp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hb1
    · exact h
  have hgen : zpowers b = W₁ := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hbW) ?_
    rw [Nat.card_zpowers, hordb, hq]
  have hordb' : orderOf (⟨b, hW₁M hbW⟩ : ↥M) = q := by
    rw [← Subgroup.orderOf_coe]; exact hordb
  have hHab : IsMulCommutative ↥(hallCoreOf M) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  haveI : IsMulCommutative ↥((hallCoreOf M).subgroupOf M) := isMulCommutative_subgroupOf hHab
  haveI : ((hallCoreOf M).subgroupOf M).Normal := hsemiM.normal_subgroupOf
  have hH' : Nat.card ↥((hallCoreOf M).subgroupOf M) = p ^ q :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv).trans hHcard
  have hUQ' := isInternalSemidirectProduct_subgroupOf hsemiUW hsemiM.right_le
  rw [Subgroup.subgroupOf_sup hUM hW₁M] at hUQ'
  have hM' := isInternalSemidirectProduct_subgroupOf hsemiM le_rfl
  rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hUM hW₁M] at hM'
  have hCU : U.subgroupOf M ⊓ Subgroup.centralizer {(⟨b, hW₁M hbW⟩ : ↥M)} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxb⟩
    rw [Subgroup.mem_bot]
    have hc : (x : G) * b = b * x :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hxb)
    have hx : (x : G) ∈ centralizerIn U (zpowers b) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hxU, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_right hc n).symm
    rw [hfreeUW b hbW hb1, Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  have hCH : Nat.card ↥((hallCoreOf M).subgroupOf M ⊓
      Subgroup.centralizer {(⟨b, hW₁M hbW⟩ : ↥M)}) = p := by
    have heq : (hallCoreOf M).subgroupOf M ⊓ Subgroup.centralizer {(⟨b, hW₁M hbW⟩ : ↥M)}
        = W₂.subgroupOf M := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hCHW,
        CFSG.FeitThompson.Prep05.centralizerIn_eq, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
      refine and_congr_right fun _ => ⟨fun hxb => ?_, fun hx => ?_⟩
      · intro g hg
        rw [← hgen] at hg
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have hc : (x : G) * b = b * x := congrArg Subtype.val hxb
        exact (Commute.zpow_right hc n).symm
      · exact Subtype.ext (hx b hbW).symm
    rw [heq, hp]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₂M).toEquiv
  have hUH : ∀ x ∈ U.subgroupOf M, x ≠ 1 →
      (hallCoreOf M).subgroupOf M ⊓ Subgroup.centralizer {x} = ⊥ := by
    intro x hxU hx1
    rw [eq_bot_iff]
    rintro y ⟨hyH, hyx⟩
    rw [Subgroup.mem_bot]
    by_contra hy1
    set h : ↥(hallCoreOf M) := ⟨(y : G), Subgroup.mem_subgroupOf.1 hyH⟩ with hhdef
    have hfix : conjLinear p hHM e x (Multiplicative.toAdd (e h)) = Multiplicative.toAdd (e h) :=
      (rho_apply_eq_self_iff hρ hHM x h).2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyx)).symm
    obtain ⟨s, -, hs⟩ := (hS (conjLinear p hHM e x)).1 (Subgroup.mem_map_of_mem _ hxU)
    have hv : Multiplicative.toAdd (e h) ≠ 0 := by
      intro h0
      apply hy1
      have he1 : e h = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
      have hh1 : h = 1 := e.injective (he1.trans (map_one e).symm)
      have hval : ((h : ↥(hallCoreOf M)) : G) = 1 := by rw [hh1]; rfl
      exact Subtype.ext hval
    have hφv : φ (Multiplicative.toAdd (e h)) ≠ 0 := fun h0 => hv (φ.map_eq_zero_iff.1 h0)
    have hs1 : (s : E) = 1 := by
      have h2 := hs (Multiplicative.toAdd (e h))
      rw [hfix] at h2
      exact mul_right_cancel₀ hφv (h2.symm.trans (one_mul _).symm)
    have hρ1 : conjLinear p hHM e x = 1 := by
      refine LinearEquiv.ext fun v => φ.injective ?_
      rw [hs v, hs1, one_mul]
      rfl
    have hxC : ((x : ↥M) : G) ∈ centralizerIn U (hallCoreOf M) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hxU, (rho_eq_one_iff hρ hHM x).1 hρ1⟩
    rw [hC', Subgroup.mem_bot] at hxC
    exact hx1 (Subtype.ext hxC)
  have hsub : fittingRaw ↥M = (hallCoreOf M).subgroupOf M := by
    ext z
    rw [Subgroup.mem_subgroupOf, ← mem_fittingOf_iff, show fittingOf M = hallCoreOf M from hF]
  have hno' : ∀ θ : ↥(nonprincipalIrr ↥((hallCoreOf M).subgroupOf M)),
      indClassFun ((hallCoreOf M).subgroupOf M) (θ : ↥((hallCoreOf M).subgroupOf M) → ℂ)
        ∉ Irr ↥M := by
    rw [hsub] at hno
    intro θ hθ
    obtain ⟨hθirr, hθ1⟩ := mem_nonprincipalIrr.1 θ.2
    obtain ⟨χ, hχ⟩ := exists_monoidHom_coe_eq_of_mem_Irr hθirr
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, (θ : ↥((hallCoreOf M).subgroupOf M) → ℂ) x₀ ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hθ1 (funext hcon)
    refine hno ⟨θ, hθirr, apply_one_eq_one_of_mem_Irr hθirr, hθ, ?_⟩
    intro hall
    have hNnorm : ((hallCoreOf M).subgroupOf M).Normal := inferInstance
    have hmem : ∀ x : ↥M, x⁻¹ * ((x₀ : ↥M)) * x ∈ (hallCoreOf M).subgroupOf M := fun x => by
      simpa [mul_assoc] using hNnorm.conj_mem _ x₀.2 x⁻¹
    have hne := indClassFun_apply_ne_index_of_apply_ne_one χ hmem (by
      rw [← hχ] at hx₀; simpa using hx₀)
    rw [hχ] at hne
    have hone : indClassFun ((hallCoreOf M).subgroupOf M)
        (θ : ↥((hallCoreOf M).subgroupOf M) → ℂ) 1
        = (((hallCoreOf M).subgroupOf M).index : ℂ) := by
      rw [indClassFun_one, apply_one_eq_one_of_mem_Irr hθirr, mul_one]
      have hne0 : (Nat.card ↥((hallCoreOf M).subgroupOf M) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 Nat.card_pos.ne'
      rw [div_eq_iff hne0, ← Nat.cast_mul, Subgroup.index_mul_card]
    exact hne ((hall (x₀ : ↥M) (Subgroup.mem_subgroupOf.1 x₀.2)).trans hone)
  have key := FreeCore.natCard_eq_of_no_induced_irr (M := ↥M)
    (H := (hallCoreOf M).subgroupOf M) (U := U.subgroupOf M) (Q := W₁.subgroupOf M)
    (b := ⟨b, hW₁M hbW⟩) hpp.two_le hqp hordb' (subgroupOf_eq_zpowers hW₁M hbW hgen)
    hUQ' hM' hH' hqU hCU hCH hUH hno'
  rw [hUcard, ← hU', key, Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p q)]

private theorem minimality_aux
    (_h₁ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (_hM : IsPConfigSetup G M U W₁ W₂)
    (_hC : cent U (hallCoreIn M : Set G) = ⊥)
    (_hF : fittingIn M = hallCoreIn M)
    (_hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1)
    {p q u : ℕ} (_hp : p = Nat.card ↥W₂) (_hq : q = Nat.card ↥W₁)
    (_hu : u = (cent U (hallCoreIn M : Set G)).relIndex U) :
    ∀ N : Subgroup G, N ≤ hallCoreIn M →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → (∀ x ∈ N, x ^ p = 1) →
      (∀ g ∈ U, conjSub N g = N) → N = ⊥ ∨ N = hallCoreIn M := by
  classical
  intro N hNH _ _ hNinv
  have hG : IsMinimalSimpleOdd G :=
    ⟨_hM.ambient.odd_natCard, _hM.ambient.isSimpleGroup, _hM.ambient.not_isMulCommutative,
      _hM.ambient.forall_isSolvable⟩
  obtain ⟨-, hpp, -, -, -, -, -, -, -, -, -, -, hVex, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    _h₁ G hG M U W₁ W₂ _hM.isCoatom _hM.config p (Nat.card ↥W₁) _hp rfl
  have : Fact p.Prime := ⟨hpp⟩
  have : NeZero p := ⟨hpp.pos.ne'⟩
  obtain ⟨V, _, _, -, ⟨e⟩⟩ := hVex
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hρ := isConjModule_conjLinear p hHM e
  have hirr := isIrreducibleLinear_of_no_witness _h₁ _hM _hno _hF _hp e hρ
  have hpow : ∀ (v : V) (n : ℕ), e.symm (Multiplicative.ofAdd (n • v))
      = (e.symm (Multiplicative.ofAdd v)) ^ n := by
    intro v n
    rw [ofAdd_nsmul, map_pow]
  let W : Submodule (ZMod p) V :=
    { carrier := {v | ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) ∈ N}
      zero_mem' := by
        show ((e.symm (Multiplicative.ofAdd 0) : ↥(hallCoreOf M)) : G) ∈ N
        rw [ofAdd_zero, map_one]
        exact N.one_mem
      add_mem' := by
        intro a b ha hb
        show ((e.symm (Multiplicative.ofAdd (a + b)) : ↥(hallCoreOf M)) : G) ∈ N
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        exact N.mul_mem ha hb
      smul_mem' := by
        intro c v hv
        show ((e.symm (Multiplicative.ofAdd (c • v)) : ↥(hallCoreOf M)) : G) ∈ N
        have hc : c • v = c.val • v := by
          conv_lhs => rw [← ZMod.natCast_zmod_val c]
          exact Nat.cast_smul_eq_nsmul (ZMod p) c.val v
        rw [hc, hpow, Subgroup.coe_pow]
        exact N.pow_mem hv _ }
  have hmemW : ∀ v : V,
      v ∈ W ↔ ((e.symm (Multiplicative.ofAdd v) : ↥(hallCoreOf M)) : G) ∈ N := fun _ => Iff.rfl
  have hWinv : IsInvariantSubmodule ((U.subgroupOf M).map (conjLinear p hHM e)) W := by
    rintro g ⟨x, hx, rfl⟩ v hv
    rw [hmemW] at hv ⊢
    set h : ↥(hallCoreOf M) := e.symm (Multiplicative.ofAdd v) with hh
    have hxU : ((x : G))⁻¹ ∈ U := inv_mem (Subgroup.mem_subgroupOf.1 hx)
    have hconjN : (x : G) * (h : G) * (x : G)⁻¹ ∈ N := by
      have h1 := hNinv _ hxU
      rw [← h1]
      refine ⟨(h : G), hv, ?_⟩
      simp [MulAut.conj_apply]
    have hc : (x : G) * (h : G) * (x : G)⁻¹ ∈ hallCoreOf M := hNH hconjN
    have key := hρ.conj_eq x h hc
    have hev : Multiplicative.toAdd (e h) = v := by rw [hh, MulEquiv.apply_symm_apply]; rfl
    rw [hev] at key
    have : e.symm (Multiplicative.ofAdd (conjLinear p hHM e x v))
        = ⟨(x : G) * (h : G) * (x : G)⁻¹, hc⟩ := by
      rw [← key, MulEquiv.symm_apply_apply]
    rw [this]
    exact hconjN
  rcases hirr W hWinv with hW | hW
  · left
    refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
    have hnH : n ∈ hallCoreOf M := hNH hn
    have hv : Multiplicative.toAdd (e ⟨n, hnH⟩) ∈ W := by
      rw [hmemW]
      simpa using hn
    rw [hW, Submodule.mem_bot] at hv
    have h1 : e ⟨n, hnH⟩ = 1 := hv
    have h2 : (⟨n, hnH⟩ : ↥(hallCoreOf M)) = 1 := by
      rw [← map_eq_one_iff e e.injective]; exact h1
    exact congrArg Subtype.val h2
  · right
    refine le_antisymm hNH fun n hnH => ?_
    have hv : Multiplicative.toAdd (e ⟨n, hnH⟩) ∈ W := by rw [hW]; trivial
    rw [hmemW] at hv
    simpa using hv

private theorem field_identification_aux
    (_h₁ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (_hM : IsPConfigSetup G M U W₁ W₂)
    (_hC : cent U (hallCoreIn M : Set G) = ⊥)
    (_hF : fittingIn M = hallCoreIn M)
    (_hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1)
    {p q u : ℕ} (_hp : p = Nat.card ↥W₂) (_hq : q = Nat.card ↥W₁)
    (_hu : u = (cent U (hallCoreIn M : Set G)).relIndex U) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (ι : ↥(hallCoreIn M) → E),
      Nat.card E = p ^ q ∧ Function.Bijective ι ∧
      (∀ x y : ↥(hallCoreIn M), ι (x * y) = ι x + ι y) ∧
      (∀ g ∈ U, ∃ a : E,
        a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 ∧
        ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
          ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
      (∀ a : E, a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 →
        ∃ g ∈ U, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
          ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
      (∀ w ∈ W₁, ∃ φ : E ≃+* E,
        (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) ∧
        ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
          ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩)) ∧
      ∀ φ : E ≃+* E, (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) →
        ∃ w ∈ W₁, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
          ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩) := by
  classical
  have hG : IsMinimalSimpleOdd G :=
    ⟨_hM.ambient.odd_natCard, _hM.ambient.isSimpleGroup, _hM.ambient.not_isMulCommutative,
      _hM.ambient.forall_isSolvable⟩
  obtain ⟨-, hpp, hqp, -, -, -, -, -, -, -, -, -, ⟨V, _, _, -, ⟨e⟩⟩, -, -, -, -, -, -, -, -, -,
    -, -⟩ := _h₁ G hG M U W₁ W₂ _hM.isCoatom _hM.config p q _hp _hq
  have : Fact p.Prime := ⟨hpp⟩
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hρ := isConjModule_conjLinear p hHM e
  set ρ := conjLinear p hHM e with hρdef
  obtain ⟨-, -, hDcard, -, -, -, -, -, -, hxor, -⟩ :=
    FNI_type_p_core_linear_alternative _h₁ G hG M U W₁ W₂ _hM.isCoatom _hM.config
      p q ((centralizerIn U (hallCoreOf M)).relIndex U)
      ((p ^ q - 1) / (p - 1)) _hp _hq rfl rfl V e ρ hρ
      ((U.subgroupOf M).map ρ) ((W₁.subgroupOf M).map ρ) rfl rfl
  have hirr := isIrreducibleLinear_of_no_witness _h₁ _hM _hno _hF _hp e hρ
  obtain ⟨⟨hnirr, -⟩, -⟩ | ⟨⟨-, E', _, _, hcardE', φ, -, ⟨S, -, hS⟩, hB, -, -, -⟩, -⟩ := hxor
  · exact absurd hirr hnirr
  have hcount := order_equation_aux _h₁ _hM _hC _hF _hno _hp _hq _hu
  have hsum : ∑ k ∈ Finset.range q, p ^ k = u := by
    rw [Nat.geomSum_eq hpp.two_le]
    exact Nat.div_eq_of_eq_mul_left (by have := hpp.two_le; omega) hcount.symm
  have hDu : Nat.card ↥((U.subgroupOf M).map ρ) = u := by
    rw [hDcard, _hu]; rfl
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have h1 : 1 < p ^ q := Nat.one_lt_pow hqp.ne_zero hpp.one_lt
    omega
  let ψ : E' ≃ₐ[ZMod p] GaloisField p q := GaloisField.algEquivGaloisField p q hcardE'
  have hconj : ∀ (x : ↥M) (g : G), (x : G) = g⁻¹ → ∀ (h : G) (hh : h ∈ hallCoreOf M)
      (hc : g⁻¹ * h * g ∈ hallCoreOf M),
      Multiplicative.toAdd (e ⟨g⁻¹ * h * g, hc⟩) = ρ x (Multiplicative.toAdd (e ⟨h, hh⟩)) := by
    rintro ⟨x, hxM⟩ g hxg h hh hc
    simp only at hxg
    subst hxg
    have hc' : ((⟨g⁻¹, hxM⟩ : ↥M) : G) * ((⟨h, hh⟩ : ↥(hallCoreOf M)) : G) *
        ((⟨g⁻¹, hxM⟩ : ↥M) : G)⁻¹ ∈ hallCoreOf M := by simpa using hc
    have key := hρ.conj_eq ⟨g⁻¹, hxM⟩ ⟨h, hh⟩ hc'
    have heq : (⟨g⁻¹ * h * g, hc⟩ : ↥(hallCoreOf M)) = ⟨_, hc'⟩ := Subtype.ext (by simp)
    rw [heq, key]
    rfl
  have hpow : ∀ (g : V ≃ₗ[ZMod p] V) (s : E'), (∀ v, φ (g v) = s * φ v) →
      ∀ n : ℕ, ∀ v, φ ((g ^ n) v) = s ^ n * φ v := by
    intro g s hs n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [pow_succ, LinearEquiv.mul_apply, ih, hs, pow_succ]; ring
  have hroot : ∀ g ∈ (U.subgroupOf M).map ρ, ∀ s : E', (∀ v, φ (g v) = s * φ v) → s ^ u = 1 := by
    intro g hg s hs
    have h1 : g ^ u = 1 := by
      have := pow_card_eq_one' (G := ↥((U.subgroupOf M).map ρ)) (x := ⟨g, hg⟩)
      rw [hDu] at this
      exact congrArg Subtype.val this
    have h2 := hpow g s hs u (φ.symm 1)
    rw [h1] at h2
    simpa using h2.symm
  have hval : ∀ (g : V ≃ₗ[ZMod p] V) (s : E'), (∀ v, φ (g v) = s * φ v) →
      φ (g (φ.symm 1)) = s := by
    intro g s hs
    rw [hs, LinearEquiv.apply_symm_apply, mul_one]
  have hall : ∀ t : E', t ^ u = 1 →
      ∃ g ∈ (U.subgroupOf M).map ρ, ∀ v, φ (g v) = t * φ v := by
    intro t ht
    have : Finite ↥((U.subgroupOf M).map ρ) :=
      Nat.finite_of_card_ne_zero (by rw [hDu]; exact hu0)
    have : Fintype ↥((U.subgroupOf M).map ρ) := Fintype.ofFinite _
    let f : ↥((U.subgroupOf M).map ρ) → E' := fun g => φ ((g : V ≃ₗ[ZMod p] V) (φ.symm 1))
    have hfinj : Function.Injective f := by
      intro g₁ g₂ h12
      obtain ⟨s₁, -, hs₁⟩ := (hS g₁).1 g₁.2
      obtain ⟨s₂, -, hs₂⟩ := (hS g₂).1 g₂.2
      have e1 : f g₁ = s₁ := hval _ _ hs₁
      have e2 : f g₂ = s₂ := hval _ _ hs₂
      have hs : (s₁ : E') = s₂ := e1.symm.trans (h12.trans e2)
      refine Subtype.ext (LinearEquiv.ext fun v => φ.injective ?_)
      rw [hs₁, hs₂, hs]
    have hsub : Finset.univ.image f ⊆ Polynomial.nthRootsFinset u (1 : E') := by
      intro x hx
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨s, -, hs⟩ := (hS g).1 g.2
      rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hu0)]
      have e1 : f g = s := hval _ _ hs
      rw [e1]
      exact hroot g g.2 s hs
    have hcard : (Polynomial.nthRootsFinset u (1 : E')).card ≤ (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
        hDu]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots u 1)
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have htmem : t ∈ Polynomial.nthRootsFinset u (1 : E') :=
      (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hu0) 1).2 ht
    rw [← heq] at htmem
    obtain ⟨g, -, hgt⟩ := Finset.mem_image.1 htmem
    obtain ⟨s, -, hs⟩ := (hS g).1 g.2
    have e1 : f g = s := hval _ _ hs
    refine ⟨g, g.2, fun v => ?_⟩
    rw [hs, ← e1, hgt]
  refine ⟨GaloisField p q, inferInstance, Fintype.ofFinite _,
    fun h => ψ (φ (Multiplicative.toAdd (e h))), GaloisField.card p q hqp.ne_zero,
    (ψ.bijective.comp φ.bijective).comp (Multiplicative.toAdd.bijective.comp e.bijective),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    show ψ (φ (Multiplicative.toAdd (e (x * y))))
      = ψ (φ (Multiplicative.toAdd (e x))) + ψ (φ (Multiplicative.toAdd (e y)))
    have h1 : e (x * y) = e x * e y := map_mul e x y
    rw [h1, toAdd_mul, map_add, map_add]
  · intro g hg
    have hgM : g ∈ M := _hM.config.le_M_E hg
    have hmem : ρ ⟨g⁻¹, inv_mem hgM⟩ ∈ (U.subgroupOf M).map ρ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (inv_mem hg))
    obtain ⟨s, -, hs⟩ := (hS _).1 hmem
    refine ⟨ψ s, ?_, ?_⟩
    · rw [hsum, ← map_pow, hroot _ hmem s hs, map_one]
    · intro h hh hc
      show ψ (φ (Multiplicative.toAdd (e ⟨g⁻¹ * h * g, hc⟩)))
        = ψ s * ψ (φ (Multiplicative.toAdd (e ⟨h, hh⟩)))
      rw [hconj ⟨g⁻¹, inv_mem hgM⟩ g rfl h hh hc, hs, map_mul]
  · intro a ha
    rw [hsum] at ha
    have ht : (ψ.symm a) ^ u = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨g, hgD, hgv⟩ := hall _ ht
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hgD
    refine ⟨(x : G)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 hx), ?_⟩
    intro h hh hc
    show ψ (φ (Multiplicative.toAdd (e ⟨(x : G)⁻¹⁻¹ * h * (x : G)⁻¹, hc⟩)))
      = a * ψ (φ (Multiplicative.toAdd (e ⟨h, hh⟩)))
    rw [hconj x (x : G)⁻¹ (inv_inv _).symm h hh hc, hgv, map_mul, AlgEquiv.apply_symm_apply]
  · intro w hw
    have hwM : w ∈ M := _hM.config.le_M_W₁ hw
    have hmem : ρ ⟨w⁻¹, inv_mem hwM⟩ ∈ (W₁.subgroupOf M).map ρ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (inv_mem hw))
    obtain ⟨σ, hσ⟩ := (hB _).1 hmem
    refine ⟨(ψ.symm.trans (σ.trans ψ)).toRingEquiv, ?_, ?_⟩
    · rintro c ⟨n, rfl⟩
      exact map_natCast _ n
    · intro h hh hc
      show ψ (φ (Multiplicative.toAdd (e ⟨w⁻¹ * h * w, hc⟩)))
        = (ψ.symm.trans (σ.trans ψ)).toRingEquiv (ψ (φ (Multiplicative.toAdd (e ⟨h, hh⟩))))
      rw [hconj ⟨w⁻¹, inv_mem hwM⟩ w rfl h hh hc, hσ]
      simp
  · intro φE _
    have hφE : ∀ c : ZMod p, φE (algebraMap (ZMod p) (GaloisField p q) c)
        = algebraMap (ZMod p) (GaloisField p q) c := fun c =>
      RingHom.congr_fun (RingHom.ext_zmod
        ((φE : GaloisField p q →+* GaloisField p q).comp (algebraMap (ZMod p) _))
        (algebraMap (ZMod p) _)) c
    let φA : GaloisField p q ≃ₐ[ZMod p] GaloisField p q := AlgEquiv.ofRingEquiv hφE
    let σ' : E' ≃ₐ[ZMod p] E' := ψ.trans (φA.trans ψ.symm)
    let b : V ≃ₗ[ZMod p] V := φ.trans (σ'.toLinearEquiv.trans φ.symm)
    have hbB : b ∈ (W₁.subgroupOf M).map ρ := (hB b).2 ⟨σ', fun v => by simp [b]⟩
    obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.1 hbB
    refine ⟨(x : G)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 hx), ?_⟩
    intro h hh hc
    show ψ (φ (Multiplicative.toAdd (e ⟨(x : G)⁻¹⁻¹ * h * (x : G)⁻¹, hc⟩)))
      = φE (ψ (φ (Multiplicative.toAdd (e ⟨h, hh⟩))))
    rw [hconj x (x : G)⁻¹ (inv_inv _).symm h hh hc, hxb]
    simp [b, σ', φA]

private theorem field_alternative_aux
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (hM : IsPConfigSetup G M U W₁ W₂)
    (hC : cent U (hallCoreIn M : Set G) = ⊥)
    (hF : fittingIn M = hallCoreIn M)
    (hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1)
    {p q u : ℕ} (hp : p = Nat.card ↥W₂) (hq : q = Nat.card ↥W₁)
    (hu : u = (cent U (hallCoreIn M : Set G)).relIndex U) :
    u * (p - 1) = p ^ q - 1 ∧
      (∀ N : Subgroup G, N ≤ hallCoreIn M →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → (∀ x ∈ N, x ^ p = 1) →
      (∀ g ∈ U, conjSub N g = N) → N = ⊥ ∨ N = hallCoreIn M) ∧
      ∃ (E : Type) (_ : Field E) (_ : Fintype E) (ι : ↥(hallCoreIn M) → E),
      Nat.card E = p ^ q ∧ Function.Bijective ι ∧
      (∀ x y : ↥(hallCoreIn M), ι (x * y) = ι x + ι y) ∧
      (∀ g ∈ U, ∃ a : E,
        a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 ∧
        ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
          ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
      (∀ a : E, a ^ (∑ k ∈ Finset.range q, p ^ k) = 1 →
        ∃ g ∈ U, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : g⁻¹ * h * g ∈ hallCoreIn M),
          ι ⟨g⁻¹ * h * g, hc⟩ = a * ι ⟨h, hh⟩) ∧
      (∀ w ∈ W₁, ∃ φ : E ≃+* E,
        (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) ∧
        ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
          ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩)) ∧
      ∀ φ : E ≃+* E, (∀ c : E, (∃ n : ℕ, c = (n : E)) → φ c = c) →
        ∃ w ∈ W₁, ∀ (h : G) (hh : h ∈ hallCoreIn M) (hc : w⁻¹ * h * w ∈ hallCoreIn M),
          ι ⟨w⁻¹ * h * w, hc⟩ = φ (ι ⟨h, hh⟩) :=
  ⟨order_equation_aux h₁ hM hC hF hno hp hq hu,
    minimality_aux h₁ hM hC hF hno hp hq hu,
    field_identification_aux h₁ hM hC hF hno hp hq hu⟩

end NoFittingInducedWitness

open NoFittingInducedWitness

theorem FCH_type_p_no_fitting_induced_witness
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FCH_type_p_no_fitting_induced_witness.{u} := by
  intro G _ _ hG M U W₁ W₂ hM p q u hp hq hu hno
  have hG' : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₁ G hG' M U W₁ W₂ hM.isCoatom hM.config p q hp hq
  have hC : cent U (hallCoreIn M : Set G) = ⊥ :=
    centralizerIn_eq_bot_of_no_witness h₁ hG' hM.isCoatom hM.config hno
  have hF : fittingIn M = hallCoreIn M :=
    fittingOf_eq_hallCoreOf_of_centralizerIn_eq_bot h₁ hG' hM.isCoatom hM.config hC
  obtain ⟨hcount, hmin, hfield⟩ := field_alternative_aux h₁ hM hC hF hno hp hq hu
  exact ⟨hpp, hqp, hop, hoq, hpq, hC, hF, by rw [hu, hC, Subgroup.relIndex_bot_left],
    hcount, hmin, hfield⟩

end CFSG.FeitThompson.Proofs

end
