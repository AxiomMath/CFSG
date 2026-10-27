module

public import CFSG.FeitThompson.Representations.OddDimCyclicActionFixedVector
public import CFSG.FeitThompson.Representations.ExtraspecialCyclicRestriction
public import CFSG.FeitThompson.Representations.ComplementConjEndomorphismBasisOrbits
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module SemidirectProduct

universe u v w

variable {p r : ℕ} {P H : Type u} [Group P] [Group H] {α : H →* MulAut P} {h : H}
  {k : Type v} [Field k] {V : Type w} [AddCommGroup V] [Module k V]
  {ρ : Representation k (P ⋊[α] H) V} {zeta : ↥(Subgroup.center P) →* kˣ}

theorem resInl_eq_comp_inl (ρ : Representation k (P ⋊[α] H) V) :
    resInl ρ = ρ.comp (SemidirectProduct.inl : P →* P ⋊[α] H) :=
  MonoidHom.ext fun x => resInl_apply ρ x

def resInr (ρ : Representation k (P ⋊[α] H) V) : Representation k H V :=
  ρ.comp (SemidirectProduct.inr : H →* P ⋊[α] H)

theorem resInr_apply (ρ : Representation k (P ⋊[α] H) V) (a : H) :
    resInr ρ a = ρ (SemidirectProduct.inr a) := (rfl)

theorem resInr_eq_comp_inr (ρ : Representation k (P ⋊[α] H) V) :
    resInr ρ = ρ.comp (SemidirectProduct.inr : H →* P ⋊[α] H) := (rfl)

theorem mem_invariants_resInr {x : V} :
    x ∈ (resInr ρ).invariants ↔ ∀ a : H, ρ (SemidirectProduct.inr a) x = x :=
  Representation.mem_invariants _ x

noncomputable def repEquivHom (ρ : Representation k (P ⋊[α] H) V) : H →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    (ρ.asGroupHom.comp (SemidirectProduct.inr : H →* P ⋊[α] H))

theorem repEquivHom_apply (ρ : Representation k (P ⋊[α] H) V) (a : H) :
    repEquivHom ρ a = repEquiv ρ a :=
  LinearEquiv.toLinearMap_injective (by rw [coe_repEquiv]; rfl)

theorem linearEquiv_zpow_apply_eq_self {T : V ≃ₗ[k] V} {x : V} (hx : T x = x) (m : ℤ) :
    (T ^ m) x = x := by
  have hn : ∀ n : ℕ, (T ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; simp [ih, hx]
  match m with
  | Int.ofNat n => simpa using hn n
  | Int.negSucc n =>
    rw [zpow_negSucc, show ((T ^ (n + 1))⁻¹ : V ≃ₗ[k] V) = (T ^ (n + 1)).symm from rfl,
      LinearEquiv.symm_apply_eq, hn]

theorem mem_invariants_resInr_of_repEquiv_fixed (hgen : Subgroup.zpowers h = ⊤) {x : V}
    (hx : repEquiv ρ h x = x) : x ∈ (resInr ρ).invariants := by
  rw [mem_invariants_resInr]
  intro a
  obtain ⟨m, hm⟩ : a ∈ Subgroup.zpowers h := by rw [hgen]; exact Subgroup.mem_top a
  have hpow : repEquiv ρ a = repEquiv ρ h ^ m := by
    rw [← repEquivHom_apply, ← hm, map_zpow, repEquivHom_apply]
  rw [← repEquiv_apply, hpow, linearEquiv_zpow_apply_eq_self hx]

theorem isCyclic_of_zpowers_eq_top (hgen : Subgroup.zpowers h = ⊤) : IsCyclic H :=
  ⟨⟨h, fun x => by rw [← Subgroup.mem_zpowers_iff, hgen]; exact Subgroup.mem_top x⟩⟩

theorem finite_of_orderOf_eq (hr : 0 < r) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤) : Finite H := by
  have hc : Nat.card H = r := by
    rw [← hho, ← Nat.card_zpowers, hgen]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  exact Nat.finite_of_card_ne_zero (by omega)

theorem exists_ne_zero_mem_invariants_resInr (hP : IsExtraspecial p P) [IsAlgClosed k]
    (hp : (p : k) ≠ 0) (hpodd : Odd p) (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    (hr : r.Prime) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    ∃ x : V, x ≠ 0 ∧ x ∈ (resInr ρ).invariants := by
  have : NeZero r := ⟨hr.ne_zero⟩
  have : NeZero ((r : k)) := ⟨hrk⟩
  have : Finite H := finite_of_orderOf_eq hr.pos hho hgen
  have : IsCyclic H := isCyclic_of_zpowers_eq_top hgen
  have hzP : ∀ (z : ↥(Subgroup.center P)) (w : V),
      ρ (SemidirectProduct.inl (z : P)) w = (zeta z : k) • w := fun z w => by
    rw [← resInl_apply]; exact hz z w
  have hirrP : (resInl ρ).IsIrreducible := by
    rw [resInl_eq_comp_inl]
    exact isIrreducible_comp_inl hP hp hirr zeta hzeta hzP
  obtain ⟨n, hn1, -, hdim⟩ := exists_finrank_eq_pow hP hp
    (by rw [← resInl_eq_comp_inl]; exact hirrP) zeta hzeta hzP
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := hpodd
    have := hP.prime.two_le
    omega
  have hV1 : 1 < finrank k V := by rw [hdim]; exact Nat.one_lt_pow (by omega) (by omega)
  have hVodd : Odd (finrank k V) := by rw [hdim]; exact hpodd.pow
  have : FiniteDimensional k V := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨ε, hε⟩ : ∃ ε : k, IsPrimitiveRoot ε r := HasEnoughRootsOfUnity.prim (M := k) (n := r)
  have hTr : repEquiv ρ h ^ r = 1 := repEquiv_pow_eq_one ρ (hho ▸ pow_orderOf_eq_one h)
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_fixed_of_finrank_conjEigenspace
    (by obtain ⟨t, ht⟩ := hrodd; have := hr.two_le; omega) hrodd hrk hε hTr hV1 hVodd
    (fun m hm => finrank_conjEigenspace_zero_eq_succ' hP hp hirrP hzeta hz hr hrk hε hho hgen
      hfix hm)
  exact ⟨x, hx0, mem_invariants_resInr_of_repEquiv_fixed hgen hx⟩

theorem invariants_resInr_ne_bot (hP : IsExtraspecial p P) [IsAlgClosed k]
    (hp : (p : k) ≠ 0) (hpodd : Odd p) (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    (hr : r.Prime) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    (resInr ρ).invariants ≠ ⊥ := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_invariants_resInr hP hp hpodd hirr hzeta hz hr hrodd
    hrk hho hgen hfix
  exact fun hbot => hx0 (Submodule.mem_bot k |>.1 (hbot ▸ hx))

end

end CFSG.FeitThompson
