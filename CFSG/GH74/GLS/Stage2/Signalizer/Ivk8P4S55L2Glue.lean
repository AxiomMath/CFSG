module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

section Glue

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem Hyp89.bAutN_pow (hf : Hyp89 p ρ K a) : bAutN K a hf.norm ^ p = 1 := by
  have hpow : (⟨a, hf.norm⟩ : ↥(normalizer (K : Set Γ))) ^ p = 1 :=
    Subtype.ext (by simpa using hf.pow_prime)
  rw [bAutN, ← map_pow, hpow, map_one]

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem Hyp89.bAutN_ne_one (hf : Hyp89 p ρ K a) : bAutN K a hf.norm ≠ 1 := by
  have : Group.IsPerfect ↥K := hf.quasi.1
  intro h1
  have hc : a ∈ centralizer (K : Set Γ) := (YCfg.yAct_eq_one_iff K ⟨a, hf.norm⟩).mp h1
  apply hf.acts
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hcom : Commute a x := (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  exact (hcom.zpow_left n).eq

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem Hyp89.bAutN_orderOf (hf : Hyp89 p ρ K a) : orderOf (bAutN K a hf.norm) = p := by
  have : Fact p.Prime := ⟨hf.prime⟩
  exact orderOf_eq_prime hf.bAutN_pow hf.bAutN_ne_one

theorem Hyp89.no_invariant_of_E1 (hf : Hyp89 p ρ K a) (hE1 : CrossE1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hY : OddChev r (↥K ⧸ center ↥K)) :
    ∀ E : Subgroup (↥K ⧸ center ↥K), IsPGroup r ↥E → (∀ x ∈ E, bAutN K a hf.norm x ∈ E) →
      E = ⊥ := by
  have hrord : ¬ r ∣ orderOf (bAutN K a hf.norm) := by
    rw [hf.bAutN_orderOf]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hf.prime).mp h)
  refine hE1 r (↥K ⧸ center ↥K) hY (bAutN K a hf.norm) hf.bAutN_ne_one hrord ?_
  intro E hEp hEinv x hx
  by_contra hne
  exact hf.false_of_hhobsAt (fun h => absurd h hr2) ⟨hr, hrp, E, hEp, fun h => absurd h hr2, hEinv,
    x, hx, hne⟩

theorem Hyp89.l2_inner (hf : Hyp89 p ρ K a) (hE1 : CrossE1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hL : FL2d r (↥K ⧸ center ↥K)) :
    ∃ y : ↥K ⧸ center ↥K, bAutN K a hf.norm = MulAut.conj y := by
  obtain ⟨f, hf1, hmod⟩ := hL
  have hno := hf.no_invariant_of_E1 hE1 hr hr2 hrp ⟨hr, hr2, Or.inl ⟨f, hf1, hmod⟩⟩
  obtain ⟨y, hy⟩ := l2_inner_of_no_invariant hr hr2 hf.prime hf.odd hmod hf.bAutN_ne_one
    hf.bAutN_pow hno
  exact ⟨y, hy.symm⟩

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem Hyp89.exists_inner_decomp (hf : Hyp89 p ρ K a) {y : ↥K ⧸ center ↥K}
    (hy : bAutN K a hf.norm = MulAut.conj y) :
    ∃ (yh : ↥K) (c : Γ), (QuotientGroup.mk yh : ↥K ⧸ center ↥K) = y ∧
      c ∈ centralizer (K : Set Γ) ∧ a = (yh : Γ) * c := by
  have : Group.IsPerfect ↥K := hf.quasi.1
  obtain ⟨yh, rfl⟩ := QuotientGroup.mk_surjective y
  have hyhN : ((yh : Γ)⁻¹) ∈ normalizer (K : Set Γ) :=
    (normalizer (K : Set Γ)).inv_mem (le_normalizer yh.2)
  set c : Γ := (yh : Γ)⁻¹ * a with hc
  have hcN : c ∈ normalizer (K : Set Γ) := (normalizer (K : Set Γ)).mul_mem hyhN hf.norm
  refine ⟨yh, c, rfl, ?_, by rw [hc]; group⟩
  have h1 : YCfg.yAct K ⟨c, hcN⟩ = 1 := by
    have e1 : (⟨c, hcN⟩ : ↥(normalizer (K : Set Γ))) =
        ⟨(yh : Γ)⁻¹, hyhN⟩ * ⟨a, hf.norm⟩ := rfl
    rw [e1, map_mul]
    have e2 : YCfg.yAct K ⟨(yh : Γ)⁻¹, hyhN⟩ = (YCfg.yAct K ⟨(yh : Γ), le_normalizer yh.2⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e2, YCfg.yAct_of_mem K yh, YCfg.innHom_apply]
    have e3 : YCfg.yAct K ⟨a, hf.norm⟩ = bAutN K a hf.norm := rfl
    rw [e3, hy, inv_mul_cancel]
  exact (YCfg.yAct_eq_one_iff K ⟨c, hcN⟩).mp h1

end Glue

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
