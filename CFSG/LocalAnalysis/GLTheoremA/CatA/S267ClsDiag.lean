module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsLagrange
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {A : Type*} [CommGroup A] [Finite A]
variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module K V]

section Block

@[expose] noncomputable def scal (φ : Module.End K V) (c : K) : Module.End K V :=
  1 + (c - 1) • φ

theorem scal_apply (φ : Module.End K V) (c : K) (v : V) : scal φ c v = v + (c - 1) • φ v :=
  rfl

theorem scal_mul (φ : Module.End K V) (hφ : φ * φ = φ) (c d : K) :
    scal φ c * scal φ d = scal φ (c * d) := by
  ext v
  have hφv : φ (φ v) = φ v := by rw [← Module.End.mul_apply, hφ]
  simp only [Module.End.mul_apply, scal_apply, map_add, map_smul, hφv, smul_add, smul_smul]
  module

theorem scal_one (φ : Module.End K V) : scal φ 1 = 1 := by simp [scal]

@[expose] noncomputable def scalEquiv (φ : Module.End K V) (hφ : φ * φ = φ) {c : K} (hc : c ≠ 0) :
    V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (scal φ c) (scal φ c⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← Module.End.mul_apply, scal_mul φ hφ, mul_inv_cancel₀ hc,
        scal_one]; rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← Module.End.mul_apply, scal_mul φ hφ, inv_mul_cancel₀ hc,
        scal_one]; rfl)

theorem scalEquiv_apply (φ : Module.End K V) (hφ : φ * φ = φ) {c : K} (hc : c ≠ 0) (v : V) :
    scalEquiv φ hφ hc v = v + (c - 1) • φ v :=
  rfl

theorem scalEquiv_pow_apply (φ : Module.End K V) (hφ : φ * φ = φ) {c : K} (hc : c ≠ 0) (n : ℕ)
    (v : V) : (scalEquiv φ hφ hc ^ n) v = scal φ (c ^ n) v := by
  induction n generalizing v with
  | zero => simp [scal_one]
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, scalEquiv_apply, ← scal_apply,
      ← Module.End.mul_apply, scal_mul φ hφ, pow_succ]

theorem scal_comm (φ T : Module.End K V) (h : Commute φ T) (c : K) (v : V) :
    scal φ c (T v) = T (scal φ c v) := by
  have h' : φ (T v) = T (φ v) := by
    have := congrArg (fun f : Module.End K V => f v) h.eq
    simpa [Module.End.mul_apply] using this
  rw [scal_apply, scal_apply, map_add, map_smul, h']

end Block

section Cyclic

variable (ρ : Representation K A V)

theorem exists_pow_of_weightSpace (hp : p.Prime) {H : Hyperplane A p} {x : A} (hx : x ∉ H.1)
    (a : A) : ∃ n : ℕ, ∀ v ∈ weightSpace ρ H.1, ρ a v = ρ (x ^ n) v := by
  have htop : H.1 ⊔ Subgroup.zpowers x = ⊤ := by
    have hd := Subgroup.index_dvd_of_le (le_sup_left : H.1 ≤ H.1 ⊔ Subgroup.zpowers x)
    rw [H.2] at hd
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hle : H.1 ≤ H.1 ⊔ Subgroup.zpowers x := le_sup_left
      have h3 := Subgroup.relIndex_mul_index hle
      rw [h1, H.2] at h3
      have h4 : H.1.relIndex (H.1 ⊔ Subgroup.zpowers x) = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (h3.trans (one_mul p).symm)
      exact hx (Subgroup.relIndex_eq_one.mp h4 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top a)
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hz
  refine ⟨n, fun v hv => ?_⟩
  rw [map_mul, Module.End.mul_apply]
  exact apply_eq_of_mem_weightSpace ρ hh (apply_mem_weightSpace ρ H.1 _ hv)

theorem rho_pow_card (hA : ∀ a : A, a ^ p = 1) (hq : p ∣ Fintype.card K - 1) (a : A) :
    ρ a ^ Fintype.card K = ρ a := by
  have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
  obtain ⟨m, hm⟩ := hq
  have : a ^ Fintype.card K = a := by
    have e : Fintype.card K = p * m + 1 := by omega
    rw [e, pow_succ, pow_mul, hA, one_pow, one_mul]
  rw [← map_pow, this]

end Cyclic

section Linear

theorem exists_root_ne_one (hp : p.Prime) (hq : p ∣ Fintype.card K - 1) :
    ∃ ζ : K, ζ ^ p = 1 ∧ ζ ≠ 1 := by
  haveI := Fact.mk hp
  have hcard : p ∣ Fintype.card Kˣ := by rw [Fintype.card_units]; exact hq
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card p hcard
  refine ⟨u, by rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one], ?_⟩
  intro h1
  have : u = 1 := Units.ext h1
  rw [this, orderOf_one] at hu
  exact hp.one_lt.ne hu

variable (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

local notation "β₀" => (0 : V →ₗ[K] V →ₛₗ[RingHom.id K] K)

omit [Fintype K] [DecidableEq K] in
theorem isIsomRep_zero : IsIsomRep β₀ ρ := fun _ _ _ => rfl

include hp hA hpK

theorem finrank_weightSpace_eq_one_lin [FiniteDimensional K V] (hmax : IsMaxElem β₀ ρ p ∅)
    (hq : p ∣ Fintype.card K - 1) (H : Hyperplane A p) (hH : weightSpace ρ H.1 ≠ ⊥) :
    Module.finrank K (weightSpace ρ H.1) = 1 := by
  classical
  obtain ⟨x, hx⟩ := exists_not_mem_hyperplane hp H
  have hg : ρ x ^ Fintype.card K = ρ x := rho_pow_card ρ hA hq x
  have hW : ∀ w ∈ weightSpace ρ H.1, ρ x w ∈ weightSpace ρ H.1 :=
    fun w hw => apply_mem_weightSpace ρ H.1 x hw
  obtain ⟨c, w, hw, hw0, hgw⟩ := exists_eigenvector (ρ x) hg _ hW hH
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [one_smul] at hgw
    exact hw0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK hx hw hgw)
  have hpow : ∀ n : ℕ, ρ (x ^ n) w = c ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hgw, map_smul, ih, smul_smul,
        pow_succ']
  have hcp : c ^ p = 1 := by
    have h := hpow p
    rw [hA x, map_one, Module.End.one_apply] at h
    have h' : (c ^ p - 1) • w = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hw0)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hcp; exact zero_ne_one hcp
  set πH := ρ.asAlgebraHom (eps K A p (some H)) with hπH
  have hπHρ : ∀ a : A, Commute πH (ρ a) := fun a => by
    ext v; exact (apply_asAlgebraHom_comm ρ _ a v).symm
  have hππ : πH * πH = πH := ((orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).idem
    (some H)).eq
  have hπmem : ∀ v, πH v ∈ weightSpace ρ H.1 := fun v => ⟨v, rfl⟩
  have hπfix : ∀ v ∈ weightSpace ρ H.1, πH v = v := fun v hv =>
    eps_apply_of_mem ρ hp hA hpK (some H) hv
  have hπoff : ∀ i : Option (Hyperplane A p), i ≠ some H → ∀ v ∈ weightFamily (p := p) ρ i,
      πH v = 0 := fun i hi v hv => eps_apply_of_mem_ne ρ hp hA hpK hi.symm hv
  have hscal : ∀ u ∈ weightSpace ρ H.1, ρ x u = c • u := by
    by_contra hne
    push Not at hne
    obtain ⟨u, hu, hgu⟩ := hne
    set P := lagProj (ρ x) c
    have hPπ : Commute P πH := lagProj_comm (ρ x) πH (hπHρ x).symm c
    have hPρ : ∀ a : A, Commute P (ρ a) := fun a =>
      lagProj_comm (ρ x) (ρ a) (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]) c
    have hPP : P * P = P := by
      ext v
      rw [Module.End.mul_apply]
      exact lagProj_apply_of_eigen (ρ x) (apply_lagProj (ρ x) hg c v)
    set φ := P * πH
    have hφ : φ * φ = φ := by
      calc P * πH * (P * πH) = P * P * (πH * πH) := by
            rw [mul_assoc, ← mul_assoc πH, ← hPπ.eq, mul_assoc, mul_assoc]
        _ = P * πH := by rw [hPP, hππ]
    set y := scalEquiv φ hφ hc0
    have hPu : P u ≠ u := fun h => hgu (by rw [← h, apply_lagProj (ρ x) hg c u])
    have hPmem : P u ∈ weightSpace ρ H.1 := by
      rw [← hπfix u hu, ← Module.End.mul_apply, hPπ.eq, Module.End.mul_apply]
      exact hπmem _
    have hmem : u - P u ∈ weightSpace ρ H.1 := Submodule.sub_mem _ hu hPmem
    have hfix : y (u - P u) = u - P u := by
      rw [scalEquiv_apply]
      have : φ (u - P u) = 0 := by
        change P (πH (u - P u)) = 0
        rw [hπfix _ hmem, map_sub, ← Module.End.mul_apply P P, hPP, sub_self]
      rw [this, smul_zero, add_zero]
    have hy1 := eq_one_of_supported_of_fixed (𝒮 := ∅) β₀ ρ hp hA hpK (isIsomRep_zero ρ) hmax H y
      (fun _ _ => rfl) (fun v => by rw [scalEquiv_pow_apply, hcp, scal_one]; rfl)
      (fun a v => scal_comm φ (ρ a) ((hPρ a).mul_left (hπHρ a)) c v)
      (fun s hs => absurd hs (Set.notMem_empty s))
      (fun i hi v hv => by
        rw [scalEquiv_apply]
        change v + (c - 1) • P (πH v) = v
        rw [hπoff i hi v hv, map_zero, smul_zero, add_zero])
      hmem (sub_ne_zero.mpr (Ne.symm hPu)) hfix
    have hyw := congrArg (fun g : V ≃ₗ[K] V => g w) hy1
    simp only [y, scalEquiv_apply, LinearEquiv.coe_one, id] at hyw
    change w + (c - 1) • P (πH w) = w at hyw
    rw [hπfix w hw, lagProj_apply_of_eigen (ρ x) hgw, add_eq_left] at hyw
    exact hc1 (sub_eq_zero.mp ((smul_eq_zero.mp hyw).resolve_right hw0))
  have hscalA : ∀ a : A, ∃ μ : K, ∀ v ∈ weightSpace ρ H.1, ρ a v = μ • v := by
    intro a
    obtain ⟨n, hn⟩ := exists_pow_of_weightSpace ρ hp hx a
    refine ⟨c ^ n, fun v hv => ?_⟩
    rw [hn v hv]
    clear hn
    induction n generalizing v with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hscal v hv, map_smul, ih v hv, smul_smul,
        pow_succ']
  by_contra hdim
  have hne0 : Module.finrank K (weightSpace ρ H.1) ≠ 0 := fun h0 =>
    hH (Submodule.finrank_eq_zero.mp h0)
  have hge : 2 ≤ Module.finrank K (weightSpace ρ H.1) := by omega
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K
    (show (⟨w, hw⟩ : weightSpace ρ H.1) ≠ 0 from fun h => hw0 (congrArg Subtype.val h))
  set ℓ : V →ₗ[K] K := f ∘ₗ (πH.codRestrict (weightSpace ρ H.1) hπmem)
  have hℓ : ∀ v (hv : v ∈ weightSpace ρ H.1), ℓ v = f ⟨v, hv⟩ := by
    intro v hv
    change f ⟨πH v, _⟩ = f ⟨v, hv⟩
    congr 2
    exact hπfix v hv
  have hℓw : ℓ w = 1 := by rw [hℓ w hw]; exact hf
  set φ : Module.End K V := ℓ.smulRight w
  have hφ : φ * φ = φ := by ext v; simp [φ, Module.End.mul_apply, hℓw]
  have hφρ : ∀ a : A, Commute φ (ρ a) := by
    intro a
    obtain ⟨μ, hμ⟩ := hscalA a
    ext v
    simp only [φ, Module.End.mul_apply, LinearMap.smulRight_apply]
    have h1 : ℓ (ρ a v) = μ * ℓ v := by
      have e : (⟨πH (ρ a v), hπmem _⟩ : weightSpace ρ H.1) = μ • ⟨πH v, hπmem v⟩ :=
        Subtype.ext (by
          show πH (ρ a v) = μ • πH v
          rw [← Module.End.mul_apply, (hπHρ a).eq, Module.End.mul_apply, hμ _ (hπmem v)])
      change f ⟨πH (ρ a v), _⟩ = μ * f ⟨πH v, _⟩
      rw [e, map_smul, smul_eq_mul]
    rw [h1, map_smul, hμ w hw, smul_smul, mul_comm]
  obtain ⟨u, hu0, hfu⟩ : ∃ u : weightSpace ρ H.1, u ≠ 0 ∧ f u = 0 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hrange : Module.finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa using this
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hrk
      omega
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    exact ⟨u, hu0, hu⟩
  set y := scalEquiv φ hφ hc0
  have hy1 := eq_one_of_supported_of_fixed (𝒮 := ∅) β₀ ρ hp hA hpK (isIsomRep_zero ρ) hmax H y
    (fun _ _ => rfl) (fun v => by rw [scalEquiv_pow_apply, hcp, scal_one]; rfl)
    (fun a v => scal_comm φ (ρ a) (hφρ a) c v)
    (fun s hs => absurd hs (Set.notMem_empty s))
    (fun i hi v hv => by
      rw [scalEquiv_apply]
      have : ℓ v = 0 := by
        have h0' : (⟨πH v, hπmem v⟩ : weightSpace ρ H.1) = 0 := Subtype.ext (hπoff i hi v hv)
        change f ⟨πH v, hπmem v⟩ = 0
        rw [h0', map_zero]
      simp [φ, this])
    u.2 (fun h => hu0 (Subtype.ext h))
    (by
      rw [scalEquiv_apply]
      have : ℓ u = 0 := by rw [hℓ u u.2]; exact hfu
      simp [φ, this])
  have hyw := congrArg (fun g : V ≃ₗ[K] V => g w) hy1
  simp only [y, scalEquiv_apply, LinearEquiv.coe_one, id, φ, LinearMap.smulRight_apply, hℓw,
    one_smul] at hyw
  have h' : (c - 1) • w = 0 := by rwa [add_eq_left] at hyw
  exact hc1 (sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hw0))

end Linear

section Unitary

variable {σ : K →+* K} (β : V →ₗ[K] V →ₛₗ[σ] K)

theorem scal_isometry (φ : Module.End K V) (c : K)
    (hφ1 : ∀ u v, β (φ u) v = β (φ u) (φ v)) (hφ2 : ∀ u v, β u (φ v) = β (φ u) (φ v))
    (hc : c * σ c = 1) (u v : V) : β (scal φ c u) (scal φ c v) = β u v := by
  rw [scal_apply, scal_apply]
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, map_sub, map_one]
  rw [hφ1 u v, hφ2 u v]
  linear_combination (β (φ u) (φ v)) * hc

@[expose] noncomputable def coordOn (w : V) : V →ₗ[K] K where
  toFun v := β v w * (β w w)⁻¹
  map_add' u v := by rw [map_add, LinearMap.add_apply, add_mul]
  map_smul' c v := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.id_apply, mul_assoc]

theorem coordOn_apply (w v : V) : coordOn β w v = β v w * (β w w)⁻¹ := rfl

variable (hherm : ∀ u v, β v u = σ (β u v))

include hherm in
theorem coordOn_proj {w : V} (hw : β w w ≠ 0) :
    (∀ u v, β ((coordOn β w).smulRight w u) v =
      β ((coordOn β w).smulRight w u) ((coordOn β w).smulRight w v)) ∧
    (∀ u v, β u ((coordOn β w).smulRight w v) =
      β ((coordOn β w).smulRight w u) ((coordOn β w).smulRight w v)) := by
  have hn : σ (β w w) = β w w := (hherm w w).symm
  have hσinv : σ (β w w)⁻¹ = (β w w)⁻¹ := by rw [map_inv₀, hn]
  refine ⟨fun u v => ?_, fun u v => ?_⟩ <;>
  · simp only [LinearMap.smulRight_apply, coordOn_apply, map_smul, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, map_mul, hσinv, ← hherm]
    field_simp

theorem coordOn_self {w : V} (hw : β w w ≠ 0) : coordOn β w w = 1 := by
  rw [coordOn_apply, mul_inv_cancel₀ hw]

include hherm in
theorem exists_aniso (h2 : (2 : K) ≠ 0) (W : Submodule K V)
    (hW : ∀ u ∈ W, (∀ w ∈ W, β u w = 0) → u = 0) (hW0 : W ≠ ⊥) :
    ∃ w ∈ W, β w w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsum : ∀ u ∈ W, ∀ v ∈ W, β u v + β v u = 0 := by
    intro u hu v hv
    have h := hcon (u + v) (W.add_mem hu hv)
    simp only [map_add, LinearMap.add_apply, hcon u hu, hcon v hv, zero_add, add_zero] at h
    rw [add_comm]; exact h
  have hzero : ∀ u ∈ W, ∀ v ∈ W, β u v = 0 := by
    intro u hu v hv
    by_cases hσ : ∃ c : K, σ c ≠ c
    · obtain ⟨c, hc⟩ := hσ
      have h1 := hsum u hu (c • v) (W.smul_mem c hv)
      have h2' := hsum u hu v hv
      rw [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
      have h3 : (σ c - c) * β u v = 0 := by linear_combination h1 - c * h2'
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc)
    · push Not at hσ
      have h1 := hsum u hu v hv
      rw [hherm u v, hσ] at h1
      have : (2 : K) * β u v = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left h2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  exact hu0 (hW u hu fun w hw => hzero u hu w hw)

end Unitary

section UnitaryD1

variable {σ : K →+* K} (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0) (hρ : IsIsomRep β ρ)
variable (hherm : ∀ u v, β v u = σ (β u v)) (hσp : ∀ c : K, c ^ p = 1 → c * σ c = 1)
variable (h2 : (2 : K) ≠ 0)

include hp hA hpK hρ hherm hσp h2

theorem finrank_weightSpace_eq_one_uni [FiniteDimensional K V] (hβ : β.SeparatingLeft)
    (hmax : IsMaxElem β ρ p ∅) (hq : p ∣ Fintype.card K - 1) (H : Hyperplane A p)
    (hH : weightSpace ρ H.1 ≠ ⊥) : Module.finrank K (weightSpace ρ H.1) = 1 := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_not_mem_hyperplane hp H
  have hg : ρ x ^ Fintype.card K = ρ x := rho_pow_card ρ hA hq x
  have hW : ∀ w ∈ weightSpace ρ H.1, ρ x w ∈ weightSpace ρ H.1 :=
    fun w hw => apply_mem_weightSpace ρ H.1 x hw
  obtain ⟨c, w, hw, hw0, hgw⟩ := exists_eigenvector (ρ x) hg _ hW hH
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [one_smul] at hgw
    exact hw0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK hx hw hgw)
  have hpowv : ∀ (μ : K) (e : V), ρ x e = μ • e → ∀ n : ℕ, ρ (x ^ n) e = μ ^ n • e := by
    intro μ e he n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, he, map_smul, ih, smul_smul,
        pow_succ']
  have hrootv : ∀ (μ : K) (e : V), ρ x e = μ • e → e ≠ 0 → μ ^ p = 1 := by
    intro μ e he he0
    have h := hpowv μ e he p
    rw [hA x, map_one, Module.End.one_apply] at h
    have h' : (μ ^ p - 1) • e = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right he0)
  have hcp : c ^ p = 1 := hrootv c w hgw hw0
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hcp; exact zero_ne_one hcp
  have horth : ∀ μ : K, μ ≠ c → ∀ e e' : V, ρ x e = c • e → ρ x e' = μ • e' → β e e' = 0 := by
    intro μ hμ e e' he he'
    by_cases he'0 : e' = 0
    · rw [he'0, map_zero]
    have hμp := hrootv μ e' he' he'0
    have hμ0 : μ ≠ 0 := by
      rintro rfl; rw [zero_pow hp.ne_zero] at hμp; exact zero_ne_one hμp
    have hσμ : σ μ = μ⁻¹ := eq_inv_of_mul_eq_one_right (hσp μ hμp)
    have h1 := hρ x e e'
    rw [he, he'] at h1
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσμ] at h1
    have h3 : (c * μ⁻¹ - 1) * β e e' = 0 := by linear_combination h1
    have hne : c * μ⁻¹ - 1 ≠ 0 := by
      intro h
      apply hμ
      have : c * μ⁻¹ = 1 := sub_eq_zero.mp h
      field_simp at this
      exact this.symm
    exact (mul_eq_zero.mp h3).resolve_left hne
  set πH := ρ.asAlgebraHom (eps K A p (some H)) with hπH
  have hπHρ : ∀ a : A, Commute πH (ρ a) := fun a => by
    ext v; exact (apply_asAlgebraHom_comm ρ _ a v).symm
  have hππ : πH * πH = πH := ((orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).idem
    (some H)).eq
  have hπmem : ∀ v, πH v ∈ weightSpace ρ H.1 := fun v => ⟨v, rfl⟩
  have hπfix : ∀ v ∈ weightSpace ρ H.1, πH v = v := fun v hv =>
    eps_apply_of_mem ρ hp hA hpK (some H) hv
  have hπoff : ∀ i : Option (Hyperplane A p), i ≠ some H → ∀ v ∈ weightFamily (p := p) ρ i,
      πH v = 0 := fun i hi v hv => eps_apply_of_mem_ne ρ hp hA hpK hi.symm hv
  have hoff : ∀ e ∈ weightSpace ρ H.1, ∀ v, β e (v - πH v) = 0 := by
    intro e he v
    have hsum := sum_eps_apply ρ hp hA hpK v
    have hv : v - πH v = ∑ i ∈ Finset.univ.erase (some H), ρ.asAlgebraHom (eps K A p i) v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (some H))] at hsum
      rw [sub_eq_iff_eq_add, add_comm]; exact hsum.symm
    rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i hi => weightFamily_orthogonal β ρ hρ hp hA hpK
      (Finset.ne_of_mem_erase hi).symm he ⟨v, rfl⟩
  have hscal : ∀ u ∈ weightSpace ρ H.1, ρ x u = c • u := by
    by_contra hne
    push Not at hne
    obtain ⟨u, hu, hgu⟩ := hne
    set P := lagProj (ρ x) c
    have hPπ : Commute P πH := lagProj_comm (ρ x) πH (hπHρ x).symm c
    have hPρ : ∀ a : A, Commute P (ρ a) := fun a =>
      lagProj_comm (ρ x) (ρ a) (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]) c
    have hPP : P * P = P := by
      ext v
      rw [Module.End.mul_apply]
      exact lagProj_apply_of_eigen (ρ x) (apply_lagProj (ρ x) hg c v)
    set φ := P * πH
    have hφ : φ * φ = φ := by
      calc P * πH * (P * πH) = P * P * (πH * πH) := by
            rw [mul_assoc, ← mul_assoc πH, ← hPπ.eq, mul_assoc, mul_assoc]
        _ = P * πH := by rw [hPP, hππ]
    have hφeig : ∀ v, ρ x (φ v) = c • φ v := fun v => apply_lagProj (ρ x) hg c (πH v)
    have hφmem : ∀ v, φ v ∈ weightSpace ρ H.1 := by
      intro v
      change P (πH v) ∈ weightSpace ρ H.1
      rw [← Module.End.mul_apply, hPπ.eq, Module.End.mul_apply]
      exact hπmem _
    have hrel1 : ∀ u v, β (φ u) (v - φ v) = 0 := by
      intro u v
      have hsplit : v - φ v = (v - πH v) + (πH v - P (πH v)) := by
        change v - P (πH v) = (v - πH v) + (πH v - P (πH v)); abel
      rw [hsplit, map_add, hoff _ (hφmem u) v, zero_add]
      have hw : πH v - P (πH v) = ∑ μ ∈ Finset.univ.erase c, lagProj (ρ x) μ (πH v) := by
        have h1 := congrArg (fun f : Module.End K V => f (πH v)) (sum_lagProj (ρ x))
        simp only [LinearMap.sum_apply, Module.End.one_apply] at h1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at h1
        rw [sub_eq_iff_eq_add, add_comm]; exact h1.symm
      rw [hw, map_sum]
      exact Finset.sum_eq_zero fun μ hμ => horth μ (Finset.ne_of_mem_erase hμ) _ _ (hφeig u)
        (apply_lagProj (ρ x) hg μ (πH v))
    have hφ1 : ∀ u v, β (φ u) v = β (φ u) (φ v) := fun u v => by
      have h := hrel1 u v
      rwa [map_sub, sub_eq_zero] at h
    have hφ2 : ∀ u v, β u (φ v) = β (φ u) (φ v) := fun u v => by
      have h : β (u - φ u) (φ v) = 0 := by rw [hherm (φ v) (u - φ u), hrel1 v u, map_zero]
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
    set y := scalEquiv φ hφ hc0
    have hPu : P u ≠ u := fun h => hgu (by rw [← h, apply_lagProj (ρ x) hg c u])
    have hPmem : P u ∈ weightSpace ρ H.1 := by
      rw [← hπfix u hu]; exact hφmem u
    have hmem : u - P u ∈ weightSpace ρ H.1 := Submodule.sub_mem _ hu hPmem
    have hfix : y (u - P u) = u - P u := by
      rw [scalEquiv_apply]
      have : φ (u - P u) = 0 := by
        change P (πH (u - P u)) = 0
        rw [hπfix _ hmem, map_sub, ← Module.End.mul_apply P P, hPP, sub_self]
      rw [this, smul_zero, add_zero]
    have hy1 := eq_one_of_supported_of_fixed (𝒮 := ∅) β ρ hp hA hpK hρ hmax H y
      (fun u v => scal_isometry β φ c hφ1 hφ2 (hσp c hcp) u v)
      (fun v => by rw [scalEquiv_pow_apply, hcp, scal_one]; rfl)
      (fun a v => scal_comm φ (ρ a) ((hPρ a).mul_left (hπHρ a)) c v)
      (fun s hs => absurd hs (Set.notMem_empty s))
      (fun i hi v hv => by
        rw [scalEquiv_apply]
        change v + (c - 1) • P (πH v) = v
        rw [hπoff i hi v hv, map_zero, smul_zero, add_zero])
      hmem (sub_ne_zero.mpr (Ne.symm hPu)) hfix
    have hyw := congrArg (fun g : V ≃ₗ[K] V => g w) hy1
    simp only [y, scalEquiv_apply, LinearEquiv.coe_one, id] at hyw
    change w + (c - 1) • P (πH w) = w at hyw
    rw [hπfix w hw, lagProj_apply_of_eigen (ρ x) hgw, add_eq_left] at hyw
    exact hc1 (sub_eq_zero.mp ((smul_eq_zero.mp hyw).resolve_right hw0))
  have hscalA : ∀ a : A, ∃ μ : K, μ * σ μ = 1 ∧ ∀ v ∈ weightSpace ρ H.1, ρ a v = μ • v := by
    intro a
    obtain ⟨n, hn⟩ := exists_pow_of_weightSpace ρ hp hx a
    refine ⟨c ^ n, hσp _ (by rw [← pow_mul, mul_comm, pow_mul, hcp, one_pow]), fun v hv => ?_⟩
    rw [hn v hv]
    clear hn
    induction n generalizing v with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hscal v hv, map_smul, ih v hv, smul_smul,
        pow_succ']
  by_contra hdim
  have hne0 : Module.finrank K (weightSpace ρ H.1) ≠ 0 := fun h0 =>
    hH (Submodule.finrank_eq_zero.mp h0)
  have hge : 2 ≤ Module.finrank K (weightSpace ρ H.1) := by omega
  have hnd : ∀ u ∈ weightSpace ρ H.1, (∀ w ∈ weightSpace ρ H.1, β u w = 0) → u = 0 :=
    fun u hu h => weightFamily_nondeg β ρ hρ hp hA hpK hβ (some H) hu h
  obtain ⟨w', hw', hn⟩ := exists_aniso β hherm h2 _ hnd hH
  set φ : Module.End K V := (coordOn β w').smulRight w'
  have hφ : φ * φ = φ := by
    ext v; simp [φ, Module.End.mul_apply, coordOn_self β hn]
  obtain ⟨hφ1, hφ2⟩ := coordOn_proj β hherm hn
  have hφρ : ∀ a : A, Commute φ (ρ a) := by
    intro a
    obtain ⟨μ, hμσ, hμ⟩ := hscalA a
    have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμσ
    ext v
    simp only [φ, Module.End.mul_apply, LinearMap.smulRight_apply, coordOn_apply]
    have hw'eq : w' = ρ a (μ⁻¹ • w') := by rw [map_smul, hμ w' hw', smul_smul,
      inv_mul_cancel₀ hμ0, one_smul]
    have h1 : β (ρ a v) w' = μ * β v w' := by
      conv_lhs => rw [hw'eq]
      rw [hρ a v, map_smulₛₗ, smul_eq_mul, map_inv₀, eq_inv_of_mul_eq_one_right hμσ, inv_inv]
    rw [h1, map_smul, hμ w' hw', smul_smul]
    congr 1
    ring
  obtain ⟨u, hu, hu0, hfu⟩ : ∃ u ∈ weightSpace ρ H.1, u ≠ 0 ∧ β u w' = 0 := by
    set f : weightSpace ρ H.1 →ₗ[K] K := (coordOn β w').comp (weightSpace ρ H.1).subtype
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hrange : Module.finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa using this
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hrk
      omega
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    refine ⟨u, u.2, fun h => hu0 (Subtype.ext h), ?_⟩
    have : f u = 0 := hu
    simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, coordOn_apply] at this
    exact (mul_eq_zero.mp this).resolve_right (inv_ne_zero hn)
  set y := scalEquiv φ hφ hc0
  have hy1 := eq_one_of_supported_of_fixed (𝒮 := ∅) β ρ hp hA hpK hρ hmax H y
    (fun u v => scal_isometry β φ c hφ1 hφ2 (hσp c hcp) u v)
    (fun v => by rw [scalEquiv_pow_apply, hcp, scal_one]; rfl)
    (fun a v => scal_comm φ (ρ a) (hφρ a) c v)
    (fun s hs => absurd hs (Set.notMem_empty s))
    (fun i hi v hv => by
      rw [scalEquiv_apply]
      have : β v w' = 0 := weightFamily_orthogonal β ρ hρ hp hA hpK hi hv hw'
      simp [φ, coordOn_apply, this])
    hu hu0 (by rw [scalEquiv_apply]; simp [φ, coordOn_apply, hfu])
  have hyw := congrArg (fun g : V ≃ₗ[K] V => g w') hy1
  simp only [y, scalEquiv_apply, LinearEquiv.coe_one, id, φ, LinearMap.smulRight_apply,
    coordOn_self β hn, one_smul] at hyw
  have h' : (c - 1) • w' = 0 := by rwa [add_eq_left] at hyw
  have hw'0 : w' ≠ 0 := by rintro rfl; simp at hn
  exact hc1 (sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hw'0))

end UnitaryD1

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
