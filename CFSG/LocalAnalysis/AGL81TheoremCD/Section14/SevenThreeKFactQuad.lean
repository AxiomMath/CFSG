module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsInvolution

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem apply_sq_add_self {J : Module.End K V} (hJ3 : J ^ 2 + J + 1 = 0) (v : V) :
    J (J v) = -v - J v := by
  have h := congrArg (fun f : Module.End K V => f v) hJ3
  have h' : J (J v) + J v + v = 0 := by simpa [pow_two, Module.End.mul_apply] using h
  have h'' : J (J v) = -(J v + v) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using h')
  rw [h'']
  abel

omit [FiniteDimensional K V] in
theorem map_smul_add_smul_of_isometry {Q : QuadraticForm K V} {J : Module.End K V}
    (hJ : ∀ v, Q (J v) = Q v) (hJ2 : ∀ v, J (J v) = -v - J v) (a b : K) (v : V) :
    Q (a • v + b • J v) = (a * a - a * b + b * b) * Q v := by
  have hp : polar Q v (J v) = - Q v := by
    have hsum : Q (v + J v) = Q v := by
      have hneg : J (J v) = -(v + J v) := by rw [hJ2 v]; abel
      calc Q (v + J v) = Q (-(v + J v)) := (QuadraticMap.map_neg Q _).symm
        _ = Q (J (J v)) := by rw [hneg]
        _ = Q (J v) := hJ (J v)
        _ = Q v := hJ v
    have hone := QuadraticMap.map_add Q v (J v)
    rw [hJ v, hsum] at hone
    have h2 : Q v + (Q v + polar Q v (J v)) = Q v := by
      simpa [add_assoc] using hone.symm
    have hzero : Q v + polar Q v (J v) = 0 :=
      add_left_cancel (a := Q v) (b := Q v + polar Q v (J v)) (c := 0) (by simpa using h2)
    exact eq_neg_of_add_eq_zero_right hzero
  calc Q (a • v + b • J v)
      = Q (a • v) + Q (b • J v) + polar Q (a • v) (b • J v) :=
        QuadraticMap.map_add Q _ _
    _ = (a * a - a * b + b * b) * Q v := by
        rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hJ v, polar_smul_left,
          polar_smul_right, hp, smul_smul]
        simp only [smul_eq_mul, neg_mul]
        ring

omit [FiniteDimensional K V] in
theorem linearIndependent_pair_of_quadratic {J : Module.End K V}
    (hJ2 : ∀ v, J (J v) = -v - J v)
    (hnosplit : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {v : V} (hv : v ≠ 0) :
    LinearIndependent K ![v, J v] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    have h : a • v = 0 := by simpa using hab
    exact ⟨(smul_eq_zero.mp h).resolve_right hv, rfl⟩
  · have hJv : J v = (-(a * b⁻¹)) • v := by
      have h1 : b • J v = -(a • v) := by
        rw [add_comm] at hab
        exact eq_neg_of_add_eq_zero_left hab
      calc J v = b⁻¹ • (b • J v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • (-(a • v)) := by rw [h1]
        _ = (-(a * b⁻¹)) • v := by module
    let c : K := -(a * b⁻¹)
    have h1 : J (J v) = (c * c) • v := by rw [hJv, map_smul, hJv, smul_smul]
    have h2 : J (J v) = (-1 - c) • v := by
      rw [hJ2 v, hJv]
      module
    have hcoef : (c * c) • v = (-1 - c) • v := by rw [← h1, h2]
    have hzero : (c * c - (-1 - c)) • v = 0 := by rw [sub_smul, hcoef, sub_self]
    have hc : c * c - (-1 - c) = 0 := (smul_eq_zero.mp hzero).resolve_right hv
    apply absurd _ (hnosplit c)
    have hcc : c * c = -1 - c := sub_eq_zero.mp hc
    rw [pow_two]
    calc c * c + c + 1 = (-1 - c) + c + 1 := by rw [hcc]
      _ = 0 := by ring

omit [FiniteDimensional K V] in
theorem mul_factor_eq_zero {J : Module.End K V} (hJ2 : ∀ v, J (J v) = -v - J v)
    {a b : K} (hsum : a + b = -1) (hprod : a * b = 1) :
    (J - a • (1 : Module.End K V)) * (J - b • (1 : Module.End K V)) = 0 := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, smul_sub]
  rw [hJ2 v]
  have hba : b * a = 1 := by rw [mul_comm, hprod]
  have hc : (1 : K) + a + b = 0 := by rw [add_assoc, hsum]; ring
  rw [show -v - J v - a • J v - (b • J v - b • a • v)
      = -((1 : K) + a + b) • J v by
    rw [show b • a • v = (b * a) • v from smul_smul b a v, hba]
    module, hc]
  simp

omit [FiniteDimensional K V] in
private theorem range_pair_eq (a b : V) : Set.range ![a, b] = ({a, b} : Set V) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

omit [FiniteDimensional K V] in
private theorem finrank_span_pair_eq_two {J : Module.End K V}
    (hJ2 : ∀ v, J (J v) = -v - J v)
    (hnosplit : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {v : V} (hv : v ≠ 0) :
    Module.finrank K (Submodule.span K ({v, J v} : Set V)) = 2 := by
  have hli := linearIndependent_pair_of_quadratic hJ2 hnosplit hv
  have h := finrank_span_eq_card (b := ![v, J v]) hli
  rw [range_pair_eq v (J v)] at h
  simpa [Fintype.card_fin] using h

omit [FiniteDimensional K V] in
private theorem exists_le_finrank_eq_of_le (U : Submodule K V) {n : ℕ}
    (hn : n ≤ Module.finrank K U) : ∃ T : Submodule K V, T ≤ U ∧ Module.finrank K T = n := by
  classical
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := U) hn
  refine ⟨(Submodule.span K (s : Set U)).map U.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_finset_eq_card hli, hs]

theorem quadratic_eq_zero_of_mem_ker_sub_smul {Q : QuadraticForm K V} {J : Module.End K V}
    (hJ : ∀ v, Q (J v) = Q v) {a : K} (ha : a * a ≠ 1) {u : V}
    (hu : u ∈ LinearMap.ker (J - a • (1 : Module.End K V))) : Q u = 0 := by
  have hJu : J u = a • u := by simpa [sub_eq_zero] using (LinearMap.mem_ker.mp hu)
  have h := hJ u
  rw [hJu, QuadraticMap.map_smul, smul_eq_mul] at h
  have hzero : (a * a - 1) * Q u = 0 := by
    calc (a * a - 1) * Q u = a * a * Q u - Q u := by ring
      _ = 0 := by rw [h, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha)

omit [FiniteDimensional K V] in
theorem disjoint_ker_sub_smul {J : Module.End K V} {a b : K} (hab : a ≠ b) :
    Disjoint (LinearMap.ker (J - a • (1 : Module.End K V)))
      (LinearMap.ker (J - b • (1 : Module.End K V))) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : J x - a • x = 0 := by simpa using hx
  have h2 : J x - b • x = 0 := by simpa using hx'
  have hcoef : (b - a) • x = 0 := by
    calc (b - a) • x = (J x - a • x) - (J x - b • x) := by module
      _ = 0 := by rw [h1, h2, sub_self]
  exact (smul_eq_zero.mp hcoef).resolve_left (sub_ne_zero.mpr hab.symm)

theorem finrank_ker_add_finrank_ker_of_mul_eq_zero {f g : Module.End K V}
    (hcomm : Commute f g) (hdisj : Disjoint f.ker g.ker) (hfg : f * g = 0) :
    Module.finrank K f.ker + Module.finrank K g.ker = Module.finrank K V := by
  have hcomp : (f ∘ₗ g).ker = f.ker ⊔ g.ker :=
    LinearMap.ker_comp_eq_of_commute_of_disjoint_ker hcomm hdisj
  have htop : f.ker ⊔ g.ker = ⊤ := by
    rw [← hcomp, ← Module.End.mul_eq_comp, hfg, LinearMap.ker_zero]
  have h := Submodule.finrank_sup_add_finrank_inf_eq f.ker g.ker
  rw [htop, disjoint_iff.mp hdisj, finrank_top, finrank_bot, add_zero] at h
  exact h.symm

theorem cube_root_mul_identities {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 ∧ ω + ω ^ 2 = -1 ∧ ω * ω ^ 2 = 1 := by
  have hω3 : ω ^ 3 = 1 := by
    have hprod : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hfac] at hprod
    exact sub_eq_zero.mp hprod
  have hsum : ω + ω ^ 2 = -1 := by
    have := congrArg (fun x => x - 1) hω
    have h' : ω ^ 2 + ω = -1 := by simpa [sub_eq_add_neg, add_assoc] using this
    rwa [add_comm] at h'
  refine ⟨hω3, hsum, ?_⟩
  calc ω * ω ^ 2 = ω ^ 3 := by ring
    _ = 1 := hω3

theorem cube_root_ne_one_and_ne_sq (hK : (3 : K) ≠ 0) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have hω_ne_one : ω ≠ 1 := by
    intro h
    have h3 : (3 : K) = 0 := by
      calc (3 : K) = ω ^ 2 + ω + 1 := by rw [h]; ring
        _ = 0 := hω
    exact hK h3
  refine ⟨hω_ne_one, ?_⟩
  intro heq
  have hprod : ω * (ω - 1) = 0 := by
    calc ω * (ω - 1) = ω ^ 2 - ω := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hprod with h0 | h1
  · have hone : (1 : K) = 0 := by
      calc (1 : K) = ω ^ 2 + ω + 1 := by rw [h0]; ring
        _ = 0 := hω
    exact one_ne_zero hone
  · exact hω_ne_one (sub_eq_zero.mp h1)

theorem cube_root_sq_ne_one (hK : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω * ω ≠ 1 ∧ ω ^ 2 * ω ^ 2 ≠ 1 := by
  obtain ⟨hω3, hsum, hωprod⟩ := cube_root_mul_identities hω
  obtain ⟨hω_ne_one, hω_ne_sq⟩ := cube_root_ne_one_and_ne_sq hK hω
  have hωm : ω ≠ -1 := by
    intro h
    have hone : (1 : K) = 0 := by
      calc (1 : K) = ω ^ 2 + ω + 1 := by rw [h]; ring
        _ = 0 := hω
    exact one_ne_zero hone
  have hω4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω * ω ^ 3 := by ring
      _ = ω := by rw [hω3, mul_one]
  constructor
  · intro hsq
    have hfac : (ω - 1) * (ω + 1) = 0 := by
      calc (ω - 1) * (ω + 1) = ω ^ 2 - 1 := by ring
        _ = 0 := sub_eq_zero.mpr (by simpa [pow_two] using hsq)
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact hω_ne_one (sub_eq_zero.mp h1)
    · exact hωm (eq_neg_of_add_eq_zero_left h2)
  · intro h
    have hω1 : ω = 1 := by
      calc ω = ω ^ 4 := hω4.symm
        _ = ω ^ 2 * ω ^ 2 := by ring
        _ = 1 := h
    exact hω_ne_one hω1

theorem exists_totallySingular_of_isometry_split (hK : (3 : K) ≠ 0)
    (Q : QuadraticForm K V) (J : Module.End K V) (hJ : ∀ v, Q (J v) = Q v)
    (hJ3 : J ^ 2 + J + 1 = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hdim : 8 ≤ Module.finrank K V) :
    ∃ W : Submodule K V, Module.finrank K W = 4 ∧ ∀ w ∈ W, Q w = 0 := by
  obtain ⟨hω3, hωsum, hωprod⟩ := cube_root_mul_identities hω
  obtain ⟨hω_ne_one, hω_ne_sq⟩ := cube_root_ne_one_and_ne_sq hK hω
  obtain ⟨hωsq_ne_one, hω4_ne_one⟩ := cube_root_sq_ne_one hK hω
  let f : Module.End K V := J - ω • 1
  let g : Module.End K V := J - ω ^ 2 • 1
  have hJ2 : ∀ v, J (J v) = -v - J v := apply_sq_add_self hJ3
  have hfg : f * g = 0 := by
    simpa [f, g] using mul_factor_eq_zero hJ2 (a := ω) (b := ω ^ 2) hωsum hωprod
  have hgf : g * f = 0 := by
    simpa [f, g] using mul_factor_eq_zero hJ2 (a := ω ^ 2) (b := ω)
      (by rw [add_comm]; exact hωsum) (by rw [mul_comm]; exact hωprod)
  have hcomm : Commute f g := by
    show f * g = g * f
    rw [hfg, hgf]
  have hdisj : Disjoint f.ker g.ker := by
    simpa [f, g] using disjoint_ker_sub_smul (J := J) (a := ω) (b := ω ^ 2) hω_ne_sq.symm
  have hdimfg := finrank_ker_add_finrank_ker_of_mul_eq_zero hcomm hdisj hfg
  have hf_sing : ∀ u ∈ f.ker, Q u = 0 := by
    intro u hu
    exact quadratic_eq_zero_of_mem_ker_sub_smul hJ hωsq_ne_one hu
  have hg_sing : ∀ u ∈ g.ker, Q u = 0 := by
    intro u hu
    exact quadratic_eq_zero_of_mem_ker_sub_smul hJ hω4_ne_one hu
  have hbig : 4 ≤ Module.finrank K f.ker ∨ 4 ≤ Module.finrank K g.ker := by omega
  rcases hbig with hf | hg
  · obtain ⟨W, hWle, hWdim⟩ := exists_le_finrank_eq_of_le f.ker (n := 4) hf
    exact ⟨W, hWdim, fun w hw => hf_sing w (hWle hw)⟩
  · obtain ⟨W, hWle, hWdim⟩ := exists_le_finrank_eq_of_le g.ker (n := 4) hg
    exact ⟨W, hWdim, fun w hw => hg_sing w (hWle hw)⟩

private noncomputable def polarPairMap (Q : QuadraticForm K V) (J : Module.End K V) (s : V) :
    V →ₗ[K] K × K :=
  { toFun := fun u => (polar Q u s, polar Q u (J s))
    map_add' := by intro x y; simp [polar_add_left]
    map_smul' := by intro a x; simp [polar_smul_left] }

private noncomputable def polarPair (Q : QuadraticForm K V) (J : Module.End K V) (s : V) :
    Submodule K V :=
  LinearMap.ker (polarPairMap Q J s)

private theorem mem_polarPair {Q : QuadraticForm K V} {J : Module.End K V} {s u : V} :
    u ∈ polarPair Q J s ↔ polar Q u s = 0 ∧ polar Q u (J s) = 0 := by
  simp [polarPair, polarPairMap]

private theorem finrank_polarPair_ge (Q : QuadraticForm K V) (J : Module.End K V) (s : V) :
    Module.finrank K V - 2 ≤ Module.finrank K (polarPair Q J s) := by
  have h := LinearMap.finrank_range_add_finrank_ker (polarPairMap Q J s)
  have h2 : Module.finrank K (polarPairMap Q J s).range ≤ 2 := by
    calc Module.finrank K (polarPairMap Q J s).range ≤ Module.finrank K (K × K) :=
          Submodule.finrank_le _
      _ = 2 := by simp [Module.finrank_prod]
  rw [polarPair]
  omega

private theorem map_mem_polarPair {Q : QuadraticForm K V} {J : Module.End K V}
    (hJ : ∀ v, Q (J v) = Q v) (hJ2 : ∀ v, J (J v) = -v - J v) {s u : V}
    (hu : u ∈ polarPair Q J s) : J u ∈ polarPair Q J s := by
  rw [mem_polarPair] at hu ⊢
  have h2 : polar Q (J u) (J s) = 0 := by
    rw [show polar Q (J u) (J s) = polar Q u s from by
      rw [polar, polar, ← map_add]; simp only [hJ]]
    exact hu.1
  constructor
  · have h1 : polar Q (J u) (J (J s)) = 0 := by
      rw [show polar Q (J u) (J (J s)) = polar Q u (J s) from by
        rw [polar, polar, ← map_add]; simp only [hJ]]
      exact hu.2
    rw [hJ2 s, show -s - J s = -(s) + -(J s) by abel, polar_add_right, polar_neg_right,
      polar_neg_right, h2] at h1
    simpa using h1
  · exact h2

private theorem quadratic_eq_zero_of_mem_span_pair {Q : QuadraticForm K V} {J : Module.End K V}
    (hJ : ∀ v, Q (J v) = Q v) (hJ2 : ∀ v, J (J v) = -v - J v) {s : V} (hs : Q s = 0) :
    ∀ w ∈ Submodule.span K ({s, J s} : Set V), Q w = 0 := by
  intro w hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
  rw [map_smul_add_smul_of_isometry hJ hJ2, hs, mul_zero]

private theorem span_pair_le_polarPair {Q : QuadraticForm K V} {J : Module.End K V}
    (hJ : ∀ v, Q (J v) = Q v) (hJ2 : ∀ v, J (J v) = -v - J v) {s : V} (hsQ : Q s = 0) :
    Submodule.span K ({s, J s} : Set V) ≤ polarPair Q J s := by
  intro w hw
  rw [mem_polarPair]
  exact ⟨CFSG.SeitzReduction.OmegaPilot.polar_eq_zero_of_totallySingular
      (quadratic_eq_zero_of_mem_span_pair hJ hJ2 hsQ) hw (Submodule.subset_span (by simp)),
    CFSG.SeitzReduction.OmegaPilot.polar_eq_zero_of_totallySingular
      (quadratic_eq_zero_of_mem_span_pair hJ hJ2 hsQ) hw (Submodule.subset_span (by simp))⟩

private theorem exists_singular_mem_polarPair_not_mem [Finite K]
    (Q : QuadraticForm K V) (J : Module.End K V) (hJ : ∀ v, Q (J v) = Q v)
    (hJ2 : ∀ v, J (J v) = -v - J v) (hnosplit : ∀ s : K, s ^ 2 + s + 1 ≠ 0)
    {s : V} (hs0 : s ≠ 0) (hsQ : Q s = 0) (hdim : 8 ≤ Module.finrank K V) :
    ∃ u ∈ polarPair Q J s, u ∉ Submodule.span K ({s, J s} : Set V) ∧ Q u = 0 := by
  let R : Submodule K V := Submodule.span K ({s, J s} : Set V)
  have hRdim : Module.finrank K R = 2 := finrank_span_pair_eq_two hJ2 hnosplit hs0
  have hRle : R ≤ polarPair Q J s := span_pair_le_polarPair hJ hJ2 hsQ
  have hUdim : Module.finrank K V - 2 ≤ Module.finrank K (polarPair Q J s) :=
    finrank_polarPair_ge Q J s
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl R
  let C : Submodule K V := C₀ ⊓ polarPair Q J s
  have hCR : C ⊓ R = ⊥ := by
    rw [show C ⊓ R = (C₀ ⊓ polarPair Q J s) ⊓ R by rfl, inf_assoc,
      inf_eq_right.mpr hRle, inf_comm, hC₀.inf_eq_bot]
  have hCsup : R ⊔ C = polarPair Q J s := by
    rw [show C = C₀ ⊓ polarPair Q J s by rfl,
      ← sup_inf_assoc_of_le C₀ hRle, hC₀.sup_eq_top, top_inf_eq]
  have hCdim : 4 ≤ Module.finrank K C := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R C
    rw [hCsup, show R ⊓ C = ⊥ from by rw [inf_comm, hCR], finrank_bot, add_zero,
      hRdim] at h
    omega
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨u, hu0, huQ⟩ :=
    CFSG.SeitzReduction.OmegaPilot.exists_ne_zero_map_eq_zero_of_three_le
      (p := ringChar K) (Q.comp C.subtype) (by omega)
  refine ⟨u, u.2.2, ?_, ?_⟩
  · intro huR
    have hmem : (u : V) ∈ C ⊓ R := ⟨u.2, huR⟩
    rw [hCR] at hmem
    have hzero : (u : V) = 0 := by simpa using hmem
    exact hu0 (Subtype.ext hzero)
  · simpa [QuadraticMap.comp_apply] using huQ

private theorem map_mem_span_pair_of_mem {J : Module.End K V}
    (hJ2 : ∀ v, J (J v) = -v - J v) {v x : V}
    (hx : x ∈ Submodule.span K ({v, J v} : Set V)) :
    J x ∈ Submodule.span K ({v, J v} : Set V) := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  have hJexp : J (a • v + b • J v) = (-b) • v + (a - b) • J v := by
    rw [map_add, map_smul, map_smul, hJ2 v]
    module
  rw [hJexp]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem polar_eq_zero_of_mem_span_pair_of_mem_polarPair {Q : QuadraticForm K V}
    {J : Module.End K V} (hJ : ∀ v, Q (J v) = Q v) (hJ2 : ∀ v, J (J v) = -v - J v)
    {s u : V} (hu : u ∈ polarPair Q J s) :
    ∀ x ∈ Submodule.span K ({s, J s} : Set V),
      ∀ y ∈ Submodule.span K ({u, J u} : Set V), polar Q x y = 0 := by
  have hu_mem : u ∈ polarPair Q J s := hu
  rw [mem_polarPair] at hu
  have hJu : J u ∈ polarPair Q J s := map_mem_polarPair hJ hJ2 hu_mem
  rw [mem_polarPair] at hJu
  have hsu : polar Q s u = 0 := (polar_comm Q s u).trans hu.1
  have hsJu : polar Q s (J u) = 0 := (polar_comm Q s (J u)).trans hJu.1
  have hJsu : polar Q (J s) u = 0 := (polar_comm Q (J s) u).trans hu.2
  have hJsJu : polar Q (J s) (J u) = 0 := (polar_comm Q (J s) (J u)).trans hJu.2
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  rw [polar_add_left, polar_smul_left, polar_smul_left, polar_add_right,
    polar_smul_right, polar_smul_right]
  simp [hsu, hsJu, hJsu, hJsJu]

private theorem disjoint_span_pair_of_mem_polarPair_not_mem {Q : QuadraticForm K V}
    {J : Module.End K V} (hJ2 : ∀ v, J (J v) = -v - J v)
    (hnosplit : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {s u : V} (hu : u ∈ polarPair Q J s)
    (huR : u ∉ Submodule.span K ({s, J s} : Set V)) :
    Disjoint (Submodule.span K ({s, J s} : Set V))
      (Submodule.span K ({u, J u} : Set V)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  by_contra hx0
  have hR2dim : Module.finrank K (Submodule.span K ({u, J u} : Set V)) = 2 :=
    finrank_span_pair_eq_two hJ2 hnosplit (fun h => huR (h ▸ Submodule.zero_mem _))
  have hli : LinearIndependent K ![x, J x] := linearIndependent_pair_of_quadratic hJ2 hnosplit hx0
  have hspan : Submodule.span K ({x, J x} : Set V) =
      Submodule.span K ({u, J u} : Set V) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hy
      · exact map_mem_span_pair_of_mem hJ2 hy
    · have hdimx : Module.finrank K (Submodule.span K ({x, J x} : Set V)) = 2 := by
        have h := finrank_span_eq_card (b := ![x, J x]) hli
        rw [range_pair_eq x (J x)] at h
        simpa [Fintype.card_fin] using h
      rw [hdimx, hR2dim]
  have hspanle : Submodule.span K ({x, J x} : Set V) ≤
      Submodule.span K ({s, J s} : Set V) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact map_mem_span_pair_of_mem hJ2 hx
  have huR' : u ∈ Submodule.span K ({s, J s} : Set V) := by
    apply hspanle
    rw [hspan]
    exact Submodule.subset_span (by simp)
  exact huR huR'

theorem exists_totallySingular_of_isometry_nonsplit [Finite K] (hK : (3 : K) ≠ 0)
    (Q : QuadraticForm K V) (J : Module.End K V) (hJ : ∀ v, Q (J v) = Q v)
    (hJ3 : J ^ 2 + J + 1 = 0)
    (hnosplit : ∀ s : K, s ^ 2 + s + 1 ≠ 0) (hdim : 8 ≤ Module.finrank K V) :
    ∃ W : Submodule K V, Module.finrank K W = 4 ∧ ∀ w ∈ W, Q w = 0 := by
  have hJ2 : ∀ v, J (J v) = -v - J v := apply_sq_add_self hJ3
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨s, hs0, hsQ⟩ :=
    CFSG.SeitzReduction.OmegaPilot.exists_ne_zero_map_eq_zero_of_three_le
      (p := ringChar K) Q (by omega)
  obtain ⟨u, huU, huR, huQ⟩ :=
    exists_singular_mem_polarPair_not_mem Q J hJ hJ2 hnosplit hs0 hsQ hdim
  let R1 : Submodule K V := Submodule.span K ({s, J s} : Set V)
  let R2 : Submodule K V := Submodule.span K ({u, J u} : Set V)
  have hu0 : u ≠ 0 := fun h => huR (h ▸ Submodule.zero_mem _)
  have hR1dim : Module.finrank K R1 = 2 := finrank_span_pair_eq_two hJ2 hnosplit hs0
  have hR2dim : Module.finrank K R2 = 2 := finrank_span_pair_eq_two hJ2 hnosplit hu0
  have hR1sing : ∀ w ∈ R1, Q w = 0 := quadratic_eq_zero_of_mem_span_pair hJ hJ2 hsQ
  have hR2sing : ∀ w ∈ R2, Q w = 0 := quadratic_eq_zero_of_mem_span_pair hJ hJ2 huQ
  have horth : ∀ x ∈ R1, ∀ y ∈ R2, polar Q x y = 0 :=
    polar_eq_zero_of_mem_span_pair_of_mem_polarPair hJ hJ2 huU
  have hdisj : R1 ⊓ R2 = ⊥ := by
    rw [← disjoint_iff]
    simpa [R1, R2] using disjoint_span_pair_of_mem_polarPair_not_mem hJ2 hnosplit huU huR
  have hdimR12 : Module.finrank K ↥(R1 ⊔ R2) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R1 R2
    rw [hdisj, finrank_bot, hR1dim, hR2dim] at h
    omega
  have hsing : ∀ w ∈ R1 ⊔ R2, Q w = 0 := by
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    rw [QuadraticMap.map_add Q x y, hR1sing x hx, hR2sing y hy, horth x hx y hy]
    simp
  exact ⟨R1 ⊔ R2, hdimR12, hsing⟩

omit [FiniteDimensional K V] in
theorem polar_eq_zero_of_fixed_of_mem_range {Q : QuadraticForm K V} {Y : V →ₗ[K] V}
    (hY : ∀ v, Q (Y v) = Q v) {c w : V} (hc : Y c = c) (hw : w ∈ LinearMap.range (Y - 1)) :
    polar Q c w = 0 := by
  obtain ⟨u, rfl⟩ := hw
  simp only [LinearMap.sub_apply, Module.End.one_apply, polar_sub_right]
  have h1 : polar Q c (Y u) = polar Q (Y c) (Y u) := by rw [hc]
  have h2 : polar Q (Y c) (Y u) = polar Q c u := by
    rw [polar, polar, ← map_add]
    simp only [hY]
  rw [h1, h2, sub_self]

private noncomputable def proj (T : Module.End K V) : Module.End K V :=
  (3⁻¹ : K) • (1 + T + T ^ 2)

omit [FiniteDimensional K V] in
private theorem proj_mul_self (hK : (3 : K) ≠ 0) {T : Module.End K V}
    (hT3v : ∀ v, T (T (T v)) = v) : proj T * proj T = proj T := by
  have h3inv : (3⁻¹ : K) * 3 = 1 := inv_mul_cancel₀ hK
  have hPP : (1 + T + T ^ 2 : Module.End K V) * (1 + T + T ^ 2) =
      (3 : K) • (1 + T + T ^ 2) := by
    have h3 : (3 : K) • (1 + T + T ^ 2 : Module.End K V)
        = (1 + T + T ^ 2) + (1 + T + T ^ 2) + (1 + T + T ^ 2) := by module
    rw [h3]
    ext v
    simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add]
    simp only [hT3v]
    abel
  calc proj T * proj T
      = ((3⁻¹ : K) * (3⁻¹ : K)) • ((1 + T + T ^ 2) * (1 + T + T ^ 2)) := by
        change ((3⁻¹ : K) • (1 + T + T ^ 2 : Module.End K V)) *
            ((3⁻¹ : K) • (1 + T + T ^ 2))
          = ((3⁻¹ : K) * (3⁻¹ : K)) • ((1 + T + T ^ 2) * (1 + T + T ^ 2))
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    _ = ((3⁻¹ : K) * (3⁻¹ : K)) • ((3 : K) • (1 + T + T ^ 2)) := by rw [hPP]
    _ = proj T := by
        change ((3⁻¹ : K) * (3⁻¹ : K)) • ((3 : K) • (1 + T + T ^ 2 : Module.End K V))
          = (3⁻¹ : K) • (1 + T + T ^ 2)
        rw [smul_smul]
        congr 1
        rw [show (3⁻¹ : K) * 3⁻¹ * 3 = 3⁻¹ * (3⁻¹ * 3) by ring, h3inv, mul_one]

omit [FiniteDimensional K V] in
private theorem proj_mul_eq (hK : (3 : K) ≠ 0) {T : Module.End K V}
    (hT3v : ∀ v, T (T (T v)) = v) :
    proj T * T = proj T ∧ T * proj T = proj T := by
  constructor
  · ext v
    simp only [proj, pow_two, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul]
    simp only [hT3v]
    abel
  · ext v
    simp only [proj, pow_two, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul]
    simp only [hT3v]
    abel

omit [FiniteDimensional K V] in
private theorem proj_apply_fixed (hK : (3 : K) ≠ 0) {T : Module.End K V}
    (hT3v : ∀ v, T (T (T v)) = v) (v : V) : T (proj T v) = proj T v :=
  congrArg (fun f : Module.End K V => f v) (proj_mul_eq hK hT3v).2

omit [FiniteDimensional K V] in
private theorem proj_sub_mem_range (hK : (3 : K) ≠ 0) {T : Module.End K V}
    (hT3v : ∀ v, T (T (T v)) = v) (v : V) :
    (1 - proj T) v ∈ LinearMap.range (T - 1) := by
  refine ⟨-((3⁻¹ : K) • (((2 : K) • (1 : Module.End K V) + T) v)), ?_⟩
  simp only [proj, pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, map_neg, one_smul]
  have hc : (3⁻¹ : K) * 3 = 1 := inv_mul_cancel₀ hK
  calc -((3⁻¹ : K) • ((2 : K) • (T v - v) + (T (T v) - T v)))
      = (3⁻¹ : K) • (-((2 : K) • (T v - v) + (T (T v) - T v))) := by rw [smul_neg]
    _ = (3⁻¹ : K) • ((3 : K) • v - (v + T v + T (T v))) := by
        congr 1
        module
    _ = (3⁻¹ : K) • ((3 : K) • v) - (3⁻¹ : K) • (v + T v + T (T v)) := by rw [smul_sub]
    _ = v - (3⁻¹ : K) • (v + T v + T (T v)) := by rw [smul_smul, hc, one_smul]

omit [FiniteDimensional K V] in
private theorem proj_commute_of_commute {T U : Module.End K V} (hTU : Commute T U) :
    Commute (proj T) U := by
  have hP : Commute (1 + T + T ^ 2 : Module.End K V) U :=
    ((Commute.one_left U).add_left hTU).add_left (hTU.pow_left 2)
  change Commute ((3⁻¹ : K) • (1 + T + T ^ 2 : Module.End K V)) U
  exact hP.smul_left (3⁻¹)

omit [FiniteDimensional K V] in
private theorem proj_commute_proj {T U : Module.End K V} (hTU : Commute T U) :
    Commute (proj T) (proj U) := by
  have h1 : Commute (proj T) U := proj_commute_of_commute hTU
  have h2 : Commute (proj T) (1 + U + U ^ 2 : Module.End K V) :=
    ((Commute.one_right (proj T)).add_right h1).add_right (h1.pow_right 2)
  change Commute (proj T) ((3⁻¹ : K) • (1 + U + U ^ 2 : Module.End K V))
  exact h2.smul_right (3⁻¹)

omit [FiniteDimensional K V] in
private theorem sq_add_self_add_one_eq_three_smul_proj (hK : (3 : K) ≠ 0)
    (T : Module.End K V) : (T ^ 2 + T + 1 : Module.End K V) = (3 : K) • proj T := by
  have h3 : (3 : K) • proj T = (1 + T + T ^ 2 : Module.End K V) := by
    change (3 : K) • ((3⁻¹ : K) • (1 + T + T ^ 2 : Module.End K V)) = 1 + T + T ^ 2
    rw [smul_smul, mul_inv_cancel₀ hK, one_smul]
  rw [h3]
  abel

omit [FiniteDimensional K V] in
private theorem proj_mul_proj_eq_zero {Y Z : Module.End K V}
    (hfix : LinearMap.ker (Y - 1) ⊓ LinearMap.ker (Z - 1) = ⊥)
    (heez : Commute (proj Y) (proj Z)) (hYe : Y * proj Y = proj Y)
    (hZez : Z * proj Z = proj Z) : proj Z * proj Y = 0 := by
  ext v
  have hcomm : proj Z (proj Y v) = proj Y (proj Z v) := by
    have h := congrArg (fun f : Module.End K V => f v) heez.eq
    simpa [Module.End.mul_apply] using h.symm
  have hmem : proj Z (proj Y v) ∈ LinearMap.ker (Y - 1) ⊓ LinearMap.ker (Z - 1) := by
    constructor
    · exact LinearMap.mem_ker.mpr (by
        rw [hcomm]
        have h := congrArg (fun f : Module.End K V => f (proj Z v)) hYe
        simpa [Module.End.mul_apply] using sub_eq_zero.mpr h)
    · exact LinearMap.mem_ker.mpr (by
        have h := congrArg (fun f : Module.End K V => f (proj Y v)) hZez
        simpa [Module.End.mul_apply] using sub_eq_zero.mpr h)
  rw [hfix] at hmem
  have hzero : proj Z (proj Y v) = 0 := by simpa using hmem
  simpa [Module.End.mul_apply] using hzero

omit [FiniteDimensional K V] in
private theorem apply_composite {J Y Z e : Module.End K V}
    (hJ : J = Z * e + Y * (1 - e)) (v : V) :
    J v = Z (e v) + Y ((1 - e) v) := by
  rw [hJ]
  simp [Module.End.mul_apply]

omit [FiniteDimensional K V] in
private theorem composite_e_apply {J Y Z e : Module.End K V}
    (hJ : J = Z * e + Y * (1 - e)) (heY : e * Y = e) (heZ : e * Z = Z * e)
    (hee : e * e = e) (he1 : e * (1 - e) = 0) :
    ∀ v, e (J v) = Z (e v) := by
  intro v
  have hZev : e (Z (e v)) = Z (e v) := by
    have h := congrArg (fun f : Module.End K V => f (e v)) heZ
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [show e (e v) = e v from congrArg (fun f : Module.End K V => f v) hee] at h
    exact h
  have hYev : e (Y ((1 - e) v)) = 0 := by
    have h := congrArg (fun f : Module.End K V => f ((1 - e) v)) heY
    rw [Module.End.mul_apply] at h
    rw [show e ((1 - e) v) = 0 from by
      have h2 := congrArg (fun f : Module.End K V => f v) he1
      simpa [Module.End.mul_apply] using h2] at h
    exact h
  calc e (J v) = e (Z (e v) + Y ((1 - e) v)) := by rw [apply_composite hJ v]
    _ = e (Z (e v)) + e (Y ((1 - e) v)) := map_add e _ _
    _ = Z (e v) + 0 := by rw [hZev, hYev]
    _ = Z (e v) := add_zero _

omit [FiniteDimensional K V] in
private theorem composite_one_sub_e_apply {J Y Z e : Module.End K V}
    (hJ : J = Z * e + Y * (1 - e)) (hee : e * e = e)
    (h1eZ : (1 - e) * Z = Z * (1 - e)) (h1eY : (1 - e) * Y = Y * (1 - e)) :
    ∀ v, (1 - e) (J v) = Y ((1 - e) v) := by
  have h1ee : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have h1e1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee]
    abel
  intro v
  have hZev : (1 - e) (Z (e v)) = 0 := by
    have h := congrArg (fun f : Module.End K V => f (e v)) h1eZ
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [show (1 - e) (e v) = 0 from by
      have h2 := congrArg (fun f : Module.End K V => f v) h1ee
      simpa [Module.End.mul_apply] using h2] at h
    simpa using h
  have hYev : (1 - e) (Y ((1 - e) v)) = Y ((1 - e) v) := by
    have h := congrArg (fun f : Module.End K V => f ((1 - e) v)) h1eY
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [show (1 - e) ((1 - e) v) = (1 - e) v from by
      have h2 := congrArg (fun f : Module.End K V => f v) h1e1
      simpa [Module.End.mul_apply] using h2] at h
    exact h
  calc (1 - e) (J v) = (1 - e) (Z (e v) + Y ((1 - e) v)) := by rw [apply_composite hJ v]
    _ = (1 - e) (Z (e v)) + (1 - e) (Y ((1 - e) v)) := map_add (1 - e) _ _
    _ = 0 + Y ((1 - e) v) := by rw [hZev, hYev]
    _ = Y ((1 - e) v) := zero_add _

omit [FiniteDimensional K V] in
private theorem composite_isometry {Q : QuadraticForm K V} {J Y Z e : Module.End K V}
    (hJ : J = Z * e + Y * (1 - e))
    (hY : ∀ v, Q (Y v) = Q v) (hZ : ∀ v, Q (Z v) = Q v)
    (hcross : ∀ v, polar Q (Z (e v)) (Y ((1 - e) v)) = 0)
    (hcross_ev : ∀ v, polar Q (e v) ((1 - e) v) = 0)
    (hdecomp : ∀ v, v = e v + (1 - e) v) :
    ∀ v, Q (J v) = Q v := by
  intro v
  have hQv : Q v = Q (e v) + Q ((1 - e) v) := by
    calc Q v = Q (e v + (1 - e) v) := congrArg Q (hdecomp v)
      _ = Q (e v) + Q ((1 - e) v) + polar Q (e v) ((1 - e) v) :=
          QuadraticMap.map_add Q _ _
      _ = Q (e v) + Q ((1 - e) v) := by rw [hcross_ev v, add_zero]
  calc Q (J v) = Q (Z (e v) + Y ((1 - e) v)) := by rw [apply_composite hJ v]
    _ = Q (Z (e v)) + Q (Y ((1 - e) v)) + polar Q (Z (e v)) (Y ((1 - e) v)) :=
        QuadraticMap.map_add Q _ _
    _ = Q (e v) + Q ((1 - e) v) + 0 := by
        rw [hZ (e v), hY ((1 - e) v), hcross v]
    _ = Q (e v) + Q ((1 - e) v) := by rw [add_zero]
    _ = Q v := by rw [hQv]

omit [FiniteDimensional K V] in
private theorem composite_poly_eq_zero {J Y Z e : Module.End K V}
    (hJ : J = Z * e + Y * (1 - e))
    (heJ : ∀ v, e (J v) = Z (e v))
    (h1eJ : ∀ v, (1 - e) (J v) = Y ((1 - e) v))
    (hZterm : (Z ^ 2 + Z + 1 : Module.End K V) * e = 0)
    (hYterm : (Y ^ 2 + Y + 1 : Module.End K V) * (1 - e) = 0)
    (hdecomp : ∀ v, v = e v + (1 - e) v) :
    J ^ 2 + J + 1 = 0 := by
  ext v
  set x : V := e v with hx
  set w : V := (1 - e) v with hw
  have hJvw : J v = Z x + Y w := by rw [apply_composite hJ v, hx, hw]
  have hJJw : J (J v) = Z (Z x) + Y (Y w) := by
    calc J (J v) = Z (e (J v)) + Y ((1 - e) (J v)) := by rw [apply_composite hJ (J v)]
      _ = Z (Z x) + Y (Y w) := by rw [heJ v, h1eJ v, hx, hw]
  have hvw : v = x + w := by rw [hdecomp v, hx, hw]
  have hZsum : Z (Z x) + Z x + x = 0 := by
    have h := congrArg (fun f : Module.End K V => f v) hZterm
    rw [show ((Z ^ 2 + Z + 1 : Module.End K V) * e) v = Z (Z x) + Z x + x by
        rw [Module.End.mul_apply, ← hx]
        simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply,
          Module.End.one_apply, map_add]] at h
    exact h
  have hYsum : Y (Y w) + Y w + w = 0 := by
    have h := congrArg (fun f : Module.End K V => f v) hYterm
    rw [show ((Y ^ 2 + Y + 1 : Module.End K V) * (1 - e)) v = Y (Y w) + Y w + w by
        rw [Module.End.mul_apply, ← hw]
        simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply,
          Module.End.one_apply, LinearMap.sub_apply, map_add, map_sub]] at h
    exact h
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
    Module.End.mul_apply, hJJw, hJvw]
  calc Z (Z x) + Y (Y w) + (Z x + Y w) + v
      = (Z (Z x) + Z x + x) + (Y (Y w) + Y w + w) := by
        rw [hvw]
        abel
    _ = 0 := by rw [hZsum, hYsum, add_zero]

omit [FiniteDimensional K V] in
private theorem add_sub_proj_apply (e : Module.End K V) (v : V) : e v + (1 - e) v = v := by
  simp [LinearMap.sub_apply, Module.End.one_apply]

omit [FiniteDimensional K V] in
private theorem exists_isometry_of_commute_aux (hK : (3 : K) ≠ 0) (Q : QuadraticForm K V)
    {Y Z : Module.End K V} (hYiso : ∀ v, Q (Y v) = Q v)
    (hZiso : ∀ v, Q (Z v) = Q v)
    (hY3v : ∀ v, Y (Y (Y v)) = v) (hZ3v : ∀ v, Z (Z (Z v)) = v)
    (hYZc : Commute Y Z)
    (hfix : LinearMap.ker (Y - 1) ⊓ LinearMap.ker (Z - 1) = ⊥) :
    ∃ J : Module.End K V, (∀ v, Q (J v) = Q v) ∧ J ^ 2 + J + 1 = 0 := by
  let e : Module.End K V := proj Y
  let ez : Module.End K V := proj Z
  have hee : e * e = e := proj_mul_self hK hY3v
  have hYe : Y * e = e := (proj_mul_eq hK hY3v).2
  have heY : e * Y = e := (proj_mul_eq hK hY3v).1
  have hZez : Z * ez = ez := (proj_mul_eq hK hZ3v).2
  have heZ : e * Z = Z * e := (proj_commute_of_commute hYZc).eq
  have heez : Commute e ez := proj_commute_proj hYZc
  have he1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h1eZ : (1 - e) * Z = Z * (1 - e) := by
    calc (1 - e) * Z = Z - e * Z := by rw [sub_mul, one_mul]
      _ = Z - Z * e := by rw [heZ]
      _ = Z * (1 - e) := by rw [mul_sub, mul_one]
  have h1eY : (1 - e) * Y = Y * (1 - e) := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hYe, heY]
  have hZez_e : ez * e = 0 := proj_mul_proj_eq_zero hfix heez hYe hZez
  have hZterm : (Z ^ 2 + Z + 1 : Module.End K V) * e = 0 := by
    rw [sq_add_self_add_one_eq_three_smul_proj hK Z, Algebra.smul_mul_assoc, hZez_e, smul_zero]
  have hYterm : (Y ^ 2 + Y + 1 : Module.End K V) * (1 - e) = 0 := by
    rw [sq_add_self_add_one_eq_three_smul_proj hK Y, Algebra.smul_mul_assoc, he1, smul_zero]
  let J : Module.End K V := Z * e + Y * (1 - e)
  have hJdef : J = Z * e + Y * (1 - e) := rfl
  have hdecomp : ∀ v, v = e v + (1 - e) v := fun v => (add_sub_proj_apply e v).symm
  have heJ : ∀ v, e (J v) = Z (e v) := composite_e_apply hJdef heY heZ hee he1
  have h1eJ : ∀ v, (1 - e) (J v) = Y ((1 - e) v) :=
    composite_one_sub_e_apply hJdef hee h1eZ h1eY
  have hcross : ∀ v, polar Q (Z (e v)) (Y ((1 - e) v)) = 0 := by
    intro v
    have hZev : Z (e v) = e (Z v) := by
      have h := congrArg (fun f : Module.End K V => f v) heZ
      simpa [Module.End.mul_apply] using h.symm
    have hfixZev : Y (Z (e v)) = Z (e v) := by
      rw [hZev]
      have h := congrArg (fun f : Module.End K V => f (Z v)) hYe
      simpa [Module.End.mul_apply] using h
    have hmem : Y ((1 - e) v) ∈ LinearMap.range (Y - 1) := by
      have h := congrArg (fun f : Module.End K V => f v) h1eY
      rw [Module.End.mul_apply, Module.End.mul_apply] at h
      rw [← h]
      exact proj_sub_mem_range hK hY3v (Y v)
    exact polar_eq_zero_of_fixed_of_mem_range hYiso hfixZev hmem
  have hcross_ev : ∀ v, polar Q (e v) ((1 - e) v) = 0 := by
    intro v
    exact polar_eq_zero_of_fixed_of_mem_range hYiso
      (proj_apply_fixed hK hY3v v) (proj_sub_mem_range hK hY3v v)
  refine ⟨J, composite_isometry hJdef hYiso hZiso hcross hcross_ev hdecomp, ?_⟩
  exact composite_poly_eq_zero hJdef heJ h1eJ hZterm hYterm hdecomp

omit [FiniteDimensional K V] in
theorem exists_isometry_of_commute (hK : (3 : K) ≠ 0) (Q : QuadraticForm K V)
    {y z : V ≃ₗ[K] V} (hy : ∀ v, Q (y v) = Q v) (hz : ∀ v, Q (z v) = Q v)
    (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hyz : Commute y z)
    (hfix : LinearMap.ker (y.toLinearMap - 1) ⊓ LinearMap.ker (z.toLinearMap - 1) = ⊥) :
    ∃ J : Module.End K V, (∀ v, Q (J v) = Q v) ∧ J ^ 2 + J + 1 = 0 := by
  let Y : Module.End K V := y.toLinearMap
  let Z : Module.End K V := z.toLinearMap
  have hY3v : ∀ v, Y (Y (Y v)) = v := by
    intro v
    have h := congrArg (fun f : V ≃ₗ[K] V => f v) hy3
    simpa [Y, LinearEquiv.pow_apply, Function.iterate_succ, Function.iterate_zero] using h
  have hZ3v : ∀ v, Z (Z (Z v)) = v := by
    intro v
    have h := congrArg (fun f : V ≃ₗ[K] V => f v) hz3
    simpa [Z, LinearEquiv.pow_apply, Function.iterate_succ, Function.iterate_zero] using h
  have hYZc : Commute Y Z := by
    show Y * Z = Z * Y
    have h := congrArg LinearEquiv.toLinearMap hyz.eq
    simpa [Y, Z, LinearEquiv.coe_toLinearMap_mul] using h
  exact exists_isometry_of_commute_aux hK Q (fun v => hy v) (fun v => hz v) hY3v hZ3v hYZc hfix

theorem exists_totallySingular_of_isometry [Finite K] (hK : (3 : K) ≠ 0)
    (Q : QuadraticForm K V) (J : Module.End K V) (hJ : ∀ v, Q (J v) = Q v)
    (hJ3 : J ^ 2 + J + 1 = 0) (hdim : 8 ≤ Module.finrank K V) :
    ∃ W : Submodule K V, Module.finrank K W = 4 ∧ ∀ w ∈ W, Q w = 0 := by
  by_cases hsplit : ∃ ω : K, ω ^ 2 + ω + 1 = 0
  · obtain ⟨ω, hω⟩ := hsplit
    exact exists_totallySingular_of_isometry_split hK Q J hJ hJ3 hω hdim
  · push Not at hsplit
    exact exists_totallySingular_of_isometry_nonsplit hK Q J hJ hJ3 hsplit hdim

theorem exists_totallySingular_of_commute [Finite K] (hK : (3 : K) ≠ 0)
    (Q : QuadraticForm K V) {y z : V ≃ₗ[K] V} (hy : ∀ v, Q (y v) = Q v)
    (hz : ∀ v, Q (z v) = Q v) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hyz : Commute y z)
    (hfix : LinearMap.ker (y.toLinearMap - 1) ⊓ LinearMap.ker (z.toLinearMap - 1) = ⊥)
    (hdim : 8 ≤ Module.finrank K V) :
    ∃ W : Submodule K V, Module.finrank K W = 4 ∧ ∀ w ∈ W, Q w = 0 := by
  obtain ⟨J, hJ, hJ3⟩ := exists_isometry_of_commute hK Q hy hz hy3 hz3 hyz hfix
  exact exists_totallySingular_of_isometry hK Q J hJ hJ3 hdim
