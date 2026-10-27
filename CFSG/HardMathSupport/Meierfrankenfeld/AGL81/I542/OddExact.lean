module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Polynomial Module

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

theorem le_comap_aeval {T : Module.End K M} {P : Submodule K M} (hP : P ≤ P.comap T)
    (p : K[X]) : P ≤ P.comap (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    simp only [Submodule.mem_comap, map_add, LinearMap.add_apply]
    exact P.add_mem (hp hx) (hq hx)
  | monomial n a =>
    intro x hx
    simp only [Submodule.mem_comap, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply]
    refine P.smul_mem a ?_
    have : ∀ k : ℕ, ∀ y ∈ P, (T ^ k) y ∈ P := by
      intro k
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ih =>
        intro y hy
        rw [pow_succ, Module.End.mul_apply]
        exact ih _ (hP hy)
    simpa using this n x hx

theorem aeval_mapQ {T : Module.End K M} {P : Submodule K M} (hP : P ≤ P.comap T) (p : K[X]) :
    aeval (P.mapQ P T hP) p = P.mapQ P (aeval T p) (le_comap_aeval hP p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq]
    ext x
    simp
  | monomial n a =>
    ext x
    simp only [aeval_monomial, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← Submodule.mapQ_pow P hP n, Submodule.mapQ_apply, Submodule.Quotient.mk_smul]

theorem aeval_restrict_apply {T : Module.End K M} {Z : Submodule K M} (hZ : ∀ x ∈ Z, T x ∈ Z)
    (p : K[X]) (z : ↥Z) : ((aeval (T.restrict hZ) p z : ↥Z) : M) = aeval T p (z : M) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    congr 1
    induction n generalizing z with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

variable [FiniteDimensional K M]

theorem finrank_inf_ker_aeval_eq {T : Module.End K M} {f h : K[X]} (hcop : IsCoprime f h)
    (hfh : aeval T (f * h) = 0) {Z₀ Z₁ : Submodule K M} (hle : Z₀ ≤ Z₁)
    (h₀ : ∀ x ∈ Z₀, T x ∈ Z₀) (h₁ : ∀ x ∈ Z₁, T x ∈ Z₁) :
    finrank K ↥(Z₁ ⊓ LinearMap.ker (aeval T f)) =
      finrank K ↥(Z₀ ⊓ LinearMap.ker (aeval T f)) +
      finrank K ↥(LinearMap.ker (aeval ((Z₀.comap Z₁.subtype).mapQ (Z₀.comap Z₁.subtype)
        (T.restrict h₁) (fun _ hz => h₀ _ hz)) f)) := by
  classical
  set P : Submodule K ↥Z₁ := Z₀.comap Z₁.subtype with hPdef
  set T₁ : Module.End K ↥Z₁ := T.restrict h₁ with hT₁
  have hP : P ≤ P.comap T₁ := fun z hz => h₀ _ hz
  set Tb : Module.End K (↥Z₁ ⧸ P) := P.mapQ P T₁ hP with hTb
  set K₁ : Submodule K ↥Z₁ := LinearMap.ker (aeval T₁ f) with hK₁
  have hK₁mem : ∀ z : ↥Z₁, z ∈ K₁ ↔ aeval T f (z : M) = 0 := by
    intro z
    rw [hK₁, LinearMap.mem_ker, ← aeval_restrict_apply h₁ f z]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact Subtype.ext h
  have e₁ : finrank K ↥(Z₁ ⊓ LinearMap.ker (aeval T f)) = finrank K ↥K₁ := by
    have : (K₁.map Z₁.subtype) = Z₁ ⊓ LinearMap.ker (aeval T f) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, (hK₁mem z).1 hz⟩
      · rintro ⟨hv, hf⟩
        exact ⟨⟨v, hv⟩, (hK₁mem ⟨v, hv⟩).2 hf, rfl⟩
    rw [← this, Submodule.finrank_map_subtype_eq]
  have e₀ : finrank K ↥(Z₀ ⊓ LinearMap.ker (aeval T f)) = finrank K ↥(K₁ ⊓ P) := by
    have : ((K₁ ⊓ P).map Z₁.subtype) = Z₀ ⊓ LinearMap.ker (aeval T f) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, hPdef,
        Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
        exact ⟨hz0, (hK₁mem z).1 hz⟩
      · rintro ⟨hv0, hf⟩
        exact ⟨⟨v, hle hv0⟩, ⟨(hK₁mem ⟨v, hle hv0⟩).2 hf, hv0⟩, rfl⟩
    rw [← this, Submodule.finrank_map_subtype_eq]
  set φ : ↥K₁ →ₗ[K] ↥(LinearMap.ker (aeval Tb f)) :=
    (P.mkQ.comp K₁.subtype).codRestrict (LinearMap.ker (aeval Tb f)) (fun z => by
      rw [LinearMap.mem_ker, hTb, aeval_mapQ hP f]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Submodule.mkQ_apply, Submodule.mapQ_apply]
      have hz : aeval T₁ f (z : ↥Z₁) = 0 := z.2
      rw [hz]
      rfl) with hφ
  have hφsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P q
    obtain ⟨a, b, hab⟩ := hcop
    have hqz : aeval T₁ f z ∈ P := by
      rw [LinearMap.mem_ker, hTb, aeval_mapQ hP f, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hq
      exact hq
    have hz₁ : aeval T₁ (b * h) z ∈ K₁ := by
      rw [hK₁, LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul]
      have : f * (b * h) = b * (f * h) := by ring
      rw [this, map_mul, Module.End.mul_apply]
      have h0 : aeval T₁ (f * h) = 0 := by
        ext w
        rw [aeval_restrict_apply h₁, hfh]
        rfl
      rw [h0, LinearMap.zero_apply, map_zero]
    refine ⟨⟨_, hz₁⟩, ?_⟩
    apply Subtype.ext
    simp only [hφ, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have hsplit : z = aeval T₁ (a * f) z + aeval T₁ (b * h) z := by
      rw [← LinearMap.add_apply, ← map_add, hab, map_one, Module.End.one_apply]
    have hmem : aeval T₁ (a * f) z ∈ P := by
      rw [map_mul, Module.End.mul_apply]
      exact le_comap_aeval hP a hqz
    have : aeval T₁ (b * h) z - z = -aeval T₁ (a * f) z := by
      have h' : aeval T₁ (a * f) z + aeval T₁ (b * h) z - z = 0 := by rw [← hsplit, sub_self]
      rw [← sub_eq_zero]
      calc aeval T₁ (b * h) z - z - -aeval T₁ (a * f) z
          = aeval T₁ (a * f) z + aeval T₁ (b * h) z - z := by abel
        _ = 0 := h'
    rw [this]
    exact P.neg_mem hmem
  have hφker : finrank K ↥(LinearMap.ker φ) = finrank K ↥(K₁ ⊓ P) := by
    have : (LinearMap.ker φ).map K₁.subtype = K₁ ⊓ P := by
      ext z
      simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.2, ?_⟩
        have := congrArg Subtype.val hw
        simp only [hφ, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, Submodule.mkQ_apply, ZeroMemClass.coe_zero,
          Submodule.Quotient.mk_eq_zero] at this
        exact this
      · rintro ⟨hz, hzP⟩
        refine ⟨⟨z, hz⟩, ?_, rfl⟩
        apply Subtype.ext
        simp only [hφ, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, Submodule.mkQ_apply, ZeroMemClass.coe_zero,
          Submodule.Quotient.mk_eq_zero]
        exact hzP
    rw [← this, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, hφker] at hrn
  rw [e₁, e₀, ← hrn, add_comm]

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
