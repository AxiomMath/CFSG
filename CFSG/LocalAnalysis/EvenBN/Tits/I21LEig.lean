module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.AdjoinRoot

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Polynomial

namespace Eig

theorem core {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    {p : ℕ} (hp : p.Prime) {f : (ZMod 2)[X]} (hf : Irreducible f) (hfd : f ∣ X ^ p - 1)
    (a b c : W →ₗ[ZMod 2] W) (hai : Function.Injective a) (hbi : Function.Injective b)
    (hca : c * a = a * c) (hcb : c * b = b * c) (hba : b * a = c * (a * b))
    (hker : aeval c f = 0) (hfix : ∀ w, c w = w → w = 0) : p ∣ finrank (ZMod 2) W := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  let ψ : AdjoinRoot f →ₐ[ZMod 2] Module.End (ZMod 2) W :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval c) (by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
      simp [hker])
  have hψ : ∀ q : (ZMod 2)[X], ψ (AdjoinRoot.mk f q) = aeval c q := fun q => rfl
  letI : Module (AdjoinRoot f) W := Module.compHom W ψ.toRingHom
  have hsmul : ∀ (k : AdjoinRoot f) (w : W), k • w = ψ k w := fun k w => rfl
  haveI : IsScalarTower (ZMod 2) (AdjoinRoot f) W :=
    ⟨fun r k w => by simp [hsmul]⟩
  haveI : Module.Finite (AdjoinRoot f) W := Module.Finite.of_restrictScalars_finite (ZMod 2) _ W
  have hcomm : ∀ (x : W →ₗ[ZMod 2] W), x * c = c * x → ∀ (k : AdjoinRoot f) (w : W),
      x (ψ k w) = ψ k (x w) := by
    intro x hx k w
    induction k using AdjoinRoot.induction_on with
    | ih q =>
      rw [hψ]
      have := Algebra.commute_of_mem_adjoin_singleton_of_commute
        (q.aeval_mem_adjoin_singleton (ZMod 2) c) (show Commute x c from hx)
      exact congrArg (fun y => y w) this.eq
  let aK : W →ₗ[AdjoinRoot f] W :=
    { toFun := a, map_add' := a.map_add,
      map_smul' := fun k w => hcomm a hca.symm k w }
  let bK : W →ₗ[AdjoinRoot f] W :=
    { toFun := b, map_add' := b.map_add,
      map_smul' := fun k w => hcomm b hcb.symm k w }
  rcases subsingleton_or_nontrivial W with hW | hW
  · have : finrank (ZMod 2) W = 0 := Module.finrank_zero_of_subsingleton
    rw [this]; exact dvd_zero _
  set ω : AdjoinRoot f := AdjoinRoot.root f with hω
  have hωw : ∀ w, ω • w = c w := fun w => by
    rw [hsmul]
    show ψ (AdjoinRoot.mk f X) w = _
    rw [hψ]; simp
  have hrel : bK ∘ₗ aK = ω • (aK ∘ₗ bK) := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    show b (a w) = ω • a (b w)
    rw [hωw]
    exact congrArg (fun x => x w) hba
  have hωp : ω ^ p = 1 := by
    have h1 : AdjoinRoot.mk f (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hfd
    rw [map_sub, map_pow, map_one, sub_eq_zero, AdjoinRoot.mk_X] at h1
    exact h1
  have hω1 : ω ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    apply hfix
    rw [← hωw, h, one_smul]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ω = p := orderOf_eq_prime hωp hω1
  have hd := congrArg LinearMap.det hrel
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hd
  have ha0 : LinearMap.det aK ≠ 0 := fun h0 =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hai)
  have hb0 : LinearMap.det bK ≠ 0 := fun h0 =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hbi)
  have hpow : ω ^ finrank (AdjoinRoot f) W = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero ha0 hb0)
    rw [one_mul]
    linear_combination (-1 : AdjoinRoot f) * hd
  have h1 : p ∣ finrank (AdjoinRoot f) W := hord ▸ orderOf_dvd_of_pow_eq_one hpow
  exact h1.trans (Dvd.intro_left _ (Module.finrank_mul_finrank (ZMod 2) (AdjoinRoot f) W))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem coe_restrict_pow (c : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) (hc : ∀ x ∈ U, c x ∈ U)
    (n : ℕ) (w : U) : (((c.restrict hc) ^ n) w : V) = (c ^ n) (w : V) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem aeval_restrict (c : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) (hc : ∀ x ∈ U, c x ∈ U)
    (q : (ZMod 2)[X]) (w : U) :
    ((aeval (c.restrict hc) q w : U) : V) = aeval c q (w : V) := by
  induction q using Polynomial.induction_on' generalizing w with
  | add f g hf hg => simp [hf, hg]
  | monomial n k =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, coe_restrict_pow]

theorem commute_aeval {a c : V →ₗ[ZMod 2] V} (h : c * a = a * c) (q : (ZMod 2)[X]) :
    aeval c q * a = a * aeval c q := by
  have := Algebra.commute_of_mem_adjoin_singleton_of_commute
    (q.aeval_mem_adjoin_singleton (ZMod 2) c) (show Commute a c from h.symm)
  exact this.eq.symm

theorem dvd_of_le_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b c : V →ₗ[ZMod 2] V)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (hca : c * a = a * c) (hcb : c * b = b * c) (hba : b * a = c * (a * b))
    (hfix : ∀ v, c v = v → v = 0) :
    ∀ (n : ℕ) (g : (ZMod 2)[X]), g.natDegree = n → g ∣ X ^ p - 1 →
      ∀ U : Submodule (ZMod 2) V, (∀ u ∈ U, a u ∈ U) → (∀ u ∈ U, b u ∈ U) → (∀ u ∈ U, c u ∈ U) →
        U ≤ LinearMap.ker (aeval c g) → p ∣ finrank (ZMod 2) U := by
  have hsep : (X ^ p - 1 : (ZMod 2)[X]).Separable := by
    have h1 : ((p : ℕ) : ZMod 2) ≠ 0 := by
      rw [ZMod.natCast_eq_one_iff_odd.mpr (hp.odd_of_ne_two hp2)]
      exact one_ne_zero
    simpa using Polynomial.separable_X_pow_sub_C (1 : ZMod 2) h1 one_ne_zero
  have hne : (X ^ p - 1 : (ZMod 2)[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hp.pos (1 : ZMod 2)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hgn hgd U ha hb hc hU
    have hg0 : g ≠ 0 := fun h0 => hne (by rw [h0, zero_dvd_iff] at hgd; exact hgd)
    by_cases hgu : IsUnit g
    · have hker : LinearMap.ker (aeval c g) = ⊥ := by
        rw [← LinearMap.isUnit_iff_ker_eq_bot]
        exact hgu.map (aeval c)
      have : U = ⊥ := le_bot_iff.mp (hker ▸ hU)
      subst this
      simp
    · obtain ⟨f, hf, hfg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg0
      obtain ⟨h, rfl⟩ := hfg
      have hf0 : f ≠ 0 := hf.ne_zero
      have hh0 : h ≠ 0 := right_ne_zero_of_mul hg0
      have hdeg : h.natDegree < n := by
        rw [← hgn, natDegree_mul hf0 hh0]
        have := Irreducible.natDegree_pos hf
        omega
      have hfd : f ∣ X ^ p - 1 := (dvd_mul_right f h).trans hgd
      have hhd : h ∣ X ^ p - 1 := (dvd_mul_left h f).trans hgd
      have hcop : IsCoprime f h := (hsep.of_dvd hgd).isCoprime
      have hap : ∀ (x : V →ₗ[ZMod 2] V), c * x = x * c → ∀ (q : (ZMod 2)[X]) (u : V),
          aeval c q (x u) = x (aeval c q u) := fun x hx q u =>
        congrArg (fun y => y u) (commute_aeval hx q)
      have hstab : ∀ (x : V →ₗ[ZMod 2] V), (∀ u ∈ U, x u ∈ U) → c * x = x * c →
          ∀ q : (ZMod 2)[X], ∀ u ∈ U ⊓ LinearMap.ker (aeval c q),
            x u ∈ U ⊓ LinearMap.ker (aeval c q) := by
        intro x hx hcx q u hu
        obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
        refine Submodule.mem_inf.mpr ⟨hx u hu1, ?_⟩
        rw [LinearMap.mem_ker, hap x hcx q u, LinearMap.mem_ker.mp hu2, map_zero]
      have hcc : c * c = c * c := rfl
      have hsup : (U ⊓ LinearMap.ker (aeval c f)) ⊔ (U ⊓ LinearMap.ker (aeval c h)) = U := by
        apply le_antisymm
        · exact sup_le inf_le_left inf_le_left
        · intro u hu
          obtain ⟨s, t, hst⟩ := hcop
          have hu' : aeval c (f * h) u = 0 := LinearMap.mem_ker.mp (hU hu)
          have hmem : ∀ q : (ZMod 2)[X], aeval c q u ∈ U := fun q =>
            Polynomial.aeval_apply_smul_mem_of_le_comap hu q c (fun x hx => hc x hx)
          rw [Submodule.mem_sup]
          refine ⟨aeval c (t * h) u, Submodule.mem_inf.mpr ⟨hmem _, ?_⟩, aeval c (s * f) u,
            Submodule.mem_inf.mpr ⟨hmem _, ?_⟩, ?_⟩
          · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul]
            have : f * (t * h) = t * (f * h) := by ring
            rw [this, map_mul, Module.End.mul_apply, hu', map_zero]
          · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul]
            have : h * (s * f) = s * (f * h) := by ring
            rw [this, map_mul, Module.End.mul_apply, hu', map_zero]
          · rw [← LinearMap.add_apply, ← map_add]
            have : t * h + s * f = 1 := by linear_combination hst
            rw [this]; simp
      have hdisj : Disjoint (U ⊓ LinearMap.ker (aeval c f)) (U ⊓ LinearMap.ker (aeval c h)) :=
        (Polynomial.disjoint_ker_aeval_of_isCoprime c hcop).mono inf_le_right inf_le_right
      have hfin := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ LinearMap.ker (aeval c f))
        (U ⊓ LinearMap.ker (aeval c h))
      rw [hsup, disjoint_iff.mp hdisj, finrank_bot, add_zero] at hfin
      rw [hfin]
      refine dvd_add ?_ (ih h.natDegree hdeg h rfl hhd _ ?_ ?_ ?_ inf_le_right)
      · have ha₁ : ∀ u ∈ U ⊓ LinearMap.ker (aeval c f), a u ∈ U ⊓ LinearMap.ker (aeval c f) :=
          fun u hu => hstab a ha hca f u hu
        have hb₁ : ∀ u ∈ U ⊓ LinearMap.ker (aeval c f), b u ∈ U ⊓ LinearMap.ker (aeval c f) :=
          fun u hu => hstab b hb hcb f u hu
        have hc₁ : ∀ u ∈ U ⊓ LinearMap.ker (aeval c f), c u ∈ U ⊓ LinearMap.ker (aeval c f) :=
          fun u hu => hstab c hc hcc f u hu
        refine core hp hf hfd (a.restrict ha₁) (b.restrict hb₁) (c.restrict hc₁)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro x y hxy; exact Subtype.ext (hai (congrArg Subtype.val hxy))
        · intro x y hxy; exact Subtype.ext (hbi (congrArg Subtype.val hxy))
        · exact LinearMap.ext fun w => Subtype.ext (by
            simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply]
            exact congrArg (fun z => z (w : V)) hca)
        · exact LinearMap.ext fun w => Subtype.ext (by
            simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply]
            exact congrArg (fun z => z (w : V)) hcb)
        · exact LinearMap.ext fun w => Subtype.ext (by
            simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply]
            exact congrArg (fun z => z (w : V)) hba)
        · refine LinearMap.ext fun w => Subtype.ext ?_
          rw [aeval_restrict]
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp w.2).2
        · intro w hw
          exact Subtype.ext (hfix w (congrArg Subtype.val hw))
      · exact fun u hu => hstab a ha hca h u hu
      · exact fun u hu => hstab b hb hcb h u hu
      · exact fun u hu => hstab c hc hcc h u hu

end Eig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem eigen_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b c : V ≃ₗ[ZMod 2] V}
    (hc : c = b * a * b⁻¹ * a⁻¹) (hcp : orderOf c = p) (hca : c * a = a * c)
    (hcb : c * b = b * c) (hfix : ∀ v : V, c v = v → v = 0) : p ∣ finrank (ZMod 2) V := by
  let ι := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)
  have hcp' : (ι c) ^ p = 1 := by rw [← map_pow, ← hcp, pow_orderOf_eq_one, map_one]
  have hrel : ι b * ι a = ι c * (ι a * ι b) := by
    rw [← map_mul, ← map_mul, ← map_mul]
    congr 1
    rw [hc]; group
  have hca' : ι c * ι a = ι a * ι c := by rw [← map_mul, ← map_mul, hca]
  have hcb' : ι c * ι b = ι b * ι c := by rw [← map_mul, ← map_mul, hcb]
  have hai : Function.Injective (ι a) := a.injective
  have hbi : Function.Injective (ι b) := b.injective
  have key := Eig.dvd_of_le_ker hp hp2 (ι a) (ι b) (ι c) hai hbi hca' hcb' hrel hfix
    ((X ^ p - 1 : (ZMod 2)[X]).natDegree) (X ^ p - 1) rfl dvd_rfl ⊤ (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (by
      intro v _
      simp [hcp'])
  simpa [finrank_top] using key

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
