module

public import CFSG.GroupTheory.SteinbergCBHHBNilpotentCentralizer
public import CFSG.GroupTheory.SteinbergCBHHBMonomialFixed
public import CFSG.GroupTheory.SteinbergCBHHBBurnside
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K W G : Type*} [Field K] [AddCommGroup W] [Module K W] [Group G]

section Characters

variable (ρ : G →* (Module.End K W)ˣ)
  (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
    ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)

@[expose] def centralScalar (c : Subgroup.center G) : K := Classical.choose (hsc c c.2)

theorem centralScalar_spec (c : Subgroup.center G) :
    ((ρ c : (Module.End K W)ˣ) : Module.End K W) = centralScalar ρ hsc c • 1 :=
  Classical.choose_spec (hsc c c.2)

variable [Nontrivial W]

theorem smul_one_injective : Function.Injective fun μ : K => μ • (1 : Module.End K W) :=
  smul_left_injective K one_ne_zero

theorem centralScalar_mul (c c' : Subgroup.center G) :
    centralScalar ρ hsc (c * c') = centralScalar ρ hsc c * centralScalar ρ hsc c' := by
  have h1 := centralScalar_spec ρ hsc (c * c')
  have h2 := centralScalar_spec ρ hsc c
  have h3 := centralScalar_spec ρ hsc c'
  have h4 : ((ρ ((c * c' : Subgroup.center G) : G) : (Module.End K W)ˣ) : Module.End K W) =
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) * ((ρ c' : (Module.End K W)ˣ) :
        Module.End K W) := by
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  apply smul_one_injective (K := K) (W := W)
  simp only
  rw [← h1, h4, h2, h3, smul_mul_assoc, one_mul, smul_smul]

theorem centralScalar_one : centralScalar ρ hsc 1 = 1 := by
  have h1 := centralScalar_spec ρ hsc 1
  rw [Subgroup.coe_one, map_one, Units.val_one] at h1
  apply smul_one_injective (K := K) (W := W)
  simp only
  rw [← h1, one_smul]

omit [Nontrivial W] in
theorem centralScalar_injective (hρ : Function.Injective ρ) :
    Function.Injective (centralScalar ρ hsc) := by
  intro c c' h
  apply Subtype.ext
  apply hρ
  apply Units.ext
  rw [centralScalar_spec ρ hsc c, centralScalar_spec ρ hsc c', h]

variable (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)

@[expose] def commChar (s : G) : G →* K where
  toFun t := centralScalar ρ hsc ⟨t * s * t⁻¹ * s⁻¹, hcl s t⟩
  map_one' := by
    rw [← centralScalar_one ρ hsc]
    congr 1
    apply Subtype.ext
    simp
  map_mul' t t' := by
    rw [← centralScalar_mul]
    congr 1
    apply Subtype.ext
    have hc := Subgroup.mem_center_iff.1 (hcl s t')
    change t * t' * s * (t * t')⁻¹ * s⁻¹ =
      (t * s * t⁻¹ * s⁻¹) * (t' * s * t'⁻¹ * s⁻¹)
    calc t * t' * s * (t * t')⁻¹ * s⁻¹ = t * ((t' * s * t'⁻¹ * s⁻¹) * s) * t⁻¹ * s⁻¹ := by
          group
      _ = t * (t' * s * t'⁻¹ * s⁻¹) * s * t⁻¹ * s⁻¹ := by group
      _ = (t' * s * t'⁻¹ * s⁻¹) * t * s * t⁻¹ * s⁻¹ := by rw [← hc t]
      _ = (t * s * t⁻¹ * s⁻¹) * (t' * s * t'⁻¹ * s⁻¹) := by
          have hc' := Subgroup.mem_center_iff.1 (hcl s t') (t * s * t⁻¹ * s⁻¹)
          calc (t' * s * t'⁻¹ * s⁻¹) * t * s * t⁻¹ * s⁻¹ =
              (t' * s * t'⁻¹ * s⁻¹) * (t * s * t⁻¹ * s⁻¹) := by group
            _ = (t * s * t⁻¹ * s⁻¹) * (t' * s * t'⁻¹ * s⁻¹) := hc'.symm

theorem conj_eq_commChar_smul (s t : G) :
    ((ρ t : (Module.End K W)ˣ) : Module.End K W) * ((ρ s : (Module.End K W)ˣ) :
      Module.End K W) * ((ρ t⁻¹ : (Module.End K W)ˣ) : Module.End K W) =
      commChar ρ hsc hcl s t • ((ρ s : (Module.End K W)ˣ) : Module.End K W) := by
  have h1 : t * s * t⁻¹ = (t * s * t⁻¹ * s⁻¹) * s := by group
  rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, h1, map_mul, Units.val_mul]
  change ((ρ ((⟨t * s * t⁻¹ * s⁻¹, hcl s t⟩ : Subgroup.center G) : G) :
    (Module.End K W)ˣ) : Module.End K W) * _ = _
  rw [centralScalar_spec ρ hsc, smul_mul_assoc, one_mul]
  rfl

theorem mem_center_of_commChar_eq (hρ : Function.Injective ρ) {s s' : G}
    (h : commChar ρ hsc hcl s = commChar ρ hsc hcl s') : s⁻¹ * s' ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := congrArg (fun χ : G →* K => χ g) h
  simp only [commChar, MonoidHom.coe_mk, OneHom.coe_mk] at hg
  have hc := congrArg Subtype.val (centralScalar_injective ρ hsc hρ hg)
  simp only at hc
  calc g * (s⁻¹ * s') = (s'⁻¹ * g⁻¹ * (g * s * g⁻¹ * s⁻¹) * s)⁻¹ := by group
    _ = (s'⁻¹ * g⁻¹ * (g * s' * g⁻¹ * s'⁻¹) * s)⁻¹ := by rw [hc]
    _ = s⁻¹ * s' * g := by group

end Characters

section Basis

variable (ρ : G →* (Module.End K W)ˣ) (hρ : Function.Injective ρ)
  (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
    ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
  (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G) [Nontrivial W]

@[expose] def adRep : G →* Module.End K (Module.End K W) where
  toFun t := (LinearMap.mulLeft K ((ρ t : (Module.End K W)ˣ) : Module.End K W)).comp
    (LinearMap.mulRight K ((ρ t⁻¹ : (Module.End K W)ˣ) : Module.End K W))
  map_one' := by
    ext φ
    simp
  map_mul' t t' := by
    ext φ
    simp [mul_assoc]

include hρ hsc hcl in
theorem linearIndependent_rho_out :
    LinearIndependent K fun x : G ⧸ Subgroup.center G =>
      ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) := by
  refine linearIndependent_of_ne_monoidHom (adRep ρ) _ (fun x => commChar ρ hsc hcl x.out)
    (fun x x' h => ?_) (fun x => (ρ x.out).ne_zero) fun t x => ?_
  · have := mem_center_of_commChar_eq ρ hsc hcl hρ h
    rw [← x.out_eq', ← x'.out_eq']
    exact QuotientGroup.eq.2 this
  · change ((ρ t : (Module.End K W)ˣ) : Module.End K W) * _ * _ = _
    exact conj_eq_commChar_smul ρ hsc hcl x.out t

end Basis

section Core

variable [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W] [Finite G]

omit [Finite G] in
theorem span_range_rho (ρ : G →* (Module.End K W)ˣ)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤) :
    Submodule.span K (Set.range fun g => ((ρ g : (Module.End K W)ˣ) : Module.End K W)) = ⊤ := by
  have h := span_eq_top_of_irreducible
    (MonoidHom.mrange ((Units.coeHom (Module.End K W)).comp ρ)) fun W₁ hW₁ =>
      hirr W₁ fun g w hw => hW₁ _ ⟨g, rfl⟩ w hw
  rw [MonoidHom.coe_mrange] at h
  exact h

omit [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W] [Finite G] in
theorem rho_eq_smul_rho_out (ρ : G →* (Module.End K W)ˣ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1) (g : G) :
    ((ρ g : (Module.End K W)ˣ) : Module.End K W) =
      centralScalar ρ hsc ⟨((g : G ⧸ Subgroup.center G).out)⁻¹ * g,
        QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ Subgroup.center G))⟩ •
        ((ρ ((g : G ⧸ Subgroup.center G).out) : (Module.End K W)ˣ) : Module.End K W) := by
  set y := (g : G ⧸ Subgroup.center G).out
  have hc : y⁻¹ * g ∈ Subgroup.center G := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have h1 : ((ρ g : (Module.End K W)ˣ) : Module.End K W) =
      ((ρ y : (Module.End K W)ˣ) : Module.End K W) *
        ((ρ (y⁻¹ * g) : (Module.End K W)ˣ) : Module.End K W) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  rw [h1]
  change _ * ((ρ ((⟨y⁻¹ * g, hc⟩ : Subgroup.center G) : G) : (Module.End K W)ˣ) :
    Module.End K W) = _
  rw [centralScalar_spec ρ hsc, mul_smul_comm, mul_one]

omit [Finite G] in
theorem span_range_rho_out (ρ : G →* (Module.End K W)ˣ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤) :
    Submodule.span K (Set.range fun x : G ⧸ Subgroup.center G =>
      ((ρ x.out : (Module.End K W)ˣ) : Module.End K W)) = ⊤ := by
  rw [eq_top_iff, ← span_range_rho ρ hirr]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  change ((ρ g : (Module.End K W)ˣ) : Module.End K W) ∈ _
  rw [rho_eq_smul_rho_out ρ hsc g]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [Finite G] in
theorem finrank_sq_eq_card_quotient_center (ρ : G →* (Module.End K W)ˣ)
    (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤) :
    finrank K W ^ 2 = Nat.card (G ⧸ Subgroup.center G) := by
  let b := Basis.mk (linearIndependent_rho_out ρ hρ hsc hcl) (span_range_rho_out ρ hsc hirr).ge
  rw [← Module.finrank_eq_nat_card_basis b, Module.finrank_linearMap, sq]

end Core

section Main

variable [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W] [Finite G]

theorem irreducible_core {p m : ℕ} [hp : Fact p.Prime] [CharP K p] (hm : 1 ≤ m)
    (ρ : G →* (Module.End K W)ˣ) (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤)
    (hnab : ∃ g : G, g ∉ Subgroup.center G) (A : (Module.End K W)ˣ) (θ : MulAut G)
    (hAθ : ∀ g, A * ρ g * A⁻¹ = ρ (θ g)) (hAP : A ^ (p ^ m) = 1)
    (hfpf : ∀ g : G, g⁻¹ * (θ ^ (p ^ (m - 1))) g ∈ Subgroup.center G →
      g ∈ Subgroup.center G) :
    ((A : Module.End K W) - 1) ^ (p ^ m - 1) ≠ 0 ∨
      (finrank K W = p ^ m - 1 ∧ ((A : Module.End K W) - 1) ^ (p ^ m - 2) ≠ 0) := by
  classical
  have : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  set P := p ^ m with hPdef
  have hP2 : 2 ≤ P := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
  set b := Basis.mk (linearIndependent_rho_out ρ hρ hsc hcl)
    (span_range_rho_out ρ hsc hirr).ge with hbdef
  have hbx : ∀ x, b x = ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) := fun x => by
    rw [hbdef, Basis.mk_apply]
  have hθZ : ∀ (φ : MulAut G), ∀ c ∈ Subgroup.center G, φ c ∈ Subgroup.center G := by
    intro φ c hc
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hc g']
  have hθmap : (Subgroup.center G).map θ.toMonoidHom = Subgroup.center G := by
    refine le_antisymm ?_ fun c hc => ⟨θ.symm c, hθZ θ.symm c hc, by simp⟩
    rintro _ ⟨c, hc, rfl⟩
    exact hθZ θ c hc
  set π : Equiv.Perm (G ⧸ Subgroup.center G) :=
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) θ hθmap).toEquiv with hπdef
  have hπ : ∀ g : G, π (g : G ⧸ Subgroup.center G) = ((θ g : G) : G ⧸ Subgroup.center G) :=
    fun g => QuotientGroup.congr_mk _ _ _ _ g
  have hπpow : ∀ (n : ℕ) (g : G), (π ^ n) (g : G ⧸ Subgroup.center G) =
      (((θ ^ n) g : G) : G ⧸ Subgroup.center G) := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hπ, pow_succ', MulAut.mul_apply]
  have hAθn : ∀ (n : ℕ) (g : G), A ^ n * ρ g * (A ^ n)⁻¹ = ρ ((θ ^ n) g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' θ n, MulAut.mul_apply, ← hAθ, ← ih, pow_succ' A n]
      group
  have hθP : ∀ g, (θ ^ P) g = g := fun g => hρ (by rw [← hAθn, hAP]; group)
  set T : Module.End K (Module.End K W) := (LinearMap.mulLeft K (A : Module.End K W)).comp
    (LinearMap.mulRight K ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W)) with hTdef
  have hmemc : ∀ x : G ⧸ Subgroup.center G,
      (π x).out⁻¹ * θ x.out ∈ Subgroup.center G := fun x => by
    refine QuotientGroup.eq.1 ?_
    rw [QuotientGroup.out_eq', ← hπ, QuotientGroup.out_eq']
  set c : G ⧸ Subgroup.center G → K := fun x => centralScalar ρ hsc ⟨_, hmemc x⟩ with hcdef
  have hT : ∀ x, T (b x) = c x • b (π x) := by
    intro x
    rw [hbx, hbx]
    change (A : Module.End K W) * ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) *
      ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) = _
    rw [← Units.val_mul, ← Units.val_mul, hAθ]
    have h1 : θ x.out = (π x).out * ((π x).out⁻¹ * θ x.out) := by group
    rw [h1, map_mul, Units.val_mul]
    change _ * ((ρ ((⟨_, hmemc x⟩ : Subgroup.center G) : G) : (Module.End K W)ˣ) :
      Module.End K W) = _
    rw [centralScalar_spec ρ hsc, mul_smul_comm, mul_one]
  have he : π 1 = 1 := by
    rw [← QuotientGroup.mk_one, hπ, map_one]
  have hπP : ∀ x, (π ^ P) x = x := fun x => by
    rw [← QuotientGroup.out_eq' x, hπpow, hθP]
  have hfree : ∀ x : G ⧸ Subgroup.center G, x ≠ 1 → ∀ i j, i < P → j < P →
      (π ^ i) x = (π ^ j) x → i = j := by
    intro x hx i j hi hj hij
    have hper : Function.minimalPeriod π x = P := by
      have hdvd : Function.minimalPeriod π x ∣ P := by
        refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
        change (⇑π)^[P] x = x
        rw [← Equiv.Perm.coe_pow, hπP]
      obtain ⟨a, ha, heq⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
      rcases Nat.lt_or_ge a m with hlt | hge
      · exfalso
        apply hx
        have hpt : Function.IsPeriodicPt π (p ^ (m - 1)) x := by
          have h0 : Function.IsPeriodicPt π (Function.minimalPeriod π x) x :=
            Function.isPeriodicPt_minimalPeriod π x
          rw [heq] at h0
          obtain ⟨k, hk⟩ := pow_dvd_pow p (show a ≤ m - 1 by omega)
          rw [hk]
          exact h0.mul_const k
        have h2 : (π ^ (p ^ (m - 1))) x = x := by
          rw [Equiv.Perm.coe_pow]
          exact hpt.eq
        rw [← QuotientGroup.out_eq' x, hπpow] at h2
        have h3 := QuotientGroup.eq.1 h2.symm
        rw [← QuotientGroup.out_eq' x]
        exact (QuotientGroup.eq_one_iff _).2 (hfpf _ h3)
      · rw [heq, le_antisymm ha hge]
    have hi' : i < Function.minimalPeriod π x := hper ▸ hi
    have hj' : j < Function.minimalPeriod π x := hper ▸ hj
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at hij
    exact Function.iterate_injOn_Iio_minimalPeriod hi' hj' hij
  have hB := mul_finrank_ker_sub_one_le b T π c hT (by omega) 1 he hπP hfree
  set N : Module.End K W := (A : Module.End K W) - 1 with hNdef
  have hker : LinearMap.ker (T - 1) = homN N N := by
    ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, mem_homN]
    change (A : Module.End K W) * φ * ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) = φ ↔
      φ * N = N * φ
    rw [hNdef, mul_sub, sub_mul, mul_one, one_mul, sub_left_inj]
    constructor
    · intro h
      calc φ * (A : Module.End K W) =
          (A : Module.End K W) * φ * ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) *
            (A : Module.End K W) := by rw [h]
        _ = (A : Module.End K W) * φ := by rw [mul_assoc, Units.inv_mul, mul_one]
    · intro h
      rw [← h, mul_assoc, Units.mul_inv, mul_one]
  rw [hker] at hB
  have hd2 := finrank_sq_eq_card_quotient_center ρ hρ hsc hcl hirr
  rw [← Nat.card_eq_fintype_card, ← hd2] at hB
  have hcard : 2 ≤ Nat.card (G ⧸ Subgroup.center G) := by
    obtain ⟨g, hg⟩ := hnab
    have hne : ((g : G ⧸ Subgroup.center G)) ≠ 1 := fun h =>
      hg ((QuotientGroup.eq_one_iff g).1 h)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.2 ⟨_, _, hne⟩
  have hd : 2 ≤ finrank K W := by
    by_contra h
    have : finrank K W ^ 2 ≤ 1 := by
      have : finrank K W ≤ 1 := by omega
      nlinarith
    omega
  refine pow_ne_zero_of_finrank_homN_le N hP2 hd ?_
  have h1 : 1 ≤ finrank K W ^ 2 := by nlinarith
  rw [Nat.mul_sub_one]
  generalize P * finrank K (homN N N) = D at hB ⊢
  generalize finrank K W ^ 2 = E at hB h1 hd2 ⊢
  omega

end Main

end CFSG.GroupTheory.HallHigmanB
