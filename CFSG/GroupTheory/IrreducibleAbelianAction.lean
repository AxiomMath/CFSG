module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

universe u

section Linear

variable {k V : Type*} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]

noncomputable def glEndHom {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (A : Subgroup (LinearMap.GeneralLinearGroup k V)) : A →* Module.End k V :=
  (Units.coeHom (Module.End k V)).comp A.subtype

@[simp] theorem glEndHom_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (A : Subgroup (LinearMap.GeneralLinearGroup k V)) (a : A) :
    glEndHom A a = ((a : LinearMap.GeneralLinearGroup k V) : Module.End k V) := by
  simp [glEndHom]

 theorem adjoin_isField_of_irreducible {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hirr : ∀ W : Submodule k V,
      (∀ a ∈ A, ∀ v ∈ W, (a : Module.End k V) v ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsField (Algebra.adjoin k (Set.range (glEndHom A))) := by
  classical
  have hVfin : Finite V := Module.finite_of_finite k
  have hEndfin : Finite (Module.End k V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[k] V))
  set R := Algebra.adjoin k (Set.range (glEndHom A)) with hRdef
  have hRfin : Finite R := Subtype.finite
  have hpair : (Set.range (glEndHom A)).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact (commute_iff_eq _ _).mpr (congrArg (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V))
      (hAcomm a a.2 b b.2))
  have hcommR : ∀ x y : R, x * y = y * x :=
    (Algebra.isMulCommutative_adjoin k hpair).is_comm.comm
  have hRcentral : R ≤ Subalgebra.centralizer k (Set.range (glEndHom A)) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨a, rfl⟩
    change glEndHom A a ∈ Subalgebra.centralizer k (Set.range (glEndHom A))
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (commute_iff_eq _ _).mpr (congrArg
      (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V))
      (hAcomm b b.2 a a.2))
  have hinj : ∀ f ∈ R, f ≠ 0 → Function.Injective f := by
    intro f hf hf0
    have hker : ∀ a ∈ A, ∀ v ∈ LinearMap.ker f, (a : Module.End k V) v ∈ LinearMap.ker f := by
      intro a ha v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hcomm : f * (glEndHom A ⟨a, ha⟩) = (glEndHom A ⟨a, ha⟩) * f :=
        ((hRcentral hf) (glEndHom A ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).symm
      change f ((glEndHom A ⟨a, ha⟩) v) = 0
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hv, map_zero]
    rcases hirr (LinearMap.ker f) hker with hbot | htop
    · exact LinearMap.ker_eq_bot.1 hbot
    · exact absurd (LinearMap.ker_eq_top.1 htop) hf0
  refine ⟨⟨0, 1, fun h => ?_⟩, hcommR, fun {x} hx => ?_⟩
  · have h' := congrArg (fun y : R => (y : Module.End k V)) h
    exact zero_ne_one h'
  · have hxi := hinj x x.2 (fun h => hx (Subtype.ext h))
    have hmul : Function.Injective fun y : R => x * y := by
      intro y y' hyy'
      apply Subtype.ext
      refine LinearMap.ext fun v => hxi ?_
      exact congrArg (fun z : R => (z : Module.End k V) v) hyy'
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hmul) 1
    exact ⟨y, hy⟩

private theorem eq_one_of_pow_prime_eq_one_of_centralizes
    {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hirr : ∀ W : Submodule k V,
      (∀ a ∈ A, ∀ v ∈ W, (a : Module.End k V) v ∈ W) → W = ⊥ ∨ W = ⊤)
    {x : LinearMap.GeneralLinearGroup k V} (hxpow : x ^ p = 1)
    (hxcomm : ∀ a ∈ A, (x : Module.End k V) * (a : Module.End k V) =
      (a : Module.End k V) * (x : Module.End k V)) : x = 1 := by
  classical
  haveI : CharP (Module.End k V) p := charP_of_injective_algebraMap' k p
  by_contra hx1
  let N : Module.End k V := (x : Module.End k V) - 1
  have hN_ne : N ≠ 0 := by
    intro hN
    apply hx1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp hN
  have hNpow : N ^ p = 0 := by
    have hxEnd : (x : Module.End k V) ^ p = 1 := by
      simpa using congrArg (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V)) hxpow
    calc
      N ^ p = (x : Module.End k V) ^ p - 1 ^ p :=
        sub_pow_char_of_commute p (Commute.one_right _)
      _ = 0 := by rw [hxEnd, one_pow, sub_self]
  have hker : ∀ a ∈ A, ∀ v ∈ N.ker, (a : Module.End k V) v ∈ N.ker := by
    intro a ha v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hNa : N * (a : Module.End k V) = (a : Module.End k V) * N := by
      change ((x : Module.End k V) - 1) * (a : Module.End k V) =
        (a : Module.End k V) * ((x : Module.End k V) - 1)
      rw [sub_mul, mul_sub, hxcomm a ha, one_mul, mul_one]
    change N ((a : Module.End k V) v) = 0
    rw [← Module.End.mul_apply, hNa, Module.End.mul_apply, hv, map_zero]
  have hker_ne : N.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective N := LinearMap.ker_eq_bot.mp hbot
    have hsurj : Function.Surjective N := (LinearMap.injective_iff_surjective).mp hinj
    have hunit : IsUnit N := (Module.End.isUnit_iff N).mpr ⟨hinj, hsurj⟩
    have hpowunit : IsUnit (N ^ p) := hunit.pow p
    exact hpowunit.ne_zero hNpow
  rcases hirr N.ker hker with hbot | htop
  · exact hker_ne hbot
  · exact hN_ne (LinearMap.ker_eq_top.mp htop)

private theorem conj_mem_adjoin
    {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (g : LinearMap.GeneralLinearGroup k V)
    (hg : g ∈ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    {r : Module.End k V} (hr : r ∈ Algebra.adjoin k (Set.range (glEndHom A))) :
    (g : Module.End k V) * r * ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) ∈
      Algebra.adjoin k (Set.range (glEndHom A)) := by
  classical
  haveI : Finite V := Module.finite_of_finite k
  haveI : Finite (Module.End k V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[k] V))
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      let a' : A := ⟨g * a * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hg (a : LinearMap.GeneralLinearGroup k V)).mp a.2⟩
      have hx' : (g : Module.End k V) * (glEndHom A a : Module.End k V) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
          (glEndHom A a' : Module.End k V) := by
        simp [glEndHom, a', Subgroup.coe_mul, mul_assoc]
      rw [hx']
      exact Algebra.subset_adjoin (Set.mem_range_self a')
  | algebraMap c =>
      have hc : (g : Module.End k V) * (algebraMap k (Module.End k V) c) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
          algebraMap k (Module.End k V) c := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        simp
      rw [hc]
      exact Subalgebra.algebraMap_mem (Algebra.adjoin k (Set.range (glEndHom A))) c
  | add x y hx hy ihx ihy =>
      have h : (g : Module.End k V) * (x + y) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
          (g : Module.End k V) * x * ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) +
            (g : Module.End k V) * y *
              ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) := by
        noncomm_ring
      rw [h]
      exact (Algebra.adjoin k (Set.range (glEndHom A))).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      have hg' : ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
          (g : Module.End k V) = 1 := by
        simpa using congrArg
          (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V)) (inv_mul_cancel g)
      have h : (g : Module.End k V) * (x * y) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
          ((g : Module.End k V) * x * ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)) *
            ((g : Module.End k V) * y *
              ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)) := by
        calc
          (g : Module.End k V) * (x * y) *
              ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)
              = (g : Module.End k V) * x *
                  (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
                    (g : Module.End k V)) * y *
                  ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) := by
                rw [hg']
                noncomm_ring
          _ = ((g : Module.End k V) * x *
                ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)) *
              ((g : Module.End k V) * y *
                ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)) := by
                noncomm_ring
      rw [h]
      exact (Algebra.adjoin k (Set.range (glEndHom A))).mul_mem ihx ihy

theorem not_dvd_card_of_irreducible {A : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hirr : ∀ W : Submodule k V,
      (∀ a ∈ A, ∀ v ∈ W, (a : Module.End k V) v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ¬ p ∣ Nat.card A := by
  classical
  have hVfin : Finite V := Module.finite_of_finite k
  have hEndfin : Finite (Module.End k V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[k] V))
  set R := Algebra.adjoin k (Set.range (glEndHom A)) with hRdef
  have hRfin : Finite R := Subtype.finite
  have hRfield : IsField R := adjoin_isField_of_irreducible hAcomm hirr
  letI : Field R := hRfield.toField
  haveI : CharP R p := charP_of_injective_algebraMap' k p
  letI : Fintype R := Fintype.ofFinite R
  obtain ⟨n, hp, hcardR⟩ := FiniteField.card R p
  have hcardR_nat : Nat.card R = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardR]
  have hRtwo : 2 ≤ Fintype.card R := Fintype.one_lt_card
  have hnpos : 0 < (n : ℕ) := n.pos
  let aR (a : A) : R := ⟨glEndHom A a, Algebra.subset_adjoin (Set.mem_range_self a)⟩
  have haR_ne : ∀ a : A, aR a ≠ 0 := by
    intro a h
    have h' : ((a : LinearMap.GeneralLinearGroup k V) : Module.End k V) = 0 := by
      simpa [aR, glEndHom] using congrArg (fun r : R => (r : Module.End k V)) h
    exact (Units.ne_zero (a : LinearMap.GeneralLinearGroup k V)) h'
  let e : A →* Rˣ :=
    { toFun := fun a => (isUnit_iff_ne_zero.mpr (haR_ne a)).unit
      map_one' := by
        apply Units.ext
        show ((isUnit_iff_ne_zero.mpr (haR_ne 1)).unit : R) = (1 : R)
        rw [IsUnit.unit_spec]
        apply Subtype.ext
        simp [aR]
      map_mul' := by
        intro a b
        apply Units.ext
        show ((isUnit_iff_ne_zero.mpr (haR_ne (a * b))).unit : R) =
          ((isUnit_iff_ne_zero.mpr (haR_ne a)).unit : R) *
            ((isUnit_iff_ne_zero.mpr (haR_ne b)).unit : R)
        rw [IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
        apply Subtype.ext
        simp [aR, map_mul] }
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have h' : aR a = aR b := by
      simpa [e, IsUnit.unit_spec] using congrArg (fun u : Rˣ => (u : R)) hab
    have h'' : ((a : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
        ((b : LinearMap.GeneralLinearGroup k V) : Module.End k V) := by
      simpa [aR, glEndHom] using congrArg (fun r : R => (r : Module.End k V)) h'
    exact Units.ext h''
  have hdvd : Nat.card A ∣ Nat.card Rˣ := Subgroup.card_dvd_of_injective e he_inj
  rw [Nat.card_units, hcardR_nat] at hdvd
  intro hpdiv
  have hpn_dvd : p ∣ p ^ (n : ℕ) := dvd_pow_self p hnpos.ne'
  have hpn1_dvd : p ∣ p ^ (n : ℕ) - 1 := hpdiv.trans hdvd
  have hsub : p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) = 1 := by
    have : 0 < p ^ (n : ℕ) := pow_pos hp.pos n
    omega
  have hone : p ∣ 1 := by
    simpa [hsub] using Nat.dvd_sub hpn_dvd hpn1_dvd
  exact hp.not_dvd_one hone

private noncomputable def conjRingEquiv
    {A P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPnorm : P ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (g : P) :
    Algebra.adjoin k (Set.range (glEndHom A)) ≃+* Algebra.adjoin k (Set.range (glEndHom A)) := by
  let gG : LinearMap.GeneralLinearGroup k V := g
  let gInv : LinearMap.GeneralLinearGroup k V := g⁻¹
  have hgG : gG ∈ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)) := hPnorm g.2
  have hgInv : gInv ∈ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)) := by
    simpa [gInv] using hPnorm (g⁻¹).2
  have hleft : (gInv : Module.End k V) * (gG : Module.End k V) = 1 := by
    have := congrArg (fun u : P => ((u : LinearMap.GeneralLinearGroup k V) : Module.End k V))
      (inv_mul_cancel g)
    simpa [gG, gInv] using this
  have hright : (gG : Module.End k V) * (gInv : Module.End k V) = 1 := by
    have := congrArg (fun u : P => ((u : LinearMap.GeneralLinearGroup k V) : Module.End k V))
      (mul_inv_cancel g)
    simpa [gG, gInv] using this
  refine
  { toFun := fun r => ⟨(gG : Module.End k V) * (r : Module.End k V) * (gInv : Module.End k V),
      conj_mem_adjoin gG hgG r.2⟩
    invFun := fun r => ⟨(gInv : Module.End k V) * (r : Module.End k V) * (gG : Module.End k V),
      conj_mem_adjoin gInv hgInv r.2⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_
    map_add' := ?_ }
  · intro r
    apply Subtype.ext
    calc
      (gInv : Module.End k V) *
          ((gG : Module.End k V) * (r : Module.End k V) * (gInv : Module.End k V)) *
          (gG : Module.End k V)
          = ((gInv : Module.End k V) * (gG : Module.End k V)) * (r : Module.End k V) *
            ((gInv : Module.End k V) * (gG : Module.End k V)) := by
            noncomm_ring
      _ = (r : Module.End k V) := by rw [hleft]; simp
  · intro r
    apply Subtype.ext
    calc
      (gG : Module.End k V) *
          ((gInv : Module.End k V) * (r : Module.End k V) * (gG : Module.End k V)) *
          (gInv : Module.End k V)
          = ((gG : Module.End k V) * (gInv : Module.End k V)) * (r : Module.End k V) *
            ((gG : Module.End k V) * (gInv : Module.End k V)) := by
            noncomm_ring
      _ = (r : Module.End k V) := by rw [hright]; simp
  · intro r s
    apply Subtype.ext
    calc
      (gG : Module.End k V) * ((r : Module.End k V) * (s : Module.End k V)) *
          (gInv : Module.End k V)
          = (gG : Module.End k V) * (r : Module.End k V) *
              ((gInv : Module.End k V) * (gG : Module.End k V)) * (s : Module.End k V) *
              (gInv : Module.End k V) := by
            rw [hleft]
            noncomm_ring
      _ = ((gG : Module.End k V) * (r : Module.End k V) * (gInv : Module.End k V)) *
            ((gG : Module.End k V) * (s : Module.End k V) * (gInv : Module.End k V)) := by
            noncomm_ring
  · intro r s
    apply Subtype.ext
    change (gG : Module.End k V) * ((r : Module.End k V) + (s : Module.End k V)) *
        (gInv : Module.End k V) =
      (gG : Module.End k V) * (r : Module.End k V) * (gInv : Module.End k V) +
        (gG : Module.End k V) * (s : Module.End k V) * (gInv : Module.End k V)
    noncomm_ring

private noncomputable def conjAlgEquiv
    {A P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPnorm : P ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (g : P) :
    Algebra.adjoin k (Set.range (glEndHom A)) ≃ₐ[k]
      Algebra.adjoin k (Set.range (glEndHom A)) := by
  let gG : LinearMap.GeneralLinearGroup k V := g
  let gInv : LinearMap.GeneralLinearGroup k V := g⁻¹
  have hright : (gG : Module.End k V) * (gInv : Module.End k V) = 1 := by
    have := congrArg (fun u : P => ((u : LinearMap.GeneralLinearGroup k V) : Module.End k V))
      (mul_inv_cancel g)
    simpa [gG, gInv] using this
  refine AlgEquiv.ofRingEquiv (f := conjRingEquiv hPnorm g) (fun c => ?_)
  apply Subtype.ext
  calc
    (gG : Module.End k V) * (algebraMap k (Module.End k V) c) * (gInv : Module.End k V)
        = (algebraMap k (Module.End k V) c) * (gG : Module.End k V) * (gInv : Module.End k V) := by
          rw [← (Algebra.commute_algebraMap_left c (gG : Module.End k V)).eq]
    _ = (algebraMap k (Module.End k V) c) * ((gG : Module.End k V) * (gInv : Module.End k V)) := by
          noncomm_ring
    _ = algebraMap k (Module.End k V) c := by rw [hright]; simp

private noncomputable def conjRhom
    {A P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPnorm : P ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) :
    P →* (Algebra.adjoin k (Set.range (glEndHom A)) ≃ₐ[k]
      Algebra.adjoin k (Set.range (glEndHom A))) where
  toFun g := conjAlgEquiv hPnorm g
  map_one' := by
    apply AlgEquiv.ext
    intro r
    apply Subtype.ext
    change (((1 : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
        (r : Module.End k V) *
        ((((1 : P)⁻¹ : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
        (r : Module.End k V)
    simp
  map_mul' g h := by
    apply AlgEquiv.ext
    intro r
    apply Subtype.ext
    change (((g * h : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
        (r : Module.End k V) *
        ((((g * h : P)⁻¹ : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
      ((g : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
        (((h : LinearMap.GeneralLinearGroup k V) : Module.End k V) * (r : Module.End k V) *
          (((h⁻¹ : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V)) *
        (((g⁻¹ : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V)
    simp [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]

private theorem conjRhom_apply_coe
    {A P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPnorm : P ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (g : P) (r : Algebra.adjoin k (Set.range (glEndHom A))) :
    ((conjRhom hPnorm g r : Algebra.adjoin k (Set.range (glEndHom A))) :
        Module.End k V) =
      (((g : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V) * (r : Module.End k V) *
        ((((g⁻¹ : P) : LinearMap.GeneralLinearGroup k V) : Module.End k V)) := by
  rfl

theorem isCyclic_of_isPGroup_normalizer {A P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hirr : ∀ W : Submodule k V,
      (∀ a ∈ A, ∀ v ∈ W, (a : Module.End k V) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hPnorm : P ≤ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (hP : IsPGroup p P) : IsCyclic P := by
  classical
  have hVfin : Finite V := Module.finite_of_finite k
  have hEndfin : Finite (Module.End k V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[k] V))
  haveI : Finite (Module.End k V) := hEndfin
  haveI : Finite (LinearMap.GeneralLinearGroup k V) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V))
      Units.val_injective
  haveI : Finite P :=
    Finite.of_injective (Subgroup.subtype P) Subtype.val_injective
  set R := Algebra.adjoin k (Set.range (glEndHom A)) with hRdef
  have hRfield : IsField R := adjoin_isField_of_irreducible hAcomm hirr
  letI : Field R := hRfield.toField
  have hRfin : Finite R := Subtype.finite
  letI : Fintype R := Fintype.ofFinite R
  letI : IsCyclic (R ≃ₐ[k] R) := FiniteField.instIsCyclicAlgEquivOfFinite k R
  let conj : P →* (R ≃ₐ[k] R) := conjRhom hPnorm
  have hker : conj.ker = ⊥ := by
    by_contra hKne
    haveI : Finite conj.ker := Subtype.finite
    have hKcard : 1 < Nat.card conj.ker :=
      (Subgroup.one_lt_card_iff_ne_bot conj.ker).mpr hKne
    have hKp : IsPGroup p conj.ker :=
      IsPGroup.of_injective hP (Subgroup.subtype conj.ker) Subtype.val_injective
    have hpdvd : p ∣ Nat.card conj.ker := by
      rcases hKp.card_eq_or_dvd with h1 | hpd
      · omega
      · exact hpd
    letI : Fintype conj.ker := Fintype.ofFinite conj.ker
    have hpdvd' : p ∣ Fintype.card conj.ker := by
      rwa [Nat.card_eq_fintype_card] at hpdvd
    obtain ⟨y, hyorder⟩ := exists_prime_orderOf_dvd_card (G := conj.ker) p hpdvd'
    have hyPorder : orderOf (y : P) = p := by
      simpa [hyorder] using
        orderOf_injective (Subgroup.subtype conj.ker) Subtype.val_injective y
    let yG : LinearMap.GeneralLinearGroup k V := (y : P)
    let yInv : LinearMap.GeneralLinearGroup k V := ((y : P)⁻¹ : P)
    have hyGLpow : yG ^ p = 1 := by
      have hy' : (y : P) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hyPorder])
      simpa [yG] using congrArg
        (fun u : P => ((u : LinearMap.GeneralLinearGroup k V))) hy'
    have hyInv_left : (yInv : Module.End k V) * (yG : Module.End k V) = 1 := by
      have := congrArg (fun u : P => ((u : LinearMap.GeneralLinearGroup k V) : Module.End k V))
        (inv_mul_cancel (y : P))
      simpa [yG, yInv] using this
    have hcommA : ∀ a ∈ A, (yG : Module.End k V) * (a : Module.End k V) =
        (a : Module.End k V) * (yG : Module.End k V) := by
      intro a ha
      have hy1 : conjRhom hPnorm (y : P) = 1 :=
        MonoidHom.mem_ker.mp y.2
      let aA : A := ⟨a, ha⟩
      have hgen : glEndHom A aA ∈ Algebra.adjoin k (Set.range (glEndHom A)) :=
        Algebra.subset_adjoin (Set.mem_range_self aA)
      have hfix : (yG : Module.End k V) *
          (glEndHom A aA : Module.End k V) * (yInv : Module.End k V) =
          (glEndHom A aA : Module.End k V) := by
        have h := congrArg (fun e : R ≃ₐ[k] R =>
          ((e ⟨glEndHom A aA, hgen⟩ : R) : Module.End k V)) hy1
        rw [conjRhom_apply_coe] at h
        simpa [yG, yInv, glEndHom] using h
      have := congrArg (fun z : Module.End k V => z * (yG : Module.End k V)) hfix
      simpa [glEndHom, mul_assoc, hyInv_left] using this
    have hyGLone : yG = 1 :=
      eq_one_of_pow_prime_eq_one_of_centralizes hirr hyGLpow hcommA
    have hyPone : (y : P) = 1 := Subtype.ext hyGLone
    have hyKone : y = 1 := Subtype.ext hyPone
    have hpone : p = 1 := by
      rw [← hyorder, hyKone, orderOf_one]
    exact (Fact.out : Nat.Prime p).ne_one hpone
  exact isCyclic_of_injective conj (MonoidHom.ker_eq_bot_iff conj |>.mp hker)

end Linear

section GroupAux

@[instance_reducible] noncomputable def elemModule (p : ℕ) [NeZero p] {A : Type*}
    [CommGroup A] (hp : ∀ a : A, a ^ p = 1) : Module (ZMod p) (Additive A) :=
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp _

private theorem map_sup_le_left_of_le_ker {M N : Type*} [Group M] [Group N]
    {f : M →* N} {A C : Subgroup M} (hC : C ≤ f.ker) :
    Subgroup.map f (A ⊔ C) ≤ Subgroup.map f A := by
  rw [Subgroup.map_sup]
  refine sup_le le_rfl ?_
  have h : Subgroup.map f C = ⊥ := (Subgroup.map_eq_bot_iff C).mpr hC
  rw [h]
  exact bot_le

end GroupAux

section GroupForm

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem conj_comm_of_apply {A U : Subgroup G} [CommGroup U]
    [Module (ZMod p) (Additive U)]
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hA_comm : ⁅A, A⁆ ≤ Subgroup.centralizer (U : Set G))
    (ρA : A →* (Additive U ≃ₗ[ZMod p] Additive U))
    (toGL : (Additive U ≃ₗ[ZMod p] Additive U) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive U))
    (A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)))
    (hA'_map : A' = Subgroup.map toGL.toMonoidHom ρA.range)
    (hρA_apply : ∀ (a : A) (x : Additive U),
      ((Additive.toMul (ρA a x) : U) : G) =
        (a : G) * ((Additive.toMul x : U) : G) * (a : G)⁻¹) :
    ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
  have hA''comm : ∀ a ∈ ρA.range, ∀ b ∈ ρA.range, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a0, rfl⟩ := ha
    obtain ⟨b0, rfl⟩ := hb
    apply LinearEquiv.ext
    intro x
    apply (Additive.toMul (α := U)).injective
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    apply Subtype.ext
    rw [hρA_apply, hρA_apply, hρA_apply, hρA_apply]
    let c : G := ⁅(a0 : G), (b0 : G)⁆
    let v : G := (b0 : G) * ((a0 : G) * (u : G) * (a0 : G)⁻¹) * (b0 : G)⁻¹
    have hav : (a0 : G) * (u : G) * (a0 : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hA_norm a0.2) (u : G)).mp u.2
    have hvU : v ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hA_norm b0.2) _).mp hav
      simpa [v, mul_assoc] using this
    have hcC : c ∈ Subgroup.centralizer (U : Set G) :=
      hA_comm (Subgroup.commutator_mem_commutator a0.2 b0.2)
    have hcv : c * v = v * c :=
      (Subgroup.mem_centralizer_iff.mp hcC v hvU).symm
    rw [show Additive.toMul (Additive.ofMul u) = u from rfl]
    have hident :
        (a0 : G) * ((b0 : G) * (u : G) * (b0 : G)⁻¹) * (a0 : G)⁻¹ =
          c * v * c⁻¹ := by
      simp only [c, v, commutatorElement_def]
      group
    rw [hident]
    calc
      c * v * c⁻¹ = v * c * c⁻¹ := by rw [hcv]
      _ = v := by simp
  intro a ha b hb
  rw [hA'_map] at ha hb
  obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
  simpa using congrArg toGL (hA''comm a0 ha0 b0 hb0)

theorem pSubgroup_le_centralizer_of_irreducible {U A : Subgroup G}
    (hU : CFSG.Open.IsElemAbelian p U) (hUne : U ≠ ⊥)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hA_comm : ⁅A, A⁆ ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ U → A ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = U)
    {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQ : Q ≤ A ⊔ Subgroup.centralizer (U : Set G)) :
    Q ≤ Subgroup.centralizer (U : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (U : Set G)
  have hC_norm : C ≤ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
  have hAC_norm : A ⊔ C ≤ Subgroup.normalizer (U : Set G) := sup_le hA_norm hC_norm
  have hQAC : Q ≤ A ⊔ C := hQ
  have hQ_norm : Q ≤ Subgroup.normalizer (U : Set G) := hQAC.trans hAC_norm
  let hc : ∀ a b : U, a * b = b * a := fun a b => hU.1.is_comm.comm a b
  let hp : ∀ a : U, a ^ p = 1 := fun a => by
    apply Subtype.ext
    simpa using hU.2 (a : G) a.2
  letI : IsMulCommutative U := ⟨⟨hc⟩⟩
  letI : CommGroup U := IsMulCommutative.instCommGroup
  letI : Module (ZMod p) (Additive U) := elemModule p hp
  let actN : Subgroup.normalizer (U : Set G) →* MulAut U := U.normalizerMonoidHom
  let conjN : Subgroup.normalizer (U : Set G) →* (Additive U ≃ₗ[ZMod p] Additive U) :=
  { toFun := fun n => (MulEquiv.toAdditive (actN n)).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive (actN n)))
    map_one' := LinearEquiv.ext fun x => by
      change Additive.ofMul (actN 1 (Additive.toMul x)) = x
      rw [map_one]
      rfl
    map_mul' := fun n m => LinearEquiv.ext fun x => by
      change Additive.ofMul (actN (n * m) (Additive.toMul x)) =
        Additive.ofMul (actN n (actN m (Additive.toMul x)))
      rw [map_mul]
      rfl }
  have hconjN_ofMul : ∀ (n : Subgroup.normalizer (U : Set G)) (u : U),
      Additive.toMul (conjN n (Additive.ofMul u)) = (n : G) * (u : G) * (n : G)⁻¹ := by
    intro n u
    change ((actN n u : U) : G) = _
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := U) n u
  let ρAC : ↥(A ⊔ C) →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    conjN.comp (Subgroup.inclusion hAC_norm)
  let ρA : A →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    conjN.comp (Subgroup.inclusion hA_norm)
  let ρQ : Q →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    conjN.comp (Subgroup.inclusion hQ_norm)
  let toGL : (Additive U ≃ₗ[ZMod p] Additive U) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive U)).symm
  let ρA' : A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    toGL.toMonoidHom.comp ρA
  let ρQ' : Q →* LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    toGL.toMonoidHom.comp ρQ
  let A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) := ρA'.range
  have htoGL_apply : ∀ f : Additive U ≃ₗ[ZMod p] Additive U,
      (toGL f).toLinearEquiv = f := by
    intro f
    simpa [toGL, LinearMap.GeneralLinearGroup.generalLinearEquiv] using
      (MulEquiv.apply_symm_apply
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive U)) f)
  have hA'_map : A' = Subgroup.map toGL.toMonoidHom ρA.range := by
    simp [A', ρA', MonoidHom.range_eq_map, Subgroup.map_map]
  have hρA_apply : ∀ (a : A) (x : Additive U),
      ((Additive.toMul (ρA a x) : U) : G) =
        (a : G) * ((Additive.toMul x : U) : G) * (a : G)⁻¹ := by
    intro a x
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx]
    change ((Additive.toMul (conjN ⟨(a : G), hA_norm a.2⟩ (Additive.ofMul u)) : U) : G) =
      (a : G) * (u : G) * (a : G)⁻¹
    exact hconjN_ofMul ⟨(a : G), hA_norm a.2⟩ u
  have hC_ker : C.subgroupOf (A ⊔ C) ≤ ρAC.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro x
    have hcC : (c : G) ∈ C := (Subgroup.mem_subgroupOf).mp hc
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx]
    change conjN ⟨(c : G), hAC_norm c.2⟩ (Additive.ofMul u) = Additive.ofMul u
    apply (Additive.toMul (α := U)).injective
    rw [show Additive.toMul (Additive.ofMul u) = u from rfl]
    apply Subtype.ext
    rw [hconjN_ofMul]
    have hcu : (c : G) * (u : G) = (u : G) * (c : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC (u : G) u.2).symm
    calc
      (c : G) * (u : G) * (c : G)⁻¹ = (u : G) * (c : G) * (c : G)⁻¹ := by rw [hcu]
      _ = (u : G) := by simp
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a :=
    conj_comm_of_apply hA_norm hA_comm ρA toGL A' hA'_map hρA_apply
  have hA'irr : ∀ W : Submodule (ZMod p) (Additive U),
      (∀ a ∈ A', ∀ v ∈ W,
        ((a : LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) :
          Module.End (ZMod p) (Additive U)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let WU : Subgroup U := AddSubgroup.toSubgroup' W.toAddSubgroup
    let Wsub : Subgroup G := WU.map U.subtype
    have hWsub_le : Wsub ≤ U := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    have memWsub : ∀ u : U, (u : G) ∈ Wsub ↔ Additive.ofMul u ∈ W := by
      intro u
      constructor
      · rintro ⟨u', hu', huu'⟩
        have hu'' : u' = u := Subtype.ext huu'
        rw [hu''] at hu'
        change u ∈ AddSubgroup.toSubgroup' W.toAddSubgroup at hu'
        simpa using (AddSubgroup.mem_toSubgroup' W.toAddSubgroup u).mp hu'
      · intro hu
        exact ⟨u, (AddSubgroup.mem_toSubgroup' W.toAddSubgroup u).mpr (by simpa using hu), rfl⟩
    have hρA'_apply : ∀ (a : A) (x : Additive U),
        (ρA' a).toLinearEquiv x = ρA a x := by
      intro a x
      change (toGL (ρA a)).toLinearEquiv x = ρA a x
      rw [htoGL_apply]
    have hmap_mem : ∀ b ∈ A, ∀ w ∈ Wsub, b * w * b⁻¹ ∈ Wsub := by
      intro b hb w hw
      obtain ⟨u, huW, rfl⟩ := Subgroup.mem_map.mp hw
      have hmemU : (b : G) * (u : G) * (b : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hA_norm hb) (u : G)).mp u.2
      refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩, ?_, rfl⟩
      have hA'mem : ρA' ⟨b, hb⟩ ∈ A' := ⟨⟨b, hb⟩, rfl⟩
      have hinv : (ρA' ⟨b, hb⟩).toLinearEquiv (Additive.ofMul u) =
          Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩ := by
        rw [hρA'_apply]
        change conjN ⟨(b : G), hA_norm hb⟩ (Additive.ofMul u) = Additive.ofMul _
        apply (Additive.toMul (α := U)).injective
        apply Subtype.ext
        change ((Additive.toMul (conjN ⟨(b : G), hA_norm hb⟩ (Additive.ofMul u)) : U) : G) =
          ((Additive.toMul (Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩) : U) : G)
        rw [hconjN_ofMul]
        simp
      have hWinv := hW (ρA' ⟨b, hb⟩) hA'mem (Additive.ofMul u) huW
      have hWinv' : Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩ ∈ W := by
        rw [← hinv]
        exact hWinv
      exact (AddSubgroup.mem_toSubgroup' W.toAddSubgroup
        ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩).mpr (by simpa using hWinv')
    have hAnorm : A ≤ Subgroup.normalizer (Wsub : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        exact hmap_mem a ha w hw
      · intro hw
        have h := hmap_mem a⁻¹ (A.inv_mem ha) (a * w * a⁻¹) hw
        simpa [mul_assoc] using h
    rcases hirr Wsub hWsub_le hAnorm with hbot | htop
    · left
      apply Submodule.ext
      intro x
      constructor
      · intro hx
        have hxsub : ((Additive.toMul x : U) : G) ∈ Wsub :=
          (memWsub _).mpr (by simpa using hx)
        rw [hbot] at hxsub
        have hx1 : (Additive.toMul x : U) = 1 := Subtype.ext (Subgroup.mem_bot.mp hxsub)
        have : Additive.ofMul (Additive.toMul x) = (0 : Additive U) := by
          rw [hx1]
          rfl
        simpa using this
      · intro hx
        rw [Submodule.mem_bot] at hx
        simp [hx]
    · right
      apply top_unique
      intro x _
      have hxsub : ((Additive.toMul x : U) : G) ∈ Wsub := by
        rw [htop]
        exact (Additive.toMul x).2
      have hxW := (memWsub _).mp hxsub
      simpa using hxW
  haveI : Finite U := Subtype.finite
  haveI : Finite (Additive U) := inferInstance
  haveI : FiniteDimensional (ZMod p) (Additive U) := Module.Finite.of_finite
  haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
  haveI : Nontrivial (Additive U) := inferInstance
  haveI : Finite (Module.End (ZMod p) (Additive U)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Additive U →ₗ[ZMod p] Additive U))
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup (ZMod p) (Additive U) =>
      (u : Module.End (ZMod p) (Additive U))) Units.val_injective
  have hA1 : ¬ p ∣ Nat.card A' :=
    not_dvd_card_of_irreducible (k := ZMod p) (V := Additive U) (p := p) (A := A')
      hA'comm hA'irr
  have hQrange_le : ρQ'.range ≤ A' := by
    have htopAC : (⊤ : Subgroup ↥(A ⊔ C)) =
        A.subgroupOf (A ⊔ C) ⊔ C.subgroupOf (A ⊔ C) := by
      rw [← Subgroup.subgroupOf_sup (show A ≤ A ⊔ C from le_sup_left)
        (show C ≤ A ⊔ C from le_sup_right)]
      exact (Subgroup.subgroupOf_self (A ⊔ C)).symm
    have hmapA : Subgroup.map ρAC (A.subgroupOf (A ⊔ C)) = ρA.range := by
      have hAeq : A.subgroupOf (A ⊔ C) =
          Subgroup.map (Subgroup.inclusion (show A ≤ A ⊔ C from le_sup_left)) ⊤ := by
        rw [← MonoidHom.range_eq_map, Subgroup.inclusion_range]
      have hcomp : ρAC.comp (Subgroup.inclusion (show A ≤ A ⊔ C from le_sup_left)) = ρA := by
        ext a
        rfl
      rw [hAeq, Subgroup.map_map, hcomp, MonoidHom.range_eq_map]
    have hQcomp : ρAC.comp (Subgroup.inclusion hQAC) = ρQ := by
      ext q
      rfl
    have hQlin : ρQ.range ≤ ρA.range := by
      calc
        ρQ.range = Subgroup.map ρAC (Subgroup.map (Subgroup.inclusion hQAC) ⊤) := by
          rw [← hQcomp, MonoidHom.range_eq_map]
          exact (Subgroup.map_map (K := ⊤) ρAC (Subgroup.inclusion hQAC)).symm
        _ ≤ Subgroup.map ρAC ⊤ := Subgroup.map_mono le_top
        _ = Subgroup.map ρAC (A.subgroupOf (A ⊔ C) ⊔ C.subgroupOf (A ⊔ C)) := by
          rw [htopAC]
        _ ≤ Subgroup.map ρAC (A.subgroupOf (A ⊔ C)) := map_sup_le_left_of_le_ker hC_ker
        _ = ρA.range := hmapA
    have hmapQ' : ρQ'.range = Subgroup.map toGL.toMonoidHom ρQ.range := by
      simp [ρQ', MonoidHom.range_eq_map, Subgroup.map_map]
    have hmapA' : A' = Subgroup.map toGL.toMonoidHom ρA.range := by
      simp [A', ρA', MonoidHom.range_eq_map, Subgroup.map_map]
    rw [hmapQ', hmapA']
    exact Subgroup.map_mono hQlin
  have hρQ_bot : ρQ'.range = ⊥ := by
    by_contra hne
    haveI : Finite ρQ'.range := Subtype.finite
    have hpg : IsPGroup p ρQ'.range :=
      IsPGroup.of_surjective hQp ρQ'.rangeRestrict ρQ'.rangeRestrict_surjective
    have hpdvd : p ∣ Nat.card ρQ'.range := by
      rcases hpg.card_eq_or_dvd with h1 | hpd
      · have hlt : 1 < Nat.card ρQ'.range :=
          (Subgroup.one_lt_card_iff_ne_bot ρQ'.range).mpr hne
        omega
      · exact hpd
    exact hA1 (hpdvd.trans (Subgroup.card_dvd_of_le hQrange_le))
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hq1 : ρQ ⟨q, hq⟩ = 1 := by
    have hmem : ρQ' ⟨q, hq⟩ ∈ ρQ'.range := ⟨⟨q, hq⟩, rfl⟩
    rw [hρQ_bot] at hmem
    have hq' : ρQ' ⟨q, hq⟩ = 1 := (MonoidHom.mem_ker).mp hmem
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod p) (Additive U) =>
      (toGL.symm g : Additive U ≃ₗ[ZMod p] Additive U)) hq'
    simpa [ρQ', toGL] using this
  have hconj : (q : G) * (u : G) * (q : G)⁻¹ = (u : G) := by
    have hcongr := congrArg (fun f : Additive U ≃ₗ[ZMod p] Additive U =>
      ((Additive.toMul (f (Additive.ofMul ⟨u, hu⟩)) : U) : G)) hq1
    change ((Additive.toMul (ρQ ⟨q, hq⟩ (Additive.ofMul ⟨u, hu⟩)) : U) : G) =
      ((Additive.toMul ((1 : Additive U ≃ₗ[ZMod p] Additive U) (Additive.ofMul ⟨u, hu⟩)) : U) : G)
      at hcongr
    rw [show ρQ ⟨q, hq⟩ (Additive.ofMul ⟨u, hu⟩) =
      conjN ⟨q, hQ_norm hq⟩ (Additive.ofMul ⟨u, hu⟩) from rfl] at hcongr
    rw [hconjN_ofMul] at hcongr
    simpa using hcongr
  have hqu : (u : G) * (q : G) = (q : G) * (u : G) := by
    have := congrArg (fun z : G => z * (q : G)) hconj
    simpa [mul_assoc] using this.symm
  exact hqu

theorem isCyclic_mod_centralizer_of_isPGroup_normalizer {U A P : Subgroup G}
    (hU : CFSG.Open.IsElemAbelian p U) (hUne : U ≠ ⊥)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hA_comm : ⁅A, A⁆ ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ U → A ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = U)
    (hP : IsPGroup p P)
    (hP_normU : P ≤ Subgroup.normalizer (U : Set G))
    (hP_normA : P ≤ Subgroup.normalizer (A : Set G)) :
    ∃ x ∈ P, ∀ y ∈ P, ∃ m : ℕ, y⁻¹ * x ^ m ∈ Subgroup.centralizer (U : Set G) := by
  classical
  let hc : ∀ a b : U, a * b = b * a := fun a b => hU.1.is_comm.comm a b
  let hp : ∀ a : U, a ^ p = 1 := fun a => by
    apply Subtype.ext
    simpa using hU.2 (a : G) a.2
  letI : IsMulCommutative U := ⟨⟨hc⟩⟩
  letI : CommGroup U := IsMulCommutative.instCommGroup
  letI : Module (ZMod p) (Additive U) := elemModule p hp
  let actN : Subgroup.normalizer (U : Set G) →* MulAut U := U.normalizerMonoidHom
  let conjN : Subgroup.normalizer (U : Set G) →* (Additive U ≃ₗ[ZMod p] Additive U) :=
  { toFun := fun n => (MulEquiv.toAdditive (actN n)).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive (actN n)))
    map_one' := LinearEquiv.ext fun x => by
      change Additive.ofMul (actN 1 (Additive.toMul x)) = x
      rw [map_one]
      rfl
    map_mul' := fun n m => LinearEquiv.ext fun x => by
      change Additive.ofMul (actN (n * m) (Additive.toMul x)) =
        Additive.ofMul (actN n (actN m (Additive.toMul x)))
      rw [map_mul]
      rfl }
  have hconjN_ofMul : ∀ (n : Subgroup.normalizer (U : Set G)) (u : U),
      Additive.toMul (conjN n (Additive.ofMul u)) = (n : G) * (u : G) * (n : G)⁻¹ := by
    intro n u
    change ((actN n u : U) : G) = _
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := U) n u
  let ρA : A →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    conjN.comp (Subgroup.inclusion hA_norm)
  let toGL : (Additive U ≃ₗ[ZMod p] Additive U) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive U)).symm
  let ρA' : A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    toGL.toMonoidHom.comp ρA
  let A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) := ρA'.range
  have htoGL_apply : ∀ f : Additive U ≃ₗ[ZMod p] Additive U,
      (toGL f).toLinearEquiv = f := by
    intro f
    simpa [toGL, LinearMap.GeneralLinearGroup.generalLinearEquiv] using
      (MulEquiv.apply_symm_apply
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive U)) f)
  have hA'_map : A' = Subgroup.map toGL.toMonoidHom ρA.range := by
    simp [A', ρA', MonoidHom.range_eq_map, Subgroup.map_map]
  have hρA_apply : ∀ (a : A) (x : Additive U),
      ((Additive.toMul (ρA a x) : U) : G) =
        (a : G) * ((Additive.toMul x : U) : G) * (a : G)⁻¹ := by
    intro a x
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx]
    change ((Additive.toMul (conjN ⟨(a : G), hA_norm a.2⟩ (Additive.ofMul u)) : U) : G) =
      (a : G) * (u : G) * (a : G)⁻¹
    exact hconjN_ofMul ⟨(a : G), hA_norm a.2⟩ u

  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a :=
    conj_comm_of_apply hA_norm hA_comm ρA toGL A' hA'_map hρA_apply
  have hA'irr : ∀ W : Submodule (ZMod p) (Additive U),
      (∀ a ∈ A', ∀ v ∈ W,
        ((a : LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) :
          Module.End (ZMod p) (Additive U)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let WU : Subgroup U := AddSubgroup.toSubgroup' W.toAddSubgroup
    let Wsub : Subgroup G := WU.map U.subtype
    have hWsub_le : Wsub ≤ U := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    have memWsub : ∀ u : U, (u : G) ∈ Wsub ↔ Additive.ofMul u ∈ W := by
      intro u
      constructor
      · rintro ⟨u', hu', huu'⟩
        have hu'' : u' = u := Subtype.ext huu'
        rw [hu''] at hu'
        change u ∈ AddSubgroup.toSubgroup' W.toAddSubgroup at hu'
        simpa using (AddSubgroup.mem_toSubgroup' W.toAddSubgroup u).mp hu'
      · intro hu
        exact ⟨u, (AddSubgroup.mem_toSubgroup' W.toAddSubgroup u).mpr (by simpa using hu), rfl⟩
    have hρA'_apply : ∀ (a : A) (x : Additive U),
        (ρA' a).toLinearEquiv x = ρA a x := by
      intro a x
      change (toGL (ρA a)).toLinearEquiv x = ρA a x
      rw [htoGL_apply]
    have hmap_mem : ∀ b ∈ A, ∀ w ∈ Wsub, b * w * b⁻¹ ∈ Wsub := by
      intro b hb w hw
      obtain ⟨u, huW, rfl⟩ := Subgroup.mem_map.mp hw
      have hmemU : (b : G) * (u : G) * (b : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hA_norm hb) (u : G)).mp u.2
      refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩, ?_, rfl⟩
      have hA'mem : ρA' ⟨b, hb⟩ ∈ A' := ⟨⟨b, hb⟩, rfl⟩
      have hinv : (ρA' ⟨b, hb⟩).toLinearEquiv (Additive.ofMul u) =
          Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩ := by
        rw [hρA'_apply]
        change conjN ⟨(b : G), hA_norm hb⟩ (Additive.ofMul u) = Additive.ofMul _
        apply (Additive.toMul (α := U)).injective
        apply Subtype.ext
        change ((Additive.toMul (conjN ⟨(b : G), hA_norm hb⟩ (Additive.ofMul u)) : U) : G) =
          ((Additive.toMul (Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩) : U) : G)
        rw [hconjN_ofMul]
        simp
      have hWinv := hW (ρA' ⟨b, hb⟩) hA'mem (Additive.ofMul u) huW
      have hWinv' : Additive.ofMul ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩ ∈ W := by
        rw [← hinv]
        exact hWinv
      exact (AddSubgroup.mem_toSubgroup' W.toAddSubgroup
        ⟨(b : G) * (u : G) * (b : G)⁻¹, hmemU⟩).mpr (by simpa using hWinv')
    have hAnorm : A ≤ Subgroup.normalizer (Wsub : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        exact hmap_mem a ha w hw
      · intro hw
        have h := hmap_mem a⁻¹ (A.inv_mem ha) (a * w * a⁻¹) hw
        simpa [mul_assoc] using h
    rcases hirr Wsub hWsub_le hAnorm with hbot | htop
    · left
      apply Submodule.ext
      intro x
      constructor
      · intro hx
        have hxsub : ((Additive.toMul x : U) : G) ∈ Wsub :=
          (memWsub _).mpr (by simpa using hx)
        rw [hbot] at hxsub
        have hx1 : (Additive.toMul x : U) = 1 := Subtype.ext (Subgroup.mem_bot.mp hxsub)
        have : Additive.ofMul (Additive.toMul x) = (0 : Additive U) := by
          rw [hx1]
          rfl
        simpa using this
      · intro hx
        rw [Submodule.mem_bot] at hx
        simp [hx]
    · right
      apply top_unique
      intro x _
      have hxsub : ((Additive.toMul x : U) : G) ∈ Wsub := by
        rw [htop]
        exact (Additive.toMul x).2
      have hxW := (memWsub _).mp hxsub
      simpa using hxW
  let ρP : P →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    conjN.comp (Subgroup.inclusion hP_normU)
  let ρP' : P →* LinearMap.GeneralLinearGroup (ZMod p) (Additive U) :=
    toGL.toMonoidHom.comp ρP
  let P' : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) := ρP'.range
  have hρP_apply : ∀ (p : P) (x : Additive U),
      ((Additive.toMul (ρP p x) : U) : G) =
        (p : G) * ((Additive.toMul x : U) : G) * (p : G)⁻¹ := by
    intro p x
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx]
    change ((Additive.toMul (conjN ⟨(p : G), hP_normU p.2⟩ (Additive.ofMul u)) : U) : G) =
      (p : G) * (u : G) * (p : G)⁻¹
    exact hconjN_ofMul ⟨(p : G), hP_normU p.2⟩ u
  have hP'_p : IsPGroup p P' :=
    IsPGroup.of_surjective hP ρP'.rangeRestrict ρP'.rangeRestrict_surjective
  have hconjP : ∀ (p : P) (a : A),
      ρP p * ρA a * (ρP p)⁻¹ =
        ρA ⟨(p : G) * (a : G) * (p : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hP_normA p.2) (a : G)).mp a.2⟩ := by
    intro p a
    apply LinearEquiv.ext
    intro x
    apply (Additive.toMul (α := U)).injective
    let u : U := Additive.toMul x
    have hx : Additive.ofMul u = x := rfl
    rw [← hx, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    apply Subtype.ext
    rw [← map_inv]
    simp only [hρP_apply, hρA_apply]
    rw [show Additive.toMul (Additive.ofMul u) = u from rfl]
    simp only [Subgroup.coe_inv, inv_inv]
    group
  have hP'_le : P' ≤ Subgroup.normalizer (A' : Set (LinearMap.GeneralLinearGroup (ZMod p) (Additive U))) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp a ha
    obtain ⟨p0, rfl⟩ := MonoidHom.mem_range.mp hp
    rw [hA'_map] at ha ⊢
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨a1, ha1, rfl⟩ := MonoidHom.mem_range.mp ha0
    let a2 : A := ⟨(p0 : G) * (a1 : G) * (p0 : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hP_normA p0.2) (a1 : G)).mp a1.2⟩
    refine Subgroup.mem_map.mpr ⟨ρA a2, ?_, ?_⟩
    · exact ⟨a2, rfl⟩
    · simpa [ρP', ρA', a2] using (congrArg toGL (hconjP p0 a1)).symm
  haveI : Finite U := Subtype.finite
  haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
  haveI : Finite (Additive U) := inferInstance
  haveI : FiniteDimensional (ZMod p) (Additive U) := Module.Finite.of_finite
  haveI : Nontrivial (Additive U) := inferInstance
  haveI : Finite (Module.End (ZMod p) (Additive U)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := Additive U →ₗ[ZMod p] Additive U))
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod p) (Additive U)) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup (ZMod p) (Additive U) =>
      (u : Module.End (ZMod p) (Additive U))) Units.val_injective
  haveI : Finite P' := Subtype.finite
  haveI : IsCyclic P' :=
    isCyclic_of_isPGroup_normalizer (k := ZMod p) (V := Additive U) (p := p)
      (A := A') (P := P') hA'comm hA'irr hP'_le hP'_p
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P')
  obtain ⟨x, hxρ⟩ := MonoidHom.mem_range.mp g.2
  refine ⟨x, x.2, ?_⟩
  intro y hy
  have hyP' : (⟨ρP' ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : P') ∈ (⊤ : Subgroup P') := Subgroup.mem_top _
  have hmem : (⟨ρP' ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : P') ∈ Subgroup.zpowers g := hg _
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_iff_mem_zpowers.2 hmem)
  let z : G := y⁻¹ * x ^ m
  let zP : P := ⟨z, P.mul_mem (P.inv_mem hy) (P.pow_mem x.2 m)⟩
  have hzρ' : ρP' zP = 1 := by
    have hzP_eq : zP = (⟨y, hy⟩ : P)⁻¹ * x ^ m := by
      apply Subtype.ext
      rfl
    rw [hzP_eq, map_mul, map_inv, map_pow, hxρ]
    rw [← Subgroup.coe_pow]
    rw [hm]
    simp
  have hzρ : ρP zP = 1 := by
    apply toGL.injective
    rw [map_one]
    simpa [ρP'] using hzρ'
  refine ⟨m, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hzconj : (z : G) * (u : G) * (z : G)⁻¹ = (u : G) := by
    have h := congrArg (fun f : Additive U ≃ₗ[ZMod p] Additive U =>
      ((Additive.toMul (f (Additive.ofMul ⟨u, hu⟩)) : U) : G)) hzρ
    change ((Additive.toMul (ρP zP (Additive.ofMul ⟨u, hu⟩)) : U) : G) =
      ((Additive.toMul ((1 : Additive U ≃ₗ[ZMod p] Additive U) (Additive.ofMul ⟨u, hu⟩)) : U) : G)
      at h
    rw [hρP_apply] at h
    simpa [zP, z] using h
  have hzu : (u : G) * (z : G) = (z : G) * (u : G) := by
    have := congrArg (fun w : G => w * (z : G)) hzconj
    simpa [mul_assoc] using this.symm
  simpa [z] using hzu

end GroupForm

section CyclicQuotient

variable {G : Type u} [Group G]

theorem isCyclic_quotient_of_cyclic_mod {P C K H : Subgroup G}
    (hPH : P ≤ H) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hPCK : P ⊓ C ≤ K)
    (hcyc : ∃ x ∈ P, ∀ y ∈ P, ∃ m : ℕ, y⁻¹ * x ^ m ∈ C) :
    IsCyclic ((P.subgroupOf H).map
      (@QuotientGroup.mk' H _ (K.subgroupOf H) hKn)) := by
  classical
  letI : (K.subgroupOf H).Normal := hKn
  let π : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  obtain ⟨x, hxP, hxcyc⟩ := hcyc
  have hxH : x ∈ H := hPH hxP
  have hEq : (P.subgroupOf H).map π = Subgroup.zpowers (π ⟨x, hxH⟩) := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ P := hp
      obtain ⟨m, hm⟩ := hxcyc (p : G) hpP
      have hpm : (p : G)⁻¹ * x ^ m ∈ K :=
        hPCK ⟨P.mul_mem (P.inv_mem hpP) (P.pow_mem hxP m), hm⟩
      have hπ : π p = π ((⟨x, hxH⟩ : H) ^ m) := by
        change (↑p : H ⧸ K.subgroupOf H) = ↑((⟨x, hxH⟩ : H) ^ m)
        rw [QuotientGroup.eq]
        exact Subgroup.mem_subgroupOf.mpr (by simpa using hpm)
      rw [hπ]
      have hpow : π ((⟨x, hxH⟩ : H) ^ m) = (π ⟨x, hxH⟩) ^ m := map_pow π _ m
      rw [hpow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (π ⟨x, hxH⟩)) hEq.le

end CyclicQuotient

end CFSG.GroupTheory
