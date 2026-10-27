module

public import CFSG.LieType.Steinberg.Minuscule.Valid
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

section SignedMap

variable {R : Type*} [CommRing R] {d : ℕ}

@[expose] def IsSign (σ : R) : Prop := σ = 1 ∨ σ = -1

theorem isSign_one : IsSign (1 : R) := Or.inl rfl

theorem isSign_neg_one : IsSign (-1 : R) := Or.inr rfl

theorem IsSign.mul_self {σ : R} (h : IsSign σ) : σ * σ = 1 := by
  rcases h with rfl | rfl <;> simp

theorem IsSign.mul {σ τ : R} (hσ : IsSign σ) (hτ : IsSign τ) : IsSign (σ * τ) := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp [IsSign]

theorem IsSign.smul_smul_self {M : Type*} [AddCommMonoid M] [Module R M] {σ : R}
    (h : IsSign σ) (x : M) : σ • σ • x = x := by
  rw [smul_smul, h.mul_self, one_smul]

@[expose] def IsSigned (w : Fin d →₀ R) (b : Fin d) : Prop :=
  w = Finsupp.single b 1 ∨ w = -Finsupp.single b 1

@[expose] def IsSignedMap (f : Module.End R (Fin d →₀ R)) (P : Fin d → Fin d → Prop) : Prop :=
  ∀ a, f (Finsupp.single a 1) = 0 ∨ ∃ b, P a b ∧ IsSigned (f (Finsupp.single a 1)) b

theorem IsSigned.neg {w : Fin d →₀ R} {b : Fin d} (h : IsSigned w b) : IsSigned (-w) b := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem IsSigned.smul {w : Fin d →₀ R} {b : Fin d} {σ : R} (hσ : IsSign σ) (h : IsSigned w b) :
    IsSigned (σ • w) b := by
  rcases hσ with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]
    exact h.neg

theorem IsSignedMap.mono {f : Module.End R (Fin d →₀ R)} {P Q : Fin d → Fin d → Prop}
    (h : IsSignedMap f P) (hPQ : ∀ a b, P a b → Q a b) : IsSignedMap f Q := fun a =>
  (h a).imp_right fun ⟨b, hb, hs⟩ => ⟨b, hPQ a b hb, hs⟩

theorem IsSignedMap.mul {f g : Module.End R (Fin d →₀ R)} {P Q : Fin d → Fin d → Prop}
    (hf : IsSignedMap f P) (hg : IsSignedMap g Q) :
    IsSignedMap (f * g) fun a c => ∃ b, Q a b ∧ P b c := by
  intro a
  rw [Module.End.mul_apply]
  rcases hg a with h0 | ⟨b, hb, hs⟩
  · exact Or.inl (by rw [h0, map_zero])
  rcases hf b with h0' | ⟨c, hc, hs'⟩
  · left
    rcases hs with h | h <;> rw [h] <;> simp [h0']
  · right
    refine ⟨c, ⟨b, hb, hc⟩, ?_⟩
    rcases hs with h | h <;> rw [h]
    · exact hs'
    · rw [map_neg]
      exact hs'.neg

theorem IsSignedMap.smul {f : Module.End R (Fin d →₀ R)} {P : Fin d → Fin d → Prop} {σ : R}
    (hσ : IsSign σ) (h : IsSignedMap f P) : IsSignedMap (σ • f) P := fun a =>
  (h a).imp (fun h0 => by rw [LinearMap.smul_apply, h0, smul_zero])
    fun ⟨b, hb, hs⟩ => ⟨b, hb, hs.smul hσ⟩

end SignedMap

namespace MinData

variable {τ : Tag} (D : MinData τ) (R : Type*) [CommRing R]

@[expose] def E (k : ℕ) : Module.End R (Fin D.d →₀ R) := toEnd R D.d (D.op k)

@[expose] def nOp (i : Fin τ.rank) : Module.End R (Fin D.d →₀ R) := toEnd R D.d (D.weylOp i)

@[expose] def nInv (i : Fin τ.rank) : Module.End R (Fin D.d →₀ R) :=
  toEnd R D.d (inv D.d (D.weylOp i))

open _root_.Classical in
@[expose] def rootOp (γ : Fin τ.rank → ℤ) : Module.End R (Fin D.d →₀ R) :=
  if h : ∃ k, k < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root k = γ then
    D.E R (Nat.find h) else 0

@[expose] def PairRel (γ δ : Fin τ.rank → ℤ) : Prop :=
  (IsRoot τ (γ + δ) →
      (∃ σ : R, IsSign σ ∧
        D.rootOp R γ * D.rootOp R δ - D.rootOp R δ * D.rootOp R γ = σ • D.rootOp R (γ + δ)) ∧
      D.rootOp R γ * D.rootOp R δ * D.rootOp R γ = 0 ∧
      D.rootOp R δ * D.rootOp R γ * D.rootOp R δ = 0) ∧
    (¬ IsRoot τ (γ + δ) → D.rootOp R γ * D.rootOp R δ = D.rootOp R δ * D.rootOp R γ)

variable {D R}

theorem rootOp_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    D.rootOp R (τ.rootCertificate.root k) = D.E R k := by
  classical
  have h : ∃ k', k' < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root k' = τ.rootCertificate.root k := ⟨k, hk, rfl⟩
  rw [rootOp, dite_eq_left h]
  congr 1
  exact root_injOn (Nat.find_spec h).1 hk (Nat.find_spec h).2

theorem rootOp_eq_zero {γ : Fin τ.rank → ℤ} (hγ : ¬ IsRoot τ γ) : D.rootOp R γ = 0 := by
  classical
  rw [rootOp, dite_eq_right]
  rintro ⟨k, hk, rfl⟩
  exact hγ (RootCertificate.isRoot_root τ.rootCertificate_check k hk)

namespace Valid

variable (hV : D.Valid)
include hV

private theorem two_weyl_lt (i : Fin τ.rank) (b : ℕ) (hb : b < D.d) :
    2 * (D.weyl b i + 1) + 1 < 256 := by
  have := hV.weyl_lt hb i
  have := hV.d_le
  omega

theorem dig_simpleE (i : Fin τ.rank) (a : Fin D.d) :
    dig (D.simpleE i) a = if D.wt a i = -1 then 2 * (D.weyl a i + 1) else 0 :=
  dig_ofDigits (fun b hb => by have := hV.two_weyl_lt i b hb; split_ifs <;> omega) a.2

theorem dig_simpleF (i : Fin τ.rank) (a : Fin D.d) :
    dig (D.simpleF i) a = if D.wt a i = 1 then 2 * (D.weyl a i + 1) else 0 :=
  dig_ofDigits (fun b hb => by have := hV.two_weyl_lt i b hb; split_ifs <;> omega) a.2

theorem dig_weylOp (i : Fin τ.rank) (a : Fin D.d) :
    dig (D.weylOp i) a = 2 * (D.weyl a i + 1) + if D.wt a i = 1 then 1 else 0 :=
  dig_ofDigits (fun b hb => by have := hV.two_weyl_lt i b hb; split_ifs <;> omega) a.2

private theorem digVec_two_mul (i : Fin τ.rank) (a : Fin D.d) :
    digVec R D.d (2 * (D.weyl a i + 1)) = Finsupp.single (hV.sRefl i a) 1 := by
  have h1 := (hV.sRefl i a).2
  rw [hV.sRefl_val] at h1
  rw [digVec_of_le (by omega) (by omega), pow_mul, neg_one_sq, one_pow, one_smul]
  congr 1
  exact Fin.ext (by rw [hV.sRefl_val]; simp only; omega)

theorem toEnd_simpleE_single (i : Fin τ.rank) (a : Fin D.d) :
    toEnd R D.d (D.simpleE i) (Finsupp.single a 1) =
      if D.wt a i = -1 then Finsupp.single (hV.sRefl i a) 1 else 0 := by
  rw [toEnd_single, hV.dig_simpleE]
  split_ifs
  · exact hV.digVec_two_mul i a
  · exact digVec_zero

theorem toEnd_simpleF_single (i : Fin τ.rank) (a : Fin D.d) :
    toEnd R D.d (D.simpleF i) (Finsupp.single a 1) =
      if D.wt a i = 1 then Finsupp.single (hV.sRefl i a) 1 else 0 := by
  rw [toEnd_single, hV.dig_simpleF]
  split_ifs
  · exact hV.digVec_two_mul i a
  · exact digVec_zero

theorem isSPerm_weylOp (i : Fin τ.rank) : IsSPerm D.d (D.weylOp i) := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · have h1 := hV.weyl_lt ha i
    have := hV.dig_weylOp i ⟨a, ha⟩
    simp only at this
    rw [this]
    split_ifs <;> omega
  · have h1 := hV.dig_weylOp i ⟨a, ha⟩
    have h2 := hV.dig_weylOp i ⟨b, hb⟩
    simp only at h1 h2
    rw [h1, h2] at hab
    have : D.weyl a i = D.weyl b i := by split_ifs at hab <;> omega
    have := hV.sRefl_injective i (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (Fin.ext (by rw [hV.sRefl_val, hV.sRefl_val]; exact this))
    exact congrArg Fin.val this

theorem nOp_single (i : Fin τ.rank) (a : Fin D.d) :
    D.nOp R i (Finsupp.single a 1) =
      if D.wt a i = 1 then -Finsupp.single (hV.sRefl i a) 1
      else Finsupp.single (hV.sRefl i a) 1 := by
  rw [nOp, toEnd_single, hV.dig_weylOp]
  split_ifs
  · rw [← hV.digVec_two_mul i a, ← digVec_negDigit]
    congr 1
    simp only [negDigit]
    split_ifs <;> omega
  · rw [add_zero]
    exact hV.digVec_two_mul i a

theorem nOp_single_of_eq_neg_one {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = -1) :
    D.nOp R i (Finsupp.single a 1) = Finsupp.single (hV.sRefl i a) 1 := by
  rw [hV.nOp_single, ite_eq_right (by omega)]

theorem nOp_single_of_eq_one {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = 1) :
    D.nOp R i (Finsupp.single a 1) = -Finsupp.single (hV.sRefl i a) 1 := by
  rw [hV.nOp_single, ite_eq_left h]

theorem nOp_single_of_eq_zero {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = 0) :
    D.nOp R i (Finsupp.single a 1) = Finsupp.single a 1 := by
  rw [hV.nOp_single, ite_eq_right (by omega), hV.sRefl_eq_self h]

theorem nInv_mul_nOp (i : Fin τ.rank) : D.nInv R i * D.nOp R i = 1 :=
  (hV.isSPerm_weylOp i).toEnd_inv_mul hV.d_le

theorem nOp_mul_nInv (i : Fin τ.rank) : D.nOp R i * D.nInv R i = 1 :=
  (hV.isSPerm_weylOp i).toEnd_mul_inv hV.d_le

theorem nInv_nOp_apply (i : Fin τ.rank) (v : Fin D.d →₀ R) : D.nInv R i (D.nOp R i v) = v := by
  rw [← Module.End.mul_apply, hV.nInv_mul_nOp, Module.End.one_apply]

theorem nInv_single (i : Fin τ.rank) (a : Fin D.d) :
    D.nInv R i (Finsupp.single a 1) =
      if D.wt a i = -1 then -Finsupp.single (hV.sRefl i a) 1
      else Finsupp.single (hV.sRefl i a) 1 := by
  have h := congrArg (D.nInv R i) (hV.nOp_single (R := R) i (hV.sRefl i a))
  rw [hV.nInv_nOp_apply, hV.sRefl_sRefl, hV.wt_sRefl_self] at h
  by_cases ha : D.wt a i = -1
  · rw [ite_eq_left (by omega), map_neg] at h
    rw [ite_eq_left ha, h, neg_neg]
  · rw [ite_eq_right (by omega)] at h
    rw [ite_eq_right ha, h]

theorem isSignedMap_nOp (i : Fin τ.rank) :
    IsSignedMap (D.nOp R i) fun a b => b = hV.sRefl i a := fun a => by
  right
  refine ⟨_, rfl, ?_⟩
  rw [hV.nOp_single]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem isSignedMap_nInv (i : Fin τ.rank) :
    IsSignedMap (D.nInv R i) fun a b => b = hV.sRefl i a := fun a => by
  right
  refine ⟨_, rfl, ?_⟩
  rw [hV.nInv_single]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem rootOp_single (i : Fin τ.rank) :
    D.rootOp R (Pi.single i 1) = toEnd R D.d (D.simpleE i) := by
  rw [← root_basis i, rootOp_root (lt_of_lt_of_le i.2 rank_le_length), E, hV.op_single]

theorem rootOp_neg_single (i : Fin τ.rank) :
    D.rootOp R (-Pi.single i 1) = toEnd R D.d (D.simpleF i) := by
  rw [← root_image_self i,
    rootOp_root (image_lt (lt_of_lt_of_le i.2 rank_le_length) i), E, hV.op_image_self]

theorem rootOp_single_apply (i : Fin τ.rank) (a : Fin D.d) :
    D.rootOp R (Pi.single i 1) (Finsupp.single a 1) =
      if D.wt a i = -1 then Finsupp.single (hV.sRefl i a) 1 else 0 := by
  rw [hV.rootOp_single, hV.toEnd_simpleE_single]

theorem rootOp_neg_single_apply (i : Fin τ.rank) (a : Fin D.d) :
    D.rootOp R (-Pi.single i 1) (Finsupp.single a 1) =
      if D.wt a i = 1 then Finsupp.single (hV.sRefl i a) 1 else 0 := by
  rw [hV.rootOp_neg_single, hV.toEnd_simpleF_single]

theorem conj_rootOp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (i : Fin τ.rank) :
    ∃ σ : R, IsSign σ ∧
      D.nOp R i * D.rootOp R γ * D.nInv R i = σ • D.rootOp R (reflect τ i γ) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  rw [rootOp_root hk, ← root_image hk i, rootOp_root (image_lt hk i), nOp, E, nInv,
    ← (hV.isSPerm_weylOp i).toEnd_conj hV.d_le (hV.wf_op k), hV.conj_op hk i]
  split_ifs
  · refine ⟨-1, isSign_neg_one, ?_⟩
    rw [toEnd_neg]
    exact (neg_one_smul R (toEnd R D.d (D.op (τ.rootCertificate.image k i)))).symm
  · exact ⟨1, isSign_one, (one_smul R (toEnd R D.d (D.op (τ.rootCertificate.image k i)))).symm⟩

theorem rootOp_reflect {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (i : Fin τ.rank) :
    ∃ σ : R, IsSign σ ∧
      D.rootOp R (reflect τ i γ) = σ • (D.nOp R i * D.rootOp R γ * D.nInv R i) := by
  obtain ⟨σ, hσ, h⟩ := hV.conj_rootOp (R := R) hγ i
  exact ⟨σ, hσ, by rw [h, hσ.smul_smul_self]⟩

theorem conj_mul (i : Fin τ.rank) (X Y : Module.End R (Fin D.d →₀ R)) :
    D.nOp R i * (X * Y) * D.nInv R i =
      (D.nOp R i * X * D.nInv R i) * (D.nOp R i * Y * D.nInv R i) := by
  have h := hV.nInv_mul_nOp (R := R) i
  calc D.nOp R i * (X * Y) * D.nInv R i = D.nOp R i * X * (D.nInv R i * D.nOp R i) * Y *
        D.nInv R i := by rw [h, mul_one]; noncomm_ring
    _ = _ := by noncomm_ring

theorem conj_injective (i : Fin τ.rank) {X Y : Module.End R (Fin D.d →₀ R)}
    (h : D.nOp R i * X * D.nInv R i = D.nOp R i * Y * D.nInv R i) : X = Y := by
  have hl := hV.nInv_mul_nOp (R := R) i
  calc X = D.nInv R i * (D.nOp R i * X * D.nInv R i) * D.nOp R i := by
        rw [show D.nInv R i * (D.nOp R i * X * D.nInv R i) * D.nOp R i =
          (D.nInv R i * D.nOp R i) * X * (D.nInv R i * D.nOp R i) by noncomm_ring, hl, one_mul,
          mul_one]
    _ = D.nInv R i * (D.nOp R i * Y * D.nInv R i) * D.nOp R i := by rw [h]
    _ = Y := by
        rw [show D.nInv R i * (D.nOp R i * Y * D.nInv R i) * D.nOp R i =
          (D.nInv R i * D.nOp R i) * Y * (D.nInv R i * D.nOp R i) by noncomm_ring, hl, one_mul,
          mul_one]

theorem isSignedMap_rootOp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    IsSignedMap (D.rootOp R γ) fun a b => D.wt b = D.wt a + toWeight γ := by
  induction hγ with
  | basis j =>
    intro a
    rw [hV.rootOp_single_apply]
    split_ifs with h
    · exact Or.inr ⟨_, show D.wt (hV.sRefl j a) = _ by
        rw [hV.wt_sRefl, reflectWeight_eq_add_of_eq_neg_one h], Or.inl rfl⟩
    · exact Or.inl rfl
  | @reflect i v hv ih =>
    obtain ⟨σ, hσ, h⟩ := hV.rootOp_reflect (R := R) hv i
    rw [h]
    refine (((hV.isSignedMap_nOp i).mul ih).mul (hV.isSignedMap_nInv i)).smul hσ |>.mono ?_
    rintro a c ⟨b, rfl, b', hb', rfl⟩
    rw [hV.wt_sRefl, hb', hV.wt_sRefl, reflectWeight_add, reflectWeight_reflectWeight,
      toWeight_reflect]

theorem rootOp_mul_self (γ : Fin τ.rank → ℤ) : D.rootOp R γ * D.rootOp R γ = 0 := by
  by_cases hγ : IsRoot τ γ
  swap
  · rw [rootOp_eq_zero hγ, mul_zero]
  induction hγ with
  | basis j =>
    refine ext_single fun a => ?_
    rw [Module.End.mul_apply, hV.rootOp_single_apply, LinearMap.zero_apply]
    split_ifs with h
    · rw [hV.rootOp_single_apply, ite_eq_right]
      rw [hV.wt_sRefl_self, h]
      norm_num
    · exact map_zero _
  | @reflect i v hv ih =>
    obtain ⟨σ, -, h⟩ := hV.rootOp_reflect (R := R) hv i
    rw [h, smul_mul_smul_comm, ← hV.conj_mul, ih, mul_zero, zero_mul, smul_zero]

theorem rootOp_ne_zero [Nontrivial R] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    D.rootOp R γ ≠ 0 := by
  induction hγ with
  | basis j =>
    have h := hV.simpleE_ne_zero j
    have : ∃ a : Fin D.d, D.wt a j = -1 := by
      by_contra hne
      simp only [not_exists] at hne
      apply h
      rw [simpleE, ofDigits_eq_sum]
      exact Finset.sum_eq_zero fun a _ => by rw [ite_eq_right (hne a), zero_mul]
    obtain ⟨a, ha⟩ := this
    intro h0
    have := hV.rootOp_single_apply (R := R) j a
    rw [h0, ite_eq_left ha, LinearMap.zero_apply] at this
    exact Finsupp.single_ne_zero.2 one_ne_zero this.symm
  | @reflect i v hv ih =>
    intro h0
    obtain ⟨σ, -, h⟩ := hV.conj_rootOp (R := R) hv i
    rw [h0, smul_zero] at h
    exact ih (hV.conj_injective i (by rw [h, mul_zero, zero_mul]))

omit hV in
theorem reflectWeight_dotProduct (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (i : Fin τ.rank)
    (μ γ : Fin τ.rank → ℤ) : reflectWeight i μ ⬝ᵥ γ = μ ⬝ᵥ reflect τ i γ := by
  have h : toWeight (Pi.single i 1) ⬝ᵥ γ = toWeight γ i := by
    simp only [dotProduct, toWeight_single]
    rw [toWeight_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hsymm]
  rw [reflectWeight, reflect_eq, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dotProduct_single, mul_one, h, smul_eq_mul, smul_eq_mul, mul_comm]

theorem rootOp_single_ne_zero_iff [Nontrivial R] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (a : Fin D.d) :
    D.rootOp R γ (Finsupp.single a 1) ≠ 0 ↔ D.wt a ⬝ᵥ γ = -1 := by
  induction hγ generalizing a with
  | basis j =>
    rw [hV.rootOp_single_apply, dotProduct_single, mul_one]
    split_ifs with h
    · exact iff_of_true (Finsupp.single_ne_zero.2 one_ne_zero) h
    · exact iff_of_false (fun h0 => h0 rfl) h
  | @reflect i v hv ih =>
    obtain ⟨σ, hσ, h⟩ := hV.rootOp_reflect (R := R) hv i
    have hinj : ∀ w : Fin D.d →₀ R, D.nOp R i w = 0 → w = 0 := fun w hw => by
      rw [← hV.nInv_nOp_apply i w, hw, map_zero]
    rw [← reflectWeight_dotProduct hsymm, ← hV.wt_sRefl, ← ih, h, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hV.nInv_single]
    constructor
    · intro hne h0
      apply hne
      split_ifs <;> simp [h0]
    · intro hne h0
      have h1 : D.nOp R i (D.rootOp R v (if D.wt a i = -1 then -Finsupp.single (hV.sRefl i a) 1
          else Finsupp.single (hV.sRefl i a) 1)) = 0 := by
        rw [← hσ.smul_smul_self (D.nOp R i _), h0, smul_zero]
      apply hne
      have h2 := hinj _ h1
      split_ifs at h2
      · rw [map_neg, neg_eq_zero] at h2
        exact h2
      · exact h2

omit hV in
theorem conj_sub (i : Fin τ.rank) (X Y : Module.End R (Fin D.d →₀ R)) :
    D.nOp R i * (X - Y) * D.nInv R i =
      D.nOp R i * X * D.nInv R i - D.nOp R i * Y * D.nInv R i := by
  noncomm_ring

omit hV in
theorem conj_smul (i : Fin τ.rank) (σ : R) (X : Module.End R (Fin D.d →₀ R)) :
    D.nOp R i * (σ • X) * D.nInv R i = σ • (D.nOp R i * X * D.nInv R i) := by
  rw [mul_smul_comm, smul_mul_assoc]

omit hV in
theorem reflect_add (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u + v) = reflect τ i u + reflect τ i v := by
  simp only [← reflectHom_apply, map_add]

omit hV in
theorem reflect_zero (i : Fin τ.rank) : reflect τ i 0 = 0 := by
  rw [← reflectHom_apply, map_zero]

theorem pairRel_single (j : Fin τ.rank) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hne : Pi.single j 1 + δ ≠ 0) : D.PairRel R (Pi.single j 1) δ := by
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hδ
  have hj : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 rank_le_length
  have hEj : D.rootOp R (Pi.single j 1) = D.E R j := by rw [← root_basis j, rootOp_root hj]
  have hA : toEnd R D.d (comp D.d (D.op j) (D.op l)) = D.E R j * D.E R l :=
    toEnd_comp (hV.wf_op l)
  have hB : toEnd R D.d (comp D.d (D.op l) (D.op j)) = D.E R l * D.E R j :=
    toEnd_comp (hV.wf_op j)
  rw [PairRel, hEj, rootOp_root hl]
  rcases hV.pairs hl j with h | ⟨hnr, hAB⟩ | ⟨m, hm, hroot, hdisj, hunion, hA0, hB0⟩
  · exact absurd (by rw [h, add_neg_cancel]) hne
  · refine ⟨fun hr => absurd hr hnr, fun _ => ?_⟩
    rw [← hA, ← hB, hAB]
  · have hr : IsRoot τ (Pi.single j 1 + τ.rootCertificate.root l) :=
      hroot ▸ RootCertificate.isRoot_root τ.rootCertificate_check m hm
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hnr => absurd hr hnr⟩
    · have hu := toEnd_union_neg (R := R) hdisj
      rw [hA, hB] at hu
      rw [← hroot, rootOp_root hm, ← hu]
      rcases hunion with h | h
      · exact ⟨1, isSign_one, by rw [h, one_smul]; rfl⟩
      · refine ⟨-1, isSign_neg_one, ?_⟩
        rw [h, toEnd_neg]
        exact (neg_one_smul R (D.E R m)).symm
    · have h3 := toEnd_comp (R := R) (M := comp D.d (D.op j) (D.op l)) (hV.wf_op j)
      rw [hA0, toEnd_zero, hA] at h3
      exact h3.symm
    · have h3 := toEnd_comp (R := R) (M := comp D.d (D.op l) (D.op j)) (hV.wf_op l)
      rw [hB0, toEnd_zero, hB] at h3
      exact h3.symm

theorem pairRel_reflect {v δ : Fin τ.rank → ℤ} (hv : IsRoot τ v) (hδ : IsRoot τ δ)
    (i : Fin τ.rank) (h : D.PairRel R v (reflect τ i δ)) : D.PairRel R (reflect τ i v) δ := by
  obtain ⟨σ1, hσ1, h1⟩ := hV.conj_rootOp (R := R) hv i
  obtain ⟨σ2, hσ2, h2⟩ := hV.conj_rootOp (R := R) (hδ.reflect i) i
  rw [reflect_reflect] at h2
  have hsum : reflect τ i (v + reflect τ i δ) = reflect τ i v + δ := by
    rw [reflect_add, reflect_reflect]
  have hiff : IsRoot τ (reflect τ i v + δ) ↔ IsRoot τ (v + reflect τ i δ) := by
    rw [← hsum, isRoot_reflect_iff]
  have e1 : D.rootOp R (reflect τ i v) = σ1 • (D.nOp R i * D.rootOp R v * D.nInv R i) := by
    rw [h1, hσ1.smul_smul_self]
  have e2 : D.rootOp R δ = σ2 • (D.nOp R i * D.rootOp R (reflect τ i δ) * D.nInv R i) := by
    rw [h2, hσ2.smul_smul_self]
  have hprod : D.rootOp R (reflect τ i v) * D.rootOp R δ =
      (σ1 * σ2) • (D.nOp R i * (D.rootOp R v * D.rootOp R (reflect τ i δ)) * D.nInv R i) := by
    rw [e1, e2, smul_mul_smul_comm, hV.conj_mul]
  have hprod' : D.rootOp R δ * D.rootOp R (reflect τ i v) =
      (σ1 * σ2) • (D.nOp R i * (D.rootOp R (reflect τ i δ) * D.rootOp R v) * D.nInv R i) := by
    rw [e1, e2, smul_mul_smul_comm, hV.conj_mul, mul_comm σ2]
  obtain ⟨hroot, hcomm⟩ := h
  refine ⟨fun hr => ?_, fun hnr => ?_⟩
  · obtain ⟨⟨σ, hσ, hc⟩, h3, h4⟩ := hroot (hiff.1 hr)
    obtain ⟨σ3, hσ3, h5⟩ := hV.conj_rootOp (R := R) (hiff.1 hr) i
    rw [hsum] at h5
    refine ⟨⟨σ1 * σ2 * σ * σ3, ((hσ1.mul hσ2).mul hσ).mul hσ3, ?_⟩, ?_, ?_⟩
    · rw [hprod, hprod']
      calc _ = (σ1 * σ2) • (D.nOp R i * (D.rootOp R v * D.rootOp R (reflect τ i δ) -
              D.rootOp R (reflect τ i δ) * D.rootOp R v) * D.nInv R i) := by
            rw [conj_sub]
            exact (smul_sub _ _ _).symm
        _ = _ := by rw [hc, conj_smul, h5, smul_smul, smul_smul]
    · rw [hprod, e1, smul_mul_smul_comm, ← hV.conj_mul, h3, mul_zero, zero_mul, smul_zero]
    · rw [hprod', e2, smul_mul_smul_comm, ← hV.conj_mul, h4, mul_zero, zero_mul, smul_zero]
  · rw [hprod, hprod', hcomm (fun h' => hnr (hiff.2 h'))]

theorem pairRel {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ + δ ≠ 0) :
    D.PairRel R γ δ := by
  induction hγ generalizing δ with
  | basis j => exact hV.pairRel_single j hδ hne
  | @reflect i v hv ih =>
    refine hV.pairRel_reflect hv hδ i (ih (hδ.reflect i) fun h0 => hne ?_)
    have := congrArg (reflect τ i) h0
    rwa [reflect_add, reflect_reflect, reflect_zero] at this

theorem nOp_comm {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j = 0) :
    D.nOp R i * D.nOp R j = D.nOp R j * D.nOp R i := by
  rcases hV.braid hij with ⟨-, hc⟩ | ⟨hc, -⟩
  · rw [nOp, nOp, ← toEnd_comp (hV.isSPerm_weylOp j).wf, hc,
      toEnd_comp (hV.isSPerm_weylOp i).wf]
  · rw [h, zero_mul] at hc
    exact absurd hc zero_ne_one

theorem cartan_mul_cartan {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j ≠ 0) :
    τ.cartan i j * τ.cartan j i = 1 := by
  rcases hV.braid hij with ⟨h0, -⟩ | ⟨hc, -⟩
  · exact absurd h0 h
  · exact hc

theorem nOp_braid {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j ≠ 0) :
    D.nOp R i * D.nOp R j * D.nOp R i = D.nOp R j * D.nOp R i * D.nOp R j := by
  rcases hV.braid hij with ⟨h0, -⟩ | ⟨-, hc⟩
  · exact absurd h0 h
  · have hwf := fun k => (hV.isSPerm_weylOp k).wf
    have e1 : toEnd R D.d (comp D.d (D.weylOp i) (comp D.d (D.weylOp j) (D.weylOp i))) =
        D.nOp R i * D.nOp R j * D.nOp R i := by
      rw [toEnd_comp ((hwf j).comp (hwf i)), toEnd_comp (hwf i), mul_assoc]
      rfl
    have e2 : toEnd R D.d (comp D.d (D.weylOp j) (comp D.d (D.weylOp i) (D.weylOp j))) =
        D.nOp R j * D.nOp R i * D.nOp R j := by
      rw [toEnd_comp ((hwf i).comp (hwf j)), toEnd_comp (hwf j), mul_assoc]
      rfl
    rw [← e1, ← e2, hc]

end Valid

end MinData

end CFSG.LieType.Steinberg.Minuscule
