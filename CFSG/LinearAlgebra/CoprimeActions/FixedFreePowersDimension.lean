module

public import CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LinearAlgebra.CoprimeActions.FixedFreePowersDimension

open TensorProduct
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

theorem character_eq_one_of_fixed_by_fixedPointFree {Q M : Type*} [CommGroup Q] [Finite Q]
    [CommGroup M] (c : MulAut Q) (hfree : ∀ q : Q, c q = q → q = 1) (χ : Q →* M)
    (hχfix : ∀ q : Q, χ (c q) = χ q) : χ = 1 := by
  classical
  let φ : Q → Q := fun q => c q * q⁻¹
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : c x * x⁻¹ = c y * y⁻¹ := hxy
    have hmul : c x * y = c y * x := (mul_inv_eq_mul_inv_iff_mul_eq_mul).mp hxy'
    have htarget : c (x * y⁻¹) = x * y⁻¹ := by
      calc c (x * y⁻¹) = c x * (c y)⁻¹ := by rw [map_mul, map_inv]
        _ = x * y⁻¹ := (mul_inv_eq_mul_inv_iff_mul_eq_mul).mpr (by rw [hmul, mul_comm])
    exact mul_inv_eq_one.mp (hfree (x * y⁻¹) htarget)
  have hφsurj : Function.Surjective φ := by
    rwa [← Finite.injective_iff_surjective]
  apply MonoidHom.ext
  intro q
  obtain ⟨r, hr⟩ := hφsurj q
  rw [← hr]
  simp [φ, hχfix r]

theorem exists_ne_one_weightSpace_ne_bot {F V E : Type*} [Field F] [IsAlgClosed F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [CommGroup E] [Finite E]
    [Nontrivial E] (τ : Representation F E V) (hτ : Function.Injective τ)
    (hcard : (Nat.card E : F) ≠ 0) :
    ∃ χ : E →* Fˣ, χ ≠ 1 ∧ weightSpace τ χ ≠ ⊥ := by
  classical
  have htop :=
    CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition.span_eq_top τ hcard
  by_contra h
  push Not at h
  have hW1 : weightSpace τ (1 : E →* Fˣ) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ = 1
    · rw [hχ]
    · rw [h χ hχ]
      exact bot_le
  have hτ1 : ∀ g : E, τ g = 1 := by
    intro g
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ weightSpace τ (1 : E →* Fˣ) := hW1 ▸ Submodule.mem_top
    have := (mem_weightSpace τ (1 : E →* Fˣ) v).1 hv g
    simpa using this
  obtain ⟨g, hg⟩ := exists_ne (1 : E)
  exact hg (hτ (by simpa using hτ1 g))

theorem finrank_ge_of_weightSpace_ne_bot {F V E : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [CommGroup E] [Finite E]
    (τ : Representation F E V) (σ : V →ₗ[F] V) (hσ : Function.Injective σ)
    (c : MulAut E) (m : ℕ) (hcov : ∀ g v, σ (τ g v) = τ (c g) (σ v))
    (hfree : ∀ k : ℕ, 0 < k → k < m → ∀ s : E, (c ^ k) s = s → s = 1)
    (χ : E →* Fˣ) (hχ1 : χ ≠ 1) (hχ : weightSpace τ χ ≠ ⊥) :
    m ≤ Module.finrank F V := by
  classical
  let cinv : MulAut E := c⁻¹
  let χi : ℕ → E →* Fˣ := fun n => χ.comp ((cinv ^ n).toMonoidHom)
  have hmap : ∀ (n : ℕ) (v : V), v ∈ weightSpace τ (χi n) →
      σ v ∈ weightSpace τ (χi (n + 1)) := by
    intro n v hv h
    have h1 := hcov (cinv h) v
    have h2 : c (cinv h) = h := by simp [cinv]
    rw [h2] at h1
    rw [← h1, (mem_weightSpace τ (χi n) v).1 hv (cinv h), map_smul]
    congr 1
  have hne : ∀ n : ℕ, weightSpace τ (χi n) ≠ ⊥ := by
    intro n
    induction n with
    | zero =>
      have : χi 0 = χ := by ext g; simp [χi]
      rw [this]
      exact hχ
    | succ n ih =>
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      refine (Submodule.ne_bot_iff _).2 ⟨σ v, hmap n v hv, ?_⟩
      intro h0
      exact hv0 (hσ (by simpa using h0))
  have hcinv_pow : ∀ n : ℕ, cinv ^ n * c ^ n = 1 := by
    intro n
    change (c⁻¹) ^ n * c ^ n = 1
    rw [inv_pow, inv_mul_cancel]
  have hc_cinv_pow : ∀ n : ℕ, c ^ n * cinv ^ n = 1 := by
    intro n
    change c ^ n * (c⁻¹) ^ n = 1
    rw [inv_pow, mul_inv_cancel]
  have hkey : ∀ i j : Fin m, (i : ℕ) < (j : ℕ) → χi (i : ℕ) ≠ χi (j : ℕ) := by
    intro i j hij heq
    let k : ℕ := (j : ℕ) - (i : ℕ)
    have hkpos : 0 < k := Nat.sub_pos_of_lt hij
    have hklt : k < m := by omega
    have hijk : (i : ℕ) + k = (j : ℕ) := by omega
    let ψ : E →* Fˣ := χi (i : ℕ)
    have hψfix : ∀ q : E, ψ ((cinv ^ k) q) = ψ q := by
      intro q
      have h1 : ψ ((cinv ^ k) q) = χi (j : ℕ) q := by
        change χ ((cinv ^ (i : ℕ)) ((cinv ^ k) q)) = χ ((cinv ^ (j : ℕ)) q)
        rw [← MulAut.mul_apply, ← pow_add, hijk]
      rw [h1, ← heq]
    have hfree_inv : ∀ q : E, (cinv ^ k) q = q → q = 1 := by
      intro q hq
      have hck : (c ^ k) q = q := by
        have h1 : (c ^ k) ((cinv ^ k) q) = (c ^ k) q := by rw [hq]
        have h2 : (c ^ k) ((cinv ^ k) q) = (c ^ k * cinv ^ k) q := rfl
        rw [h2, hc_cinv_pow k, MulAut.one_apply] at h1
        exact h1.symm
      exact hfree k hkpos hklt q hck
    have hψ1 : ψ = 1 :=
      character_eq_one_of_fixed_by_fixedPointFree (cinv ^ k) hfree_inv ψ hψfix
    apply hχ1
    have hcomp : ψ.comp ((c ^ (i : ℕ)).toMonoidHom) = χ := by
      refine MonoidHom.ext fun x => ?_
      change χ ((cinv ^ (i : ℕ)) ((c ^ (i : ℕ)) x)) = χ x
      rw [← MulAut.mul_apply, hcinv_pow (i : ℕ), MulAut.one_apply]
    rw [← hcomp, hψ1]
    simp
  have hdistinct : Function.Injective (fun i : Fin m => χi (i : ℕ)) := by
    intro i j hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hkey i j hlt hij
    · exact hkey j i hgt hij.symm
  have hind := independent τ (fun i : Fin m => χi (i : ℕ)) hdistinct
  have hcard : Fintype.card {i : Fin m // weightSpace τ (χi (i : ℕ)) ≠ ⊥} = m := by
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun i : Fin m =>
        weightSpace τ (χi (i : ℕ)) ≠ ⊥) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => hne (i : ℕ)
    rw [hfilter]
    simp
  have := hind.subtype_ne_bot_le_finrank
  rwa [hcard] at this

theorem finrank_ge_of_faithful_fixedFree_normalizer {F V E : Type*} [Field F] [IsAlgClosed F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [CommGroup E] [Finite E]
    [Nontrivial E] (τ : Representation F E V) (hτ : Function.Injective τ)
    (hcard : (Nat.card E : F) ≠ 0) (σ : V →ₗ[F] V) (hσ : Function.Injective σ)
    (c : MulAut E) (m : ℕ) (hcov : ∀ g v, σ (τ g v) = τ (c g) (σ v))
    (hfree : ∀ k : ℕ, 0 < k → k < m → ∀ s : E, (c ^ k) s = s → s = 1) :
    m ≤ Module.finrank F V := by
  obtain ⟨χ, hχ1, hχ⟩ := exists_ne_one_weightSpace_ne_bot τ hτ hcard
  exact finrank_ge_of_weightSpace_ne_bot τ σ hσ c m hcov hfree χ hχ1 hχ

theorem pow_le_card_of_fixedFree {ℓ : ℕ} (hℓ : ℓ.Prime) {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hpow : ∀ v : V, v ^ ℓ = 1) {J : Type*} [Group J]
    [Finite J] (ρ : J →* MulAut V) (S : Subgroup J) (hS : S ≠ ⊥)
    (hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hcop : Nat.Coprime (Nat.card S) ℓ)
    (hfaith : ∀ s ∈ S, ρ s = 1 → s = 1) (t : J) (ht : t ∈ Subgroup.normalizer (S : Set J))
    (m : ℕ) (hfree : ∀ k : ℕ, 0 < k → k < m → ∀ s ∈ S, t ^ k * s * (t ^ k)⁻¹ = s → s = 1) :
    ℓ ^ m ≤ Nat.card V := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hVp : IsPGroup ℓ V := fun v => ⟨1, by simpa using hpow v⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hVp
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hd
  letI : Module (ZMod ℓ) (Fin d → ZMod ℓ) :=
    Pi.Function.module (Fin d) (ZMod ℓ) (ZMod ℓ)
  let φ : MulAut V ≃* GL (Fin d) (ZMod ℓ) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  let toEnd : GL (Fin d) (ZMod ℓ) →* Module.End (ZMod ℓ) (Fin d → ZMod ℓ) :=
    (Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d)).toAlgHom.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin d) (Fin d) (ZMod ℓ)))
  have htoEnd_inj : Function.Injective toEnd := by
    intro A B h
    apply Units.ext
    have h1 : (Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d))
        (A : Matrix (Fin d) (Fin d) (ZMod ℓ)) =
        (Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d))
          (B : Matrix (Fin d) (Fin d) (ZMod ℓ)) := h
    simpa using (Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d)).injective h1
  let τK : Representation (AlgebraicClosure (ZMod ℓ)) J
      (TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ)) :=
    (Module.End.baseChangeHom (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))
      (Fin d → ZMod ℓ)).toMonoidHom.comp (toEnd.comp (φ.toMonoidHom.comp ρ))
  let τS₀ : Representation (ZMod ℓ) S (Fin d → ZMod ℓ) :=
    toEnd.comp (φ.toMonoidHom.comp (ρ.comp S.subtype))
  let τS : Representation (AlgebraicClosure (ZMod ℓ)) S
      (TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ)) :=
    τK.comp S.subtype
  have hτS₀ : Function.Injective τS₀ := by
    intro s u hsu
    have h1 : φ (ρ (s : J)) = φ (ρ (u : J)) := htoEnd_inj hsu
    have h2 : ρ (s : J) = ρ (u : J) := φ.injective h1
    have h3 : ρ (((s * u⁻¹ : S) : J)) = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h2, mul_inv_cancel]
    have h4 : ((s * u⁻¹ : S) : J) = 1 := hfaith _ (s * u⁻¹).2 h3
    exact mul_inv_eq_one.mp (Subtype.ext h4)
  have hbase : Function.Injective
      (Module.End.baseChangeHom (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))
        (Fin d → ZMod ℓ)) := by
    intro f g hfg
    exact LinearMap.baseChangeHom_injective (ZMod ℓ) (Fin d → ZMod ℓ)
      (AlgebraicClosure (ZMod ℓ)) hfg
  have hτS : Function.Injective τS := by
    intro s u hsu
    apply hτS₀
    apply hbase
    exact hsu
  letI : CommGroup S :=
    { (inferInstance : Group S) with
      mul_comm := fun a b => Subtype.ext (hScomm a a.2 b b.2) }
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS
  have hcardS : (Nat.card S : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
    intro h0
    have hdvd : ℓ ∣ Nat.card S :=
      (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod ℓ)) ℓ (Nat.card S)).mp h0
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp (Nat.coprime_comm.mp hcop) hdvd
  let c : MulAut S := S.normalizerMonoidHom ⟨t, ht⟩
  have hc_pow : ∀ (k : ℕ) (s : S),
      (((c ^ k) s : S) : J) = t ^ k * (s : J) * (t ^ k)⁻¹ := by
    intro k s
    have h1 : c ^ k = S.normalizerMonoidHom (⟨t, ht⟩ ^ k) := by
      change (S.normalizerMonoidHom ⟨t, ht⟩) ^ k =
        S.normalizerMonoidHom (⟨t, ht⟩ ^ k)
      rw [map_pow]
    rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [Subgroup.coe_pow]
  let σK : TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ) →ₗ[
      AlgebraicClosure (ZMod ℓ)]
      TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ) := τK t
  have hσK : Function.Injective σK := by
    have hleft : ∀ x, τK t⁻¹ (τK t x) = x := by
      intro x
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    intro x y hxy
    exact (hleft x).symm.trans ((congrArg (τK t⁻¹) hxy).trans (hleft y))
  have hcov : ∀ g : S, ∀ v, σK (τS g v) = τS (c g) (σK v) := by
    intro g v
    change τK t (τK (g : J) v) = τK ((c g : S) : J) (τK t v)
    rw [show (c : MulAut S) g = (c ^ 1) g by rw [pow_one], hc_pow 1 g, pow_one]
    calc τK t (τK (g : J) v) = τK (t * (g : J)) v := by
          rw [← Module.End.mul_apply, ← map_mul]
      _ = τK ((t * (g : J) * t⁻¹) * t) v := by
          congr 1
          group
      _ = τK (t * (g : J) * t⁻¹) (τK t v) := by
          rw [← Module.End.mul_apply, ← map_mul]
  have hfreeS : ∀ k : ℕ, 0 < k → k < m → ∀ s : S, (c ^ k) s = s → s = 1 := by
    intro k hk0 hkm s hs
    apply Subtype.ext
    have h1 : t ^ k * (s : J) * (t ^ k)⁻¹ = (s : J) := by
      rw [← hc_pow k s, hs]
    simpa using hfree k hk0 hkm (s : J) s.2 h1
  have hmain : m ≤ Module.finrank (AlgebraicClosure (ZMod ℓ))
      (TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ)) :=
    finrank_ge_of_faithful_fixedFree_normalizer (F := AlgebraicClosure (ZMod ℓ)) τS hτS
      hcardS σK hσK c m hcov hfreeS
  have hdim : Module.finrank (AlgebraicClosure (ZMod ℓ))
      (TensorProduct (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ)) = d := by
    rw [Module.finrank_baseChange]
    simp [Module.finrank_fin_fun]
  have hmd : m ≤ d := by
    rwa [hdim] at hmain
  calc ℓ ^ m ≤ ℓ ^ d := Nat.pow_le_pow_right hℓ.pos hmd
    _ = Nat.card V := hd.symm
