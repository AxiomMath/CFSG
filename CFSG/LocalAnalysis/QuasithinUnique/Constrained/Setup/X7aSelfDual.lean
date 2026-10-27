module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Sub

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open scoped IsMulCommutative

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7

@[expose] def SelfDualInvolutionRank : Prop :=
  ∀ (f : ℕ) (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ f → 1 ≤ f →
    ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
      (ρ : Representation (ZMod 2) SL(3, F) U), ρ.IsIrreducible → (∃ x, ρ x ≠ 1) →
      Nonempty (ρ.Equiv ρ.dual) →
        ∀ t : SL(3, F), t ≠ 1 → t * t = 1 →
          4 * f ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1))

section SchurPart

variable {F : Type} [Field F] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem eq_one_of_commutes_sq_one (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (a : U ≃ₗ[ZMod 2] U) (hcomm : ∀ x u, a (ρ x u) = ρ x (a u)) (hsq : a * a = 1) : a = 1 := by
  have hnt : Nontrivial U := ((isIrreducible_iff ρ).mp hirr).1
  let c : U →ₗ[ZMod 2] U := a.toLinearMap - 1
  let cI : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := c
      isIntertwining' := fun g => by
        refine LinearMap.ext fun u => ?_
        simp [c, hcomm] }
  have hcc : ∀ u, c (c u) = 0 := by
    intro u
    have h1 : a (a u) = u := by
      have := LinearEquiv.congr_fun hsq u
      simpa using this
    simp only [c, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, h1]
    have h2 := add_self_eq_zero_of_zmod_two u
    have h3 := add_self_eq_zero_of_zmod_two (a u)
    calc u - a u - (a u - u) = (u + u) - (a u + a u) := by abel
      _ = 0 := by rw [h2, h3, sub_zero]
  rcases hirr.bijective_or_eq_zero cI with hb | h0
  · exfalso
    obtain ⟨u, v, huv⟩ := exists_pair_ne U
    have hc0 : ∀ w, c w = 0 := by
      intro w
      obtain ⟨w', hw'⟩ := hb.2 w
      rw [← hw']
      exact hcc w'
    have : c u = c v := by rw [hc0, hc0]
    exact huv (hb.1 this)
  · refine LinearEquiv.ext fun u => ?_
    have h1 : c u = 0 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0) u
    have h2 : a u - u = 0 := by simpa [c] using h1
    simpa using sub_eq_zero.mp h2

end SchurPart

section Main

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem not_scalar_up3 [CharP F 2] : ¬ ∃ c : F, ((up3 (0 : F) 0 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.scalar (Fin 3) c := by
  rintro ⟨c, hc⟩
  have := congrFun (congrFun hc 0) 1
  simp [up3_coe, upMat] at this

omit [Fintype F] in
theorem isTransvection_sq [CharP F 2] {t : SL(3, F)} (ht : IsTransvection t) : t * t = 1 := by
  obtain ⟨v, w, hv, hw, hwv, htm⟩ := ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, htm, Matrix.SpecialLinearGroup.coe_one]
  have hsq : Matrix.vecMulVec v w * Matrix.vecMulVec v w = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hwv, zero_smul, Matrix.vecMulVec_zero]
  have h2M : Matrix.vecMulVec v w + Matrix.vecMulVec v w = 0 := by
    ext i j
    simp [Matrix.vecMulVec_apply, CharTwo.add_self_eq_zero]
  calc (1 + Matrix.vecMulVec v w) * (1 + Matrix.vecMulVec v w)
      = 1 + (Matrix.vecMulVec v w + Matrix.vecMulVec v w) + Matrix.vecMulVec v w *
        Matrix.vecMulVec v w := by noncomm_ring
    _ = 1 := by rw [h2M, hsq]; simp

omit [Fintype F] in
theorem ne_one_of_isTransvection {t : SL(3, F)} (ht : IsTransvection t) : t ≠ 1 := by
  obtain ⟨v, w, hv, hw, hwv, htm⟩ := ht
  intro h
  rw [h, Matrix.SpecialLinearGroup.coe_one] at htm
  have h1 : Matrix.vecMulVec v w = 0 := by
    have := htm
    simpa using this
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (funext hc)
  have := congrFun (congrFun h1 i) j
  simp [Matrix.vecMulVec_apply] at this
  rcases this with h | h
  · exact hi h
  · exact hj h

@[expose] def fixOf {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (A : Subgroup (U ≃ₗ[ZMod 2] U)) : Submodule (ZMod 2) U :=
  ⨅ a ∈ A, LinearMap.ker ((a : U ≃ₗ[ZMod 2] U).toLinearMap - 1)

theorem mem_fixOf {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {A : Subgroup (U ≃ₗ[ZMod 2] U)} {u : U} : u ∈ fixOf A ↔ ∀ a ∈ A, a u = u := by
  simp [fixOf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem finrank_range_add_finrank_fixOf_le {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] {A : Subgroup (U ≃ₗ[ZMod 2] U)} {a : U ≃ₗ[ZMod 2] U} (ha : a ∈ A) :
    Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) +
        Module.finrank (ZMod 2) (fixOf A) ≤ Module.finrank (ZMod 2) U := by
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hle : fixOf A ≤ LinearMap.ker (a.toLinearMap - 1) := fun u hu => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    simp [(mem_fixOf.mp hu) a ha]
  have h1 := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
  have h2 := Submodule.finrank_mono hle
  omega

omit [Fintype F] in
theorem descendAut_conj (t : SL(3, F)) :
    descendAut 3 F (MulAut.conj t) = MulAut.conj (proj 3 F t) := by
  ext q
  obtain ⟨x, rfl⟩ := proj_surjective 3 F q
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem pow_eq_self_of_sq {G : Type*} [Group G] {p : G} (hp : p * p = 1) {k : ℕ} (hk : Odd k) :
    p ^ k = p := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, sq, hp, one_pow, one_mul]

theorem self_dual_full_normalizer_no_offender (h6 : SelfDualInvolutionRank) {f : ℕ} (hf : 2 ≤ f)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ f)
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
    (hirr : ρ.IsIrreducible) (hsd : Nonempty (ρ.Equiv ρ.dual))
    (A : Subgroup (U ≃ₗ[ZMod 2] U)) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    Nat.card A * Nat.card {u : U // ∀ a ∈ A, a u = u} < Nat.card U := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hNat
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hfinGL : Finite (U ≃ₗ[ZMod 2] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod 2] U => (e : U → U)) (fun a b h => LinearEquiv.ext
      (congrFun h))
  have hρnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hA2' : ∀ a : A, a * a = 1 := fun a => Subtype.ext (hA2 a a.2)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative A).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAcard : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    have h1 := natCard_eq_two_pow_finrank (Additive A)
    rwa [Nat.card_congr (Additive.toMul : Additive A ≃ A)] at h1
  set m := Module.finrank (ZMod 2) (Additive A) with hm
  let Φ : A →* MulAut (projectiveSL 3 F) := normalizerHom ρ hker A hA
  have hΦind := exists_induced ρ hker A hA
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro a ha1
    have hb := intertwines_psi ρ (Φ a) 1 (by rw [map_one, ha1]) (a : U ≃ₗ[ZMod 2] U) (hΦind a)
    refine Subtype.ext (eq_one_of_commutes_sq_one ρ hirr (a : U ≃ₗ[ZMod 2] U) ?_ (hA2 a a.2))
    intro x u
    simpa using hb x u
  have hΦel : CFSG.IsElementaryAbelian 2 Φ.range := by
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show Φ a * Φ b = Φ b * Φ a
      rw [← map_mul, ← map_mul]
      exact congrArg Φ (Subtype.ext (hAc a a.2 b b.2))
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      show Φ a ^ 2 = 1
      rw [← map_pow, pow_two, hA2' a, map_one]
  have hcardimg : Nat.card Φ.range = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective Φ hΦinj)).symm
  obtain ⟨-, -, hD3, hD4⟩ := elementary_automorphism_rank_bound hf hNat Φ.range
  have hm2 : m ≤ 2 * f + 2 := by
    have : 2 ^ m ≤ 2 ^ (2 * f + 2) := by rw [← hAcard, ← hcardimg]; exact hD3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hkey : ∃ a ∈ A, m < Module.finrank (ZMod 2)
      (LinearMap.range ((a : U ≃ₗ[ZMod 2] U).toLinearMap - 1)) := by
    by_cases hcase : Φ.range ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range
        = ⊥
    ·
      have hm4 : m ≤ 2 := by
        have : 2 ^ m ≤ 2 ^ 2 := by rw [← hAcard, ← hcardimg]; exact hD4 hcase
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
      have hα1 : Φ b ≠ 1 := fun h => hb1 (hΦinj (by rw [h, map_one]))
      have hα2 : Φ b * Φ b = 1 := by
        rw [← map_mul, hA2' b, map_one]
      have hout : Φ b ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
        intro hin
        have : Φ b ∈ Φ.range ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
          ⟨⟨b, rfl⟩, hin⟩
        rw [hcase] at this
        exact hα1 (Subgroup.mem_bot.mp this)
      obtain ⟨ψ, g, t, -, hψ, ht, hgt⟩ := outer_involution_transvection_commutator hf hNat (Φ b)
        hα2 hout
      obtain ⟨-, -, hrk⟩ := commutator_rank_bound ρ (Φ b) ψ hψ (b : U ≃ₗ[ZMod 2] U) (hΦind b) g t
        hgt
      have h4f := h6 f F hF (by omega) U ρ hirr hρnt hsd t (ne_one_of_isTransvection ht)
        (isTransvection_sq ht)
      refine ⟨b, b.2, ?_⟩
      omega
    ·
      obtain ⟨x, ⟨⟨a, rfl⟩, ⟨p, hp⟩⟩, hx1⟩ : ∃ x, x ∈ Φ.range ⊓
          (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ∧ x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hcase ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => hcon x hx)
      have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have hp1 : p ≠ 1 := fun h => hx1 (by rw [← hp, h, map_one])
      have hpp : p * p = 1 := by
        have h1 : MulAut.conj (p * p) = (1 : MulAut (projectiveSL 3 F)) := by
          rw [map_mul, hp, ← map_mul, hA2' a, map_one]
        exact conj_injective_projectiveSL (h1.trans (map_one _).symm)
      obtain ⟨y, rfl⟩ := proj_surjective 3 F p
      have hy2 : y * y ∈ scalars 3 F := by
        rw [← proj_eq_one_iff, map_mul]
        exact hpp
      have hkodd : Odd (Nat.card (scalars 3 F)) := by
        have hdvd := card_scalars_dvd (K := F) (n := 3) (by norm_num)
        have hodd : Odd (Nat.card F - 1) := by
          rw [hNat]
          have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
          have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
          rw [Nat.odd_iff]
          omega
        exact Odd.of_dvd_nat hodd hdvd
      set k := Nat.card (scalars 3 F) with hk
      have htsq : y ^ k * y ^ k = 1 := by
        have h1 : y ^ k * y ^ k = (y * y) ^ k := by
          rw [← pow_add, ← two_mul, pow_mul, sq]
        rw [h1]
        have h2 : (⟨y * y, hy2⟩ : scalars 3 F) ^ k = 1 := pow_card_eq_one'
        have h3 := congrArg Subtype.val h2
        simpa using h3
      have hproj : proj 3 F (y ^ k) = proj 3 F y := by
        rw [map_pow]
        exact pow_eq_self_of_sq hpp hkodd
      have ht1 : y ^ k ≠ 1 := fun h => hp1 (by rw [← hproj, h, map_one])
      have hdesc : descendAut 3 F (MulAut.conj (y ^ k)) = Φ a := by
        rw [descendAut_conj, hproj, hp]
      have hb := intertwines_psi ρ (Φ a) (MulAut.conj (y ^ k)) hdesc (a : U ≃ₗ[ZMod 2] U)
        (hΦind a)
      set t := y ^ k with ht
      have hcomm : ∀ x' u, (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) (ρ x' u) =
          ρ x' ((repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) u) := by
        intro x' u
        show ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) (ρ x' u)) = ρ x' (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u))
        rw [hb x' u, MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
          ← map_mul]
        congr 2
        group
      have hsq : (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) *
          (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) = 1 := by
        refine LinearEquiv.ext fun u => ?_
        show ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u))) = u
        have h1 := hb t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u)
        have haa : (a : U ≃ₗ[ZMod 2] U) ((a : U ≃ₗ[ZMod 2] U) u) = u := by
          have := LinearEquiv.congr_fun (hA2 a a.2) u
          simpa using this
        rw [h1, haa, MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul]
        have h3 : t⁻¹ * (t * t⁻¹ * t⁻¹) = 1 := by
          calc t⁻¹ * (t * t⁻¹ * t⁻¹) = (t * t)⁻¹ := by group
            _ = 1 := by rw [htsq, inv_one]
        rw [h3, map_one]
        rfl
      have hc1 := eq_one_of_commutes_sq_one ρ hirr _ hcomm hsq
      have hat : ∀ u, (a : U ≃ₗ[ZMod 2] U) u = ρ t u := by
        intro u
        have := LinearEquiv.congr_fun hc1 u
        have h2 : ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u) = u := this
        calc (a : U ≃ₗ[ZMod 2] U) u = ρ t (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u)) := by
              rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
          _ = ρ t u := by rw [h2]
      have hrank : (a : U ≃ₗ[ZMod 2] U).toLinearMap - 1 = ρ t - 1 := by
        refine LinearMap.ext fun u => ?_
        simp [hat u]
      have h4f := h6 f F hF (by omega) U ρ hirr hρnt hsd t ht1 htsq
      refine ⟨a, a.2, ?_⟩
      rw [hrank]
      omega
  obtain ⟨a, haA, ha⟩ := hkey
  have hfix := finrank_range_add_finrank_fixOf_le (A := A) haA
  have hcard1 : Nat.card {u : U // ∀ a ∈ A, a u = u} = 2 ^ Module.finrank (ZMod 2) (fixOf A) := by
    rw [← natCard_eq_two_pow_finrank]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => mem_fixOf.symm)
  rw [hAcard, hcard1, natCard_eq_two_pow_finrank U, ← pow_add]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end Main


end CFSG.QuasithinUnique.Setup.X7a
