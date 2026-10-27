module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Linear
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Module Polynomial

structure TorusData (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] where
  f : ℕ
  one_le : 1 ≤ f
  card_K : Nat.card K = 2 ^ f
  τ : Module.End (ZMod 2) M
  τ_mul_self : τ * τ = 1
  ι : (Fin 2 → K) →+ M
  ι_injective : Function.Injective ι
  τ_ι : ∀ v, τ (ι v) = ι v
  exists_ι : ∀ m, τ m = m → ∃ v, ι v = m
  h₀ : Module.End (ZMod 2) M
  c : K
  h₀_τ : h₀ * τ = τ * h₀
  h₀_ι : ∀ v, h₀ (ι v) = ι (c • v)
  c_ne_zero : c ≠ 0
  h₀_pow : h₀ ^ (Nat.card K - 1) = 1

namespace TorusData

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  (S : TorusData K M)

theorem add_self (m : M) : m + m = 0 := by
  rw [← two_smul (ZMod 2) m, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem τ_τ (m : M) : S.τ (S.τ m) = m := by
  rw [← Module.End.mul_apply, S.τ_mul_self, Module.End.one_apply]

theorem τ_sub_mem (m : M) : S.τ (S.τ m - m) = S.τ m - m := by
  rw [map_sub, S.τ_τ, ← neg_sub]
  exact neg_eq_of_add_eq_zero_right (add_self _)

theorem h₀_τ_apply (m : M) : S.h₀ (S.τ m) = S.τ (S.h₀ m) := by
  rw [← Module.End.mul_apply, S.h₀_τ, Module.End.mul_apply]

theorem aeval_h₀_τ (P : (ZMod 2)[X]) (m : M) : aeval S.h₀ P (S.τ m) = S.τ (aeval S.h₀ P m) := by
  induction P using Polynomial.induction_on generalizing m with
  | C a => rw [aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hP, hQ, map_add]
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval S.h₀) (C a * X ^ k) X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, S.h₀_τ_apply, h]

theorem aeval_h₀_ι [Algebra (ZMod 2) K] (P : (ZMod 2)[X]) (v : Fin 2 → K) :
    aeval S.h₀ P (S.ι v) = S.ι (aeval S.c P • v) := by
  induction P using Polynomial.induction_on generalizing v with
  | C a =>
    rw [aeval_C, aeval_C, Module.algebraMap_end_apply]
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
    · simp
    · simp
  | add P Q hP hQ => rw [map_add, map_add, LinearMap.add_apply, hP, hQ, add_smul, map_add]
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval S.h₀) (C a * X ^ k) X,
      map_mul (aeval S.c) (C a * X ^ k) X, Module.End.mul_apply, aeval_X, aeval_X,
      S.h₀_ι, h, smul_smul]

theorem aeval_minpoly_eq_zero [Algebra (ZMod 2) K] [Finite K] [Finite M] :
    aeval S.h₀ (minpoly (ZMod 2) S.c) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set n := Nat.card K - 1 with hn
  have hcn : S.c ^ n = 1 := by
    rw [hn, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one S.c S.c_ne_zero
  obtain ⟨r, hr⟩ : minpoly (ZMod 2) S.c ∣ X ^ n - 1 :=
    minpoly.dvd (ZMod 2) S.c (by simp [hcn])
  have hnodd : (n : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff_even, hn, S.card_K, Nat.even_iff]
    have h1 : 1 ≤ 2 ^ (S.f - 1) := Nat.one_le_two_pow
    have h2 : 2 ^ S.f = 2 * 2 ^ (S.f - 1) := by
      rw [← pow_succ']
      congr 1
      have := S.one_le
      omega
    omega
  have hsep : (X ^ n - C (1 : ZMod 2)).Separable := separable_X_pow_sub_C 1 hnodd one_ne_zero
  have hrc : aeval S.c r ≠ 0 := by
    intro h0
    obtain ⟨s, hs⟩ := minpoly.dvd (ZMod 2) S.c h0
    have hsq : minpoly (ZMod 2) S.c * minpoly (ZMod 2) S.c ∣ X ^ n - C (1 : ZMod 2) :=
      ⟨s, by rw [map_one, hr, hs]; ring⟩
    exact minpoly.not_isUnit (ZMod 2) S.c (hsep.squarefree _ hsq)
  have hinj : Function.Injective (aeval S.h₀ r) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have key : ∀ x : M, S.τ x = x → aeval S.h₀ r x = 0 → x = 0 := by
      intro x hx hx0
      obtain ⟨v, rfl⟩ := S.exists_ι x hx
      rw [S.aeval_h₀_ι] at hx0
      have hv : aeval S.c r • v = 0 := S.ι_injective (by rw [hx0, map_zero])
      rw [smul_eq_zero] at hv
      rw [hv.resolve_left hrc, map_zero]
    have h1 : S.τ m - m = 0 := key _ (S.τ_sub_mem m) (by
      rw [map_sub, S.aeval_h₀_τ, hm, map_zero, sub_zero])
    exact key m (sub_eq_zero.mp h1) hm
  have hsurj : Function.Surjective (aeval S.h₀ r) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hQ : aeval S.h₀ (minpoly (ZMod 2) S.c) * aeval S.h₀ r = 0 := by
    rw [← map_mul, ← hr, map_sub, map_pow, aeval_X, map_one, hn, S.h₀_pow, sub_self]
  ext m
  obtain ⟨m', rfl⟩ := hsurj m
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m') hQ
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using this

theorem false_of_mul_eq_pow_mul [Algebra (ZMod 2) K] [Finite K] [Finite M]
    (hgen : Nat.card (IntermediateField.adjoin (ZMod 2) {S.c}) = Nat.card K)
    (hM : Nat.card M = Nat.card K ^ 4) {r : ℕ} (hr : r.Prime) (a : ℕ)
    (h1 : ¬ r ∣ Nat.card K - 1) (h2 : ¬ r ∣ Nat.card K ^ 2 - 1) (h3 : r ∣ Nat.card K ^ 3 - 1)
    {s m : Module.End (ZMod 2) M} (hs : s ^ r ^ a = 1) (hs1 : s ≠ 1)
    (hm : Function.Surjective m) (hms : m * s = s ^ (r ^ a - 1) * m)
    (hsh : s * S.h₀ = S.h₀ * s) (hmh : m * S.h₀ = S.h₀ * m) : False := by
  classical
  have hint : IsIntegral (ZMod 2) S.c := .of_finite (ZMod 2) S.c
  set F := IntermediateField.adjoin (ZMod 2) {S.c} with hF
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have : Finite F := Finite.of_injective _ Subtype.val_injective
  set pb := IntermediateField.adjoin.powerBasis hint with hpb
  have hp : aeval S.h₀ (minpoly (ZMod 2) pb.gen) = 0 := by
    rw [hpb, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact S.aeval_minpoly_eq_zero
  set κ := pb.lift S.h₀ hp with hκ
  have hcomm : ∀ {g : Module.End (ZMod 2) M}, g * S.h₀ = S.h₀ * g → ∀ x : F,
      g * κ x = κ x * g := by
    intro g hg x
    obtain ⟨P, rfl⟩ := pb.exists_eq_aeval' x
    rw [hκ, PowerBasis.lift_aeval]
    exact mul_aeval_of_mul_eq hg P
  let : Module F M := Module.compHom M κ.toRingHom
  have hsmul : ∀ (x : F) (v : M), x • v = κ x v := fun x v => rfl
  let lin : ∀ g : Module.End (ZMod 2) M, g * S.h₀ = S.h₀ * g → Module.End F M :=
    fun g hg =>
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun x v => by
          rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply, hcomm hg x,
            Module.End.mul_apply] }
  have hlin : ∀ (g : Module.End (ZMod 2) M) (hg : g * S.h₀ = S.h₀ * g) (v : M),
      lin g hg v = g v := fun _ _ _ => rfl
  have hlinpow : ∀ (g : Module.End (ZMod 2) M) (hg : g * S.h₀ = S.h₀ * g) (k : ℕ) (v : M),
      (lin g hg ^ k) v = (g ^ k) v := by
    intro g hg k v
    rw [Module.End.pow_apply, Module.End.pow_apply]
    rfl
  have : Module.Finite F M := Module.Finite.of_finite
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdim : Module.finrank F M = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := M)
    rw [hM, hgen] at h
    exact (Nat.pow_right_injective hK2 h).symm
  refine CFSG.LocalAnalysis.EvenBN.LinearThree.false_of_mul_eq_pow_mul (F := F) (W := M)
    hdim.le hr a (hgen ▸ h1) (hgen ▸ h2) (hgen ▸ h3) (s := lin s hsh) (m := lin m hmh) ?_ ?_
    hm ?_
  · ext v
    rw [hlinpow s hsh, hs, Module.End.one_apply, Module.End.one_apply]
  · intro h1'
    apply hs1
    ext v
    have := congrArg (fun φ : Module.End F M => φ v) h1'
    simpa [hlin s hsh] using this
  · ext v
    rw [Module.End.mul_apply, Module.End.mul_apply, hlin m hmh, hlin s hsh, hlinpow s hsh,
      hlin m hmh, ← Module.End.mul_apply, hms, Module.End.mul_apply]

theorem card_dvd_card_GL [Algebra (ZMod 2) K] [Finite K] [Finite M]
    (hgen : Nat.card (IntermediateField.adjoin (ZMod 2) {S.c}) = Nat.card K)
    (hM : Nat.card M = Nat.card K ^ 4) (X : Subgroup (Module.End (ZMod 2) M)ˣ)
    (hX : ∀ x ∈ X, (x : Module.End (ZMod 2) M) * S.h₀ = S.h₀ * x) :
    Nat.card X ∣ ∏ i : Fin 4, (Nat.card K ^ 4 - Nat.card K ^ (i : ℕ)) := by
  classical
  have hint : IsIntegral (ZMod 2) S.c := .of_finite (ZMod 2) S.c
  set F := IntermediateField.adjoin (ZMod 2) {S.c} with hF
  have : Finite F := Finite.of_injective _ Subtype.val_injective
  have : Fintype F := Fintype.ofFinite F
  set pb := IntermediateField.adjoin.powerBasis hint with hpb
  have hp : aeval S.h₀ (minpoly (ZMod 2) pb.gen) = 0 := by
    rw [hpb, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact S.aeval_minpoly_eq_zero
  set κ := pb.lift S.h₀ hp with hκ
  have hcomm : ∀ {g : Module.End (ZMod 2) M}, g * S.h₀ = S.h₀ * g → ∀ x : F,
      g * κ x = κ x * g := by
    intro g hg x
    obtain ⟨P, rfl⟩ := pb.exists_eq_aeval' x
    rw [hκ, PowerBasis.lift_aeval]
    exact mul_aeval_of_mul_eq hg P
  let : Module F M := Module.compHom M κ.toRingHom
  have hsmul : ∀ (x : F) (v : M), x • v = κ x v := fun x v => rfl
  let lin : ∀ g : Module.End (ZMod 2) M, g * S.h₀ = S.h₀ * g → Module.End F M :=
    fun g hg =>
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun x v => by
          rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply, hcomm hg x,
            Module.End.mul_apply] }
  have : Module.Finite F M := Module.Finite.of_finite
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdim : Module.finrank F M = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := M)
    rw [hM, hgen] at h
    exact (Nat.pow_right_injective hK2 h).symm
  let ρ : X →* Module.End F M :=
    { toFun := fun x => lin ((x : (Module.End (ZMod 2) M)ˣ) : Module.End (ZMod 2) M)
        (hX (x : (Module.End (ZMod 2) M)ˣ) x.2)
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hρ : ∀ (x : X) (v : M),
      ρ x v = ((x : (Module.End (ZMod 2) M)ˣ) : Module.End (ZMod 2) M) v := fun _ _ => rfl
  let b := Module.finBasisOfFinrankEq F M hdim
  let τ : (Module.End F M)ˣ →* GL (Fin 4) F :=
    Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  have hτ : Function.Injective τ :=
    Units.map_injective (LinearMap.toMatrixAlgEquiv b).toRingEquiv.injective
  have hρu : Function.Injective ρ.toHomUnits := by
    intro x y hxy
    have h1 : ρ x = ρ y := congrArg Units.val hxy
    apply Subtype.ext
    apply Units.ext
    ext v
    have h2 := congrArg (fun φ : Module.End F M => φ v) h1
    simpa only [hρ] using h2
  have hinj : Function.Injective (τ.comp ρ.toHomUnits) := hτ.comp hρu
  have hcard : Nat.card X = Nat.card (τ.comp ρ.toHomUnits).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  refine (Subgroup.card_subgroup_dvd_card _).trans ?_
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hgen]

end TorusData

theorem card_adjoin_cube_eq {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K] {f : ℕ}
    (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f) {l : Kˣ} (hl : orderOf l = Nat.card K - 1) :
    Nat.card (IntermediateField.adjoin (ZMod 2) {((l : K) ^ 3)}) = Nat.card K := by
  classical
  set c : K := (l : K) ^ 3 with hc
  set F := IntermediateField.adjoin (ZMod 2) {c} with hF
  have : Finite F := Finite.of_injective _ Subtype.val_injective
  have : Fintype F := Fintype.ofFinite F
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have : Module.Finite F K := Module.Finite.of_finite
  have hKf : finrank (ZMod 2) K = f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  set d := finrank (ZMod 2) F with hd
  have hdf : d ∣ f := ⟨finrank F K, by rw [← hKf, Module.finrank_mul_finrank (ZMod 2) F K]⟩
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hFc : Nat.card F = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod]
  have hcF : c ∈ F := IntermediateField.mem_adjoin_simple_self _ _
  have hc0 : (⟨c, hcF⟩ : F) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact pow_ne_zero 3 l.ne_zero this
  have hcd : c ^ (2 ^ d - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (⟨c, hcF⟩ : F) hc0
    rw [Fintype.card_eq_nat_card, hFc] at h
    exact congrArg Subtype.val h
  have hq1 : 1 ≤ Nat.card K - 1 := by rw [hK]; have := Nat.one_lt_two_pow (n := f) (by omega); omega
  have hord : orderOf (l ^ 3) * Nat.gcd (Nat.card K - 1) 3 = Nat.card K - 1 := by
    rw [orderOf_pow' l (by norm_num), hl]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hcu : (l ^ 3) ^ (2 ^ d - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_one, ← hc]
    exact hcd
  have hdvd : orderOf (l ^ 3) ∣ 2 ^ d - 1 := orderOf_dvd_of_pow_eq_one hcu
  have hd2 : 1 ≤ 2 ^ d - 1 := by have := Nat.one_lt_two_pow (n := d) (by omega); omega
  have hle : orderOf (l ^ 3) ≤ 2 ^ d - 1 := Nat.le_of_dvd (by omega) hdvd
  have hg : Nat.gcd (Nat.card K - 1) 3 ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
  have hq : Nat.card K - 1 ≤ 3 * (2 ^ d - 1) := by
    rw [← hord]
    calc orderOf (l ^ 3) * Nat.gcd (Nat.card K - 1) 3 ≤ (2 ^ d - 1) * 3 :=
          Nat.mul_le_mul hle hg
      _ = 3 * (2 ^ d - 1) := mul_comm _ _
  have hdeq : d = f := by
    by_contra hne
    obtain ⟨k, hk⟩ := hdf
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have hx : (2 ^ d) ^ 2 ≤ 2 ^ f := by
      rw [hk, pow_mul]
      exact Nat.pow_le_pow_right (by positivity) hk2
    set x := 2 ^ d with hxd
    have hx2 : 2 ≤ x := by
      rw [hxd]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [hK] at hq
    have hx3 : x ≤ 2 := by
      by_contra h3
      push Not at h3
      have hQ : 2 ^ f + 2 ≤ 3 * x := by omega
      have hxx : 3 * x ≤ x * x := Nat.mul_le_mul_right x (by omega)
      rw [sq] at hx
      linarith
    have : x = 2 := by omega
    rw [this] at hq
    omega
  rw [hFc, hdeq, hK]

end CFSG.LocalAnalysis.EvenBN.LinearThree
