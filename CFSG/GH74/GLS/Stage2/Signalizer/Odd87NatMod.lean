module

public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

namespace NatMod

section Lift

variable {Ĝ K : Type} [Group Ĝ] [Group K] {r : ℕ}

theorem exists_lift_isPGroup [Finite Ĝ] [Fact r.Prime] (π : Ĝ →* K) (hπ : Function.Surjective π)
    {X : Subgroup K} (hX : IsPGroup r ↥X) :
    ∃ P : Subgroup Ĝ, IsPGroup r ↥P ∧ P ≤ X.comap π ∧ ∀ x ∈ X, ∃ g ∈ P, π g = x := by
  let Y : Subgroup Ĝ := X.comap π
  let ψ : Y →* X := (π.comp Y.subtype).codRestrict X (fun y => y.2)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg⟩ := hπ x
    exact ⟨⟨g, by simp [Y, hg]⟩, Subtype.ext hg⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r Y))
  have htop : (Q : Subgroup Y).map ψ = ⊤ :=
    ((Sylow.mapSurjective hψ Q).is_maximal' (hX.to_subgroup ⊤) le_top).symm
  refine ⟨(Q : Subgroup Y).map Y.subtype, Q.isPGroup'.map Y.subtype, Subgroup.map_subtype_le _, ?_⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ (Q : Subgroup Y).map ψ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨y, hyQ, hy⟩ := Subgroup.mem_map.mp hmem
  exact ⟨y, Subgroup.mem_map_of_mem _ hyQ, congrArg Subtype.val hy⟩

theorem mem_of_pow_eq_one {π : Ĝ →* K} {X : Subgroup K} {P : Subgroup Ĝ} (hP : IsPGroup r ↥P)
    (hPX : ∀ x ∈ X, ∃ g ∈ P, π g = x) (hker : π.ker ≤ Subgroup.center Ĝ)
    (hcop : Nat.Coprime r (Nat.card π.ker)) {y : Ĝ} (hy : π y ∈ X) (n : ℕ)
    (hyn : y ^ (r ^ n) = 1) : y ∈ P := by
  obtain ⟨p, hpP, hpy⟩ := hPX _ hy
  obtain ⟨m, hm⟩ := hP ⟨p, hpP⟩
  have hpm : p ^ (r ^ m) = 1 := congrArg Subtype.val hm
  have hkker : y * p⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpy, mul_inv_cancel]
  have hkc : ∀ g : Ĝ, g * (y * p⁻¹) = (y * p⁻¹) * g := Subgroup.mem_center_iff.mp (hker hkker)
  have hcomm : Commute y p⁻¹ := by
    have h1 : y = (y * p⁻¹) * p := by rw [inv_mul_cancel_right]
    have h2 : p⁻¹ * y = y * p⁻¹ :=
      calc p⁻¹ * y = p⁻¹ * ((y * p⁻¹) * p) := by rw [← h1]
        _ = (p⁻¹ * (y * p⁻¹)) * p := (mul_assoc _ _ _).symm
        _ = ((y * p⁻¹) * p⁻¹) * p := by rw [hkc p⁻¹]
        _ = (y * p⁻¹) * (p⁻¹ * p) := mul_assoc _ _ _
        _ = y * p⁻¹ := by rw [inv_mul_cancel, mul_one]
    exact h2.symm
  have hk1 : (y * p⁻¹) ^ (r ^ (n + m)) = 1 := by
    rw [hcomm.mul_pow, inv_pow]
    have hy' : y ^ (r ^ (n + m)) = 1 := by rw [pow_add, pow_mul, hyn, one_pow]
    have hp' : p ^ (r ^ (n + m)) = 1 := by rw [add_comm, pow_add, pow_mul, hpm, one_pow]
    rw [hy', hp', inv_one, mul_one]
  have hk2 : (y * p⁻¹) ^ Nat.card π.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := π.ker) (x := ⟨y * p⁻¹, hkker⟩))
  have hk : y * p⁻¹ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hk1, hk2⟩
    rwa [(hcop.pow_left (n + m)).gcd_eq_one, pow_one] at this
  rwa [mul_inv_eq_one.mp hk]

theorem conj_mem_of_mem_normalizer {π : Ĝ →* K} {X : Subgroup K} {P : Subgroup Ĝ}
    (hP : IsPGroup r ↥P) (hPY : P ≤ X.comap π) (hPX : ∀ x ∈ X, ∃ g ∈ P, π g = x)
    (hker : π.ker ≤ Subgroup.center Ĝ) (hcop : Nat.Coprime r (Nat.card π.ker)) {c g : Ĝ}
    (hc : π c ∈ Subgroup.normalizer (X : Set K)) (hg : g ∈ P) : c * g * c⁻¹ ∈ P := by
  obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
  have hgm : g ^ (r ^ m) = 1 := congrArg Subtype.val hm
  refine mem_of_pow_eq_one hP hPX hker hcop ?_ m ?_
  · rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hc _).mp (hPY hg)
  · rw [conj_pow, hgm, mul_one, mul_inv_cancel]

end Lift

end NatMod

section Main

variable {F : Type} [Field F] {r : ℕ} [Fact r.Prime] [CharP F r] {V : Type} [AddCommGroup V]
  [Module F V] [Finite V] {Ĝ K : Type} [Group Ĝ] [Finite Ĝ] [Group K]

theorem exists_proper_invariant_subspace (ρ : Ĝ →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (π : Ĝ →* K) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Ĝ)
    (hcop : Nat.Coprime r (Nat.card π.ker)) {X : Subgroup K} (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥)
    {C : Subgroup K} (hC : C ≤ Subgroup.normalizer (X : Set K)) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ ĉ : Ĝ, π ĉ ∈ C → ∀ w ∈ W, ρ ĉ w ∈ W := by
  obtain ⟨P, hP, hPY, hPX⟩ := NatMod.exists_lift_isPGroup π hπ hX
  let W : Submodule F V :=
    { carrier := {v | ∀ g ∈ P, ρ g v = v}
      add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg] }
  have hmemW : ∀ v, v ∈ W ↔ ∀ g ∈ P, ρ g v = v := fun v => Iff.rfl
  have hinv : ∀ ĉ : Ĝ, π ĉ ∈ C → ∀ w ∈ W, ρ ĉ w ∈ W := by
    intro ĉ hĉ w hw g hg
    have hg' : ĉ⁻¹ * g * ĉ⁻¹⁻¹ ∈ P :=
      NatMod.conj_mem_of_mem_normalizer hP hPY hPX hker hcop
        (by rw [map_inv]; exact hC (C.inv_mem hĉ)) hg
    rw [inv_inv] at hg'
    calc ρ g (ρ ĉ w) = ρ (g * ĉ) w := by rw [map_mul]; rfl
      _ = ρ (ĉ * (ĉ⁻¹ * g * ĉ)) w := by rw [mul_assoc ĉ⁻¹, mul_inv_cancel_left]
      _ = ρ ĉ (ρ (ĉ⁻¹ * g * ĉ) w) := by rw [map_mul]; rfl
      _ = ρ ĉ w := by rw [hw _ hg']
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  obtain ⟨g, hgP, hgx⟩ := hPX x.1 x.2
  have hg1 : ρ g ≠ 1 := by
    intro h
    have : g = 1 := hρ (by rw [h, map_one])
    apply hx1
    apply Subtype.ext
    rw [← hgx, this, map_one]
    rfl
  obtain ⟨v, hv⟩ : ∃ v, ρ g v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hg1 (LinearEquiv.ext hcon)
  have hVnt : Nontrivial V := ⟨⟨v, ρ g v, hv.symm⟩⟩
  have hWtop : W ≠ ⊤ := by
    intro h
    exact hv ((hmemW v).mp (h ▸ Submodule.mem_top) g hgP)
  obtain ⟨w, hw0⟩ := exists_ne (0 : V)
  have hrw : r • w = 0 := by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hord : addOrderOf w = r := by
    rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp (addOrderOf_dvd_of_nsmul_eq_zero hrw) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hw0
    · exact h
  have hdvd : r ∣ Nat.card V := hord ▸ addOrderOf_dvd_natCard w
  let _ : MulAction P V := MulAction.compHom V (ρ.comp P.subtype)
  have hfix0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g => by
    show ρ g.1 0 = 0
    exact map_zero _
  obtain ⟨b, hbfix, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd hfix0
  have hbW : b ∈ W := fun g hg => hbfix ⟨g, hg⟩
  refine ⟨W, ?_, hWtop, hinv⟩
  exact (Submodule.ne_bot_iff W).mpr ⟨b, hbW, fun h => hb0 h.symm⟩

end Main

namespace NatMod

section Scalars

variable {F : Type} [Field F] {r : ℕ} [Fact r.Prime] [CharP F r] {V : Type} [AddCommGroup V]
  [Module F V] {Ĝ : Type} [Group Ĝ] [Finite Ĝ]

theorem coprime_card_of_scalars (ρ : Ĝ →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    {Z : Subgroup Ĝ} (hZ : ∀ z ∈ Z, ∃ c : F, ∀ v, ρ z v = c • v) :
    Nat.Coprime r (Nat.card Z) := by
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hdvd => ?_
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) r hdvd
  have hzr : (z : Ĝ) ^ r = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
    rfl
  have hz1 : (z : Ĝ) = 1 := by
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact hρ (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    · obtain ⟨w, hw⟩ := exists_ne (0 : V)
      obtain ⟨c, hc⟩ := hZ z z.2
      have hpow : ∀ k : ℕ, ρ ((z : Ĝ) ^ k) w = c ^ k • w := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, map_mul]
          show ρ _ (ρ _ w) = _
          rw [hc, map_smul, ih, pow_succ, mul_smul]
          exact smul_comm _ _ _
      have h1 : c ^ r = 1 := by
        by_contra hne
        have hne' : c ^ r - 1 ≠ 0 := sub_ne_zero.mpr hne
        have h2 : (c ^ r - 1) • w = 0 := by
          rw [sub_smul, one_smul, ← hpow r, hzr, map_one]
          exact sub_eq_zero.mpr rfl
        apply hw
        calc w = ((c ^ r - 1)⁻¹ * (c ^ r - 1)) • w := by rw [inv_mul_cancel₀ hne', one_smul]
          _ = 0 := by rw [mul_smul, h2, smul_zero]
      have h3 : c = 1 := by
        have : (c - 1) ^ r = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
        exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : r.Prime).ne_zero |>.mp this)
      refine hρ (LinearEquiv.ext fun v => ?_)
      rw [hc, h3, one_smul, map_one]
      rfl
  rw [OneMemClass.coe_eq_one] at hz1
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : r.Prime).one_lt.ne hz

end Scalars

end NatMod

section ProjectiveSL

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime] [CharP F r]

namespace NatMod

theorem coprime_card_ker_proj : Nat.Coprime r (Nat.card (proj n F).ker) :=
  coprime_card_of_scalars (SpecialLinearGroup.toLin' :
      SpecialLinearGroup (Fin n) F →* (Fin n → F) ≃ₗ[F] (Fin n → F))
    SpecialLinearGroup.toLin'_injective fun z hz => by
      obtain ⟨c, -, hmat⟩ := mem_scalars.mp (ker_proj n F ▸ hz : z ∈ scalars n F)
      refine ⟨(c : F), fun v => ?_⟩
      rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, hmat, Matrix.scalar_apply]
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl

end NatMod

theorem exists_proper_invariant_subspace_projectiveSL
    {X : Subgroup (projectiveSL n F)} (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥)
    {C : Subgroup (projectiveSL n F)} (hC : C ≤ Subgroup.normalizer (X : Set (projectiveSL n F))) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ A : SpecialLinearGroup (Fin n) F, proj n F A ∈ C → ∀ w ∈ W,
        (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace
    (SpecialLinearGroup.toLin' : SpecialLinearGroup (Fin n) F →* (Fin n → F) ≃ₗ[F] (Fin n → F))
    SpecialLinearGroup.toLin'_injective (proj n F) (proj_surjective n F)
    ((ker_proj n F).le.trans (scalars_le_center n F)) NatMod.coprime_card_ker_proj hX hX1 hC
  exact ⟨W, hW0, hWt, fun A hA w hw => hW A hA w hw⟩

end ProjectiveSL

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
