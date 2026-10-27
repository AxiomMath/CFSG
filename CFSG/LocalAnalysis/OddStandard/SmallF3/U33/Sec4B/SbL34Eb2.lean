module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eb
public import Mathlib.Data.Finite.Perm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

private lemma two_pow_modEq_one_cases {k : ℕ} (h3 : 3 ≤ k) (h6 : k ≤ 6)
    (hmod : 2 ^ k ≡ 1 [MOD 7]) : k = 3 ∨ k = 6 := by
  interval_cases k
  · exact Or.inl rfl
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exact Or.inr rfl

theorem false_of_involution_commutes_seven_sq (hE : Module.finrank (ZMod 2) E = 6)
    (R : Subgroup (E ≃ₗ[ZMod 2] E)) (hR : Nat.card R = 49)
    (hord : ∀ g ∈ R, g ≠ 1 → orderOf g = 7) {a : E ≃ₗ[ZMod 2] E} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hcomm : ∀ g ∈ R, a * g = g * a) : False := by
  set A : Module.End (ZMod 2) E := (a : Module.End (ZMod 2) E) - 1 with hA
  let K : Submodule (ZMod 2) E := LinearMap.ker A
  have ha2' : (a : Module.End (ZMod 2) E) * (a : Module.End (ZMod 2) E) = 1 := by
    rw [← LinearEquiv.coe_toLinearMap_mul, ha2, LinearEquiv.coe_toLinearMap_one,
      Module.End.one_eq_id]
  have hAA : A * A = 0 := by
    rw [hA]
    ext x
    have haa : (a : Module.End (ZMod 2) E) ((a : Module.End (ZMod 2) E) x) = x := by
      have h := congrArg (fun f : Module.End (ZMod 2) E => f x) ha2'
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, map_sub, haa]
    rw [sub_eq_zero, sub_eq_sub_iff_add_eq_add, ZModModule.add_self, ZModModule.add_self]
  have hAA_apply : ∀ e : E, A (A e) = 0 := by
    intro e
    have h := congrArg (fun f : Module.End (ZMod 2) E => f e) hAA
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h
  have hAcomp : A.comp A = 0 := by
    rw [← Module.End.mul_eq_comp]
    exact hAA
  have hmemA : ∀ e : E, A e ∈ K := fun e => LinearMap.mem_ker.mpr (hAA_apply e)
  have hK_ge : 3 ≤ Module.finrank (ZMod 2) ↥K := by
    change 3 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker A)
    have hrn := LinearMap.finrank_range_add_finrank_ker A
    rw [hE] at hrn
    have hle : Module.finrank (ZMod 2) (LinearMap.range A) ≤
        Module.finrank (ZMod 2) (LinearMap.ker A) :=
      Submodule.finrank_mono (LinearMap.range_le_ker_iff.mpr hAcomp)
    omega
  have hK_le : Module.finrank (ZMod 2) ↥K ≤ 6 := by
    change Module.finrank (ZMod 2) ↥(LinearMap.ker A) ≤ 6
    have h := Submodule.finrank_le (R := ZMod 2) (M := E) (LinearMap.ker A)
    rw [hE] at h
    exact h
  have hA_comm : ∀ (g : E ≃ₗ[ZMod 2] E), a * g = g * a → ∀ e : E, A (g e) = g (A e) := by
    intro g hg e
    rw [hA]
    have hc : (a : Module.End (ZMod 2) E) (g e) = g ((a : Module.End (ZMod 2) E) e) := by
      have h1 : (a : Module.End (ZMod 2) E) * (g : Module.End (ZMod 2) E) =
          (g : Module.End (ZMod 2) E) * (a : Module.End (ZMod 2) E) := by
        have h := congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : Module.End (ZMod 2) E)) hg
        simpa only [LinearEquiv.coe_toLinearMap_mul] using h
      have h2 := congrArg (fun f : Module.End (ZMod 2) E => f e) h1
      simpa only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap] using h2
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [hc]
  letI : MulAction ↥R ↥K :=
    { smul := fun g k => ⟨(g : E ≃ₗ[ZMod 2] E) k.1, by
        show (g : E ≃ₗ[ZMod 2] E) k.1 ∈ LinearMap.ker A
        refine LinearMap.mem_ker.mpr ?_
        have hk : A k.1 = 0 := LinearMap.mem_ker.mp k.2
        rw [hA_comm (g : E ≃ₗ[ZMod 2] E)
          (hcomm (g : E ≃ₗ[ZMod 2] E) g.2) k.1, hk, map_zero]⟩
      one_smul := fun k => Subtype.ext (by
        change ((1 : ↥R) : E ≃ₗ[ZMod 2] E) k.1 = k.1
        rw [Subgroup.coe_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply])
      mul_smul := fun g hh k => Subtype.ext (by
        change ((g * hh : ↥R) : E ≃ₗ[ZMod 2] E) k.1 =
          (g : E ≃ₗ[ZMod 2] E) ((hh : E ≃ₗ[ZMod 2] E) k.1)
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply]) }
  haveI : Finite ↥K := Module.finite_of_finite (R := ZMod 2) (M := ↥K)
  have hfixed_subsingleton : Subsingleton (MulAction.fixedPoints ↥R ↥K) := by
    constructor
    intro x y
    have hx : (x : ↥K).1 = 0 := by
      apply eq_zero_of_fixed_seven_sq hE R hR hord
      intro g hg
      have h := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp x.2) ⟨g, hg⟩)
      change g (x : ↥K).1 = (x : ↥K).1 at h
      exact h
    have hy : (y : ↥K).1 = 0 := by
      apply eq_zero_of_fixed_seven_sq hE R hR hord
      intro g hg
      have h := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp y.2) ⟨g, hg⟩)
      change g (y : ↥K).1 = (y : ↥K).1 at h
      exact h
    exact Subtype.ext (Subtype.ext (by rw [hx, hy]))
  have hfixed_nonempty : Nonempty (MulAction.fixedPoints ↥R ↥K) := by
    refine ⟨⟨0, ?_⟩⟩
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by
      change (g : E ≃ₗ[ZMod 2] E) (0 : E) = (0 : E)
      simp)
  have hfixed_card : Nat.card (MulAction.fixedPoints ↥R ↥K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hfixed_subsingleton, hfixed_nonempty⟩
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hIsP : IsPGroup 7 ↥R :=
    IsPGroup.of_card (p := 7) (n := 2) (by rw [hR]; norm_num)
  have hmodK : Nat.card ↥K ≡ 1 [MOD 7] := by
    have h := hIsP.card_modEq_card_fixedPoints (↥K)
    rwa [hfixed_card] at h
  have hcardK : Nat.card ↥K = 2 ^ Module.finrank (ZMod 2) ↥K := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥K), Nat.card_zmod]
  have hmod2 : 2 ^ Module.finrank (ZMod 2) ↥K ≡ 1 [MOD 7] := by
    rw [← hcardK]
    exact hmodK
  have hk36 := two_pow_modEq_one_cases hK_ge hK_le hmod2
  have hk_eq3 : Module.finrank (ZMod 2) ↥K = 3 := by
    rcases hk36 with h3 | h6
    · exact h3
    · exfalso
      have hKtop : K = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [h6, hE]
      have hA0 : A = 0 := by
        rw [← LinearMap.ker_eq_top]
        exact hKtop
      have hcoeeq : (a : Module.End (ZMod 2) E) = 1 := by
        have h := hA0
        rw [hA] at h
        exact sub_eq_zero.mp h
      have haeq : a = 1 := by
        ext x
        have h := congrArg (fun f : Module.End (ZMod 2) E => f x) hcoeeq
        simpa using h
      exact ha1 haeq
  have hcardK8 : Nat.card ↥K = 8 := by
    rw [hcardK, hk_eq3]
    norm_num
  let φ : ↥R →* Equiv.Perm ↥K := MulAction.toPermHom ↥R ↥K
  have hperm8 : Nat.card (Equiv.Perm ↥K) = 40320 := by
    rw [Nat.card_perm, hcardK8]
    decide
  have hrange_dvd49 : Nat.card φ.range ∣ 49 := by
    rw [← hR]
    exact Subgroup.card_range_dvd φ
  have hrange_dvd_perm : Nat.card φ.range ∣ Nat.card (Equiv.Perm ↥K) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have hrange_dvd7 : Nat.card φ.range ∣ 7 := by
    have h : Nat.card φ.range ∣ Nat.gcd 49 (Nat.card (Equiv.Perm ↥K)) :=
      Nat.dvd_gcd hrange_dvd49 hrange_dvd_perm
    rw [hperm8, show Nat.gcd 49 40320 = 7 by norm_num] at h
    exact h
  have hrange_le7 : Nat.card φ.range ≤ 7 := Nat.le_of_dvd (by norm_num) hrange_dvd7
  have hker_ne_bot : φ.ker ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card φ.ker = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h49 : Nat.card φ.range = 49 := by
      have hcard := Subgroup.card_ker_mul_card_range φ
      rw [hR, hcard1, one_mul] at hcard
      exact hcard
    omega
  obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker_ne_bot
  let h : ↥R := u.1
  have hu1_ne : u.1 ≠ 1 := fun hh => hu_ne (Subtype.ext hh)
  have hh_ne : h ≠ 1 := hu1_ne
  have hphi : φ h = 1 := MonoidHom.mem_ker.mp u.2
  have hfix : ∀ kk : ↥K, h • kk = kk := by
    intro kk
    have hthis := congrArg (fun p : Equiv.Perm ↥K => p kk) hphi
    change h • kk = kk at hthis
    exact hthis
  have hAe_fix : ∀ e : E, (h : E ≃ₗ[ZMod 2] E) (A e) = A e := by
    intro e
    have hthis := congrArg Subtype.val (hfix ⟨A e, hmemA e⟩)
    change (h : E ≃ₗ[ZMod 2] E) (A e) = A e at hthis
    exact hthis
  have hA_sub : ∀ e : E, A ((h : E ≃ₗ[ZMod 2] E) e - e) = 0 := by
    intro e
    rw [map_sub, hA_comm (h : E ≃ₗ[ZMod 2] E)
      (hcomm (h : E ≃ₗ[ZMod 2] E) h.2) e, hAe_fix e, sub_self]
  have hsq : ∀ e : E, (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e) = e := by
    intro e
    have hmem2 : (h : E ≃ₗ[ZMod 2] E) e - e ∈ K :=
      LinearMap.mem_ker.mpr (hA_sub e)
    have hfix2 : (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e - e) =
        (h : E ≃ₗ[ZMod 2] E) e - e := by
      have hthis := congrArg Subtype.val (hfix ⟨(h : E ≃ₗ[ZMod 2] E) e - e, hmem2⟩)
      change (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e - e) =
        (h : E ≃ₗ[ZMod 2] E) e - e at hthis
      exact hthis
    have hsum : (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e) + e = 0 := by
      have h' : (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e) + e =
          (h : E ≃ₗ[ZMod 2] E) e + (h : E ≃ₗ[ZMod 2] E) e :=
        sub_eq_sub_iff_add_eq_add.mp (by simpa [map_sub] using hfix2)
      rwa [ZModModule.add_self] at h'
    have h1 : (h : E ≃ₗ[ZMod 2] E) ((h : E ≃ₗ[ZMod 2] E) e) = -e :=
      add_eq_zero_iff_eq_neg.mp hsum
    rwa [ZModModule.neg_eq_self] at h1
  have hh2 : (h : E ≃ₗ[ZMod 2] E) * (h : E ≃ₗ[ZMod 2] E) = 1 := by
    ext e
    rw [LinearEquiv.mul_apply, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
    exact hsq e
  have hord7 : orderOf (h : E ≃ₗ[ZMod 2] E) = 7 :=
    hord (h : E ≃ₗ[ZMod 2] E) h.2 (fun hh => hh_ne (Subtype.ext hh))
  have hdvd : orderOf (h : E ≃ₗ[ZMod 2] E) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hh2)
  rw [hord7] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
