module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614J

open Subgroup CFSG.OrderReductions.FrattiniAutomorphisms

theorem exists_injective_gl {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a * a = 1) :
    ∃ k : ℕ, Nat.card A = 2 ^ k ∧
      ∃ κ : MulAut A →* GL (Fin k) (ZMod 2), Function.Injective κ := by
  classical
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact h2 (Additive.toMul x)
  have : Fintype (Additive A) := Fintype.ofFinite _
  have hcard : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    exact h
  refine ⟨Module.finrank (ZMod 2) (Additive A), hcard, ?_⟩
  let b : Module.Basis (Fin (Module.finrank (ZMod 2) (Additive A))) (ZMod 2) (Additive A) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let f : MulAut A →* Module.End (ZMod 2) (Additive A) :=
    { toFun := fun σ => (MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap 2
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  let β : MulAut A →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive A) :=
    (Units.map f).comp (toUnits : MulAut A ≃* (MulAut A)ˣ).toMonoidHom
  have hβ : Function.Injective β := by
    intro σ τ h
    have h' := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Additive A) =>
      (u : Module.End (ZMod 2) (Additive A))) h
    ext x
    exact LinearMap.congr_fun h' (Additive.ofMul x)
  let γ := (Matrix.GeneralLinearGroup.toLin' b).symm
  exact ⟨γ.toMonoidHom.comp β, γ.injective.comp hβ⟩

theorem not_injective_of_card_le_sixteen {Y A : Type*} [Group Y] [Finite Y] [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a * a = 1) (hA : Nat.card A ≤ 16)
    (hY : 27 ∣ Nat.card Y) (σ : Y →* MulAut A) : ¬ Function.Injective σ := by
  intro hσ
  obtain ⟨k, hk, κ, hκ⟩ := exists_injective_gl hcomm h2
  have hdvd : Nat.card Y ∣ Nat.card (GL (Fin k) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective (κ.comp σ) (hκ.comp hσ)
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [Matrix.card_GL_field, ZMod.card] at hdvd
  have h := hY.trans hdvd
  interval_cases k <;> simp [Fin.prod_univ_succ] at h

theorem mul_mul_mul_comm_of_comm {M : Type*} [Group M] (hcomm : ∀ a b : M, a * b = b * a)
    (a b c d : M) : a * b * (c * d) = a * d * (b * c) := by
  rw [mul_assoc a b, hcomm c d, ← mul_assoc b d c, hcomm b d, mul_assoc d b c, ← mul_assoc a d]

theorem lt_relIndex_centralizer {G : Type*} [Group G] [Finite G] {Y R : Subgroup G} {z : G}
    (hR : IsPGroup 2 R) (hY : IsPGroup 3 Y) (hY27 : 27 ≤ Nat.card Y)
    (hYR : Y ≤ normalizer (R : Set G)) (hzY : z ∈ Y) (hzc : z ∈ centralizer (Y : Set G))
    (hz3 : z ^ 3 = 1)
    (hcen : ∀ w ∈ Y, w ∈ centralizer (Y : Set G) → w ^ 3 = 1 → w ∈ zpowers z)
    (hzR : ∃ r ∈ R, z * r ≠ r * z) :
    16 < (centralizer (zpowers z : Set G)).relIndex R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hle
  push Not at hle
  let ρ : ↥Y →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hYR)
  have hρ : ∀ (y : ↥Y) (r : ↥R), ((ρ y r : ↥R) : G) = (y : G) * r * (y : G)⁻¹ := fun y r => rfl
  obtain ⟨-, hRc, hR2, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hR
  set Φ : Subgroup ↥R := frattini ↥R with hΦ
  set π : ↥R →* ↥R ⧸ Φ := QuotientGroup.mk' Φ with hπ
  have hcomm : ∀ a b : ↥R ⧸ Φ, a * b = b * a := fun a b => hRc.is_comm.comm a b
  let ρ' : ↥Y →* MulAut (↥R ⧸ Φ) := quotientAction Φ ρ
  have hρ' : ∀ (y : ↥Y) (r : ↥R), ρ' y (π r) = π (ρ y r) := fun y r =>
    quotientAction_apply Φ ρ y r
  set zY : ↥Y := ⟨z, hzY⟩ with hzYdef
  set ζ : MulAut (↥R ⧸ Φ) := ρ' zY with hζ
  let ε : ↥R →* ↥R ⧸ Φ :=
    { toFun := fun r => ζ (π r) * (π r)⁻¹
      map_one' := by simp
      map_mul' := fun r s => by
        simp only [map_mul, mul_inv_rev]
        exact mul_mul_mul_comm_of_comm hcomm _ _ _ _ }
  have hε : ∀ r, ε r = ζ (π r) * (π r)⁻¹ := fun r => rfl
  set A : Subgroup (↥R ⧸ Φ) := ε.range with hA
  have hsq : ∀ v : ↥R ⧸ Φ, v * v = 1 := fun v => by rw [← sq]; exact hR2 v
  have hinv : ∀ v : ↥R ⧸ Φ, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hzcomm : ∀ y : ↥Y, y * zY = zY * y := fun y =>
    Subtype.ext (mem_centralizer_iff.mp hzc y y.2)
  have hρ'ζ : ∀ (y : ↥Y) (v : ↥R ⧸ Φ), ρ' y (ζ v) = ζ (ρ' y v) := fun y v => by
    rw [hζ, ← MulAut.mul_apply, ← map_mul, hzcomm y, map_mul, MulAut.mul_apply]
  have hAinv : ∀ (y : ↥Y) (a : ↥R ⧸ Φ), a ∈ A → ρ' y a ∈ A := by
    rintro y _ ⟨r, rfl⟩
    refine ⟨ρ y r, ?_⟩
    show ε (ρ y r) = ρ' y (ε r)
    rw [hε, hε, map_mul, map_inv, hρ'ζ, hρ' y r]
  let σ : ↥Y →* MulAut ↥A :=
    { toFun := fun y =>
        { toFun := fun a => ⟨ρ' y a, hAinv y a a.2⟩
          invFun := fun a => ⟨ρ' y⁻¹ a, hAinv y⁻¹ a a.2⟩
          left_inv := fun a => Subtype.ext (by
            show ρ' y⁻¹ (ρ' y a) = a
            rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
          right_inv := fun a => Subtype.ext (by
            show ρ' y (ρ' y⁻¹ a) = a
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
          map_mul' := fun a b => Subtype.ext (map_mul (ρ' y) (a : ↥R ⧸ Φ) b) }
      map_one' := MulEquiv.ext fun a => Subtype.ext (by
        show ρ' 1 a = a
        rw [map_one, MulAut.one_apply])
      map_mul' := fun y y' => MulEquiv.ext fun a => Subtype.ext (by
        show ρ' (y * y') a = ρ' y (ρ' y' a)
        rw [map_mul, MulAut.mul_apply]) }
  have hzY3 : zY ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hρz1 : ρ zY ≠ 1 := by
    intro h
    obtain ⟨r, hr, hne⟩ := hzR
    apply hne
    have h1 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : G)) h
    have h2 : z * r * z⁻¹ = r := h1
    calc z * r = z * r * z⁻¹ * z := by group
      _ = r * z := by rw [h2]
  have hρz3 : (ρ zY) ^ 3 = 1 := by rw [← map_pow, hzY3, map_one]
  have hord : orderOf (ρ zY) = 3 := orderOf_eq_prime hρz3 hρz1
  have hcop : ¬ 3 ∣ Nat.card ↥R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    by_contra hy1
    haveI : Group.IsNilpotent ↥Y := hY.isNilpotent
    have hKne : σ.ker ≠ ⊥ := by
      intro h
      apply hy1
      have hyk : y ∈ σ.ker := hy
      rw [h, Subgroup.mem_bot] at hyk
      exact hyk
    have hKc := Group.IsNilpotent.inf_center_ne_bot_of_normal hKne
    obtain ⟨w, hw⟩ : ∃ w : ↥(σ.ker ⊓ center ↥Y), orderOf w = 3 := by
      have hMp : IsPGroup 3 ↥(σ.ker ⊓ center ↥Y) := hY.to_subgroup _
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hMp
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.card_eq_one] at hn
        exact hKc hn
      exact exists_prime_orderOf_dvd_card' 3 (by rw [hn]; exact dvd_pow_self 3 hn0)
    have hwk : (w : ↥Y) ∈ σ.ker := (Subgroup.mem_inf.mp w.2).1
    have hwc : (w : ↥Y) ∈ center ↥Y := (Subgroup.mem_inf.mp w.2).2
    have hwY : orderOf (w : ↥Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hw
    have hwG : orderOf ((w : ↥Y) : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hwY
    have hwG3 : ((w : ↥Y) : G) ^ 3 = 1 := by rw [← hwG]; exact pow_orderOf_eq_one _
    have hwGc : ((w : ↥Y) : G) ∈ centralizer (Y : Set G) := by
      rw [mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hwc ⟨g, hg⟩)
    have hwz : ((w : ↥Y) : G) ∈ zpowers z := hcen _ (w : ↥Y).2 hwGc hwG3
    have hz1 : z ≠ 1 := by
      rintro rfl
      obtain ⟨r, -, hne⟩ := hzR
      exact hne (by rw [one_mul, mul_one])
    have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have heq : zpowers ((w : ↥Y) : G) = zpowers z := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwz)
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hwG]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers z : z ∈ zpowers ((w : ↥Y) : G))
    have hzk : zY ∈ σ.ker := by
      have : zY = (w : ↥Y) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this]
      exact zpow_mem hwk k
    have hfixA : ∀ a ∈ A, ζ a = a := by
      intro a ha
      have h := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : ↥R ⧸ Φ))
        (MonoidHom.mem_ker.mp hzk)
      exact h
    have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hzY3, map_one]
    have hfix : ∀ v, ζ v = v := by
      intro v
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective Φ v
      have h1 := hfixA _ (⟨r, rfl⟩ : ε r ∈ A)
      rw [hε, map_mul, map_inv] at h1
      have h2 : ζ (ζ (π r)) = π r := by
        rw [mul_inv_eq_iff_eq_mul.mp h1, hinv (π r), mul_assoc, hcomm (π r) (ζ (π r)),
          ← mul_assoc, hsq, one_mul]
      have h3 : ζ (ζ (ζ (π r))) = π r := by
        have h4 := congrArg (fun φ : MulAut (↥R ⧸ Φ) => φ (π r)) hζ3
        simpa [pow_succ, MulAut.mul_apply] using h4
      rw [h2] at h3
      exact h3
    have hker : ρ zY ∈ (quotientAutomorphism (frattini ↥R)).ker := by
      rw [mem_quotientAutomorphism_kernel]
      intro r
      have h := hfix (π r)
      rw [hζ, hρ'] at h
      exact h
    exact hρz1 (prime_order_frattini_kernel_trivial 3 (ρ zY) hord hcop hker)
  have hAcard : Nat.card ↥A ≤ 16 := by
    have h2 : (centralizer (zpowers z : Set G)).subgroupOf R ≤ ε.ker := by
      intro r hr
      rw [MonoidHom.mem_ker, hε]
      have hrc : (r : G) ∈ centralizer (zpowers z : Set G) := Subgroup.mem_subgroupOf.mp hr
      have hzr : z * r = r * z := mem_centralizer_iff.mp hrc z (mem_zpowers z)
      have hrz : ρ zY r = r := Subtype.ext (by
        rw [hρ]
        show z * r * z⁻¹ = r
        rw [hzr, mul_inv_cancel_right])
      rw [hζ, hρ', hrz, mul_inv_cancel]
    have h3 : ε.ker.index ∣ ((centralizer (zpowers z : Set G)).subgroupOf R).index :=
      Subgroup.index_dvd_of_le h2
    have h4 : ((centralizer (zpowers z : Set G)).subgroupOf R).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    rw [hA, ← Subgroup.index_ker ε]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h4) h3).trans hle
  have hAcomm : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (hcomm a b)
  have hA2 : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (hsq a)
  have h27 : 27 ∣ Nat.card ↥Y := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hY
    have hm3 : 3 ≤ m := by
      by_contra h
      have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hm]
    exact (Nat.pow_dvd_pow 3 hm3 : 3 ^ 3 ∣ 3 ^ m)
  exact not_injective_of_card_le_sixteen hAcomm hA2 hAcard h27 σ hσinj

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614J
