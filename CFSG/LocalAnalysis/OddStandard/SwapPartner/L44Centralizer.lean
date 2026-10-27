module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem mulAut_mul_conj_mul_inv {P : Type*} [Group P] (θ : MulAut P) (x : P) :
    θ * MulAut.conj x * θ⁻¹ = MulAut.conj (θ x) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private noncomputable def conjLift {P : Type*} [Group P] {Y : Type*} [Group Y]
    (Ψ : Y →* MulAut P) (hΨ : Function.Injective Ψ)
    (hinn : ∀ x : P, ∃ s : Y, Ψ s = MulAut.conj x) : P →* Y where
  toFun x := Classical.choose (hinn x)
  map_one' := hΨ (by
    calc Ψ (Classical.choose (hinn 1)) = MulAut.conj 1 := Classical.choose_spec (hinn 1)
      _ = 1 := map_one MulAut.conj
      _ = Ψ 1 := (map_one Ψ).symm)
  map_mul' x y := hΨ (by
    calc Ψ (Classical.choose (hinn (x * y)))
        = MulAut.conj (x * y) := Classical.choose_spec (hinn (x * y))
      _ = MulAut.conj x * MulAut.conj y := map_mul MulAut.conj x y
      _ = Ψ (Classical.choose (hinn x)) * Ψ (Classical.choose (hinn y)) := by
          rw [Classical.choose_spec (hinn x), Classical.choose_spec (hinn y)]
      _ = Ψ (Classical.choose (hinn x) * Classical.choose (hinn y)) :=
          (map_mul Ψ _ _).symm)

theorem mem_inner_of_coprime_orderOf_outer {P : Type*} [Group P] {x : MulAut P}
    (h : (orderOf x).Coprime (Nat.card (Outer P))) : x ∈ inner P := by
  have hdvd : orderOf ((QuotientGroup.mk' (inner P)) x) ∣
      Nat.gcd (orderOf x) (Nat.card (Outer P)) :=
    Nat.dvd_gcd (orderOf_map_dvd (QuotientGroup.mk' (inner P)) x)
      (orderOf_dvd_natCard ((QuotientGroup.mk' (inner P)) x))
  have h1 : orderOf ((QuotientGroup.mk' (inner P)) x) = 1 :=
    Nat.dvd_one.mp (h.gcd_eq_one ▸ hdvd)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)

theorem four_mul_card_fixedSubgroup_le {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y]
    [Finite Y] (Ψ : Y →* MulAut P) (hΨ : Function.Injective Ψ)
    (hinn : ∀ x : P, ∃ s : Y, Ψ s = MulAut.conj x) (hZ : ∀ z : P, (∀ x, x * z = z * x) → z = 1)
    (d : Y) (e : Fin 4 → Y) (hed : ∀ i, e i * d = d * e i)
    (hne : ∀ i j, i ≠ j → Ψ (e i * (e j)⁻¹) ∉ inner P) :
    4 * Nat.card (fixedSubgroup (Ψ d)) ≤ Nat.card (Subgroup.centralizer ({d} : Set Y)) := by
  let sx : P →* Y := conjLift Ψ hΨ hinn
  have hsc : ∀ x : P, Ψ (sx x) = MulAut.conj x := fun x => Classical.choose_spec (hinn x)
  have hconj_inj : ∀ {a b : P}, MulAut.conj a = MulAut.conj b → a = b := by
    intro a b hab
    have hcen : ∀ x : P, x * (b⁻¹ * a) = (b⁻¹ * a) * x := by
      intro x
      have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
        rw [map_mul, hab, map_inv, inv_mul_cancel]
      have hx := congrArg (fun θ : MulAut P => θ x) h1
      have hx' : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
        simpa only [MulAut.conj_apply, MulAut.one_apply] using hx
      calc x * (b⁻¹ * a) = ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [hx']
        _ = (b⁻¹ * a) * x := by group
    have hb : b⁻¹ * a = 1 := hZ _ hcen
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [hb]
      _ = b := by rw [mul_one]
  have hsx_inj : Function.Injective sx := by
    intro x x' hxx'
    apply hconj_inj
    rw [← hsc x, ← hsc x', hxx']
  have hb : ∀ x ∈ fixedSubgroup (Ψ d), d * sx x * d⁻¹ = sx x := by
    intro x hx
    have hfix : (Ψ d) x = x := hx
    apply hΨ
    calc Ψ (d * sx x * d⁻¹) = Ψ d * MulAut.conj x * (Ψ d)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hsc x]
      _ = MulAut.conj ((Ψ d) x) := mulAut_mul_conj_mul_inv (Ψ d) x
      _ = MulAut.conj x := by rw [hfix]
      _ = Ψ (sx x) := (hsc x).symm
  let F : fixedSubgroup (Ψ d) × Fin 4 → Subgroup.centralizer ({d} : Set Y) :=
    fun p => ⟨sx p.1 * e p.2, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : d * sx p.1 = sx p.1 * d := by
        have h := hb p.1 p.1.2
        calc d * sx p.1 = (d * sx p.1 * d⁻¹) * d := by group
          _ = sx p.1 * d := by rw [h]
      calc (sx p.1 * e p.2) * d = sx p.1 * (e p.2 * d) := by rw [mul_assoc]
        _ = sx p.1 * (d * e p.2) := by rw [hed p.2]
        _ = (sx p.1 * d) * e p.2 := by rw [mul_assoc]
        _ = (d * sx p.1) * e p.2 := by rw [h1]
        _ = d * (sx p.1 * e p.2) := by rw [mul_assoc]⟩
  have hF : Function.Injective F := by
    rintro ⟨x, i⟩ ⟨x', j⟩ h
    have hval : sx (x : P) * e i = sx (x' : P) * e j := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hij'
      have hmem : Ψ (e i * (e j)⁻¹) ∈ inner P := by
        have hkey : Ψ (e i * (e j)⁻¹) = MulAut.conj ((x : P)⁻¹ * (x' : P)) := by
          have h' : e i * (e j)⁻¹ = sx ((x : P)⁻¹ * (x' : P)) := by
            calc e i * (e j)⁻¹
                = (sx (x : P))⁻¹ * (sx (x : P) * e i) * (e j)⁻¹ := by group
              _ = (sx (x : P))⁻¹ * (sx (x' : P) * e j) * (e j)⁻¹ := by rw [hval]
              _ = (sx (x : P))⁻¹ * sx (x' : P) := by group
              _ = sx ((x : P)⁻¹ * (x' : P)) := by rw [map_mul, map_inv]
          rw [h', hsc]
        rw [hkey]
        exact ⟨(x : P)⁻¹ * (x' : P), rfl⟩
      exact (hne i j hij') hmem
    subst hij
    have hxeq : x = x' := Subtype.ext (hsx_inj (mul_right_cancel hval))
    subst hxeq
    rfl
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_fin] at hcard
  rw [Nat.mul_comm 4 (Nat.card (fixedSubgroup (Ψ d)))]
  exact hcard

theorem exists_fixed_orderOf_of_commute {P : Type*} [Group P] {Y : Type*} [Group Y]
    (Ψ : Y →* MulAut P) (hΨ : Function.Injective Ψ) (hZ : ∀ z : P, (∀ x, x * z = z * x) → z = 1)
    (hOut : Nat.Coprime 7 (Nat.card (Outer P))) {d z : Y} (hz : orderOf z = 7)
    (hdz : d * z = z * d) : ∃ w : P, orderOf w = 7 ∧ Ψ d w = w := by
  have horder : orderOf (Ψ z) = 7 := by
    rw [orderOf_injective Ψ hΨ z, hz]
  have hin : Ψ z ∈ inner P := by
    apply mem_inner_of_coprime_orderOf_outer
    rw [horder]
    exact hOut
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hin
  have hconjw : MulAut.conj w = Ψ z := hw
  have hconj_inj : ∀ {a b : P}, MulAut.conj a = MulAut.conj b → a = b := by
    intro a b hab
    have hcen : ∀ x : P, x * (b⁻¹ * a) = (b⁻¹ * a) * x := by
      intro x
      have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
        rw [map_mul, hab, map_inv, inv_mul_cancel]
      have hx := congrArg (fun θ : MulAut P => θ x) h1
      have hx' : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
        simpa only [MulAut.conj_apply, MulAut.one_apply] using hx
      calc x * (b⁻¹ * a) = ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [hx']
        _ = (b⁻¹ * a) * x := by group
    have hb : b⁻¹ * a = 1 := hZ _ hcen
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [hb]
      _ = b := by rw [mul_one]
  have hz7 : z ^ 7 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hw7 : w ^ 7 = 1 := by
    refine hZ (w ^ 7) (fun x => ?_)
    have hconj1 : MulAut.conj (w ^ 7) = 1 := by
      rw [map_pow, hconjw]
      rw [← map_pow Ψ z 7, hz7, map_one]
    have hx := congrArg (fun θ : MulAut P => θ x) hconj1
    have hx' : w ^ 7 * x * (w ^ 7)⁻¹ = x := by
      simpa only [MulAut.conj_apply, MulAut.one_apply] using hx
    calc x * w ^ 7 = (w ^ 7 * x * (w ^ 7)⁻¹) * w ^ 7 := by rw [hx']
      _ = w ^ 7 * x := by group
  have hwne : w ≠ 1 := by
    intro hw1
    have hz1 : z = 1 := by
      apply hΨ
      rw [← hconjw, hw1, map_one, map_one]
    have h1 : orderOf (1 : Y) = 7 := by rw [← hz1]; exact hz
    rw [orderOf_one] at h1
    omega
  have hworder : orderOf w = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hw7 hwne
  have hcomm : Ψ d * MulAut.conj w = MulAut.conj w * Ψ d := by
    have h := congrArg Ψ hdz
    rw [map_mul, map_mul] at h
    rw [← hconjw] at h
    exact h
  have hfix : Ψ d w = w := by
    apply hconj_inj
    calc MulAut.conj (Ψ d w) = Ψ d * MulAut.conj w * (Ψ d)⁻¹ :=
          (mulAut_mul_conj_mul_inv (Ψ d) w).symm
      _ = (MulAut.conj w * Ψ d) * (Ψ d)⁻¹ := by rw [hcomm]
      _ = MulAut.conj w := by group
  exact ⟨w, hworder, hfix⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
