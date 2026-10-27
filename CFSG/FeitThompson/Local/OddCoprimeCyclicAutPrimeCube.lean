module

public import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.OddOrder.ScalarFreePlaneGroupOrderDividesPPlusOne
public import CFSG.FeitThompson.OddOrder.DerivedPGroupInvariantAlternatingForm

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

section Pairing

variable {P : Type*} [Group P] (hz : ∀ u v : P, ⁅u, v⁆ ∈ Subgroup.center P)

include hz

def commutatorHomLeftOfCentral (v : P) : P →* P :=
  MonoidHom.mk' (fun u => ⁅u, v⁆) fun a b => by
    rw [commutatorElement_mul_left_eq_conj_mul, mem_center_iff.mp (hz b v) a,
      mul_inv_cancel_right, mem_center_iff.mp (hz b v) ⁅a, v⁆]

def commutatorHomRightOfCentral (u : P) : P →* P :=
  MonoidHom.mk' (fun v => ⁅u, v⁆) fun a b => by
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅u, a⁆ a,
      mem_center_iff.mp (hz u b) a]
    group

theorem commutatorElement_mul_left_of_central (u v w : P) : ⁅u * v, w⁆ = ⁅u, w⁆ * ⁅v, w⁆ :=
  (commutatorHomLeftOfCentral hz w).map_mul u v

theorem commutatorElement_mul_right_of_central (u v w : P) : ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ :=
  (commutatorHomRightOfCentral hz u).map_mul v w

theorem commutatorElement_zpow_left_of_central (u v : P) (m : ℤ) : ⁅u ^ m, v⁆ = ⁅u, v⁆ ^ m :=
  (commutatorHomLeftOfCentral hz v).map_zpow u m

theorem commutatorElement_zpow_right_of_central (u v : P) (m : ℤ) : ⁅u, v ^ m⁆ = ⁅u, v⁆ ^ m :=
  (commutatorHomRightOfCentral hz u).map_zpow v m

theorem commutatorElement_zpow_mul_zpow (x y : P) (α β γ δ : ℤ) :
    ⁅x ^ α * y ^ β, x ^ γ * y ^ δ⁆ = ⁅x, y⁆ ^ (α * δ - β * γ) := by
  have hxx : ⁅x ^ α, x ^ γ⁆ = 1 := by
    rw [commutatorElement_zpow_left_of_central hz, commutatorElement_zpow_right_of_central hz,
      commutatorElement_self, one_zpow, one_zpow]
  have hxy : ⁅x ^ α, y ^ δ⁆ = ⁅x, y⁆ ^ (α * δ) := by
    rw [commutatorElement_zpow_left_of_central hz, commutatorElement_zpow_right_of_central hz,
      ← zpow_mul, mul_comm δ α]
  have hyx : ⁅y ^ β, x ^ γ⁆ = ⁅x, y⁆ ^ (-(β * γ)) := by
    rw [commutatorElement_zpow_left_of_central hz, commutatorElement_zpow_right_of_central hz,
      show ⁅y, x⁆ = ⁅x, y⁆⁻¹ from (commutatorElement_inv x y).symm, ← zpow_mul,
      inv_zpow, ← zpow_neg]
    ring_nf
  have hyy : ⁅y ^ β, y ^ δ⁆ = 1 := by
    rw [commutatorElement_zpow_left_of_central hz, commutatorElement_zpow_right_of_central hz,
      commutatorElement_self, one_zpow, one_zpow]
  rw [commutatorElement_mul_left_of_central hz, commutatorElement_mul_right_of_central hz,
    commutatorElement_mul_right_of_central hz, hxx, hxy, hyx, hyy, one_mul, mul_one, ← zpow_add,
    sub_eq_add_neg]

end Pairing

namespace MulAut

variable {P : Type*} [Group P]

theorem pow_apply_of_trivial_on_center_quotient {a : MulAut P}
    (hfix : ∀ z ∈ center P, a z = z) (hquot : ∀ x : P, x⁻¹ * a x ∈ center P) (n : ℕ) (x : P) :
    (a ^ n) x = x * (x⁻¹ * a x) ^ n := by
  set c : P := x⁻¹ * a x with hcdef
  have hc : c ∈ center P := hquot x
  have hax : a x = x * c := by rw [hcdef]; group
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, hfix _ (Subgroup.pow_mem _ hc n), hax,
      pow_succ', mul_assoc]

theorem pow_eq_one_of_forall_pow_eq_one_of_trivial_on_center_quotient {p : ℕ} {a : MulAut P}
    (hexp : ∀ x : P, x ^ p = 1) (hfix : ∀ z ∈ center P, a z = z)
    (hquot : ∀ x : P, x⁻¹ * a x ∈ center P) : a ^ p = 1 := by
  ext x
  rw [pow_apply_of_trivial_on_center_quotient hfix hquot p x, hexp, mul_one]
  rfl

end MulAut

section Faithful

variable {p : ℕ} {P : Type*} [Group P]

theorem abelianizationOf_eq_one_iff_mem_center (hp : p.Prime) (hP : Nat.card P = p ^ 3)
    (hnab : ¬ IsMulCommutative P) {x : P} :
    Abelianization.of x = 1 ↔ x ∈ center P := by
  rw [← MonoidHom.mem_ker, Abelianization.ker_of,
    commutator_eq_center_of_card_eq_prime_cube hp hP hnab]

theorem exists_abelianizationOf_eq (g : Abelianization P) : ∃ x : P, Abelianization.of x = g :=
  ⟨Quotient.out g, Quotient.out_eq g⟩

theorem injective_abelianizationAut_subtype (hp : p.Prime) (hP : Nat.card P = p ^ 3)
    (hnab : ¬ IsMulCommutative P) (hexp : ∀ x : P, x ^ p = 1) {A : Subgroup (MulAut P)}
    (hcop : (Nat.card A).Coprime p)
    (hfix : ∀ a ∈ A, ∀ z ∈ center P, (a : MulAut P) z = z) :
    Function.Injective (abelianizationAut (A.subtype : A →* MulAut P)) := by
  have hfin : Finite P :=
    Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.ne_zero)
  have hfinA : Finite A := Finite.of_injective (fun a : A => ((a : MulAut P) : P → P))
    fun a b h => Subtype.ext (MulEquiv.ext (congrFun h))
  rw [injective_iff_map_eq_one]
  intro a ha
  have hquot : ∀ x : P, x⁻¹ * (a : MulAut P) x ∈ center P := by
    intro x
    have h1 : Abelianization.of ((a : MulAut P) x) = Abelianization.of x := by
      have := congrArg (fun f : MulAut (Abelianization P) => f (Abelianization.of x)) ha
      simpa using this
    rw [← abelianizationOf_eq_one_iff_mem_center hp hP hnab]
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have hap : (a : MulAut P) ^ p = 1 :=
    MulAut.pow_eq_one_of_forall_pow_eq_one_of_trivial_on_center_quotient hexp
      (fun z hz => hfix (a : MulAut P) a.2 z hz) hquot
  have hap' : a ^ p = 1 := Subtype.ext (by simpa using hap)
  have hacard : a ^ Nat.card A = 1 := pow_card_eq_one'
  have hdvd : orderOf a ∣ Nat.gcd (Nat.card A) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hacard) (orderOf_dvd_of_pow_eq_one hap')
  rw [hcop] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem natCard_range_abelianizationAut_subtype (hp : p.Prime) (hP : Nat.card P = p ^ 3)
    (hnab : ¬ IsMulCommutative P) (hexp : ∀ x : P, x ^ p = 1) {A : Subgroup (MulAut P)}
    (hcop : (Nat.card A).Coprime p)
    (hfix : ∀ a ∈ A, ∀ z ∈ center P, (a : MulAut P) z = z) :
    Nat.card (abelianizationAut (A.subtype : A →* MulAut P)).range = Nat.card A := by
  exact (Nat.card_congr (Equiv.ofInjective _
    (injective_abelianizationAut_subtype hp hP hnab hexp hcop hfix))).symm

end Faithful

section Plane

open Module

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {β : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p}

theorem finrank_eq_of_natCard_eq_pow [Finite V] {n : ℕ} (h : Nat.card V = p ^ n) :
    finrank (ZMod p) V = n := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at h
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

theorem exists_apply_apply_ne_zero (hβ : β ≠ 0) : ∃ w v : V, β w v ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hβ (by ext w v; simp [h w v])

theorem span_pair_eq_top_of_finrank_eq_two (hV : finrank (ZMod p) V = 2) {w v : V} (hw : w ≠ 0)
    (hv : v ∉ Submodule.span (ZMod p) ({w} : Set V)) :
    Submodule.span (ZMod p) ({w, v} : Set V) = ⊤ := by
  have hfd : FiniteDimensional (ZMod p) V := FiniteDimensional.of_finrank_pos (by omega)
  have hlt : Submodule.span (ZMod p) ({w} : Set V) < Submodule.span (ZMod p) ({w, v} : Set V) :=
    lt_of_le_of_ne (Submodule.span_mono (by simp))
      fun hh => hv (hh ▸ Submodule.subset_span (by simp))
  have h1 : finrank (ZMod p) (Submodule.span (ZMod p) ({w} : Set V)) = 1 :=
    finrank_span_singleton hw
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 : finrank (ZMod p) (Submodule.span (ZMod p) ({w, v} : Set V)) ≤ 2 := by
    rw [← hV]; exact Submodule.finrank_le _
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem notMem_span_singleton_of_apply_ne_zero (halt : β.IsAlt) {w v : V} (hwv : β w v ≠ 0) :
    v ∉ Submodule.span (ZMod p) ({w} : Set V) := by
  intro hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  rw [map_smul, halt.self_eq_zero w] at hwv
  simp at hwv

theorem exists_apply_ne_zero (hV : finrank (ZMod p) V = 2) (hβ : β ≠ 0) (halt : β.IsAlt)
    {u : V} (hu : u ≠ 0) : ∃ v : V, β u v ≠ 0 := by
  obtain ⟨w, v, hwv⟩ := exists_apply_apply_ne_zero hβ
  have hw : w ≠ 0 := by rintro rfl; simp at hwv
  have htop := span_pair_eq_top_of_finrank_eq_two hV hw
    (notMem_span_singleton_of_apply_ne_zero halt hwv)
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (htop ▸ Submodule.mem_top (x := u))
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 : b * β w v = 0 := by
    have h := hcon w
    rw [map_add, map_smul, map_smul] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, halt.self_eq_zero w, smul_eq_mul,
      mul_zero, zero_add] at h
    rw [← halt.neg w v] at h
    linear_combination -h
  have h2 : a * β w v = 0 := by
    have h := hcon v
    rw [map_add, map_smul, map_smul] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, halt.self_eq_zero v, smul_eq_mul,
      mul_zero, add_zero] at h
    linear_combination h
  have ha : a = 0 := by rcases mul_eq_zero.mp h2 with h | h; exacts [h, absurd h hwv]
  have hb : b = 0 := by rcases mul_eq_zero.mp h1 with h | h; exacts [h, absurd h hwv]
  exact hu (by rw [ha, hb]; simp)

theorem pow_eq_one_of_apply_eq_of_invariant (hV : finrank (ZMod p) V = 2) (halt : β.IsAlt)
    {w v : V} (hwv : β w v ≠ 0) {d : V ≃ₗ[ZMod p] V} (hinv : ∀ x y : V, β (d x) (d y) = β x y)
    (hdw : d w = w) : d ^ p = 1 := by
  have hw : w ≠ 0 := by rintro rfl; simp at hwv
  have htop := span_pair_eq_top_of_finrank_eq_two hV hw
    (notMem_span_singleton_of_apply_ne_zero halt hwv)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (htop ▸ Submodule.mem_top (x := d v))
  have hb : b = 1 := by
    have h1 : β w (d v) = β w v := by have h := hinv w v; rwa [hdw] at h
    rw [← hab, map_add, map_smul, map_smul] at h1
    simp only [halt.self_eq_zero w, smul_eq_mul, mul_zero, zero_add] at h1
    have h2 : (b - 1) * β w v = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · linear_combination h
    · exact absurd h hwv
  subst hb
  rw [one_smul] at hab
  have hdwn : ∀ n : ℕ, (d ^ n) w = w := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hs : (d ^ (n + 1)) w = d ((d ^ n) w) := by rw [pow_succ']; rfl
      rw [hs, ih, hdw]
  have key : ∀ n : ℕ, (d ^ n) v = v + ((n : ZMod p) * a) • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : (d ^ (n + 1)) v = d ((d ^ n) v) := by rw [pow_succ']; rfl
      rw [hs, ih, map_add, map_smul, hdw, ← hab]
      push_cast
      module
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨c, e, rfl⟩ := Submodule.mem_span_pair.mp (htop ▸ Submodule.mem_top (x := x))
  change (d ^ p) (c • w + e • v) = c • w + e • v
  rw [map_add, map_smul, map_smul, hdwn, key, ZMod.natCast_self]
  module

theorem natCard_dvd_sub_one_of_invariant_line (hV : finrank (ZMod p) V = 2) (hβ : β ≠ 0)
    (halt : β.IsAlt) {D : Subgroup (V ≃ₗ[ZMod p] V)} (hDcyc : IsCyclic D)
    (hcop : (Nat.card D).Coprime p)
    (hinv : ∀ d ∈ D, ∀ x y : V, β (d x) (d y) = β x y)
    {w : V} (hw : w ≠ 0) (hline : ∀ d ∈ D, d w ∈ Submodule.span (ZMod p) ({w} : Set V)) :
    Nat.card D ∣ p - 1 := by
  have hfd : FiniteDimensional (ZMod p) V := FiniteDimensional.of_finrank_pos (by omega)
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hVfin : Finite V := Module.finite_of_finite (ZMod p)
  have hLfin : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod p] V => (f : V → V)) fun f g h =>
      LinearEquiv.ext (congrFun h)
  obtain ⟨v, hwv⟩ := exists_apply_ne_zero hV hβ halt hw
  obtain ⟨g, hg⟩ := hDcyc
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hline (g : V ≃ₗ[ZMod p] V) g.2)
  have htne : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hw ((g : V ≃ₗ[ZMod p] V).injective (ht.symm.trans (map_zero _).symm))
  set m : ℕ := orderOf (Units.mk0 t htne)
  have hmdvd : m ∣ p - 1 := by
    have h1 : m ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard _
    rwa [Nat.card_units (α := ZMod p), Nat.card_zmod] at h1
  have htm : t ^ m = 1 := by
    have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) (pow_orderOf_eq_one (Units.mk0 t htne))
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
    exact h
  have hgn : ∀ n : ℕ, ((g : V ≃ₗ[ZMod p] V) ^ n) w = t ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : ((g : V ≃ₗ[ZMod p] V) ^ (n + 1)) w
          = (g : V ≃ₗ[ZMod p] V) (((g : V ≃ₗ[ZMod p] V) ^ n) w) := by rw [pow_succ']; rfl
      rw [hs, ih, map_smul, ← ht, smul_smul, pow_succ, mul_comm]
  have hfixw : ((g : V ≃ₗ[ZMod p] V) ^ m) w = w := by rw [hgn, htm, one_smul]
  have hmemD : ((g : V ≃ₗ[ZMod p] V) ^ m) ∈ D := by have := (g ^ m).2; simpa using this
  have hp1 : ((g : V ≃ₗ[ZMod p] V) ^ m) ^ p = 1 :=
    pow_eq_one_of_apply_eq_of_invariant hV halt hwv (hinv _ hmemD) hfixw
  have hp1' : (g ^ m : D) ^ p = 1 := by
    refine Subtype.ext ?_
    push_cast
    simpa using hp1
  have hdvd : orderOf (g ^ m : D) ∣ Nat.gcd p (Nat.card D) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp1') (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one hcop.symm] at hdvd
  have hg1 : (g ^ m : D) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  rw [(orderOf_eq_card_of_forall_mem_zpowers hg).symm]
  exact (orderOf_dvd_of_pow_eq_one hg1).trans hmdvd

theorem natCard_dvd_add_one_of_no_invariant_line (hV : finrank (ZMod p) V = 2) (hβ : β ≠ 0)
    {D : Subgroup (V ≃ₗ[ZMod p] V)} (hDcyc : IsCyclic D) (hDodd : Odd (Nat.card D))
    (hinv : ∀ d ∈ D, ∀ x y : V, β (d x) (d y) = β x y)
    (hno : ∀ w : V, w ≠ 0 → ¬ ∀ d ∈ D, d w ∈ Submodule.span (ZMod p) ({w} : Set V)) :
    Nat.card D ∣ p + 1 := by
  have hfd : FiniteDimensional (ZMod p) V := FiniteDimensional.of_finrank_pos (by omega)
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hntV : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  have : IsMulCommutative D := IsCyclic.isMulCommutative
  have hirr : (linearGroupRep D).IsIrreducible := by
    rw [isIrreducible_linearGroupRep_iff]
    refine ⟨hntV, fun W hW => ?_⟩
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hb, ht⟩ := hcon
    have h1 : finrank (ZMod p) W = 1 := by
      have h3 := Submodule.finrank_lt (K := ZMod p) ht
      have h4 : 1 ≤ finrank (ZMod p) W := Submodule.one_le_finrank_iff.mpr hb
      omega
    obtain ⟨w, hwW, hw0⟩ : ∃ w : V, w ∈ W ∧ w ≠ 0 := by
      obtain ⟨⟨w, hwW⟩, hw0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hb)
      exact ⟨w, hwW, fun h => hw0 (Subtype.ext h)⟩
    exact hno w hw0 fun d hd =>
      eq_span_singleton_of_mem_of_finrank_eq_one h1 hwW hw0 ▸ hW d hd w hwW
  have hscalar : D ⊓ scalarSubgroup (ZMod p) V = ⊥ := by
    rw [inf_scalarSubgroup_eq_bot_iff]
    intro a ha ⟨c, hc⟩
    obtain ⟨x, y, hxy⟩ := exists_apply_apply_ne_zero hβ
    have hc2 : ((c : ZMod p) * (c : ZMod p)) * β x y = β x y := by
      have h := hinv a ha x y
      rw [hc x, hc y, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
      linear_combination h
    have hc1 : (c : ZMod p) * (c : ZMod p) = 1 :=
      mul_right_cancel₀ hxy (hc2.trans (one_mul _).symm)
    have hprod : ((c : ZMod p) - 1) * ((c : ZMod p) + 1) = 0 := by linear_combination hc1
    rcases mul_eq_zero.mp hprod with h | h
    · have hc1' : (c : ZMod p) = 1 := by linear_combination h
      exact LinearEquiv.ext fun v => by rw [hc v, hc1', one_smul]; rfl
    · have hcm : (c : ZMod p) = -1 := by linear_combination h
      have ha2 : (⟨a, ha⟩ : D) ^ 2 = 1 := by
        refine Subtype.ext (LinearEquiv.ext fun v => ?_)
        change (a * a) v = v
        rw [LinearEquiv.mul_apply, hc v, map_smul, hc v, smul_smul, hcm]
        simp
      have hdvd : orderOf (⟨a, ha⟩ : D) ∣ Nat.gcd 2 (Nat.card D) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_natCard _)
      rw [Nat.coprime_two_left.mpr hDodd] at hdvd
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
  have h := natCard_dvd_natCard_add_one (k := ZMod p) (A := D) hV hscalar
  rwa [Nat.card_zmod] at h

theorem natCard_dvd_sub_one_or_dvd_add_one_of_faithful_plane_action
    (hV : finrank (ZMod p) V = 2) (hβ : β ≠ 0) (halt : β.IsAlt)
    {D : Subgroup (V ≃ₗ[ZMod p] V)} (hDcyc : IsCyclic D) (hDodd : Odd (Nat.card D))
    (hcop : (Nat.card D).Coprime p)
    (hinv : ∀ d ∈ D, ∀ x y : V, β (d x) (d y) = β x y) :
    Nat.card D ∣ p - 1 ∨ Nat.card D ∣ p + 1 := by
  by_cases h : ∃ w : V, w ≠ 0 ∧ ∀ d ∈ D, d w ∈ Submodule.span (ZMod p) ({w} : Set V)
  · obtain ⟨w, hw, hline⟩ := h
    exact Or.inl (natCard_dvd_sub_one_of_invariant_line hV hβ halt hDcyc hcop hinv hw hline)
  · exact Or.inr (natCard_dvd_add_one_of_no_invariant_line hV hβ hDcyc hDodd hinv
      fun w hw hline => h ⟨w, hw, hline⟩)

end Plane

section Transfer

open Module

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
  [Module (ZMod p) (Additive (Abelianization P))]

theorem injective_abelianizationLinearAut_of_injective_abelianizationAut
    {A : Subgroup (MulAut P)}
    (hinj : Function.Injective (abelianizationAut (A.subtype : A →* MulAut P))) :
    Function.Injective (abelianizationLinearAut p (A.subtype : A →* MulAut P)) := by
  intro u v huv
  refine hinj (MulEquiv.ext fun g => ?_)
  obtain ⟨x, rfl⟩ := exists_abelianizationOf_eq g
  rw [abelianizationAut_of, abelianizationAut_of]
  have h := congrArg (fun e : Additive (Abelianization P) ≃ₗ[ZMod p]
    Additive (Abelianization P) => e (Additive.ofMul (Abelianization.of x))) huv
  simp only [abelianizationLinearAut_ofMul_of] at h
  exact Additive.ofMul.injective h

theorem natCard_dvd_sub_one_or_dvd_add_one_of_invariant_form
    (hfr : finrank (ZMod p) (Additive (Abelianization P)) = 2)
    {A : Subgroup (MulAut P)} (hAcyc : IsCyclic A) (hAodd : Odd (Nat.card A))
    (hcop : (Nat.card A).Coprime p)
    (hinj : Function.Injective (abelianizationAut (A.subtype : A →* MulAut P)))
    {β : Additive (Abelianization P) →ₗ[ZMod p]
      Additive (Abelianization P) →ₗ[ZMod p] ZMod p} (hβ : β ≠ 0) (halt : β.IsAlt)
    (hinvβ : ∀ u : A, ∀ v w : Additive (Abelianization P),
      β (abelianizationLinearAut p (A.subtype : A →* MulAut P) u v)
        (abelianizationLinearAut p (A.subtype : A →* MulAut P) u w) = β v w) :
    Nat.card A ∣ p - 1 ∨ Nat.card A ∣ p + 1 := by
  set ρ := abelianizationLinearAut p (A.subtype : A →* MulAut P)
  have hinjA : Function.Injective ρ :=
    injective_abelianizationLinearAut_of_injective_abelianizationAut hinj
  have hcardD : Nat.card ρ.range = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective _ hinjA)).symm
  have hDcyc : IsCyclic ρ.range := isCyclic_of_surjective _ ρ.rangeRestrict_surjective
  have hinvD : ∀ d ∈ ρ.range, ∀ x y : Additive (Abelianization P), β (d x) (d y) = β x y := by
    rintro d ⟨u, rfl⟩ x y
    exact hinvβ u x y
  have h := natCard_dvd_sub_one_or_dvd_add_one_of_faithful_plane_action hfr hβ halt hDcyc
    (hcardD ▸ hAodd) (hcardD ▸ hcop) hinvD
  rwa [hcardD] at h

end Transfer

section PlaneStructure

variable {p : ℕ} {P : Type*} [Group P]

theorem nsmul_additive_abelianization_eq_zero (hexp : ∀ x : P, x ^ p = 1)
    (x : Additive (Abelianization P)) : p • x = 0 := by
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨z, rfl⟩ : ∃ z : P, Additive.ofMul (Abelianization.of z) = Additive.ofMul y :=
    ⟨Quotient.out y, congrArg Additive.ofMul (Quotient.out_eq y)⟩
  change Additive.ofMul ((Abelianization.of z) ^ p) = 0
  rw [← map_pow, hexp z, map_one]
  rfl

theorem natCard_additive_abelianization_of_card_eq_prime_cube (hp : p.Prime)
    (hP : Nat.card P = p ^ 3) (hnab : ¬ IsMulCommutative P) :
    Nat.card (Additive (Abelianization P)) = p ^ 2 := by
  have hfin : Finite P :=
    Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.ne_zero)
  have h1 : Nat.card (P ⧸ commutator P) * Nat.card (commutator P) = Nat.card P :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  rw [card_commutator_of_card_eq_prime_cube hp hP hnab, hP] at h1
  have h2 : Nat.card (Additive (Abelianization P)) = Nat.card (P ⧸ commutator P) :=
    Nat.card_congr (Additive.ofMul (α := Abelianization P)).symm
  rw [h2]
  exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1]; ring)

end PlaneStructure

theorem natCard_dvd_sub_one_or_natCard_dvd_add_one_of_cyclic_odd_coprime
    {p : ℕ} {P : Type*} [Group P] (hp : p.Prime) (hodd : Odd p) (hP : Nat.card P = p ^ 3)
    (hnab : ¬ IsMulCommutative P) (hexp : ∀ x : P, x ^ p = 1)
    {A : Subgroup (MulAut P)} (hAcyc : IsCyclic A) (hAodd : Odd (Nat.card A))
    (hcop : (Nat.card A).Coprime p)
    (hfix : ∀ a ∈ A, ∀ z ∈ center P, (a : MulAut P) z = z) :
    Nat.card A ∣ p - 1 ∨ Nat.card A ∣ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) (Additive (Abelianization P)) :=
    AddCommGroup.zmodModule (nsmul_additive_abelianization_eq_zero hexp)
  have hVcard : Nat.card (Additive (Abelianization P)) = p ^ 2 :=
    natCard_additive_abelianization_of_card_eq_prime_cube hp hP hnab
  have hVfin : Finite (Additive (Abelianization P)) :=
    Nat.finite_of_card_ne_zero (by rw [hVcard]; exact pow_ne_zero _ hp.ne_zero)
  have hfr : Module.finrank (ZMod p) (Additive (Abelianization P)) = 2 :=
    finrank_eq_of_natCard_eq_pow hVcard
  have hfixC : ∀ u : A, ∀ t ∈ commutator P, (A.subtype u) t = t := fun u t ht =>
    hfix (u : MulAut P) u.2 t
      (by rwa [commutator_eq_center_of_card_eq_prime_cube hp hP hnab] at ht)
  have hcomm : commutator P ≠ ⊥ := fun h => hnab ((commutator_eq_bot_iff P).mp h)
  obtain ⟨β, hβ, halt, hinvβ⟩ :=
    exists_ne_zero_isAlt_invariant_bilinForm_of_commutator_ne_bot (a := 3) hp (by norm_num) hP
      hcomm (A.subtype : A →* MulAut P) hfixC
  exact natCard_dvd_sub_one_or_dvd_add_one_of_invariant_form hfr hAcyc hAodd hcop
    (injective_abelianizationAut_subtype hp hP hnab hexp hcop hfix) hβ halt hinvβ

end

end CFSG.FeitThompson
