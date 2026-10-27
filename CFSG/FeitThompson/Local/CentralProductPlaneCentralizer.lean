module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
public import Mathlib.Data.Rat.Floor

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {R : Type*} [Group R] {p : ℕ}

private theorem normal_of_le_center {C : Subgroup R} (h : C ≤ Subgroup.center R) : C.Normal := by
  constructor
  intro x hx g
  rw [(Subgroup.mem_center_iff.mp (h hx)) g]
  simpa using hx

private theorem commute_of_isMulCommutative {X : Subgroup R} (hX : IsMulCommutative X) {x y : R}
    (hx : x ∈ X) (hy : y ∈ X) : Commute x y :=
  congrArg Subtype.val (hX.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)

private theorem le_centralizer_self {X : Subgroup R} (hX : IsMulCommutative X) :
    X ≤ Subgroup.centralizer (X : Set R) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy => (commute_of_isMulCommutative hX hy hx).eq

private theorem inf_eq_bot_of_ne_of_card_eq_prime {H K : Subgroup R} [Finite H] [Finite K]
    (hp : p.Prime) (hH : Nat.card H = p) (hK : Nat.card K = p) (hne : H ≠ K) : H ⊓ K = ⊥ := by
  have hdvd : Nat.card (H ⊓ K : Subgroup R) ∣ p := hH ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
  · exact Subgroup.card_eq_one.1 h1
  · have e1 : H ⊓ K = H := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hH])
    have e2 : H ⊓ K = K := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hK])
    exact absurd (e1 ▸ e2) hne

theorem map_center_subtype (X : Subgroup R) :
    (Subgroup.center X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set R) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.coe_subtype,
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy⟩, hz, rfl⟩
    exact ⟨hy, fun g hg => congrArg Subtype.val (hz ⟨g, hg⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, fun g => Subtype.ext (hc g g.2), rfl⟩

def omega1Subgroup (p : ℕ) (X : Subgroup R) : Subgroup R :=
  Subgroup.closure {x ∈ (X : Set R) | x ^ p = 1}

theorem omega1Subgroup_eq_closure (p : ℕ) (X : Subgroup R) :
    omega1Subgroup p X = Subgroup.closure {x ∈ (X : Set R) | x ^ p = 1} := (rfl)

theorem mem_omega1Subgroup {X : Subgroup R} {x : R} (hx : x ∈ X) (hxp : x ^ p = 1) :
    x ∈ omega1Subgroup p X :=
  Subgroup.subset_closure ⟨hx, hxp⟩

theorem omega1Subgroup_le {X H : Subgroup R} (h : ∀ x ∈ X, x ^ p = 1 → x ∈ H) :
    omega1Subgroup p X ≤ H :=
  (Subgroup.closure_le H).2 fun _ hx => h _ hx.1 hx.2

theorem omega1Subgroup_le_self (X : Subgroup R) : omega1Subgroup p X ≤ X :=
  omega1Subgroup_le fun _ hx _ => hx

theorem omega1Subgroup_mono {X Y : Subgroup R} (h : X ≤ Y) :
    omega1Subgroup p X ≤ omega1Subgroup p Y :=
  omega1Subgroup_le fun _ hx hxp => mem_omega1Subgroup (h hx) hxp

theorem mem_omega1Subgroup_iff_of_isMulCommutative {X : Subgroup R} (hX : IsMulCommutative X)
    {x : R} : x ∈ omega1Subgroup p X ↔ x ∈ X ∧ x ^ p = 1 := by
  refine ⟨fun hx => ?_, fun hx => mem_omega1Subgroup hx.1 hx.2⟩
  let S : Subgroup R :=
    { carrier := {x ∈ (X : Set R) | x ^ p = 1}
      one_mem' := ⟨X.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, by
        rw [(commute_of_isMulCommutative hX ha.1 hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  exact omega1Subgroup_le (H := S) (fun _ hy hyp => ⟨hy, hyp⟩) hx

theorem coe_omega1Subgroup_of_isMulCommutative {X : Subgroup R} (hX : IsMulCommutative X) :
    (omega1Subgroup p X : Set R) = {x ∈ (X : Set R) | x ^ p = 1} :=
  Set.ext fun _ => mem_omega1Subgroup_iff_of_isMulCommutative hX

structure IsInternalDirectProduct (X U V : Subgroup R) : Prop where
  left_le : U ≤ X
  right_le : V ≤ X
  coe_eq_mul : (X : Set R) = (U : Set R) * (V : Set R)
  inf_eq_bot : U ⊓ V = ⊥
  commutator_eq_bot : ⁅U, V⁆ = ⊥

namespace IsInternalDirectProduct

variable {X U V : Subgroup R} (h : IsInternalDirectProduct X U V)

include h

theorem commute {u v : R} (hu : u ∈ U) (hv : v ∈ V) : Commute u v :=
  (Subgroup.mem_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h.commutator_eq_bot hu) v hv).symm

theorem sup_eq : U ⊔ V = X := by
  refine le_antisymm (sup_le h.left_le h.right_le) fun x hx => ?_
  have hx' : x ∈ (U : Set R) * (V : Set R) := h.coe_eq_mul ▸ (hx : x ∈ (X : Set R))
  obtain ⟨u, hu, v, hv, rfl⟩ := hx'
  exact Subgroup.mul_mem_sup hu hv

theorem disjoint : Disjoint U V := disjoint_iff.2 h.inf_eq_bot

theorem card_eq_mul : Nat.card X = Nat.card U * Nat.card V := by
  have hc := natCard_mul_mul_natCard_inf U V
  rw [h.inf_eq_bot, Subgroup.card_bot, mul_one] at hc
  rw [← hc]
  exact Nat.card_congr (Set.equivOfEq h.coe_eq_mul)

end IsInternalDirectProduct

theorem isInternalDirectProduct_of_sup_eq {X U V : Subgroup R} [V.Normal] (hsup : U ⊔ V = X)
    (hinf : U ⊓ V = ⊥) (hcomm : ⁅U, V⁆ = ⊥) : IsInternalDirectProduct X U V where
  left_le := hsup ▸ le_sup_left
  right_le := hsup ▸ le_sup_right
  coe_eq_mul := by rw [← hsup, Subgroup.mul_normal]
  inf_eq_bot := hinf
  commutator_eq_bot := hcomm

structure IsRankTwoCentralProduct (p : ℕ) (R : Type*) [Group R] (B C Z₀ : Subgroup R) :
    Prop where
  prime : p.Prime
  odd : Odd p
  finite : Finite R
  isPGroup : IsPGroup p R
  sup_eq_top : B ⊔ C = ⊤
  card_base : Nat.card B = p ^ 3
  base_not_isMulCommutative : ¬ IsMulCommutative B
  pow_eq_one_of_mem_base : ∀ b ∈ B, b ^ p = 1
  central : C ≤ Subgroup.center R
  isCyclic : IsCyclic C
  central_ne_bot : C ≠ ⊥
  coe_socle : (Z₀ : Set R) = {c ∈ (C : Set R) | c ^ p = 1}
  inf_base_central : B ⊓ C = Z₀
  center_base : B ⊓ Subgroup.centralizer (B : Set R) = Z₀
  card_socle : Nat.card Z₀ = p

namespace IsRankTwoCentralProduct

variable {B C Z₀ : Subgroup R} (h : IsRankTwoCentralProduct p R B C Z₀)

include h

theorem normal_central : C.Normal := normal_of_le_center h.central

theorem isMulCommutative_central : IsMulCommutative C :=
  IsMulCommutative.of_comm fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (h.central b.2)) a)

theorem mem_socle_iff {x : R} : x ∈ Z₀ ↔ x ∈ C ∧ x ^ p = 1 := by
  have hs := h.coe_socle
  exact ⟨fun hx => (hs ▸ (hx : x ∈ (Z₀ : Set R)) : x ∈ {c ∈ (C : Set R) | c ^ p = 1}),
    fun hx => (hs ▸ (hx : x ∈ {c ∈ (C : Set R) | c ^ p = 1}) : x ∈ (Z₀ : Set R))⟩

theorem socle_le_base : Z₀ ≤ B := h.inf_base_central ▸ inf_le_left

theorem socle_le_central : Z₀ ≤ C := h.inf_base_central ▸ inf_le_right

theorem normal_socle : Z₀.Normal := normal_of_le_center (h.socle_le_central.trans h.central)

theorem exists_mem_base_mem_central (x : R) : ∃ b ∈ B, ∃ c ∈ C, b * c = x := by
  have hn := h.normal_central
  have hx : x ∈ ((B ⊔ C : Subgroup R) : Set R) := by rw [h.sup_eq_top]; trivial
  rw [Subgroup.mul_normal] at hx
  exact hx

theorem center_eq : Subgroup.center R = C := by
  refine le_antisymm (fun x hx => ?_) h.central
  obtain ⟨b, hb, c, hc, rfl⟩ := h.exists_mem_base_mem_central x
  have hcz : c ∈ Subgroup.center R := h.central hc
  have hbz : b ∈ Subgroup.center R := by
    have hbe : b = b * c * c⁻¹ := by group
    rw [hbe]
    exact mul_mem hx (inv_mem hcz)
  have hb0 : b ∈ Z₀ := h.center_base ▸ ⟨hb, Subgroup.center_le_centralizer _ hbz⟩
  exact mul_mem (h.socle_le_central hb0) hc

theorem mem_base_of_pow_eq_one {x : R} (hx : x ^ p = 1) : x ∈ B := by
  obtain ⟨b, hb, c, hc, rfl⟩ := h.exists_mem_base_mem_central x
  have hcomm : Commute b c := Subgroup.mem_center_iff.1 (h.central hc) b
  have hcp : c ^ p = 1 := by
    rw [hcomm.mul_pow, h.pow_eq_one_of_mem_base b hb, one_mul] at hx
    exact hx
  exact mul_mem hb (h.socle_le_base (h.mem_socle_iff.2 ⟨hc, hcp⟩))

theorem omega1_eq_base : omega1Subgroup p (⊤ : Subgroup R) = B :=
  le_antisymm (omega1Subgroup_le fun _ _ hxp => h.mem_base_of_pow_eq_one hxp)
    fun b hb => mem_omega1Subgroup (Subgroup.mem_top b) (h.pow_eq_one_of_mem_base b hb)

section Plane

variable {E : Subgroup R} (hE : IsMulCommutative E) (hEp : ∀ x ∈ E, x ^ p = 1)
  (hEcard : Nat.card E = p ^ 2)

include hE hEp hEcard

theorem plane_le_base : E ≤ B := fun _ hx => h.mem_base_of_pow_eq_one (hEp _ hx)

theorem inf_base_centralizer_plane_eq : B ⊓ Subgroup.centralizer (E : Set R) = E := by
  have hfin := h.finite
  have hp := h.prime
  set D : Subgroup R := B ⊓ Subgroup.centralizer (E : Set R) with hD
  have hED : E ≤ D := le_inf (h.plane_le_base hE hEp hEcard) (le_centralizer_self hE)
  have hDB : D ≤ B := inf_le_left
  have hdvd : Nat.card D ∣ p ^ 3 := h.card_base ▸ Subgroup.card_dvd_of_le hDB
  obtain ⟨k, hk3, hkD⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h2k : 2 ≤ k := by
    have : p ^ 2 ≤ p ^ k := hEcard ▸ hkD ▸ Subgroup.card_le_of_le hED
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hk2 : k = 2 := by
    rcases Nat.lt_or_ge k 3 with hlt | hge
    · omega
    · exfalso
      have hk3' : k = 3 := le_antisymm hk3 hge
      have hDB' : D = B := Subgroup.eq_of_le_of_card_ge hDB (by rw [hkD, hk3', h.card_base])
      have hBc : B ≤ Subgroup.centralizer (E : Set R) := hDB' ▸ inf_le_right
      have hEc : E ≤ Subgroup.centralizer (B : Set R) := Subgroup.le_centralizer_iff.1 hBc
      have hEZ : E ≤ Z₀ := h.center_base ▸ le_inf (h.plane_le_base hE hEp hEcard) hEc
      have hle : p ^ 2 ≤ p := by
        rw [← hEcard, ← h.card_socle]
        exact Subgroup.card_le_of_le hEZ
      rw [pow_two] at hle
      have hmul : p * p ≤ p * 1 := by rw [mul_one]; exact hle
      have hp1 := Nat.le_of_mul_le_mul_left hmul hp.pos
      have := hp.two_le
      omega
  exact (Subgroup.eq_of_le_of_card_ge hED (by rw [hkD, hk2, hEcard])).symm

theorem socle_le_plane : Z₀ ≤ E := by
  rw [← h.inf_base_centralizer_plane_eq hE hEp hEcard, ← h.center_base]
  exact le_inf inf_le_left
    (inf_le_right.trans (Subgroup.centralizer_le (h.plane_le_base hE hEp hEcard)))

theorem centralizer_plane_eq : Subgroup.centralizer (E : Set R) = E ⊔ C := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (le_centralizer_self hE) (h.central.trans (Subgroup.center_le_centralizer _)))
  obtain ⟨b, hb, c, hc, rfl⟩ := h.exists_mem_base_mem_central x
  have hcc : c ∈ Subgroup.centralizer (E : Set R) :=
    Subgroup.center_le_centralizer _ (h.central hc)
  have hbc : b ∈ Subgroup.centralizer (E : Set R) := by
    have hbe : b = b * c * c⁻¹ := by group
    rw [hbe]
    exact mul_mem hx (inv_mem hcc)
  have hbE : b ∈ E := h.inf_base_centralizer_plane_eq hE hEp hEcard ▸ ⟨hb, hbc⟩
  exact Subgroup.mul_mem_sup hbE hc

theorem coe_centralizer_plane_eq :
    (Subgroup.centralizer (E : Set R) : Set R) = (E : Set R) * (C : Set R) := by
  have hn := h.normal_central
  rw [h.centralizer_plane_eq hE hEp hEcard, Subgroup.mul_normal]

section Line

variable {A₀ : Subgroup R} (hA₀E : A₀ ≤ E) (hA₀card : Nat.card A₀ = p) (hA₀ : A₀ ≠ Z₀)

include hA₀E hA₀card hA₀

theorem line_inf_central_eq_bot : A₀ ⊓ C = ⊥ := by
  have hfin := h.finite
  have hle : A₀ ⊓ C ≤ A₀ ⊓ Z₀ :=
    le_inf inf_le_left (h.inf_base_central ▸
      le_inf ((inf_le_left.trans hA₀E).trans (h.plane_le_base hE hEp hEcard)) inf_le_right)
  rw [le_bot_iff.1 (hle.trans (le_of_eq
    (inf_eq_bot_of_ne_of_card_eq_prime h.prime hA₀card h.card_socle hA₀)))]

theorem line_sup_socle_eq_plane : A₀ ⊔ Z₀ = E := by
  have hfin := h.finite
  have hn := h.normal_socle
  have hZE : Z₀ ≤ E := h.socle_le_plane hE hEp hEcard
  have hinf : A₀ ⊓ Z₀ = ⊥ := inf_eq_bot_of_ne_of_card_eq_prime h.prime hA₀card h.card_socle hA₀
  have hcomm : ⁅A₀, Z₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 <|
    hA₀E.trans ((le_centralizer_self hE).trans (Subgroup.centralizer_le hZE))
  have hdp : IsInternalDirectProduct (A₀ ⊔ Z₀) A₀ Z₀ :=
    isInternalDirectProduct_of_sup_eq rfl hinf hcomm
  refine Subgroup.eq_of_le_of_card_ge (sup_le hA₀E hZE) ?_
  rw [hdp.card_eq_mul, hA₀card, h.card_socle, hEcard, pow_two]

theorem isInternalDirectProduct_centralizer_plane :
    IsInternalDirectProduct (Subgroup.centralizer (E : Set R)) A₀ C := by
  have hn := h.normal_central
  refine isInternalDirectProduct_of_sup_eq ?_
    (h.line_inf_central_eq_bot hE hEp hEcard hA₀E hA₀card hA₀)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x _ =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        ((Subgroup.mem_center_iff.1 (h.central hy)) x).symm)
  rw [h.centralizer_plane_eq hE hEp hEcard,
    ← h.line_sup_socle_eq_plane hE hEp hEcard hA₀E hA₀card hA₀, sup_assoc,
    sup_eq_right.2 (h.socle_le_central)]

end Line

end Plane

end IsRankTwoCentralProduct

end

end CFSG.FeitThompson
