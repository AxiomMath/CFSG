module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Reduce
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open scoped Pointwise
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem centralizer_singleton_eq_of_zpowers_eq' {G : Type*} [Group G] {x w : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers w) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({w} : Set G) := by
  have hx : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hw : Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hx, hw, h]

theorem no_order_mul_of_sylow {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    {y0 : G} (hy0 : orderOf y0 = p) (hfac : (Nat.card G).factorization p = 1)
    (hcent : ∀ c : G, Commute c y0 → orderOf c ≠ m) (g : G) : orderOf g ≠ m * p := by
  intro hg
  have hp : p.Prime := Fact.out
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hg
    exact (orderOf_pos g).ne' hg
  have hy : orderOf (g ^ m) = p := by
    rw [orderOf_pow' _ hm, hg, Nat.gcd_eq_right (dvd_mul_right m p)]
    exact Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hm)
  have hx : orderOf (g ^ p) = m := by
    rw [orderOf_pow' _ hp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left p m)]
    exact Nat.mul_div_cancel m hp.pos
  set y := g ^ m with hydef
  set x := g ^ p with hxdef
  have hcomm : Commute x y := Commute.pow_pow_self g p m
  have hP : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy, hfac, pow_one]
  have hQ : Nat.card (Subgroup.zpowers y0) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy0, hfac, pow_one]
  let P : Sylow p G := Sylow.ofCard (Subgroup.zpowers y) hP
  let Q : Sylow p G := Sylow.ofCard (Subgroup.zpowers y0) hQ
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P Q
  have h1 : (MulAut.conj a • y : G) ∈ MulAut.conj a • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj a) _ (Subgroup.mem_zpowers y)
  rw [← Sylow.coe_subgroup_smul, ha] at h1
  have hz : a * y * a⁻¹ ∈ Subgroup.zpowers y0 := h1
  have hzord : orderOf (a * y * a⁻¹) = p := by
    have := MulEquiv.orderOf_eq (MulAut.conj a) y
    rw [MulAut.conj_apply] at this
    rw [this, hy]
  have hle : Subgroup.zpowers (a * y * a⁻¹) ≤ Subgroup.zpowers y0 := Subgroup.zpowers_le.2 hz
  have heq : Subgroup.zpowers (a * y * a⁻¹) = Subgroup.zpowers y0 :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hy0])
  have hy0z : y0 ∈ Subgroup.zpowers (a * y * a⁻¹) := heq ▸ Subgroup.mem_zpowers y0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy0z
  have hcomm' : Commute (a * x * a⁻¹) (a * y * a⁻¹) := by
    have := hcomm.map (MulAut.conj a : G ≃* G).toMonoidHom
    simpa [MulAut.conj_apply] using this
  have hc0 : Commute (a * x * a⁻¹) y0 := by
    rw [← hk]
    exact hcomm'.zpow_right k
  have hord : orderOf (a * x * a⁻¹) = m := by
    have := MulEquiv.orderOf_eq (MulAut.conj a) x
    rw [MulAut.conj_apply] at this
    rw [this, hx]
  exact hcent _ hc0 hord

theorem no_order_mul_of_lines {G : Type*} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    (hline : ∀ j, ¬ r ∣ Nat.card ↥(Subgroup.centralizer ({line j} : Set G) ⊓ P))
    {g : G} (hgP : g ∈ P) : orderOf g ≠ p * r := by
  intro hg
  have hp : p.Prime := Fact.out
  have hr : r.Prime := Fact.out
  have hy : orderOf (g ^ r) = p := by
    rw [orderOf_pow' _ hr.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left r p)]
    exact Nat.mul_div_cancel p hr.pos
  have hc : orderOf (g ^ p) = r := by
    rw [orderOf_pow' _ hp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_right p r)]
    exact Nat.mul_div_cancel_left r hp.pos
  set y := g ^ r with hydef
  set c := g ^ p with hcdef
  have hcomm : Commute c y := Commute.pow_pow_self g p r
  have hyP : y ∈ P := P.pow_mem hgP r
  have hcP : c ∈ P := P.pow_mem hgP p
  obtain ⟨a, haP, haQ⟩ := Co3T.exists_conj_mem_of_full hQP hQ hyP hy
  set t := a⁻¹ * y * a with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj a⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, htdef, hy] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 haQ)
    (by rw [Nat.card_zpowers, hto])
  have hcent : Subgroup.centralizer ({t} : Set G) = Subgroup.centralizer ({line j} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq' hj
  set c' := a⁻¹ * c * a with hc'def
  have hc'P : c' ∈ P := P.mul_mem (P.mul_mem (P.inv_mem haP) hcP) haP
  have hc'o : orderOf c' = r := by
    have := (MulAut.conj a⁻¹ : G ≃* G).orderOf_eq c
    simpa [MulAut.conj_apply, hc'def, hc] using this
  have hc't : c' ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcomm.map (MulAut.conj a⁻¹ : G ≃* G).toMonoidHom
    have h2 : Commute (a⁻¹ * c * a) (a⁻¹ * y * a) := by
      simpa [MulAut.conj_apply] using this
    exact h2.eq
  have hmem : c' ∈ Subgroup.centralizer ({line j} : Set G) ⊓ P :=
    ⟨hcent ▸ hc't, hc'P⟩
  refine hline j ?_
  rw [← hc'o]
  exact Subgroup.orderOf_dvd_natCard _ hmem

theorem noOrder_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {n : ℕ}
    (h : NoOrder n H) : NoOrder n G := fun g hg => h (e g) (by rwa [MulEquiv.orderOf_eq])

theorem noOrder_of_conj_class {G : Type*} [Group G] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] {c : G} (hconj : ∀ s : G, orderOf s = p → IsConj c s)
    (hr : ¬ r ∣ Nat.card ↥(Subgroup.centralizer ({c} : Set G))) : NoOrder (p * r) G := by
  intro g hg
  have hp : p.Prime := Fact.out
  have hrp : r.Prime := Fact.out
  have hy : orderOf (g ^ r) = p := by
    rw [orderOf_pow' _ hrp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left r p)]
    exact Nat.mul_div_cancel p hrp.pos
  have ht : orderOf (g ^ p) = r := by
    rw [orderOf_pow' _ hp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_right p r)]
    exact Nat.mul_div_cancel_left r hp.pos
  obtain ⟨u, hu⟩ := isConj_iff.1 (hconj (g ^ r) hy)
  have hcomm : Commute (u⁻¹ * g ^ p * u) c := by
    have h1 : Commute (g ^ p) (g ^ r) := Commute.pow_pow_self g p r
    have h2 := h1.map (MulAut.conj u⁻¹ : G ≃* G).toMonoidHom
    have hc' : c = u⁻¹ * g ^ r * u := by rw [← hu]; group
    rw [hc']
    simpa [MulAut.conj_apply] using h2
  have hmem : u⁻¹ * g ^ p * u ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.eq
  have hord : orderOf (u⁻¹ * g ^ p * u) = r := by
    have := (MulAut.conj u⁻¹ : G ≃* G).orderOf_eq (g ^ p)
    simpa [MulAut.conj_apply, ht] using this
  apply hr
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard _ hmem

theorem noOrder_two_mul_of_involution_centralizer {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime)
    (h : ∀ t : G, orderOf t = 2 → ¬ p ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set G))) :
    NoOrder (2 * p) G := by
  intro g hg
  have ht : orderOf (g ^ p) = 2 := by
    rw [orderOf_pow' _ hp.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left p 2)]
    exact Nat.mul_div_cancel 2 hp.pos
  have hy : orderOf (g ^ 2) = p := by
    rw [orderOf_pow' _ two_ne_zero, hg, Nat.gcd_eq_right (dvd_mul_right 2 p)]
    exact Nat.mul_div_cancel_left p two_pos
  have hmem : g ^ 2 ∈ Subgroup.centralizer ({g ^ p} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_pow_self g 2 p).eq
  refine h (g ^ p) ht ?_
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [hy] at this

theorem noOrder_mul_of_noOrder {G : Type*} [Group G] {n k : ℕ} (hk : 0 < k) (h : NoOrder n G) :
    NoOrder (n * k) G := by
  intro g hg
  apply h (g ^ k)
  rw [orderOf_pow' _ hk.ne', hg, Nat.gcd_eq_right (dvd_mul_left k n)]
  exact Nat.mul_div_cancel n hk

end CFSG.HardMathSupport.Dickson.Sec6.I1431
