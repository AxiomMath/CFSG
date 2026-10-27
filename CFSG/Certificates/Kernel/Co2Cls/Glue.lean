module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.KC.Co2Cls

open Subgroup

section Groups

variable {G : Type*} [Group G]

theorem card_conj_mul (T : Subgroup G) (a : G) :
    Nat.card {y : G // ∃ g ∈ T, g * a = y * g} * Nat.card (T ⊓ centralizer {a} : Subgroup G) =
      Nat.card T := by
  set S : Subgroup T := (T ⊓ centralizer {a}).subgroupOf T
  have hS : Nat.card S = Nat.card (T ⊓ centralizer {a} : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmem : ∀ x : T, x ∈ S ↔ (x : G) * a = a * x := by
    intro x
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [← hS, ← card_mul_index S, mul_comm, index_eq_card]
  congr 1
  symm
  apply Nat.card_congr
  have key : ∀ g h : T, (g : G) * a * (g : G)⁻¹ = h * a * (h : G)⁻¹ ↔ g⁻¹ * h ∈ S := by
    intro g h
    rw [hmem]
    push_cast
    constructor
    · intro e
      calc (g : G)⁻¹ * h * a = (g : G)⁻¹ * (h * a * (h : G)⁻¹) * h := by group
        _ = (g : G)⁻¹ * (g * a * (g : G)⁻¹) * h := by rw [e]
        _ = a * ((g : G)⁻¹ * h) := by group
    · intro e
      calc (g : G) * a * (g : G)⁻¹ = g * (a * ((g : G)⁻¹ * h)) * (h : G)⁻¹ := by group
        _ = g * ((g : G)⁻¹ * h * a) * (h : G)⁻¹ := by rw [e]
        _ = h * a * (h : G)⁻¹ := by group
  let f : T ⧸ S → {y : G // ∃ g ∈ T, g * a = y * g} :=
    Quotient.lift (fun g : T => ⟨g * a * (g : G)⁻¹, g, g.2, by group⟩) fun g h hr =>
      Subtype.ext ((key g h).2 (QuotientGroup.leftRel_apply.1 hr))
  refine Equiv.ofBijective f ⟨fun p q => ?_, fun ⟨y, g, hg, e⟩ => ⟨QuotientGroup.mk ⟨g, hg⟩, ?_⟩⟩
  · induction p using QuotientGroup.induction_on
    induction q using QuotientGroup.induction_on
    intro e
    exact QuotientGroup.eq.2 ((key _ _).1 (congrArg Subtype.val e))
  · apply Subtype.ext
    change g * a * g⁻¹ = y
    rw [e]
    group

theorem dvd_of_orderOf (H : Subgroup G) {y w : G} (hw : w ∈ H) (hc : w * y = y * w) {p : ℕ}
    (ho : orderOf w = p) : p ∣ Nat.card (H ⊓ centralizer {y} : Subgroup G) := by
  have hm : w ∈ H ⊓ centralizer {y} := ⟨hw, mem_centralizer_singleton_iff.2 hc⟩
  rw [← ho, ← Subgroup.orderOf_mk w hm]
  exact orderOf_dvd_natCard _

theorem nine_dvd_card {K : Type*} [Group K] [Finite K] {u v : K} (huv : u * v = v * u)
    (ou : orderOf u = 3) (ov : orderOf v = 3) (h1 : v ≠ u) (h2 : v ≠ u * u) : 9 ∣ Nat.card K := by
  classical
  set A := closure ({u, v} : Set K)
  have hcomm : ∀ x ∈ A, x * u = u * x ∧ x * v = v * x := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨rfl, huv⟩
      · exact ⟨huv.symm, rfl⟩
    | one => simp
    | mul x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [mul_assoc, hy.1, ← mul_assoc, hx.1, mul_assoc]
      · rw [mul_assoc, hy.2, ← mul_assoc, hx.2, mul_assoc]
    | inv x _ hx => exact ⟨(Commute.inv_left hx.1).eq, (Commute.inv_left hx.2).eq⟩
  have hab : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := by
    intro x hx z hz
    induction hz using closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact (hcomm x hx).1
      · exact (hcomm x hx).2
    | one => simp
    | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    | inv z _ hz => exact (Commute.inv_right hz).eq
  have hcube : ∀ x ∈ A, x ^ 3 = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [← ou]
        exact pow_orderOf_eq_one _
      · rw [← ov]
        exact pow_orderOf_eq_one _
    | one => simp
    | mul x y hx' hy' hx hy => rw [(Commute.mul_pow (hab x hx' y hy') 3), hx, hy, one_mul]
    | inv x _ hx => rw [inv_pow, hx, inv_one]
  have hp : IsPGroup 3 A := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hcube x.1 x.2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hle : zpowers u ≤ A := zpowers_le.2 (subset_closure (by simp))
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h3 : Nat.card A ≤ Nat.card (zpowers u) := by
      rw [hn, Nat.card_zpowers, ou]
      calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    have he := eq_of_le_of_card_ge hle h3
    have hv : v ∈ zpowers u := by
      rw [he]
      exact subset_closure (by simp)
    rw [mem_zpowers_iff_mem_range_orderOf, ou, Finset.mem_image] at hv
    obtain ⟨k, hk, e⟩ := hv
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at e
      rw [← e, orderOf_one] at ov
      omega
    · exact h1 (by rw [← e, pow_one])
    · exact h2 (by rw [← e, pow_two])
  have h9 : 9 ∣ Nat.card A := by
    rw [hn]
    exact (pow_dvd_pow 3 hn2 : 3 ^ 2 ∣ 3 ^ n)
  exact h9.trans (card_subgroup_dvd_card A)

theorem nine_dvd [Finite G] (H : Subgroup G) {y U V : G} (hU : U ∈ H) (hV : V ∈ H)
    (hUy : U * y = y * U) (hVy : V * y = y * V) (hUV : U * V = V * U) (oU : orderOf U = 3)
    (oV : orderOf V = 3) (h1 : V ≠ U) (h2 : V ≠ U * U) :
    9 ∣ Nat.card (H ⊓ centralizer {y} : Subgroup G) := by
  have mU : U ∈ H ⊓ centralizer {y} := ⟨hU, mem_centralizer_singleton_iff.2 hUy⟩
  have mV : V ∈ H ⊓ centralizer {y} := ⟨hV, mem_centralizer_singleton_iff.2 hVy⟩
  refine nine_dvd_card (u := ⟨U, mU⟩) (v := ⟨V, mV⟩) (Subtype.ext hUV) ?_ ?_ ?_ ?_
  · rw [← Subgroup.orderOf_mk U mU] at oU
    exact oU
  · rw [← Subgroup.orderOf_mk V mV] at oV
    exact oV
  · exact fun e => h1 (congrArg Subtype.val e)
  · exact fun e => h2 (congrArg Subtype.val e)

theorem two_pow_dvd [Finite G] {H T : Subgroup G} (hTH : T ≤ H) (hT : ∀ x ∈ T, x ^ 32 = 1)
    {t : ℕ} (hTc : 2 ^ t ≤ Nat.card T) (y : G) (O : ℕ → G) {m s : ℕ}
    (hO : ∀ g ∈ T, ∃ b < m, O b * g = g * y) (hms : m * 2 ^ s = 2 ^ t) :
    2 ^ s ∣ Nat.card (H ⊓ centralizer {y} : Subgroup G) := by
  classical
  have hcm := card_conj_mul T y
  have horb : Nat.card {z : G // ∃ g ∈ T, g * y = z * g} ≤ m := by
    have hb : ∀ z : {z : G // ∃ g ∈ T, g * y = z * g}, ∃ b, b < m ∧ O b = z := by
      rintro ⟨z, g, hg, e⟩
      obtain ⟨b, hb, e2⟩ := hO g hg
      refine ⟨b, hb, ?_⟩
      have : O b * g = z * g := e2.trans e
      exact mul_right_cancel this
    let f : {z : G // ∃ g ∈ T, g * y = z * g} → Fin m := fun z =>
      ⟨Classical.choose (hb z), (Classical.choose_spec (hb z)).1⟩
    have hf : Function.Injective f := by
      intro z w e
      have e1 := (Classical.choose_spec (hb z)).2
      have e2 := (Classical.choose_spec (hb w)).2
      have e3 : Classical.choose (hb z) = Classical.choose (hb w) := congrArg Fin.val e
      apply Subtype.ext
      rw [← e1, ← e2, e3]
    simpa using Nat.card_le_card_of_injective f hf
  have hp : IsPGroup 2 (T ⊓ centralizer {y} : Subgroup G) := fun x => ⟨5, by
    apply Subtype.ext
    simpa using hT x.1 x.2.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hp
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hms
      exact absurd hms.symm (by positivity)
    · exact h
  have hse : s ≤ e := by
    have h1 : m * 2 ^ s ≤ m * 2 ^ e := by
      rw [hms]
      calc 2 ^ t ≤ Nat.card T := hTc
        _ = _ := hcm.symm
        _ ≤ m * 2 ^ e := by
          rw [he]
          exact Nat.mul_le_mul_right _ horb
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h1 hm)
  calc 2 ^ s ∣ 2 ^ e := pow_dvd_pow 2 hse
    _ = _ := he.symm
    _ ∣ _ := card_dvd_of_le (inf_le_inf_right _ hTH)

theorem class_card [Finite G] (H : Subgroup G) {a y : G} (hy : ∃ h ∈ H, h * a = y * h) {N c : ℕ}
    (hN : N ≤ Nat.card {x : G // ∃ g ∈ H, g * a = x * g})
    (hc : c ∣ Nat.card (H ⊓ centralizer {y} : Subgroup G)) (hH : N * c = Nat.card H) :
    Nat.card {x : G // ∃ g ∈ H, g * a = x * g} = N ∧
      Nat.card (H ⊓ centralizer {a} : Subgroup G) = c := by
  obtain ⟨h, hh, ehy⟩ := hy
  have hset : (fun x => ∃ g ∈ H, g * a = x * g) = (fun x => ∃ g ∈ H, g * y = x * g) := by
    funext x
    apply propext
    constructor
    · rintro ⟨g, hg, e⟩
      refine ⟨g * h⁻¹, H.mul_mem hg (H.inv_mem hh), ?_⟩
      have ey : y = h * a * h⁻¹ := by rw [ehy]; group
      rw [ey]
      calc g * h⁻¹ * (h * a * h⁻¹) = g * a * h⁻¹ := by group
        _ = x * g * h⁻¹ := by rw [e]
        _ = x * (g * h⁻¹) := by group
    · rintro ⟨g, hg, e⟩
      refine ⟨g * h, H.mul_mem hg hh, ?_⟩
      calc g * h * a = g * (h * a) := by group
        _ = g * (y * h) := by rw [ehy]
        _ = g * y * h := by group
        _ = x * (g * h) := by rw [e]; group
  have ha := card_conj_mul H a
  have hy' := card_conj_mul H y
  rw [← hset] at hy'
  set A := Nat.card {x : G // ∃ g ∈ H, g * a = x * g}
  set Ca := Nat.card (H ⊓ centralizer {a} : Subgroup G)
  set Cy := Nat.card (H ⊓ centralizer {y} : Subgroup G)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hCy : 0 < Cy := Nat.card_pos
  have hcle : c ≤ Cy := Nat.le_of_dvd hCy hc
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hH
      omega
    · exact h0
  have hA : A = N := by
    by_contra hne
    have hlt : N < A := lt_of_le_of_ne hN (Ne.symm hne)
    have : N * c < A * Cy := calc
      N * c < A * c := Nat.mul_lt_mul_of_pos_right hlt hcpos
      _ ≤ A * Cy := Nat.mul_le_mul_left _ hcle
    omega
  have hApos : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · rw [h0, zero_mul] at ha
      omega
    · exact h0
  refine ⟨hA, ?_⟩
  have e1 : A * Ca = A * c := by
    rw [ha, ← hH, hA]
  exact Nat.eq_of_mul_eq_mul_left hApos e1

end Groups

section Ranks

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]

@[expose] noncomputable def kappa (r x : Matrix n n R) : ℕ × ℕ × ℕ :=
  ((x + 1).rank, (x * r + 1).rank, ((r + 1) * (x + 1)).rank)

theorem rank_eq_of_mul {g a b : Matrix n n R} (hg : IsUnit g) (h : a * g = g * b) :
    a.rank = b.rank := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  rw [← Matrix.rank_mul_eq_left_of_isUnit_det g a hd, h, Matrix.rank_mul_eq_right_of_isUnit_det g b hd]

theorem kappa_conj {r g x y : Matrix n n R} (hg : IsUnit g) (hr : g * r = r * g)
    (h : g * x = y * g) : kappa r y = kappa r x := by
  have e1 : (y + 1) * g = g * (x + 1) := by rw [add_mul, mul_add, one_mul, mul_one, h]
  have e2 : (y * r + 1) * g = g * (x * r + 1) := calc
    (y * r + 1) * g = y * (r * g) + g := by rw [add_mul, one_mul, mul_assoc]
    _ = (y * g) * r + g := by rw [← hr, mul_assoc]
    _ = (g * x) * r + g := by rw [h]
    _ = g * (x * r + 1) := by rw [mul_add, mul_one, mul_assoc]
  have e3 : ((r + 1) * (y + 1)) * g = g * ((r + 1) * (x + 1)) := calc
    ((r + 1) * (y + 1)) * g = (r + 1) * (g * (x + 1)) := by rw [mul_assoc, e1]
    _ = ((r + 1) * g) * (x + 1) := by rw [mul_assoc]
    _ = (g * (r + 1)) * (x + 1) := by
      have hrg : (r + 1) * g = g * (r + 1) := by rw [add_mul, mul_add, hr, one_mul, mul_one]
      rw [hrg]
    _ = g * ((r + 1) * (x + 1)) := by rw [mul_assoc]
  unfold kappa
  rw [rank_eq_of_mul hg e1, rank_eq_of_mul hg e2, rank_eq_of_mul hg e3]

end Ranks

end CFSG.KC.Co2Cls

end
