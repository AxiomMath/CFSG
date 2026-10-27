module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalBSwap
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalA

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB

open Subgroup JankoTwelve JankoFinal

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_two {g x : G} (hg : orderOf g = 2) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk <;> simp [hk]

theorem ne_inv_of_orderOf_eq_three {a : G} (ha : orderOf a = 3) : a ≠ a⁻¹ := by
  intro h
  have h2 : a ^ 2 = 1 := by rw [sq]; nth_rw 2 [h]; exact mul_inv_cancel a
  have := orderOf_dvd_of_pow_eq_one h2
  rw [ha] at this
  exact absurd this (by norm_num)

theorem odd_orderOf_of_mem {K : Subgroup G} {n : ℕ} (hK : Nat.card K = 3 ^ n) {g : G}
    (hg : g ∈ K) : Odd (orderOf g) :=
  Odd.of_dvd_nat (Odd.pow (by decide)) (hK ▸ K.orderOf_dvd_natCard hg)

theorem comm_of_conj_eq_inv {g a : G} (hodd : Odd (orderOf g)) (h : g * a * g⁻¹ = a⁻¹) :
    g * a = a * g := by
  refine comm_of_comm_sq hodd ?_
  have h1 : g * a = a⁻¹ * g := mul_inv_eq_iff_eq_mul.mp h
  have h2 : g * a⁻¹ = a * g := by
    have h3 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h, inv_inv] at h3
    exact mul_inv_eq_iff_eq_mul.mp h3
  calc g ^ 2 * a = g * (g * a) := by rw [sq, mul_assoc]
    _ = g * a⁻¹ * g := by rw [h1, mul_assoc]
    _ = a * g ^ 2 := by rw [h2, sq, mul_assoc]

variable {z : G} {fr : JankoFrame G z} {m s : G} {W : Subgroup G}

theorem W_le_R (hW : JankoFinalW fr m W s) : W ≤ fr.R m :=
  hW.R_inf_centralizer ▸ inf_le_left

theorem W_le_centralizer_s (hW : JankoFinalW fr m W s) : W ≤ centralizer ({s} : Set G) :=
  hW.R_inf_centralizer ▸ inf_le_right

theorem I_le_W (hW : JankoFinalW fr m W s) : fr.I ≤ W :=
  hW.W_inf_N ▸ inf_le_left

theorem R_le_UK (hW : JankoFinalW fr m W s) : fr.R m ≤ fr.U ⊔ fr.K :=
  sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hW.choiceM.mem_K))

variable [Finite G]

theorem P3bar_le_W (h : Hyp fr) (hW : JankoFinalW fr m W s) : fr.P3bar ≤ W :=
  ((le_sup_left : fr.P3bar ≤ fr.P3bar ⊔ fr.P3bbar).trans (S_le_I h)).trans (I_le_W hW)

theorem s_mem_W (h : Hyp fr) (hW : JankoFinalW fr m W s) : s ∈ W := by
  rw [hW.W_eq]
  exact mem_sup_left ⟨h.N_le_U (h.E_le_N hW.s_mem_E), mem_centralizer_singleton_iff.mpr rfl⟩

theorem s_mem_center (h : Hyp fr) (hW : JankoFinalW fr m W s) :
    s ∈ W ⊓ centralizer (W : Set G) :=
  ⟨s_mem_W h hW, mem_centralizer_iff.mpr fun _ hw =>
    mem_centralizer_singleton_iff.mp (W_le_centralizer_s hW hw)⟩

theorem P3bar_le_center (h : Hyp fr) (hW : JankoFinalW fr m W s) :
    fr.P3bar ≤ W ⊓ centralizer (W : Set G) :=
  le_inf (P3bar_le_W h hW) (hW.S_inf_centralizer_W ▸ inf_le_right)

omit [Finite G] in
theorem center_le_I (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    W ⊓ centralizer (W : Set G) ≤ fr.I := fun _ hx =>
  p12.centralizer_I ▸ centralizer_le (SetLike.coe_subset_coe.mpr (I_le_W hW)) hx.2

theorem center_le_normalizer_S (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    W ⊓ centralizer (W : Set G) ≤ normalizer (fr.S : Set G) :=
  le_normalizer_of_commute fun x hx y hy =>
    h.p11.I_comm x (center_le_I p12 hW hx) y (S_le_I h hy)

theorem card_centralizer_eq_of_mem (h : Hyp fr) (p12 : JankoProp12 fr)
    (hW : JankoFinalW fr m W s) {b : G} (hb : b ∈ (W ⊓ centralizer (W : Set G) ⊔ fr.S) ⊓ fr.E)
    (hb1 : b ≠ 1) :
    Nat.card (centralizer ({b} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 := by
  obtain ⟨hbZS, hbE⟩ := mem_inf.mp hb
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup (center_le_normalizer_S h p12 hW) hbZS
  have hxI : x ∈ fr.I := center_le_I p12 hW hx
  have hxS : x ∉ fr.S := fun hxS => by
    have : x * y ∈ fr.E ⊓ fr.S := mem_inf.mpr ⟨hbE, mul_mem hxS hy⟩
    rw [hW.E_inf_S, mem_bot] at this
    exact hb1 this
  obtain ⟨e, heE, -, heS, u, hu, hue⟩ := hW.exists_conj_mem_E x hxI hxS
  have hex : e = x * y := by
    have : e⁻¹ * (x * y) ∈ fr.E ⊓ fr.S :=
      mem_inf.mpr ⟨mul_mem (inv_mem heE) hbE, by rw [← mul_assoc]; exact mul_mem heS hy⟩
    rw [hW.E_inf_S, mem_bot] at this
    exact (inv_mul_eq_one.mp this)
  have hconj : IsConj (x * y) fr.s₃ := by
    refine hW.isConj_of_le_UK (x * y) hbE hb1 (W.map (MulAut.conj u).toMonoidHom) ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      have hwx : w * x = x * w := mem_centralizer_iff.mp hx.2 w hw
      refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
      · have hu' : u ∈ fr.U ⊔ fr.K := mem_sup_left hu
        exact mul_mem (mul_mem hu' (R_le_UK hW (W_le_R hW hw))) (inv_mem hu')
      · rw [← hex, ← hue]
        change u * w * u⁻¹ * (u * x * u⁻¹) = u * x * u⁻¹ * (u * w * u⁻¹)
        calc u * w * u⁻¹ * (u * x * u⁻¹) = u * (w * x) * u⁻¹ := by group
          _ = u * (x * w) * u⁻¹ := by rw [hwx]
          _ = u * x * u⁻¹ * (u * w * u⁻¹) := by group
    · rw [card_map_of_injective (MulAut.conj u).injective, hW.card_W]
  exact (h.p7.isConj_s₃_iff z h.set.orderOf_z (x * y) (fr.E_le hbE)
    (fr.E_pow_three _ hbE)).mp hconj

theorem card_proj_le (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    Nat.card ((W ⊓ centralizer (W : Set G) ⊔ fr.S) ⊓ fr.E : Subgroup G) ≤ 3 := by
  set B := (W ⊓ centralizer (W : Set G) ⊔ fr.S) ⊓ fr.E with hB
  have hdvd : Nat.card B ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← fr.card_E]
    exact card_dvd_of_le inf_le_right
  obtain ⟨k, hk, hBk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    apply hlt
    rw [hBk]
    interval_cases k <;> norm_num
  obtain ⟨C, hC, -, hCB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := ⊥) (L := B) (by simp) (hBk ▸ pow_dvd_pow 3 hk2) bot_le
  obtain ⟨x, hxC, hx1, hx⟩ :=
    fr.exists_ne_type_s₃ C (hCB.trans inf_le_right) (by rw [hC]; norm_num)
  exact hx (card_centralizer_eq_of_mem h p12 hW (hCB hxC) hx1)

theorem proj_eq (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    (W ⊓ centralizer (W : Set G) ⊔ fr.S) ⊓ fr.E = zpowers s := by
  refine (eq_of_le_of_card_ge ?_ ?_).symm
  · exact zpowers_le.mpr (mem_inf.mpr ⟨mem_sup_left (s_mem_center h hW), hW.s_mem_E⟩)
  · rw [Nat.card_zpowers, hW.orderOf_s]
    exact card_proj_le h p12 hW

theorem center_W_eq (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    W ⊓ centralizer (W : Set G) = zpowers s ⊔ fr.P3bar := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (zpowers_le.mpr (s_mem_center h hW)) (P3bar_le_center h hW))
  by_cases hxS : x ∈ fr.S
  · refine mem_sup_right ?_
    rw [← hW.S_inf_centralizer_W]
    exact mem_inf.mpr ⟨hxS, hx.2⟩
  obtain ⟨e, heE, -, heS, -⟩ := hW.exists_conj_mem_E x (center_le_I p12 hW hx) hxS
  have heB : e ∈ (W ⊓ centralizer (W : Set G) ⊔ fr.S) ⊓ fr.E := by
    refine mem_inf.mpr ⟨?_, heE⟩
    have he : e = x * (e⁻¹ * x)⁻¹ := by group
    rw [he]
    exact mul_mem (mem_sup_left hx) (mem_sup_right (inv_mem heS))
  rw [proj_eq h p12 hW] at heB
  have heZ : e ∈ W ⊓ centralizer (W : Set G) := zpowers_le.mpr (s_mem_center h hW) heB
  have hP : e⁻¹ * x ∈ fr.P3bar := by
    rw [← hW.S_inf_centralizer_W]
    exact mem_inf.mpr ⟨heS, (mul_mem (inv_mem heZ) hx).2⟩
  have hx' : x = e * (e⁻¹ * x) := by group
  rw [hx']
  exact mul_mem (mem_sup_left heB) (mem_sup_right hP)

theorem V_le_normalizer_R (h : Hyp fr) (hW : JankoFinalW fr m W s) :
    fr.V ≤ normalizer (fr.R m : Set G) := by
  rw [fr.V_eq, closure_le]
  rintro x (rfl | rfl)
  · exact h.t_mem_normalizer_R hW.choiceM.t_mul_m
  · exact h.z_mem_normalizer_R hW.choiceM.mem_K

theorem mem_V (h : Hyp fr) {v : G} (hv : v ∈ fr.V) :
    v = 1 ∨ v = fr.t ∨ v = z ∨ v = fr.t * z := by
  have htz : fr.t * z = z * fr.t := mem_centralizer_singleton_iff.mp fr.t_mem
  have hle : fr.V ≤ zpowers fr.t ⊔ zpowers z := by
    rw [fr.V_eq, closure_le]
    rintro x (rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
  have hn : zpowers fr.t ≤ normalizer (zpowers z : Set G) :=
    le_normalizer_of_commute fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow htz i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hn (hle hv)
  rcases eq_one_or_eq_of_mem_zpowers_two fr.orderOf_t ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers_two h.set.orderOf_z hb with hb | hb <;> simp [hb]

theorem z_not_mem_centralizer_P3bar (h : Hyp fr) : z ∉ centralizer (fr.P3bar : Set G) := by
  intro hz
  obtain ⟨p, hp, hp3⟩ := h.exists_P3bar_eq
  have hpP : p ∈ fr.P3bar := hp ▸ mem_zpowers p
  have h1 : p * z = z * p := mem_centralizer_iff.mp hz p hpP
  have h2 : z * p * z⁻¹ = p⁻¹ :=
    h.z_inv_of_mem_S ((le_sup_left : fr.P3bar ≤ fr.P3bar ⊔ fr.P3bbar) hpP)
  rw [← h1, mul_inv_cancel_right] at h2
  exact ne_inv_of_orderOf_eq_three hp3 h2

theorem mem_W_of_comm (h : Hyp fr) (hW : JankoFinalW fr m W s) {g : G} (hgs : g * s = s * g)
    (hgP : g ∈ centralizer (fr.P3bar : Set G)) : g ∈ W := by
  have hm := hW.choiceM
  have hN : g ∈ fr.V ⊔ fr.R m := by
    rw [sup_comm, ← hm.normalizer_P3bar]
    exact centralizer_le_normalizer _ hgP
  obtain ⟨v, hv, r, hr, rfl⟩ := exists_mul_of_mem_sup (V_le_normalizer_R h hW) hN
  have hrP := h.R_le_centralizer_P3bar hm.mem_centralizer hr
  have hvP : v ∈ centralizer (fr.P3bar : Set G) := by
    have hv' : v = v * r * r⁻¹ := by group
    rw [hv']
    exact mul_mem hgP (inv_mem hrP)
  have htP := h.t_mem_centralizer_P3bar
  rcases mem_V h hv with rfl | rfl | rfl | rfl
  · rw [one_mul] at hgs ⊢
    rw [← hW.R_inf_centralizer]
    exact mem_inf.mpr ⟨hr, mem_centralizer_singleton_iff.mpr hgs⟩
  · exfalso
    have htinv : fr.t⁻¹ = fr.t := inv_eq_of_mul_eq_one_right (by
      rw [← sq, ← fr.orderOf_t, pow_orderOf_eq_one])
    have hrs : r * s * r⁻¹ = s⁻¹ := by
      have h1 : r * s * r⁻¹ = fr.t⁻¹ * (fr.t * r * s) * r⁻¹ := by group
      have h2 : fr.t⁻¹ * (s * (fr.t * r)) * r⁻¹ = fr.t⁻¹ * s * fr.t := by group
      have h3 := hW.t_mul_s
      rw [hgs, h2] at h1
      rw [h1]
      rw [htinv] at h3 ⊢
      exact h3
    have hodd := odd_orderOf_of_mem (h.card_R hm.mem_K hm.orderOf_m) hr
    have hc := comm_of_conj_eq_inv hodd hrs
    rw [hc, mul_inv_cancel_right] at hrs
    exact ne_inv_of_orderOf_eq_three hW.orderOf_s hrs
  · exact absurd hvP (z_not_mem_centralizer_P3bar h)
  · refine absurd ?_ (z_not_mem_centralizer_P3bar h)
    have hz := mul_mem (inv_mem htP) hvP
    rwa [inv_mul_cancel_left] at hz

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB
