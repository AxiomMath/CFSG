module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Dih
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Sixteen

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u : G}

@[expose] def TConj (t s : G) : Prop := ∃ g : G, g * t * g⁻¹ = s

theorem tConj_self (t : G) : TConj t t := ⟨1, by group⟩

theorem TConj.conj {s : G} (hs : TConj t s) (p : G) : TConj t (p * s * p⁻¹) := by
  obtain ⟨g, rfl⟩ := hs
  exact ⟨p * g, by group⟩

variable (h : SecTwoHyp G t u)

include h

theorem card_le_four_conj {s : G} (hs : TConj t s) {E : Subgroup G} (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hEs : E ≤ centralizer ({s} : Set G)) : Nat.card E ≤ 4 := by
  obtain ⟨g, rfl⟩ := hs
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hcard : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
  have hE' : ∀ e ∈ E.map f, e ^ 2 = 1 := by
    rintro e ⟨a, ha, rfl⟩
    change (g⁻¹ * a * g⁻¹⁻¹) ^ 2 = 1
    rw [conj_pow, hE a ha]; group
  have hEt : E.map f ≤ centralizer ({t} : Set G) := by
    rintro e ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hEs ha)
    change g⁻¹ * a * g⁻¹⁻¹ * t = t * (g⁻¹ * a * g⁻¹⁻¹)
    calc g⁻¹ * a * g⁻¹⁻¹ * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [h1]
      _ = t * (g⁻¹ * a * g⁻¹⁻¹) := by group
  rw [← hcard]
  exact h.card_le_four_of_le_centralizer hE' hEt

theorem exists_four_group :
    ∃ E : Subgroup G, E ≤ secTwoR t u ∧ t ∈ E ∧ u ^ 2 ∈ E ∧ (∀ e ∈ E, e ^ 2 = 1) ∧
      Nat.card E = 4 := by
  classical
  have hz : u ^ 2 ∈ secTwoR t u := pow_mem SecTwoHyp.u_mem_R 2
  set E : Subgroup G := closure ({t, u ^ 2} : Set G) with hE
  have htE : t ∈ E := subset_closure (by simp)
  have hzE : u ^ 2 ∈ E := subset_closure (by simp)
  have hER : E ≤ secTwoR t u := by
    rw [hE, closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact SecTwoHyp.t_mem_R
    · exact hz
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := by
    intro e he
    refine closure_induction (p := fun e _ => e ^ 2 = 1) ?_ (one_pow 2) ?_ ?_ he
    · intro g hg
      rcases hg with rfl | rfl
      · exact h.t_sq
      · exact h.z_sq
    · intro a b ha hb ha2 hb2
      have hab : a * b = b * a := h.mul_comm_of_mem_R (hER ha) (hER hb)
      rw [(show Commute a b from hab).mul_pow, ha2, hb2, one_mul]
    · intro a ha ha2
      rw [inv_pow, ha2, inv_one]
  have hle : Nat.card E ≤ 4 := by
    refine h.card_le_four_of_le_centralizer hE2 ?_
    exact hER.trans h.R_le_centralizer
  have hge : 4 ≤ Nat.card E := by
    let S : Finset G := {1, t, u ^ 2, t * u ^ 2}
    have h1t : (1 : G) ≠ t := h.t_ne_one.symm
    have h1z : (1 : G) ≠ u ^ 2 := h.z_ne_one.symm
    have htz : t ≠ u ^ 2 := h.sq_ne.symm
    have h1tz : (1 : G) ≠ t * u ^ 2 := by
      intro h0
      apply htz
      have : t = (u ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h0.symm
      rw [this, h.z_inv]
    have httz : t ≠ t * u ^ 2 := by
      intro h0
      apply h.z_ne_one
      exact (mul_eq_left.mp h0.symm)
    have hztz : u ^ 2 ≠ t * u ^ 2 := by
      intro h0
      apply h.t_ne_one
      exact (mul_eq_right.mp h0.symm)
    have hS : S.card = 4 := by
      simp [S, Finset.card_insert_of_notMem, h1t, h1z, h1tz, htz, httz, hztz]
    have hsub : (S : Set G) ⊆ (E : Set G) := by
      intro g hg
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact one_mem E
      · exact htE
      · exact hzE
      · exact mul_mem htE hzE
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hS] at this
    rwa [← Nat.card_coe_set_eq] at this
  exact ⟨E, hER, htE, hzE, hE2, le_antisymm hle hge⟩

theorem four_group_isElemAbelian {E : Subgroup G} (hER : E ≤ secTwoR t u)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (h.mul_comm_of_mem_R (hER a.2) (hER b.2))⟩⟩, hE2⟩

end CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp


namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

section ElemAbelian

variable {K : Type*} [Group K]

theorem elemAbelian_comm {V : Subgroup K} (hV : IsElemAbelian 2 V) {a b : K} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_fixed_of_elemAbelian {t : K} (ht : t * t = 1) {V : Subgroup K}
    (hV : IsElemAbelian 2 V) (hn : ∀ v ∈ V, t * v * t⁻¹ ∈ V) {a : K} (ha : a ∈ V) (ha1 : a ≠ 1) :
    ∃ v ∈ V, v ≠ 1 ∧ t * v * t⁻¹ = v := by
  by_cases hfix : t * a * t⁻¹ = a
  · exact ⟨a, ha, ha1, hfix⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hb : t * a * t⁻¹ ∈ V := hn a ha
  have ha2 : a * a = 1 := by rw [← sq]; exact hV.2 a ha
  refine ⟨a * (t * a * t⁻¹), mul_mem ha hb, ?_, ?_⟩
  · intro h1
    apply hfix
    have : t * a * t⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right ha2
  · have h2 : t * (t * a * t⁻¹) * t⁻¹ = a := by
      calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
        _ = a := by rw [ht, ← mul_inv_rev, ht, inv_one]; group
    calc t * (a * (t * a * t⁻¹)) * t⁻¹
        = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by group
      _ = (t * a * t⁻¹) * a := by rw [h2]
      _ = a * (t * a * t⁻¹) := elemAbelian_comm hV hb ha

theorem four_group_elements [Finite K] {V : Subgroup K} (hV : IsElemAbelian 2 V)
    (h4 : Nat.card V = 4) {z v : K} (hz : z ∈ V) (hv : v ∈ V) (hz1 : z ≠ 1) (hv1 : v ≠ 1)
    (hvz : v ≠ z) : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = v * z := by
  classical
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, haz, hav, havz⟩ := hcon
  have hz2 : z * z = 1 := by rw [← sq]; exact hV.2 z hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hvz1 : v * z ≠ 1 := by
    intro h0
    apply hvz
    have : v = z⁻¹ := eq_inv_of_mul_eq_one_left h0
    rw [this, hzi]
  have hvzz : v * z ≠ z := by
    intro h0
    apply hv1
    exact mul_eq_right.mp h0
  have hvzv : v * z ≠ v := by
    intro h0
    apply hz1
    exact mul_eq_left.mp h0
  let S : Finset K := {1, z, v, v * z, a}
  have hS : S.card = 5 := by
    simp [S, Finset.card_insert_of_notMem, hz1, hz1.symm, hv1, hv1.symm, hvz, hvz.symm, hvz1,
      hvz1.symm, hvzz, hvzz.symm, hvzv, hvzv.symm, ha1, ha1.symm, haz, haz.symm, hav, hav.symm,
      havz, havz.symm]
  have hsub : (S : Set K) ⊆ (V : Set K) := by
    intro g hg
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact one_mem V
    · exact hz
    · exact hv
    · exact mul_mem hv hz
    · exact ha
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hS, ← Nat.card_coe_set_eq] at this
  have h4' : Nat.card (V : Set K) = 4 := h4
  omega

end ElemAbelian

open CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

structure SixACtx {G : Type} [Group G] (t u : G) (P V : Subgroup G) : Prop where
  secTwo : SecTwoHyp G t u
  pgroup : IsPGroup 2 P
  R_le : secTwoR t u ≤ P
  no_meet : ∀ W : Subgroup G, W ≤ P → (∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W) →
    IsElemAbelian 2 W → Nat.card W = 4 → ∀ w ∈ W, ∀ g : G, g * t * g⁻¹ ≠ w
  V_le : V ≤ P
  V_norm : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V
  V_elem : IsElemAbelian 2 V
  V_card : Nat.card V = 4

namespace SixACtx

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} (C : SixACtx t u P V)

include C

theorem R_ne : secTwoR t u ≠ P := by
  intro hRP'
  obtain ⟨E, hER, htE, -, hE2, hE4⟩ := C.secTwo.exists_four_group
  refine C.no_meet E (hER.trans C.R_le) ?_ (C.secTwo.four_group_isElemAbelian hER hE2) hE4 t
    htE 1 (by group)
  intro p hp e he
  have hpR : p ∈ secTwoR t u := hRP' ▸ hp
  have hc : p * e = e * p := C.secTwo.mul_comm_of_mem_R hpR (hER he)
  have : p * e * p⁻¹ = e := by rw [hc]; group
  rw [this]
  exact he

theorem z_central {p : G} (hp : p ∈ P) : p * u ^ 2 = u ^ 2 * p :=
  C.secTwo.z_mem_center C.pgroup C.R_le hp

theorem tz_tConj : TConj t (t * u ^ 2) := by
  obtain ⟨s, -, -, -, hs⟩ := C.secTwo.exists_conj_t_eq C.pgroup C.R_le C.R_ne
  exact ⟨s, hs⟩

theorem z_not_tConj : ¬ TConj t (u ^ 2) := by
  rintro ⟨g, hg⟩
  apply C.secTwo.conj_z_ne_t g⁻¹
  rw [← hg]; group

theorem V_no_tConj {v : G} (hv : v ∈ V) : ¬ TConj t v := by
  rintro ⟨g, hg⟩
  exact C.no_meet V C.V_le C.V_norm C.V_elem C.V_card v hv g hg

theorem V_ne_bot : V ≠ ⊥ := by
  intro h0
  have := C.V_card
  rw [h0, Subgroup.card_bot] at this
  omega

theorem t_norm_V {v : G} (hv : v ∈ V) : t * v * t⁻¹ ∈ V :=
  C.V_norm t (C.R_le SecTwoHyp.t_mem_R) v hv

theorem z_mem_V : u ^ 2 ∈ V := by
  have h := C.secTwo
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp C.V_ne_bot
    exact ⟨a, ha, fun h' => ha1 (Subtype.ext h')⟩
  obtain ⟨v, hv, hv1, hvt⟩ := exists_fixed_of_elemAbelian h.t_mul_t C.V_elem
    (fun v hv => C.t_norm_V hv) ha ha1
  have hcomm : v * t = t * v := by
    calc v * t = (t * v * t⁻¹) * t := by rw [hvt]
      _ = t * v := by group
  have hvR : v ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le (C.V_le hv) hcomm
  have hv2 : v ^ 2 = 1 := C.V_elem.2 v hv
  rcases h.eq_of_mem_R_of_sq_eq_one hvR hv2 with h1 | h1 | h1 | h1
  · exact absurd h1 hv1
  · exact absurd (h1 ▸ tConj_self t) (C.V_no_tConj hv)
  · exact h1 ▸ hv
  · exact absurd (h1 ▸ C.tz_tConj) (C.V_no_tConj hv)

theorem exists_v : ∃ v ∈ V, v ≠ 1 ∧ v ≠ u ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (V : Set G) ⊆ {1, u ^ 2} := by
    intro g hg
    by_cases h1 : g = 1
    · exact Or.inl h1
    · exact Or.inr (hcon g hg h1)
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [C.V_card]; norm_num)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, u ^ 2} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  rw [← Nat.card_coe_set_eq] at this
  have h4 : Nat.card (V : Set G) = 4 := C.V_card
  omega

theorem V_eq {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hvz : v ≠ u ^ 2) :
    ∀ a ∈ V, a = 1 ∨ a = u ^ 2 ∨ a = v ∨ a = v * u ^ 2 :=
  four_group_elements C.V_elem C.V_card C.z_mem_V hv C.secTwo.z_ne_one hv1 hvz

theorem V_conj {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hvz : v ≠ u ^ 2) {p : G} (hp : p ∈ P) :
    p * v * p⁻¹ = v ∨ p * v * p⁻¹ = v * u ^ 2 := by
  have hmem : p * v * p⁻¹ ∈ V := C.V_norm p hp v hv
  rcases C.V_eq hv hv1 hvz _ hmem with h1 | h1 | h1 | h1
  · exfalso; apply hv1
    calc v = p⁻¹ * (p * v * p⁻¹) * p := by group
      _ = 1 := by rw [h1]; group
  · exfalso; apply hvz
    have hc : p⁻¹ * u ^ 2 = u ^ 2 * p⁻¹ := C.z_central (inv_mem hp)
    calc v = p⁻¹ * (p * v * p⁻¹) * p := by group
      _ = p⁻¹ * u ^ 2 * p := by rw [h1]
      _ = u ^ 2 := by rw [hc]; group
  · exact Or.inl h1
  · exact Or.inr h1

end SixACtx

@[expose] def nsub {G : Type} [Group G] (t u : G) (P : Subgroup G) : Subgroup G :=
  P ⊓ normalizer (secTwoR t u : Set G)

structure SixAV {G : Type} [Group G] (t u : G) (P V : Subgroup G) (v : G) : Prop
    extends SixACtx t u P V where
  v_mem : v ∈ V
  v_ne_one : v ≠ 1
  v_ne_z : v ≠ u ^ 2

namespace SixAV

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v : G}
  (C : SixAV t u P V v)

include C

theorem v_sq : v ^ 2 = 1 := C.V_elem.2 v C.v_mem

theorem v_mul_v : v * v = 1 := by rw [← sq]; exact C.v_sq

theorem v_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right C.v_mul_v

theorem v_mem_P : v ∈ P := C.V_le C.v_mem

theorem t_v : t * v * t⁻¹ = v * u ^ 2 := by
  have h := C.secTwo
  rcases C.toSixACtx.V_conj C.v_mem C.v_ne_one C.v_ne_z (C.R_le SecTwoHyp.t_mem_R) with h1 | h1
  · exfalso
    have hcomm : v * t = t * v := by
      calc v * t = (t * v * t⁻¹) * t := by rw [h1]
        _ = t * v := by group
    have hvR : v ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le C.v_mem_P hcomm
    rcases h.eq_of_mem_R_of_sq_eq_one hvR C.v_sq with h2 | h2 | h2 | h2
    · exact C.v_ne_one h2
    · exact C.V_no_tConj C.v_mem (h2 ▸ tConj_self t)
    · exact C.v_ne_z h2
    · exact C.V_no_tConj C.v_mem (h2 ▸ C.tz_tConj)
  · exact h1

theorem v_t : v * t * v⁻¹ = t * u ^ 2 := by
  have h1 : t * v = v * u ^ 2 * t := by
    have := C.t_v
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hz : u ^ 2 * t = t * u ^ 2 := (C.z_central (C.R_le SecTwoHyp.t_mem_R)).symm
  calc v * t * v⁻¹ = v * (t * v) := by rw [C.v_inv]; group
    _ = v * (v * u ^ 2 * t) := by rw [h1]
    _ = (v * v) * (u ^ 2 * t) := by group
    _ = t * u ^ 2 := by rw [C.v_mul_v, one_mul, hz]

theorem v_u_mem_R : v * u * v⁻¹ ∈ secTwoR t u := by
  have h := C.secTwo
  have hP : v * u * v⁻¹ ∈ P :=
    mul_mem (mul_mem C.v_mem_P (C.R_le SecTwoHyp.u_mem_R)) (inv_mem C.v_mem_P)
  have hz : (v * u * v⁻¹) * u ^ 2 = u ^ 2 * (v * u * v⁻¹) := C.z_central hP
  have htz : (v * u * v⁻¹) * (t * u ^ 2) = (t * u ^ 2) * (v * u * v⁻¹) := by
    rw [← C.v_t]
    calc v * u * v⁻¹ * (v * t * v⁻¹) = v * (u * t) * v⁻¹ := by group
      _ = v * (t * u) * v⁻¹ := by rw [h.commute.symm]
      _ = v * t * v⁻¹ * (v * u * v⁻¹) := by group
  have hct : (v * u * v⁻¹) * t = t * (v * u * v⁻¹) := by
    have h1 : (v * u * v⁻¹) * (t * u ^ 2) * u ^ 2 = (t * u ^ 2) * (v * u * v⁻¹) * u ^ 2 := by
      rw [htz]
    have hzz : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact h.u_pow_four
    have h2 : (v * u * v⁻¹) * (t * u ^ 2) * u ^ 2 = (v * u * v⁻¹) * t := by
      calc (v * u * v⁻¹) * (t * u ^ 2) * u ^ 2 = (v * u * v⁻¹) * t * (u ^ 2 * u ^ 2) := by group
        _ = (v * u * v⁻¹) * t := by rw [hzz, mul_one]
    have h3 : (t * u ^ 2) * (v * u * v⁻¹) * u ^ 2 = t * (v * u * v⁻¹) := by
      calc (t * u ^ 2) * (v * u * v⁻¹) * u ^ 2 = t * (u ^ 2 * (v * u * v⁻¹)) * u ^ 2 := by group
        _ = t * ((v * u * v⁻¹) * u ^ 2) * u ^ 2 := by rw [hz]
        _ = t * (v * u * v⁻¹) * (u ^ 2 * u ^ 2) := by group
        _ = t * (v * u * v⁻¹) := by rw [hzz, mul_one]
    rw [← h2, ← h3]; exact h1
  exact h.mem_R_of_commute C.pgroup C.R_le hP hct

theorem v_conj_mem_R {r : G} (hr : r ∈ secTwoR t u) : v * r * v⁻¹ ∈ secTwoR t u := by
  have hle : secTwoR t u ≤ (secTwoR t u).comap (MulAut.conj v).toMonoidHom := by
    rw [secTwoR, closure_le]
    intro g hg
    rcases hg with h1 | h1
    · change v * g * v⁻¹ ∈ secTwoR t u
      rw [h1, C.v_t]
      exact mul_mem SecTwoHyp.t_mem_R (pow_mem SecTwoHyp.u_mem_R 2)
    · change v * g * v⁻¹ ∈ secTwoR t u
      rw [h1]
      exact C.v_u_mem_R
  exact hle hr

theorem v_normalizer : v ∈ normalizer (secTwoR t u : Set G) := by
  rw [mem_normalizer_iff]
  intro r
  refine ⟨fun hr => C.v_conj_mem_R hr, fun hr => ?_⟩
  have := C.v_conj_mem_R hr
  have e : v * (v * r * v⁻¹) * v⁻¹ = r := by
    calc v * (v * r * v⁻¹) * v⁻¹ = (v * v) * r * (v⁻¹ * v⁻¹) := by group
      _ = r := by rw [C.v_mul_v, ← mul_inv_rev, C.v_mul_v, inv_one]; group
  rwa [e] at this

theorem v_sq_mem_R : v ^ 2 ∈ secTwoR t u := by rw [C.v_sq]; exact one_mem _

theorem exists_w : ∃ w : G, (w = u ∨ w = t * u) ∧ w ^ 2 = u ^ 2 ∧ v * w * v⁻¹ = w :=
  C.secTwo.exists_fixed_w C.v_normalizer C.v_t C.v_sq_mem_R

theorem mem_N_iff {g : G} (hg : g ∈ P) :
    g ∈ nsub t u P ↔ g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * u ^ 2 := by
  have h := C.secTwo
  constructor
  · intro hgN
    exact h.conj_t_of_normalizer hgN.2
  · intro hgt
    refine ⟨hg, ?_⟩
    rcases hgt with h1 | h1
    · have hcomm : g * t = t * g := by
        calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [h1]
      exact le_normalizer (h.mem_R_of_commute C.pgroup C.R_le hg hcomm)
    · have hvt : v * t * v⁻¹ = t * u ^ 2 := C.v_t
      have hP' : v⁻¹ * g ∈ P := mul_mem (inv_mem C.v_mem_P) hg
      have hcomm : (v⁻¹ * g) * t = t * (v⁻¹ * g) := by
        calc v⁻¹ * g * t = (v⁻¹ * (g * t * g⁻¹) * v) * (v⁻¹ * g) := by group
          _ = (v⁻¹ * (v * t * v⁻¹) * v) * (v⁻¹ * g) := by rw [h1, ← hvt]
          _ = t * (v⁻¹ * g) := by group
      have hrR : v⁻¹ * g ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le hP' hcomm
      have : g = v * (v⁻¹ * g) := by group
      rw [this]
      exact mul_mem C.v_normalizer (le_normalizer hrR)

theorem N_ne_P : nsub t u P ≠ P := by
  have h := C.secTwo
  intro hNP
  obtain ⟨E, hER, htE, hzE, hE2, hE4⟩ := h.exists_four_group
  refine C.no_meet E (hER.trans C.R_le) ?_ (h.four_group_isElemAbelian hER hE2) hE4 t htE 1
    (by group)
  intro p hp e he
  have hpN : p ∈ nsub t u P := by rw [hNP]; exact hp
  have htz : t * u ^ 2 ∈ E := mul_mem htE hzE
  have hpt : p * t * p⁻¹ ∈ E := by
    rcases h.conj_t_of_normalizer hpN.2 with h1 | h1
    · rw [h1]; exact htE
    · rw [h1]; exact htz
  have hpz : p * u ^ 2 * p⁻¹ = u ^ 2 := by
    have := C.z_central hp
    rw [this]; group
  rcases h.eq_of_mem_R_of_sq_eq_one (hER he) (hE2 e he) with h1 | h1 | h1 | h1
  · rw [h1]; simpa using one_mem E
  · rw [h1]; exact hpt
  · rw [h1, hpz]; exact hzE
  · rw [h1]
    have : p * (t * u ^ 2) * p⁻¹ = (p * t * p⁻¹) * (p * u ^ 2 * p⁻¹) := by group
    rw [this, hpz]
    exact mul_mem hpt hzE

theorem exists_g : ∃ g ∈ P, g ∉ nsub t u P ∧ g ∈ normalizer (nsub t u P : Set G) :=
  secTwo_exists_mem_normalizer C.pgroup inf_le_left C.N_ne_P

end SixAV

structure SixAW {G : Type} [Group G] (t u : G) (P V : Subgroup G) (v u₀ : G) : Prop
    extends SixAV t u P V v where
  hu₀ : u₀ = u ∨ u₀ = t * u
  u₀_sq : u₀ ^ 2 = u ^ 2
  v_u₀ : v * u₀ * v⁻¹ = u₀

namespace SixAW

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ : G}
  (C : SixAW t u P V v u₀)

include C

theorem u₀_mem_R : u₀ ∈ secTwoR t u := by
  rcases C.hu₀ with h1 | h1
  · rw [h1]; exact SecTwoHyp.u_mem_R
  · rw [h1]; exact mul_mem SecTwoHyp.t_mem_R SecTwoHyp.u_mem_R

theorem u₀_mem_P : u₀ ∈ P := C.R_le C.u₀_mem_R

theorem u₀_four : u₀ ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, C.u₀_sq]
  exact C.secTwo.z_sq

theorem u₀_order : orderOf u₀ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [C.u₀_sq] using C.secTwo.z_ne_one)
    (by simpa using C.u₀_four)

theorem t_u₀ : t * u₀ = u₀ * t := C.secTwo.mul_comm_of_mem_R SecTwoHyp.t_mem_R C.u₀_mem_R

theorem v_u₀' : v * u₀ = u₀ * v := by
  have := C.v_u₀
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem nrel : I21.NRel t u₀ v where
  t_sq := C.secTwo.t_sq
  w_four := C.u₀_four
  v_sq := C.v_sq
  tw := C.t_u₀
  vw := C.v_u₀'
  vt := by rw [C.v_t, C.u₀_sq]

theorem R_nf {r : G} (hr : r ∈ secTwoR t u) : ∃ a b : ℕ, r = t ^ a * u₀ ^ b :=
  C.secTwo.exists_pow_t_w C.hu₀ hr

theorem N_nf {n : G} (hn : n ∈ nsub t u P) : ∃ a b c : ℕ, n = t ^ a * u₀ ^ b * v ^ c := by
  have h := C.secTwo
  obtain ⟨hnP, hnN⟩ := hn
  rcases h.conj_t_of_normalizer hnN with h1 | h1
  · have hcomm : n * t = t * n := by
      calc n * t = (n * t * n⁻¹) * n := by group
        _ = t * n := by rw [h1]
    have hnR : n ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le hnP hcomm
    obtain ⟨a, b, hab⟩ := C.R_nf hnR
    exact ⟨a, b, 0, by rw [hab]; simp⟩
  ·
    have hvt : v * t * v⁻¹ = t * u ^ 2 := C.v_t
    have hP' : v⁻¹ * n ∈ P := mul_mem (inv_mem C.v_mem_P) hnP
    have hcomm : (v⁻¹ * n) * t = t * (v⁻¹ * n) := by
      calc v⁻¹ * n * t = (v⁻¹ * (n * t * n⁻¹) * v) * (v⁻¹ * n) := by group
        _ = (v⁻¹ * (v * t * v⁻¹) * v) * (v⁻¹ * n) := by rw [h1, ← hvt]
        _ = t * (v⁻¹ * n) := by group
    have hrR : v⁻¹ * n ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le hP' hcomm
    obtain ⟨a, b, hab⟩ := C.R_nf hrR
    refine ⟨a, b + 2 * a, 1, ?_⟩
    have h2 := C.nrel.nf_mul 0 0 1 a b 0
    simp only [pow_zero, one_mul, zero_add, mul_one, pow_one, add_zero] at h2
    calc n = v * (v⁻¹ * n) := by group
      _ = v * (t ^ a * u₀ ^ b) := by rw [hab]
      _ = t ^ a * u₀ ^ (b + 2 * 1 * a) * v := h2
      _ = t ^ a * u₀ ^ (b + 2 * a) * v ^ 1 := by rw [pow_one, mul_one]

theorem nf_mem_N (a b c : ℕ) : t ^ a * u₀ ^ b * v ^ c ∈ nsub t u P := by
  have htN : t ∈ nsub t u P := ⟨C.R_le SecTwoHyp.t_mem_R, le_normalizer SecTwoHyp.t_mem_R⟩
  have hwN : u₀ ∈ nsub t u P := ⟨C.u₀_mem_P, le_normalizer C.u₀_mem_R⟩
  have hvN : v ∈ nsub t u P := ⟨C.v_mem_P, C.v_normalizer⟩
  exact mul_mem (mul_mem (pow_mem htN a) (pow_mem hwN b)) (pow_mem hvN c)


theorem N_conj_cases {s : G} (hs : TConj t s) (hsN : s ∈ nsub t u P) :
    s = t ∨ s = t * u ^ 2 ∨ s = t * u₀ * v ∨ s = t * u₀ ^ 3 * v := by
  have h := C.secTwo
  have hssq : s ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := hs
    rw [conj_pow, h.t_sq]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    obtain ⟨g, hg⟩ := hs
    apply h.t_ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  obtain ⟨a, b, c, hab⟩ := C.N_nf hsN
  have hv2 := C.v_sq
  by_cases hc2 : c % 2 = 1
  · have hab' : s = t ^ (a % 2) * u₀ ^ (b % 4) * v ^ 1 := by
      rw [hab, I21.pow_mod_of_pow_eq_one h.t_sq a, I21.pow_mod_of_pow_eq_one C.u₀_four b,
        I21.pow_mod_of_pow_eq_one hv2 c, hc2]
    have hsq' := C.nrel.nf_sq (a % 2) (b % 4) 1
    rw [← hab', hssq] at hsq'
    have hdvd : 4 ∣ 2 * (b % 4 + 1 * (a % 2)) := by
      have := orderOf_dvd_of_pow_eq_one hsq'.symm
      rwa [C.u₀_order] at this
    have hcases : (a % 2 = 0 ∧ b % 4 = 0) ∨ (a % 2 = 0 ∧ b % 4 = 2) ∨ (a % 2 = 1 ∧ b % 4 = 1) ∨
        (a % 2 = 1 ∧ b % 4 = 3) := by omega
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      rw [h1, h2] at hab'
      have : s = v := by simpa using hab'
      exact C.V_no_tConj C.v_mem (this ▸ hs)
    · exfalso
      rw [h1, h2] at hab'
      have : s = u ^ 2 * v := by simpa [C.u₀_sq] using hab'
      exact C.V_no_tConj (mul_mem C.z_mem_V C.v_mem) (this ▸ hs)
    · right; right; left
      rw [h1, h2] at hab'
      simpa using hab'
    · right; right; right
      rw [h1, h2] at hab'
      simpa using hab'
  · have hc0 : c % 2 = 0 := by omega
    have hvc : v ^ c = 1 := by rw [I21.pow_mod_of_pow_eq_one hv2 c, hc0, pow_zero]
    have hsR : s ∈ secTwoR t u := by
      rw [hab, hvc, mul_one]
      exact mul_mem (pow_mem SecTwoHyp.t_mem_R a) (pow_mem C.u₀_mem_R b)
    rcases h.eq_of_mem_R_of_sq_eq_one hsR hssq with h1 | h1 | h1 | h1
    · exact absurd h1 hs1
    · exact Or.inl h1
    · exact absurd (h1 ▸ hs) C.z_not_tConj
    · exact Or.inr (Or.inl h1)

theorem exists_g_conj :
    ∃ g ∈ P, g ∉ nsub t u P ∧ g ∈ normalizer (nsub t u P : Set G) ∧
      (g * t * g⁻¹ = t * u₀ * v ∨ g * t * g⁻¹ = t * u₀ ^ 3 * v) := by
  obtain ⟨g, hgP, hgN, hgnorm⟩ := C.exists_g
  have htN : t ∈ nsub t u P := ⟨C.R_le SecTwoHyp.t_mem_R, le_normalizer SecTwoHyp.t_mem_R⟩
  have ht'N : g * t * g⁻¹ ∈ nsub t u P := (mem_normalizer_iff.mp hgnorm t).mp htN
  refine ⟨g, hgP, hgN, hgnorm, ?_⟩
  rcases C.N_conj_cases ⟨g, rfl⟩ ht'N with h1 | h1 | h1 | h1
  · exact absurd ((C.mem_N_iff hgP).mpr (Or.inl h1)) hgN
  · exact absurd ((C.mem_N_iff hgP).mpr (Or.inr h1)) hgN
  · exact Or.inl h1
  · exact Or.inr h1

end SixAW

structure SixAY {G : Type} [Group G] (t u : G) (P V : Subgroup G) (v u₀ y₀ : G) : Prop
    extends SixAW t u P V v u₀ where
  y₀_def : y₀ = u₀ * v ∨ y₀ = u₀ ^ 3 * v
  ty₀_conj : TConj t (t * y₀)

namespace SixAW

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ : G}
  (C : SixAW t u P V v u₀)

include C

theorem exists_y₀ : ∃ y₀ : G, SixAY t u P V v u₀ y₀ := by
  obtain ⟨g, -, -, -, hg⟩ := C.exists_g_conj
  have h := C.secTwo
  rcases hg with h1 | h1
  · refine ⟨u₀ * v, { toSixAW := C, y₀_def := Or.inl rfl, ty₀_conj := ⟨g, ?_⟩ }⟩
    rw [h1]; group
  · refine ⟨u₀ ^ 3 * v, { toSixAW := C, y₀_def := Or.inr rfl, ty₀_conj := ⟨g, ?_⟩ }⟩
    rw [h1]; group

end SixAW

namespace SixAY

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ y₀ : G}
  (C : SixAY t u P V v u₀ y₀)

include C

theorem y₀_mem_P : y₀ ∈ P := by
  have hv := C.v_mem_P
  have hu := C.u₀_mem_P
  rcases C.y₀_def with h1 | h1
  · rw [h1]; exact mul_mem hu hv
  · rw [h1]; exact mul_mem (pow_mem hu 3) hv

theorem ty₀_sq : (t * y₀) ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := C.ty₀_conj
  rw [← hg, conj_pow, C.secTwo.t_sq]; group

theorem y₀_sq : y₀ ^ 2 = u ^ 2 := by
  have h := C.nrel
  rcases C.y₀_def with h1 | h1
  · have := h.nf_sq 0 1 1
    simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero, mul_one] at this
    rw [h1, this, C.u₀_sq]
  · have := h.nf_sq 0 3 1
    simp only [pow_zero, one_mul, pow_one, mul_zero, add_zero, mul_one] at this
    rw [h1, this, show 2 * 3 = 4 + 2 by norm_num, pow_add, C.u₀_four, one_mul, C.u₀_sq]

theorem u₀_y₀ : u₀ * y₀ = y₀ * u₀ := by
  have hv : v * u₀ = u₀ * v := C.v_u₀'
  rcases C.y₀_def with h1 | h1
  · rw [h1]
    calc u₀ * (u₀ * v) = u₀ * (v * u₀) := by rw [hv]
      _ = u₀ * v * u₀ := by group
  · rw [h1]
    have h3 : v * u₀ ^ 3 = u₀ ^ 3 * v := by
      simpa using C.nrel.v_pow_w_pow 1 3
    calc u₀ * (u₀ ^ 3 * v) = u₀ ^ 3 * (u₀ * v) := by group
      _ = u₀ ^ 3 * (v * u₀) := by rw [hv]
      _ = (u₀ ^ 3 * v) * u₀ := by group

theorem t_y₀ : t * y₀ * t⁻¹ = y₀⁻¹ := by
  have h := C.secTwo
  have h1 : (t * y₀) * (t * y₀) = 1 := by rw [← pow_two]; exact C.ty₀_sq
  have htinv : t⁻¹ = t := h.t_inv
  rw [htinv]
  have : t * y₀ * t * y₀ = 1 := by simpa [mul_assoc] using h1
  exact (eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using this))

theorem dihRel : I21.DihRel t y₀ := ⟨C.secTwo.t_sq, by rw [C.t_y₀]⟩

theorem y₀_order : orderOf y₀ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [C.y₀_sq] using C.secTwo.z_ne_one)
    (by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, C.y₀_sq]
      exact C.secTwo.z_sq)

theorem u₀_y₀_cases : u₀ * y₀ = v ∨ u₀ * y₀ = v * u ^ 2 := by
  rcases C.y₀_def with h1 | h1
  · right
    rw [h1]
    calc u₀ * (u₀ * v) = u₀ ^ 2 * v := by rw [pow_two, mul_assoc]
      _ = u ^ 2 * v := by rw [C.u₀_sq]
      _ = v * u ^ 2 := (C.z_central C.v_mem_P).symm
  · left
    rw [h1]
    calc u₀ * (u₀ ^ 3 * v) = u₀ ^ 4 * v := by group
      _ = v := by rw [C.u₀_four, one_mul]

theorem u₀_y₀_mem_V : u₀ * y₀ ∈ V := by
  rcases C.u₀_y₀_cases with h1 | h1
  · rw [h1]; exact C.v_mem
  · rw [h1]; exact mul_mem C.v_mem C.z_mem_V

theorem u₀_y₀_ne : u₀ * y₀ ≠ 1 ∧ u₀ * y₀ ≠ u ^ 2 := by
  have h := C.secTwo
  have hzz : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact h.u_pow_four
  rcases C.u₀_y₀_cases with h1 | h1
  · rw [h1]; exact ⟨C.v_ne_one, C.v_ne_z⟩
  · rw [h1]
    refine ⟨fun h2 => C.v_ne_z ?_, fun h2 => C.v_ne_one ?_⟩
    · have := eq_inv_of_mul_eq_one_left h2
      rw [this]; exact h.z_inv
    · exact mul_eq_right.mp h2

end SixAY

end CFSG.LocalAnalysis.EvenBN.Tits
