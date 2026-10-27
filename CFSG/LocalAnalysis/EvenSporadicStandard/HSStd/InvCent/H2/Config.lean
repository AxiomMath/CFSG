module


import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Prod
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

@[expose] def kleinV {G : Type*} [Group G] (t v : G) : Subgroup G := zpowers t ⊔ zpowers v

structure H2Cfg (G : Type*) [Group G] (t v : G) (J : Subgroup G) : Prop where
  t_order : orderOf t = 2
  v_sq : v * v = 1
  J_iso : Nonempty (↥J ≃* Equiv.Perm (Fin 5))
  disj : kleinV t v ⊓ J = ⊥
  comm : ∀ a ∈ kleinV t v, ∀ b ∈ J, a * b = b * a
  cent_t : centralizer ({t} : Set G) = kleinV t v ⊔ J
  cent_v : centralizer ({v} : Set G) = centralizer ({t} : Set G)
  cent_tv : centralizer ({t * v} : Set G) = centralizer ({t} : Set G)
  center : ∀ x : G, (∀ y : G, y * x = x * y) → x = 1
  odd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

private theorem cfgAux_centralizer_one_eq_top :
    centralizer ({(1 : G)} : Set G) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  rintro x rfl
  exact Subgroup.one_mem _

theorem t_sq (cfg : H2Cfg G t v J) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [cfg.t_order] at h
  simpa [pow_two] using h

theorem t_ne_one (cfg : H2Cfg G t v J) : t ≠ 1 := by
  intro h
  have h1 : orderOf (1 : G) = 2 := by rw [← h]; exact cfg.t_order
  rw [orderOf_one] at h1
  omega

theorem tv_comm (cfg : H2Cfg G t v J) : t * v = v * t := by
  have hv : v ∈ centralizer ({t} : Set G) := by
    rw [cfg.cent_t]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  exact (mem_centralizer_singleton_iff.mp hv).symm

private theorem cfgAux_tv_sq (cfg : H2Cfg G t v J) : (t * v) * (t * v) = 1 := by
  calc (t * v) * (t * v) = t * (v * t) * v := by group
    _ = t * (t * v) * v := by rw [← cfg.tv_comm]
    _ = (t * t) * (v * v) := by group
    _ = 1 := by rw [cfg.t_sq, cfg.v_sq, mul_one]

theorem t_mem_kleinV (cfg : H2Cfg G t v J) : t ∈ kleinV t v :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers t)

theorem v_mem_kleinV (cfg : H2Cfg G t v J) : v ∈ kleinV t v :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers v)

theorem kleinV_le_centralizer (cfg : H2Cfg G t v J) :
    kleinV t v ≤ centralizer ({t} : Set G) := by
  rw [cfg.cent_t]
  exact le_sup_left

theorem J_le_centralizer (cfg : H2Cfg G t v J) : J ≤ centralizer ({t} : Set G) := by
  rw [cfg.cent_t]
  exact le_sup_right

theorem mem_kleinV_iff (cfg : H2Cfg G t v J) {x : G} :
    x ∈ kleinV t v ↔ x = 1 ∨ x = t ∨ x = v ∨ x = t * v := by
  have ht_t : t * t = 1 := cfg.t_sq
  have hv_v : v * v = 1 := cfg.v_sq
  have hvt : v * t = t * v := cfg.tv_comm.symm
  have ht_tv : t * (t * v) = v := by rw [← mul_assoc, cfg.t_sq, one_mul]
  have ht_vt : t * (v * t) = v := by rw [hvt, ht_tv]
  have hv_tv : v * (t * v) = t := by rw [← hvt, ← mul_assoc, cfg.v_sq, one_mul]
  have hv_vt : v * (v * t) = t := by rw [← mul_assoc, cfg.v_sq, one_mul]
  have htv_t : (t * v) * t = v := by rw [mul_assoc, ht_vt]
  have htv_v : (t * v) * v = t := by rw [mul_assoc, cfg.v_sq, mul_one]
  have hvt_t : (v * t) * t = v := by rw [mul_assoc, cfg.t_sq, mul_one]
  have hvt_v : (v * t) * v = t := by rw [mul_assoc, ← hvt, ← mul_assoc, cfg.v_sq, one_mul]
  have htv_tv : (t * v) * (t * v) = 1 := cfgAux_tv_sq cfg
  have htv_vt : (t * v) * (v * t) = 1 := by rw [hvt]; exact htv_tv
  have hvt_tv : (v * t) * (t * v) = 1 := by rw [hvt]; exact htv_tv
  have hvt_vt : (v * t) * (v * t) = 1 := by rw [hvt]; exact htv_tv
  let S : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = t ∨ x = v ∨ x = t * v}
      mul_mem' := by
        rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [ht_t, hv_v, hvt, ht_tv, ht_vt, hv_tv, hv_vt,
            htv_t, htv_v, hvt_t, hvt_v, htv_tv, htv_vt, hvt_tv, hvt_vt]
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro x (rfl | rfl | rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right cfg.t_sq))
        · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right cfg.v_sq)))
        · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right (cfgAux_tv_sq cfg)))) }
  have hSmem : ∀ x : G, x ∈ S ↔ x = 1 ∨ x = t ∨ x = v ∨ x = t * v := fun x => Iff.rfl
  have hVle : kleinV t v ≤ S := by
    rw [kleinV]
    apply sup_le
    · rw [Subgroup.zpowers_le]; exact Or.inr (Or.inl rfl)
    · rw [Subgroup.zpowers_le]; exact Or.inr (Or.inr (Or.inl rfl))
  constructor
  · intro hx
    exact (hSmem x).mp (hVle hx)
  · rintro (h | h | h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    · rw [h]; exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))

theorem v_ne_one (cfg : H2Cfg G t v J) : v ≠ 1 := by
  intro h
  have htop : centralizer ({t} : Set G) = ⊤ := by
    rw [← cfg.cent_v, h]
    exact cfgAux_centralizer_one_eq_top
  have hcomm : ∀ y : G, y * t = t * y := fun y => by
    have hy : y ∈ centralizer ({t} : Set G) := by rw [htop]; exact Subgroup.mem_top y
    exact mem_centralizer_singleton_iff.mp hy
  exact t_ne_one cfg (cfg.center t hcomm)

theorem v_ne_t (cfg : H2Cfg G t v J) : v ≠ t := by
  intro h
  have h1 : t * v = 1 := by rw [h, cfg.t_sq]
  have htop : centralizer ({t} : Set G) = ⊤ := by
    rw [← cfg.cent_tv, h1]
    exact cfgAux_centralizer_one_eq_top
  have hcomm : ∀ y : G, y * t = t * y := fun y => by
    have hy : y ∈ centralizer ({t} : Set G) := by rw [htop]; exact Subgroup.mem_top y
    exact mem_centralizer_singleton_iff.mp hy
  exact t_ne_one cfg (cfg.center t hcomm)

theorem tv_ne_one (cfg : H2Cfg G t v J) : t * v ≠ 1 := by
  intro h
  have h1 : t⁻¹ = v := inv_eq_of_mul_eq_one_right h
  have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right cfg.t_sq
  exact v_ne_t cfg (h1 ▸ h2)

theorem sq_eq_one_of_mem (cfg : H2Cfg G t v J) {w : G} (hw : w ∈ kleinV t v) : w * w = 1 := by
  rcases (mem_kleinV_iff cfg).mp hw with h | h | h | h
  · rw [h, one_mul]
  · rw [h]; exact cfg.t_sq
  · rw [h]; exact cfg.v_sq
  · rw [h]; exact cfgAux_tv_sq cfg

theorem comm_of_mem (cfg : H2Cfg G t v J) {a b : G} (ha : a ∈ kleinV t v) (hb : b ∈ kleinV t v) :
    a * b = b * a := by
  have ha2 : a * a = 1 := sq_eq_one_of_mem cfg ha
  have hb2 : b * b = 1 := sq_eq_one_of_mem cfg hb
  have hab2 : (a * b) * (a * b) = 1 := sq_eq_one_of_mem cfg (mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]

theorem card_kleinV [Finite G] (cfg : H2Cfg G t v J) : Nat.card ↥(kleinV t v) = 4 := by
  have hset : (kleinV t v : Set G) = {1, t, v, t * v} := by
    ext x
    change x ∈ kleinV t v ↔ x ∈ ({1, t, v, t * v} : Set G)
    rw [mem_kleinV_iff cfg]
    simp
  have ht1 : t ≠ 1 := t_ne_one cfg
  have hv1 : v ≠ 1 := v_ne_one cfg
  have htv1 : t * v ≠ 1 := tv_ne_one cfg
  have hvt : v ≠ t := v_ne_t cfg
  have httv : t ≠ t * v := by
    intro h
    exact hv1 (mul_left_cancel (show t * 1 = t * v by rw [mul_one]; exact h)).symm
  have hvtv : v ≠ t * v := by
    intro h
    exact ht1 (mul_right_cancel (show t * v = 1 * v by rw [← h, one_mul]))
  have hnot1 : (1 : G) ∉ ({t, v, t * v} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ht1.symm, hv1.symm, htv1.symm⟩
  have hnot2 : t ∉ ({v, t * v} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hvt.symm, httv⟩
  have hnot3 : v ∉ ({t * v} : Set G) := by
    simpa using hvtv
  change (kleinV t v : Set G).ncard = 4
  rw [hset, Set.ncard_insert_of_notMem hnot1, Set.ncard_insert_of_notMem hnot2,
    Set.ncard_insert_of_notMem hnot3, Set.ncard_singleton]

theorem kleinV_ne_bot (cfg : H2Cfg G t v J) : kleinV t v ≠ ⊥ := by
  intro h
  have ht : t ∈ (⊥ : Subgroup G) := h ▸ t_mem_kleinV cfg
  rw [Subgroup.mem_bot] at ht
  exact t_ne_one cfg ht

theorem centralizer_eq_of_mem (cfg : H2Cfg G t v J) {w : G} (hw : w ∈ kleinV t v) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) = centralizer ({t} : Set G) := by
  rcases (mem_kleinV_iff cfg).mp hw with h | h | h | h
  · exact absurd h hw1
  · rw [h]
  · rw [h]; exact cfg.cent_v
  · rw [h]; exact cfg.cent_tv

theorem kleinV_central (cfg : H2Cfg G t v J) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    {a : G} (ha : a ∈ kleinV t v) : a * c = c * a := by
  rcases (mem_kleinV_iff cfg).mp ha with h | h | h | h
  · rw [h, one_mul, mul_one]
  · rw [h]
    exact (Subgroup.mem_centralizer_iff.mp hc) t (by simp)
  · rw [h]
    exact (Subgroup.mem_centralizer_iff.mp (cfg.cent_v.symm ▸ hc)) v (by simp)
  · rw [h]
    exact (Subgroup.mem_centralizer_iff.mp (cfg.cent_tv.symm ▸ hc)) (t * v) (by simp)

theorem eq_kleinV_of_ne (cfg : H2Cfg G t v J) {w x : G} (hw : w ∈ kleinV t v)
    (hx : x ∈ kleinV t v) (hw1 : w ≠ 1) (hx1 : x ≠ 1) (hwx : w ≠ x) :
    zpowers w ⊔ zpowers x = kleinV t v := by
  have ht_tv : t * (t * v) = v := by rw [← mul_assoc, cfg.t_sq, one_mul]
  have hv_tv : v * (t * v) = t := by rw [cfg.tv_comm, ← mul_assoc, cfg.v_sq, one_mul]
  have htv_t : (t * v) * t = v := by rw [mul_assoc, ← cfg.tv_comm, ← mul_assoc, cfg.t_sq, one_mul]
  have htv_v : (t * v) * v = t := by rw [mul_assoc, cfg.v_sq, mul_one]
  have hWw : w ∈ zpowers w ⊔ zpowers x := Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hWx : x ∈ zpowers w ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hWwx : w * x ∈ zpowers w ⊔ zpowers x := mul_mem hWw hWx
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.mpr hw) (Subgroup.zpowers_le.mpr hx)
  · rw [kleinV]
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le] <;>
      rcases (mem_kleinV_iff cfg).mp hw with hw' | hw' | hw' | hw' <;>
      rcases (mem_kleinV_iff cfg).mp hx with hx' | hx' | hx' | hx' <;>
      subst w <;> subst x <;>
      first
        | exact absurd rfl hw1
        | exact absurd rfl hx1
        | exact absurd rfl hwx
        | assumption
        | (convert hWwx using 1; rw [ht_tv])
        | (convert hWwx using 1; rw [hv_tv])
        | (convert hWwx using 1; rw [htv_t])
        | (convert hWwx using 1; rw [htv_v])

theorem exists_other (cfg : H2Cfg G t v J) {w : G} (hw : w ∈ kleinV t v) (hw1 : w ≠ 1) :
    ∃ u ∈ kleinV t v, u ≠ 1 ∧ u ≠ w := by
  rcases (mem_kleinV_iff cfg).mp hw with h | h | h | h
  · exact absurd h hw1
  · rw [h]
    exact ⟨v, v_mem_kleinV cfg, v_ne_one cfg, v_ne_t cfg⟩
  · rw [h]
    exact ⟨t, t_mem_kleinV cfg, t_ne_one cfg, (v_ne_t cfg).symm⟩
  · rw [h]
    refine ⟨t, t_mem_kleinV cfg, t_ne_one cfg, ?_⟩
    intro hh
    exact v_ne_one cfg (mul_left_cancel (show t * 1 = t * v by rw [mul_one]; exact hh)).symm

theorem exists_mul_of_mem_centralizer (cfg : H2Cfg G t v J) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) : ∃ a ∈ kleinV t v, ∃ j ∈ J, c = a * j := by
  have hJV : J ≤ centralizer ((kleinV t v) : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact cfg.comm a ha j hj
  have hc' : c ∈ kleinV t v ⊔ J := by
    rw [← cfg.cent_t]
    exact hc
  exact CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hJV hc'

theorem card_centralizer [Finite G] (cfg : H2Cfg G t v J) :
    Nat.card ↥(centralizer ({t} : Set G)) = 480 := by
  have hJ : Nat.card ↥J = 120 := by
    obtain ⟨e⟩ := cfg.J_iso
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hcomm : ∀ a ∈ kleinV t v, ∀ b ∈ J, a * b = b * a := cfg.comm
  obtain ⟨e⟩ :=
    CFSG.EvenSporadicStandard.HSStd.InvCent.nonempty_mulEquiv_sup_prod hcomm cfg.disj
  rw [cfg.cent_t, Nat.card_congr e.toEquiv, Nat.card_prod (↥(kleinV t v)) (↥J),
    card_kleinV cfg, hJ]

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
