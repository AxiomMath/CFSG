module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Abstract

variable {Y : Type*} [Group Y]

theorem fix_prod_of_mem_normalizer {a b : Y} {V : Subgroup Y} (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hV : ∀ y, y ∈ V ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b)
    (hna : ¬ IsConj a (a * b)) (hnb : ¬ IsConj b (a * b))
    {w : Y} (hw : w ∈ normalizer (V : Set Y)) : w * (a * b) = (a * b) * w := by
  have hn := Subgroup.mem_normalizer_iff.1 hw
  have haV : a ∈ V := (hV a).2 (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hV b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hα : w * a * w⁻¹ = a ∨ w * a * w⁻¹ = b := by
    rcases (hV _).1 ((hn a).1 haV) with h | h | h | h
    · exact absurd (by simpa using h) ha1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (isConj_iff.2 ⟨w, h⟩) hna
  have hβ : w * b * w⁻¹ = a ∨ w * b * w⁻¹ = b := by
    rcases (hV _).1 ((hn b).1 hbV) with h | h | h | h
    · exact absurd (by simpa using h) hb1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (isConj_iff.2 ⟨w, h⟩) hnb
  have e : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
  have key : w * (a * b) * w⁻¹ = a * b := by
    rw [e]
    rcases hα with h | h <;> rcases hβ with h' | h'
    · exact absurd (by simpa using h.trans h'.symm) hne
    · rw [h, h']
    · rw [h, h', hab]
    · exact absurd (by simpa using h.trans h'.symm) hne
  exact mul_inv_eq_iff_eq_mul.1 key

end Abstract

section FourGroup

variable {G : Type} [Group G] {z t : G}

theorem zt_mul_self_eq_one (hU : UData z t) : z * t * (z * t) = 1 := by
  rw [mul_assoc, ← mul_assoc t, hU.comm.symm, mul_assoc z, hU.t_sq, mul_one, hU.z_sq]

theorem zt_ne_one (hU : UData z t) : z * t ≠ 1 := by
  intro h
  apply hU.zt_ne
  have h1 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [h1, inv_eq_of_mul_eq_one_right hU.t_sq]

theorem mk_zt_eq {H : Subgroup G} (hz : z ∈ H) (ht : t ∈ H) :
    P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ = P34.mkH H ⟨z, hz⟩ * P34.mkH H ⟨t, ht⟩ :=
  (map_mul (P34.mkH H) ⟨z, hz⟩ ⟨t, ht⟩).symm

theorem mul_mem_four (hU : UData z t) {a b : G} (ha : a = 1 ∨ a = z ∨ a = t ∨ a = z * t)
    (hb : b = 1 ∨ b = z ∨ b = t ∨ b = z * t) :
    a * b = 1 ∨ a * b = z ∨ a * b = t ∨ a * b = z * t := by
  have hzz := hU.z_sq
  have htt := hU.t_sq
  have hzt := hU.comm
  have e1 : z * (z * t) = t := by rw [← mul_assoc, hzz, one_mul]
  have e2 : z * t * z = t := by rw [hzt, mul_assoc, hzz, mul_one]
  have e3 : z * t * t = z := by rw [mul_assoc, htt, mul_one]
  have e4 : t * (z * t) = z := by rw [hzt, ← mul_assoc, htt, one_mul]
  have e5 : z * t * (z * t) = 1 := by rw [mul_assoc, e4, hzz]
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb]
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inl (one_mul z))
  · exact Or.inr (Or.inr (Or.inl (one_mul t)))
  · exact Or.inr (Or.inr (Or.inr (one_mul _)))
  · exact Or.inr (Or.inl (mul_one z))
  · exact Or.inl hzz
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl e1))
  · exact Or.inr (Or.inr (Or.inl (mul_one t)))
  · exact Or.inr (Or.inr (Or.inr hzt.symm))
  · exact Or.inl htt
  · exact Or.inr (Or.inl e4)
  · exact Or.inr (Or.inr (Or.inr (mul_one _)))
  · exact Or.inr (Or.inr (Or.inl e2))
  · exact Or.inr (Or.inl e3)
  · exact Or.inl e5

theorem mem_U4_iff (hU : UData z t) {a : G} : a ∈ U4 z t ↔ a = 1 ∨ a = z ∨ a = t ∨ a = z * t := by
  let K : Subgroup G :=
    { carrier := {a | a = 1 ∨ a = z ∨ a = t ∨ a = z * t}
      mul_mem' := fun {a b} ha hb => mul_mem_four hU ha hb
      one_mem' := Or.inl rfl
      inv_mem' := fun {a} ha => by
        rcases ha with ha | ha | ha | ha <;> rw [ha]
        · exact Or.inl inv_one
        · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hU.z_sq))
        · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hU.t_sq)))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hU.z_sq, inv_eq_of_mul_eq_one_right hU.t_sq,
            hU.comm] }
  have hzK : z ∈ K := Or.inr (Or.inl rfl)
  have htK : t ∈ K := Or.inr (Or.inr (Or.inl rfl))
  constructor
  · intro h
    have : U4 z t ≤ K := sup_le (zpowers_le.2 hzK) (zpowers_le.2 htK)
    exact this h
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers z)
    · exact mem_sup_right (mem_zpowers t)
    · exact mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t))

theorem mem_barIn_U4_iff {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H)
    {y : HBar H} :
    y ∈ barIn H (U4 z t) ↔ y = 1 ∨ y = P34.mkH H ⟨z, hz⟩ ∨ y = P34.mkH H ⟨t, ht⟩ ∨
      y = P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ := by
  unfold barIn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_U4_iff hU] at hh
    rcases hh with hh | hh | hh | hh
    · exact Or.inl (by rw [show h = 1 from Subtype.ext hh]; exact map_one _)
    · exact Or.inr (Or.inl (by rw [show h = ⟨z, hz⟩ from Subtype.ext hh]))
    · exact Or.inr (Or.inr (Or.inl (by rw [show h = ⟨t, ht⟩ from Subtype.ext hh])))
    · exact Or.inr (Or.inr (Or.inr (by rw [show h = ⟨z * t, H.mul_mem hz ht⟩ from Subtype.ext hh])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, map_one _⟩
    · exact ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.2 (mem_sup_left (mem_zpowers z)), rfl⟩
    · exact ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.2 (mem_sup_right (mem_zpowers t)), rfl⟩
    · exact ⟨⟨z * t, H.mul_mem hz ht⟩, Subgroup.mem_subgroupOf.2
        (mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t))), rfl⟩

end FourGroup

section Center

variable {Y : Type*} [Group Y]

theorem center_facts [Finite Y] {a b : Y} {V W : Subgroup Y} (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hV : ∀ y, y ∈ V ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b)
    (hfix : ∀ w ∈ normalizer (V : Set Y), w * (a * b) = (a * b) * w)
    (hW2 : IsPGroup 2 ↥W) (hVW : V ≤ W) (hWC : W ⊓ centralizer (V : Set Y) ≤ V) :
    (∀ c ∈ center ↥W, (c : Y) ∈ V) ∧
      (W ≠ V → ∀ c ∈ center ↥W, (c : Y) = 1 ∨ (c : Y) = a * b) ∧
      ∀ w ∈ W, w * (a * b) = (a * b) * w := by
  have haV : a ∈ V := (hV a).2 (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hV b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hcentr : ∀ w : Y, w * (a * b) = (a * b) * w → w * a = a * w → w * b = b * w →
      w ∈ centralizer (V : Set Y) := by
    intro w hwab hwa hwb
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases (hV v).1 hv with h | h | h | h <;> rw [h]
    · rw [one_mul, mul_one]
    · exact hwa.symm
    · exact hwb.symm
    · exact hwab.symm
  have h1 : ∀ c ∈ center ↥W, (c : Y) ∈ V := by
    intro c hc
    refine hWC (Subgroup.mem_inf.2 ⟨c.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨v, hVW hv⟩)
  have h2 : W ≠ V → ∀ c ∈ center ↥W, (c : Y) = 1 ∨ (c : Y) = a * b := by
    intro hWV c hc
    have hlt : V.subgroupOf W < ⊤ := by
      refine lt_top_iff_ne_top.2 (fun htop => hWV ?_)
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact le_antisymm htop hVW
    have : Group.IsNilpotent ↥W := hW2.isNilpotent
    obtain ⟨w, hwn, hwV⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    rw [← Subgroup.subgroupOf_normalizer_eq hVW] at hwn
    have hwn' : (w : Y) ∈ normalizer (V : Set Y) := hwn
    have hwV' : (w : Y) ∉ V := hwV
    have hwab : (w : Y) * (a * b) = (a * b) * w := hfix _ hwn'
    have hcw : (w : Y) * (c : Y) = (c : Y) * (w : Y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc w)
    rcases (hV _).1 (h1 c hc) with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h] at hcw
      have hwb : (w : Y) * b = b * w := by
        refine mul_left_cancel (a := a) ?_
        calc a * ((w : Y) * b) = (a * (w : Y)) * b := by rw [mul_assoc]
          _ = ((w : Y) * a) * b := by rw [hcw]
          _ = (w : Y) * (a * b) := by rw [mul_assoc]
          _ = (a * b) * w := hwab
          _ = a * (b * w) := by rw [mul_assoc]
      exact hwV' (hWC ⟨w.2, hcentr _ hwab hcw hwb⟩)
    · exfalso
      rw [h] at hcw
      have hwa : (w : Y) * a = a * w := by
        refine mul_right_cancel (b := b) ?_
        calc (w : Y) * a * b = (w : Y) * (a * b) := by rw [mul_assoc]
          _ = (a * b) * w := hwab
          _ = a * (b * w) := by rw [mul_assoc]
          _ = a * (w * b) := by rw [← hcw]
          _ = (a * w) * b := by rw [mul_assoc]
      exact hwV' (hWC ⟨w.2, hcentr _ hwab hwa hcw⟩)
    · exact Or.inr h
  refine ⟨h1, h2, fun w hw => ?_⟩
  by_cases hWV : W = V
  · have hc : Commute a b := hab
    have hwV : w ∈ V := hWV ▸ hw
    rcases (hV w).1 hwV with h | h | h | h <;> rw [h]
    · rw [one_mul, mul_one]
    · exact ((Commute.refl a).mul_right hc).eq
    · exact (hc.symm.mul_right (Commute.refl b)).eq
  · have : Nontrivial ↥W := ⟨⟨⟨a, hVW haV⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have : Nontrivial ↥(center ↥W) := hW2.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center ↥W))
    have hcab : ((c : ↥W) : Y) = a * b := by
      rcases h2 hWV (c : ↥W) c.2 with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hc1
      · exact h
    have := Subgroup.mem_center_iff.1 c.2 ⟨w, hw⟩
    rw [← hcab]
    exact congrArg Subtype.val this

end Center

section Concrete

variable {G : Type} [Group G] [Finite G] {z t : G}

theorem eq_one_of_mk_eq_one {H : Subgroup G} {u : ↥H} (hu : u * u = 1) (h : P34.mkH H u = 1) :
    u = 1 := by
  have hodd := P34.odd_orderOf_of_mem_core H ((P34.mkH_eq_one_iff H).1 h)
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu)
  have h1 : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

theorem isConj_of_isConj_mk_sq {H : Subgroup G} {a b : ↥H} (ha : a * a = 1) (hb : b * b = 1)
    (h : IsConj (P34.mkH H a) (P34.mkH H b)) : IsConj a b := by
  by_cases ha1 : a = 1
  · subst ha1
    rw [map_one, isConj_one_right] at h
    rw [eq_one_of_mk_eq_one hb h]
  · have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [map_one, isConj_one_left] at h
      exact ha1 (eq_one_of_mk_eq_one ha h)
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
    exact P34.isConj_of_mk_isConj H ha2 hb2 h

theorem isConj_of_isConj_mk {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (h : IsConj (P34.mkH H ⟨a, ha⟩) (P34.mkH H ⟨b, hb⟩)) : IsConj a b :=
  H.subtype.map_isConj (isConj_of_isConj_mk_sq (Subtype.ext ha2) (Subtype.ext hb2) h)

theorem not_isConj_mk_z_zt {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) :
    ¬ IsConj (P34.mkH H ⟨z, hz⟩) (P34.mkH H ⟨z * t, H.mul_mem hz ht⟩) := fun h =>
  hU.not_conj (isConj_of_isConj_mk hz (H.mul_mem hz ht) hU.z_sq (zt_mul_self_eq_one hU) h)

theorem not_isConj_mk_t_zt {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) :
    ¬ IsConj (P34.mkH H ⟨t, ht⟩) (P34.mkH H ⟨z * t, H.mul_mem hz ht⟩) := fun h =>
  hU.not_conj (hU.conj_zt.trans
    (isConj_of_isConj_mk ht (H.mul_mem hz ht) hU.t_sq (zt_mul_self_eq_one hU) h))

theorem mk_z_ne_one {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) : P34.mkH H ⟨z, hz⟩ ≠ 1 := by
  intro h
  exact hU.z_ne (congrArg Subtype.val (eq_one_of_mk_eq_one (Subtype.ext hU.z_sq) h))

theorem mk_t_ne_one {H : Subgroup G} (hU : UData z t) (ht : t ∈ H) : P34.mkH H ⟨t, ht⟩ ≠ 1 := by
  intro h
  exact hU.t_ne (congrArg Subtype.val (eq_one_of_mk_eq_one (Subtype.ext hU.t_sq) h))

theorem mk_zt_ne_one {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) :
    P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ ≠ 1 := by
  intro h
  exact zt_ne_one hU (congrArg Subtype.val
    (eq_one_of_mk_eq_one (Subtype.ext (zt_mul_self_eq_one hU)) h))

theorem mk_z_ne_t {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) :
    P34.mkH H ⟨z, hz⟩ ≠ P34.mkH H ⟨t, ht⟩ := by
  intro h
  apply mk_zt_ne_one hU hz ht
  rw [mk_zt_eq hz ht, h, ← map_mul]
  have : (⟨t, ht⟩ * ⟨t, ht⟩ : ↥H) = 1 := Subtype.ext hU.t_sq
  rw [this, map_one]

theorem centralizes_xbar_of_mem_normalizer {H : Subgroup G} (hU : UData z t) (hz : z ∈ H)
    (ht : t ∈ H) {w : HBar H}
    (hw : w ∈ normalizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H))) :
    w * P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ = P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ * w := by
  rw [mk_zt_eq hz ht]
  refine fix_prod_of_mem_normalizer (V := barIn H (U4 z t)) ?_ (mk_z_ne_one hU hz)
    (mk_t_ne_one hU ht) (mk_z_ne_t hU hz ht) (fun y => ?_) ?_ ?_ hw
  · rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hU.comm)
  · rw [mem_barIn_U4_iff hU hz ht, mk_zt_eq hz ht]
  · rw [← mk_zt_eq hz ht]
    exact not_isConj_mk_z_zt hU hz ht
  · rw [← mk_zt_eq hz ht]
    exact not_isConj_mk_t_zt hU hz ht

theorem W_facts {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H)
    {W : Subgroup (HBar H)} (hW2 : IsPGroup 2 ↥W) (hUW : barIn H (U4 z t) ≤ W)
    (hWC : W ⊓ centralizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) ≤
      barIn H (U4 z t)) :
    P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ ∈ W ∧
      (∀ w ∈ W, w * P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ =
        P34.mkH H ⟨z * t, H.mul_mem hz ht⟩ * w) ∧
      (∀ c ∈ center ↥W, (c : HBar H) ∈ barIn H (U4 z t)) ∧
      (W ≠ barIn H (U4 z t) → ∀ c ∈ center ↥W,
        (c : HBar H) = 1 ∨ (c : HBar H) = P34.mkH H ⟨z * t, H.mul_mem hz ht⟩) := by
  have hV : ∀ y : HBar H, y ∈ barIn H (U4 z t) ↔ y = 1 ∨ y = P34.mkH H ⟨z, hz⟩ ∨
      y = P34.mkH H ⟨t, ht⟩ ∨ y = P34.mkH H ⟨z, hz⟩ * P34.mkH H ⟨t, ht⟩ := fun y => by
    rw [mem_barIn_U4_iff hU hz ht, mk_zt_eq hz ht]
  have hab : P34.mkH H ⟨z, hz⟩ * P34.mkH H ⟨t, ht⟩ = P34.mkH H ⟨t, ht⟩ * P34.mkH H ⟨z, hz⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hU.comm)
  have hfix : ∀ w ∈ normalizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)),
      w * (P34.mkH H ⟨z, hz⟩ * P34.mkH H ⟨t, ht⟩) = (P34.mkH H ⟨z, hz⟩ * P34.mkH H ⟨t, ht⟩) * w :=
    fun w hw => by
      rw [← mk_zt_eq hz ht]
      exact centralizes_xbar_of_mem_normalizer hU hz ht hw
  obtain ⟨h1, h2, h3⟩ := center_facts hab (mk_z_ne_one hU hz) hV hfix hW2 hUW hWC
  rw [← mk_zt_eq hz ht] at h2 h3
  refine ⟨hUW ((mem_barIn_U4_iff hU hz ht).2 (Or.inr (Or.inr (Or.inr rfl)))), h3, h1, h2⟩

end Concrete

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
