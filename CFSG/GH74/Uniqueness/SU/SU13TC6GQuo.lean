module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

open Classical in
noncomputable def alphaAb (Y : Subgroup G) (x : G) : Abelianization ↥Y :=
  if h : x ∈ Y then Abelianization.of ⟨x, h⟩ else 1

theorem alphaAb_of_mem {Y : Subgroup G} {x : G} (h : x ∈ Y) :
    alphaAb Y x = Abelianization.of ⟨x, h⟩ := by
  simp [alphaAb, h]

theorem alphaAb_mul {Y : Subgroup G} {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    alphaAb Y (x * y) = alphaAb Y x * alphaAb Y y := by
  rw [alphaAb_of_mem (Y.mul_mem hx hy), alphaAb_of_mem hx, alphaAb_of_mem hy, ← map_mul]
  rfl

theorem alphaAb_one (Y : Subgroup G) : alphaAb Y 1 = 1 := by
  rw [alphaAb_of_mem Y.one_mem]
  exact map_one _

theorem alphaAb_inv {Y : Subgroup G} {x : G} (hx : x ∈ Y) : alphaAb Y x⁻¹ = (alphaAb Y x)⁻¹ := by
  rw [alphaAb_of_mem (Y.inv_mem hx), alphaAb_of_mem hx, ← map_inv]
  rfl

theorem alphaAb_conj {Y : Subgroup G} {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    alphaAb Y (y * x * y⁻¹) = alphaAb Y x := by
  rw [alphaAb_mul (Y.mul_mem hy hx) (Y.inv_mem hy), alphaAb_mul hy hx, alphaAb_inv hy]
  rw [mul_comm (alphaAb Y y) (alphaAb Y x), mul_assoc, mul_inv_cancel, mul_one]

theorem alphaAb_commutator {Y : Subgroup G} {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    alphaAb Y (x * y * x⁻¹ * y⁻¹) = 1 := by
  rw [alphaAb_mul (Y.mul_mem (Y.mul_mem hx hy) (Y.inv_mem hx)) (Y.inv_mem hy),
    alphaAb_mul (Y.mul_mem hx hy) (Y.inv_mem hx), alphaAb_mul hx hy, alphaAb_inv hx, alphaAb_inv hy,
    mul_comm (alphaAb Y x) (alphaAb Y y)]
  group

structure KleinAct (Y : Subgroup G) (t z : G) : Prop where
  tt : t * t = 1
  zz : z * z = 1
  tz : t * z = z * t
  tY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y
  zY : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y

namespace KleinAct

variable {Y : Subgroup G} {t z : G}

theorem wY (h : KleinAct Y t z) {y : G} (hy : y ∈ Y) : (t * z) * y * (t * z)⁻¹ ∈ Y := by
  have : (t * z) * y * (t * z)⁻¹ = t * (z * y * z⁻¹) * t⁻¹ := by group
  rw [this]
  exact h.tY _ (h.zY y hy)

theorem prod_tz_t (h : KleinAct Y t z) : t * z * t = z := by
  calc t * z * t = z * t * t := by rw [h.tz]
    _ = z * (t * t) := by group
    _ = z := by rw [h.tt, mul_one]

theorem prod_tz_z (h : KleinAct Y t z) : t * z * z = t := by
  calc t * z * z = t * (z * z) := by group
    _ = t := by rw [h.zz, mul_one]

theorem prod_t_tz (h : KleinAct Y t z) : t * (t * z) = z := by
  calc t * (t * z) = (t * t) * z := by group
    _ = z := by rw [h.tt, one_mul]

theorem prod_z_tz (h : KleinAct Y t z) : z * (t * z) = t := by
  calc z * (t * z) = z * (z * t) := by rw [h.tz]
    _ = (z * z) * t := by group
    _ = t := by rw [h.zz, one_mul]

theorem prod_tz_tz (h : KleinAct Y t z) : (t * z) * (t * z) = 1 := by
  calc (t * z) * (t * z) = t * (z * t) * z := by group
    _ = t * (t * z) * z := by rw [h.tz]
    _ = (t * t) * (z * z) := by group
    _ = 1 := by rw [h.tt, h.zz, mul_one]

end KleinAct

noncomputable def normAb (Y : Subgroup G) (t z y : G) : Abelianization ↥Y :=
  alphaAb Y y * alphaAb Y (t * y * t⁻¹) * alphaAb Y (z * y * z⁻¹) *
    alphaAb Y ((t * z) * y * (t * z)⁻¹)

namespace KleinAct

variable {Y : Subgroup G} {t z : G}

theorem normAb_one : normAb Y t z 1 = 1 := by
  simp [normAb, alphaAb_one]

theorem normAb_mul (h : KleinAct Y t z) {y y' : G} (hy : y ∈ Y) (hy' : y' ∈ Y) :
    normAb Y t z (y * y') = normAb Y t z y * normAb Y t z y' := by
  have e1 : t * (y * y') * t⁻¹ = (t * y * t⁻¹) * (t * y' * t⁻¹) := by group
  have e2 : z * (y * y') * z⁻¹ = (z * y * z⁻¹) * (z * y' * z⁻¹) := by group
  have e3 : (t * z) * (y * y') * (t * z)⁻¹ = ((t * z) * y * (t * z)⁻¹) * ((t * z) * y' * (t * z)⁻¹) := by
    group
  unfold normAb
  rw [e1, e2, e3, alphaAb_mul hy hy', alphaAb_mul (h.tY y hy) (h.tY y' hy'),
    alphaAb_mul (h.zY y hy) (h.zY y' hy'), alphaAb_mul (h.wY hy) (h.wY hy')]
  ac_rfl

theorem normAb_inv (h : KleinAct Y t z) {y : G} (hy : y ∈ Y) :
    normAb Y t z y⁻¹ = (normAb Y t z y)⁻¹ := by
  have := h.normAb_mul hy (Y.inv_mem hy)
  rw [mul_inv_cancel, normAb_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem normAb_conj_t (h : KleinAct Y t z) (y : G) :
    normAb Y t z (t * y * t⁻¹) = normAb Y t z y := by
  have e1 : t * (t * y * t⁻¹) * t⁻¹ = y := by
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [h.tt]; group
  have e2 : z * (t * y * t⁻¹) * z⁻¹ = (t * z) * y * (t * z)⁻¹ := by
    calc z * (t * y * t⁻¹) * z⁻¹ = (z * t) * y * (z * t)⁻¹ := by group
      _ = (t * z) * y * (t * z)⁻¹ := by rw [h.tz]
  have e3 : (t * z) * (t * y * t⁻¹) * (t * z)⁻¹ = z * y * z⁻¹ := by
    calc (t * z) * (t * y * t⁻¹) * (t * z)⁻¹ = ((t * z) * t) * y * ((t * z) * t)⁻¹ := by group
      _ = z * y * z⁻¹ := by rw [h.prod_tz_t]
  unfold normAb
  rw [e1, e2, e3]
  ac_rfl

theorem normAb_conj_z (h : KleinAct Y t z) (y : G) :
    normAb Y t z (z * y * z⁻¹) = normAb Y t z y := by
  have e1 : t * (z * y * z⁻¹) * t⁻¹ = (t * z) * y * (t * z)⁻¹ := by group
  have e2 : z * (z * y * z⁻¹) * z⁻¹ = y := by
    calc z * (z * y * z⁻¹) * z⁻¹ = (z * z) * y * (z * z)⁻¹ := by group
      _ = y := by rw [h.zz]; group
  have e3 : (t * z) * (z * y * z⁻¹) * (t * z)⁻¹ = t * y * t⁻¹ := by
    calc (t * z) * (z * y * z⁻¹) * (t * z)⁻¹ = ((t * z) * z) * y * ((t * z) * z)⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [h.prod_tz_z]
  unfold normAb
  rw [e1, e2, e3]
  ac_rfl

theorem normAb_conj_w (h : KleinAct Y t z) (y : G) :
    normAb Y t z ((t * z) * y * (t * z)⁻¹) = normAb Y t z y := by
  have e1 : t * ((t * z) * y * (t * z)⁻¹) * t⁻¹ = z * y * z⁻¹ := by
    calc t * ((t * z) * y * (t * z)⁻¹) * t⁻¹ = (t * (t * z)) * y * (t * (t * z))⁻¹ := by group
      _ = z * y * z⁻¹ := by rw [h.prod_t_tz]
  have e2 : z * ((t * z) * y * (t * z)⁻¹) * z⁻¹ = t * y * t⁻¹ := by
    calc z * ((t * z) * y * (t * z)⁻¹) * z⁻¹ = (z * (t * z)) * y * (z * (t * z))⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [h.prod_z_tz]
  have e3 : (t * z) * ((t * z) * y * (t * z)⁻¹) * (t * z)⁻¹ = y := by
    calc (t * z) * ((t * z) * y * (t * z)⁻¹) * (t * z)⁻¹
        = ((t * z) * (t * z)) * y * ((t * z) * (t * z))⁻¹ := by group
      _ = y := by rw [h.prod_tz_tz]; group
  unfold normAb
  rw [e1, e2, e3]
  ac_rfl

theorem normAb_conj (h : KleinAct Y t z) {r : G} (hr : r = t ∨ r = z ∨ r = t * z) (y : G) :
    normAb Y t z (r * y * r⁻¹) = normAb Y t z y := by
  rcases hr with rfl | rfl | rfl
  · exact h.normAb_conj_t y
  · exact h.normAb_conj_z y
  · exact h.normAb_conj_w y

theorem normAb_comm_r (h : KleinAct Y t z) {r : G} (hr : r = t ∨ r = z ∨ r = t * z) {y : G}
    (hy : y ∈ Y) : normAb Y t z (y * (r * y⁻¹ * r⁻¹)) = 1 := by
  have hry : r * y⁻¹ * r⁻¹ ∈ Y := by
    rcases hr with rfl | rfl | rfl
    · exact h.tY _ (Y.inv_mem hy)
    · exact h.zY _ (Y.inv_mem hy)
    · exact h.wY (Y.inv_mem hy)
  rw [h.normAb_mul hy hry, h.normAb_conj hr, h.normAb_inv hy, mul_inv_cancel]

theorem normAb_conjY (h : KleinAct Y t z) {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    normAb Y t z (y * x * y⁻¹) = normAb Y t z x := by
  have e1 : t * (y * x * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
  have e2 : z * (y * x * y⁻¹) * z⁻¹ = (z * y * z⁻¹) * (z * x * z⁻¹) * (z * y * z⁻¹)⁻¹ := by group
  have e3 : (t * z) * (y * x * y⁻¹) * (t * z)⁻¹ =
      ((t * z) * y * (t * z)⁻¹) * ((t * z) * x * (t * z)⁻¹) * ((t * z) * y * (t * z)⁻¹)⁻¹ := by group
  unfold normAb
  rw [e1, e2, e3, alphaAb_conj hx hy, alphaAb_conj (h.tY x hx) (h.tY y hy),
    alphaAb_conj (h.zY x hx) (h.zY y hy), alphaAb_conj (h.wY hx) (h.wY hy)]

theorem normAb_commutator (h : KleinAct Y t z) {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    normAb Y t z (x * y * x⁻¹ * y⁻¹) = 1 := by
  have e1 : t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ =
      (t * x * t⁻¹) * (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ := by group
  have e2 : z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ =
      (z * x * z⁻¹) * (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ * (z * y * z⁻¹)⁻¹ := by group
  have e3 : (t * z) * (x * y * x⁻¹ * y⁻¹) * (t * z)⁻¹ =
      ((t * z) * x * (t * z)⁻¹) * ((t * z) * y * (t * z)⁻¹) * ((t * z) * x * (t * z)⁻¹)⁻¹ *
        ((t * z) * y * (t * z)⁻¹)⁻¹ := by group
  unfold normAb
  rw [e1, e2, e3, alphaAb_commutator hx hy, alphaAb_commutator (h.tY x hx) (h.tY y hy),
    alphaAb_commutator (h.zY x hx) (h.zY y hy), alphaAb_commutator (h.wY hx) (h.wY hy)]
  simp

theorem normAb_commutator_v (h : KleinAct Y t z) {y y'' : G} (hy : y ∈ Y) (hy'' : y'' ∈ Y) {r : G}
    (hr : r = 1 ∨ r = t ∨ r = z ∨ r = t * z) :
    normAb Y t z (y * (y'' * r) * y⁻¹ * (y'' * r)⁻¹) = 1 := by
  rcases hr with rfl | hr
  · have : y * (y'' * 1) * y⁻¹ * (y'' * 1)⁻¹ = y * y'' * y⁻¹ * y''⁻¹ := by group
    rw [this]
    exact h.normAb_commutator hy hy''
  · have hr' : r = t ∨ r = z ∨ r = t * z := hr
    have e : y * (y'' * r) * y⁻¹ * (y'' * r)⁻¹ =
        (y * y'' * y⁻¹ * y''⁻¹) * (y'' * (y * (r * y⁻¹ * r⁻¹)) * y''⁻¹) := by group
    have hry : r * y⁻¹ * r⁻¹ ∈ Y := by
      rcases hr' with rfl | rfl | rfl
      · exact h.tY _ (Y.inv_mem hy)
      · exact h.zY _ (Y.inv_mem hy)
      · exact h.wY (Y.inv_mem hy)
    have hx : y * (r * y⁻¹ * r⁻¹) ∈ Y := Y.mul_mem hy hry
    rw [e, h.normAb_mul (Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy'') (Y.inv_mem hy)) (Y.inv_mem hy''))
      (Y.mul_mem (Y.mul_mem hy'' hx) (Y.inv_mem hy'')), h.normAb_commutator hy hy'',
      h.normAb_conjY hx hy'', h.normAb_comm_r hr' hy, mul_one]

end KleinAct

theorem mem_commutator_of_mem_commutator_centralizes {Y V : Subgroup G} {t z : G}
    (hY : Odd (Nat.card Y)) (ht : t * t = 1) (hz : z * z = 1) (htz : t * z = z * t)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (hzY : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y)
    (hV : ∀ v ∈ V, ∃ y ∈ Y, v = y ∨ v = y * t ∨ v = y * z ∨ v = y * (t * z))
    {s : G} (hsY : s ∈ Y) (hst : s * t = t * s) (hsz : s * z = z * s) (hs : s ∈ ⁅Y, V⁆) :
    s ∈ ⁅Y, Y⁆ := by
  have h : KleinAct Y t z := ⟨ht, hz, htz, htY, hzY⟩
  let K0 : Subgroup G :=
    { carrier := {x | x ∈ Y ∧ normAb Y t z x = 1}
      one_mem' := ⟨Y.one_mem, KleinAct.normAb_one⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        exact ⟨Y.mul_mem ha hb, by rw [h.normAb_mul ha hb, ha1, hb1, mul_one]⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨Y.inv_mem ha, by rw [h.normAb_inv ha, ha1, inv_one]⟩ }
  have hle : ⁅Y, V⁆ ≤ K0 := by
    rw [Subgroup.commutator_le]
    intro y hy v hv
    obtain ⟨y'', hy'', hv'⟩ := hV v hv
    have hrcases : ∃ r : G, (r = 1 ∨ r = t ∨ r = z ∨ r = t * z) ∧ v = y'' * r := by
      rcases hv' with h1 | h1 | h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [h1]; group⟩
      · exact ⟨t, Or.inr (Or.inl rfl), h1⟩
      · exact ⟨z, Or.inr (Or.inr (Or.inl rfl)), h1⟩
      · exact ⟨t * z, Or.inr (Or.inr (Or.inr rfl)), h1⟩
    obtain ⟨r, hr, rfl⟩ := hrcases
    have hrY : ∀ w ∈ Y, r * w * r⁻¹ ∈ Y := by
      rcases hr with rfl | rfl | rfl | rfl
      · intro w hw; simpa using hw
      · exact htY
      · exact hzY
      · exact fun w hw => h.wY hw
    have hmem : y * (y'' * r) * y⁻¹ * (y'' * r)⁻¹ ∈ Y := by
      have e : y * (y'' * r) * y⁻¹ * (y'' * r)⁻¹ =
          (y * y'' * y⁻¹ * y''⁻¹) * (y'' * (y * (r * y⁻¹ * r⁻¹)) * y''⁻¹) := by group
      rw [e]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy'') (Y.inv_mem hy)) (Y.inv_mem hy''))
        (Y.mul_mem (Y.mul_mem hy'' (Y.mul_mem hy (hrY _ (Y.inv_mem hy)))) (Y.inv_mem hy''))
    rw [commutatorElement_def]
    exact ⟨hmem, h.normAb_commutator_v hy hy'' hr⟩
  obtain ⟨-, hs1⟩ := hle hs
  have e1 : t * s * t⁻¹ = s := by rw [← hst]; group
  have e2 : z * s * z⁻¹ = s := by rw [← hsz]; group
  have e3 : (t * z) * s * (t * z)⁻¹ = s := by
    calc (t * z) * s * (t * z)⁻¹ = t * (z * s * z⁻¹) * t⁻¹ := by group
      _ = s := by rw [e2, e1]
  have hν : normAb Y t z s = (alphaAb Y s) ^ 4 := by
    unfold normAb
    rw [e1, e2, e3]
    simp [pow_succ, mul_assoc]
  rw [hν] at hs1
  have hodd : Odd (orderOf s) := by
    have h1 : orderOf (⟨s, hsY⟩ : Y) ∣ Nat.card Y := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hY h1
  have hαs : alphaAb Y s = 1 := by
    have h4 : orderOf (alphaAb Y s) ∣ 4 := orderOf_dvd_of_pow_eq_one hs1
    have hm : (alphaAb Y s) ^ (orderOf s) = 1 := by
      rw [alphaAb_of_mem hsY, ← map_pow]
      have : (⟨s, hsY⟩ : Y) ^ (orderOf s) = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have hdvd : orderOf (alphaAb Y s) ∣ orderOf s := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime 4 (orderOf s) := by
      have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
      simpa using this
    have : orderOf (alphaAb Y s) = 1 := Nat.eq_one_of_dvd_coprimes hcop h4 hdvd
    exact orderOf_eq_one_iff.mp this
  rw [alphaAb_of_mem hsY] at hαs
  have hcomm : (⟨s, hsY⟩ : Y) ∈ _root_.commutator ↥Y := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hαs
  rw [_root_.commutator_def] at hcomm
  have hmap : ((⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ : Subgroup ↥Y)).map Y.subtype = ⁅Y, Y⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap]
  exact ⟨⟨s, hsY⟩, hcomm, rfl⟩

end CFSG.GH74.Uniqueness.SU.SU13
