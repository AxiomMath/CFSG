module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveOrbit
public import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.KC.Fv8124

open CFSG.AGLEmbedding.KFactProofs.Fi22Five
open CFSG.RankThree.Native (commutator_closure_eq_closure)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem pow_mod5 {g : G} (h : g ^ 5 = 1) (n : ℕ) : g ^ n = g ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h, one_pow, one_mul]

theorem plane_of {q1 q2 : G} (h1 : q1 ^ 5 = 1) (h2 : q2 ^ 5 = 1) (hc : q1 * q2 = q2 * q1)
    (hne : q1 ≠ 1) (hn : ∀ e < 5, q2 ≠ q1 ^ e) : PlaneData q1 q2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ho : orderOf q1 = 5 := orderOf_eq_prime h1 hne
  refine ⟨h1, h2, hc, fun v hv h => ?_⟩
  have ha := ZMod.val_lt (v 0)
  have hb := ZMod.val_lt (v 1)
  by_cases hb0 : (v 1).val = 0
  · rw [hb0, pow_zero, mul_one] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ho] at hd
    have ha0 : (v 0).val = 0 := by
      obtain ⟨k, hk⟩ := hd
      omega
    exact hv (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 ha0
      · exact (ZMod.val_eq_zero _).1 hb0)
  · generalize (v 0).val = a at ha h
    generalize (v 1).val = b at hb h hb0
    have hqb : q2 ^ b = q1 ^ (5 - a) := by
      have e : q1 ^ (5 - a) * q1 ^ a = 1 := by
        rw [← pow_add, Nat.sub_add_cancel ha.le, h1]
      calc q2 ^ b = q1 ^ (5 - a) * (q1 ^ a * q2 ^ b) := by rw [← mul_assoc, e, one_mul]
        _ = q1 ^ (5 - a) := by rw [h, mul_one]
    obtain ⟨c, hc5⟩ : ∃ c, (b * c) % 5 = 1 := by
      interval_cases b
      · exact absurd rfl hb0
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    have e2 : q2 = q1 ^ ((5 - a) * c % 5) := by
      calc q2 = q2 ^ (b * c) := by rw [pow_mod5 h2, hc5, pow_one]
        _ = q1 ^ ((5 - a) * c) := by rw [pow_mul, hqb, ← pow_mul]
        _ = _ := pow_mod5 h1 _
    exact hn _ (Nat.mod_lt _ (by norm_num)) e2

@[expose] def lineExp (j : ℕ) : ℕ × ℕ :=
  if j = 0 then (1, 0) else if j = 1 then (0, 1) else (1, j - 1)

@[expose] def lineE (q1 q2 : G) (j : ℕ) : G :=
  if j = 0 then q1 else if j = 1 then q2 else q1 * q2 ^ (j - 1)

theorem lineE_pow {q1 q2 : G} (hc : q1 * q2 = q2 * q1) (h1 : q1 ^ 5 = 1) (h2 : q2 ^ 5 = 1)
    (j k : ℕ) :
    lineE q1 q2 j ^ k = q1 ^ (k * (lineExp j).1 % 5) * q2 ^ (k * (lineExp j).2 % 5) := by
  have hC : Commute q1 q2 := hc
  have e : lineE q1 q2 j ^ k = q1 ^ (k * (lineExp j).1) * q2 ^ (k * (lineExp j).2) := by
    unfold lineE lineExp
    split_ifs
    · simp
    · simp
    · rw [(hC.pow_right (j - 1)).mul_pow, ← pow_mul, mul_one, mul_comm k]
  rw [e, pow_mod5 h1 (k * (lineExp j).1), pow_mod5 h2 (k * (lineExp j).2)]

theorem planeMap_inj {q1 q2 : G} (hD : PlaneData q1 q2) {a b c d : ℕ} (ha : a < 5) (hb : b < 5)
    (hc : c < 5) (hd : d < 5) (h : q1 ^ a * q2 ^ b = q1 ^ c * q2 ^ d) : a = c ∧ b = d := by
  set v : Fin 2 → ZMod 5 := ![(a : ZMod 5), (b : ZMod 5)] with hv_def
  set u : Fin 2 → ZMod 5 := ![(c : ZMod 5), (d : ZMod 5)] with hu_def
  have hv : planeMap q1 q2 v = q1 ^ a * q2 ^ b := by
    unfold planeMap
    simp [hv_def, ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb]
  have hu : planeMap q1 q2 u = q1 ^ c * q2 ^ d := by
    unfold planeMap
    simp [hu_def, ZMod.val_natCast_of_lt hc, ZMod.val_natCast_of_lt hd]
  have e : planeHom hD (Multiplicative.ofAdd v) = planeHom hD (Multiplicative.ofAdd u) := by
    change planeMap q1 q2 v = planeMap q1 q2 u
    rw [hv, hu, h]
  have e' : v = u := Multiplicative.ofAdd.injective (hD.injective e)
  have e0 : (a : ZMod 5) = (c : ZMod 5) := by simpa [hv_def, hu_def] using congrFun e' 0
  have e1 : (b : ZMod 5) = (d : ZMod 5) := by simpa [hv_def, hu_def] using congrFun e' 1
  have f0 := congrArg ZMod.val e0
  have f1 := congrArg ZMod.val e1
  rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc] at f0
  rw [ZMod.val_natCast_of_lt hb, ZMod.val_natCast_of_lt hd] at f1
  exact ⟨f0, f1⟩

theorem lines_cover {q1 q2 : G} (hD : PlaneData q1 q2) {g : G}
    (hg : g ∈ Subgroup.closure ({q1, q2} : Set G)) (hg1 : g ≠ 1) :
    ∃ j < 6, ∃ k : ℕ, g = lineE q1 q2 j ^ k := by
  obtain ⟨v, rfl⟩ := hD.closure_facts.2.2 g hg
  unfold planeMap at hg1 ⊢
  have ha := ZMod.val_lt (v 0)
  have hb := ZMod.val_lt (v 1)
  generalize (v 0).val = a at ha hg1 ⊢
  generalize (v 1).val = b at hb hg1 ⊢
  have key : ∀ j < 6, ∀ k : ℕ, k * (lineExp j).1 % 5 = a → k * (lineExp j).2 % 5 = b →
      q1 ^ a * q2 ^ b = lineE q1 q2 j ^ k := fun j _ k e1 e2 => by
    rw [lineE_pow hD.comm hD.x_pow hD.y_pow, e1, e2]
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hg1 (by simp)
  obtain ⟨j, hj, k, -, e1, e2⟩ : ∃ j < 6, ∃ k < 5, k * (lineExp j).1 % 5 = a ∧
      k * (lineExp j).2 % 5 = b := by
    interval_cases a <;> interval_cases b <;> first | exact absurd ⟨rfl, rfl⟩ hab | decide
  exact ⟨j, hj, k, key j hj k e1 e2⟩

theorem lines_dist {q1 q2 : G} (hD : PlaneData q1 q2) {j j' k : ℕ} (hj : j < 6) (hj' : j' < 6)
    (hk : k < 5) (h : lineE q1 q2 j = lineE q1 q2 j' ^ k) : j = j' := by
  have e1 : lineE q1 q2 j = lineE q1 q2 j ^ 1 := (pow_one _).symm
  rw [e1, lineE_pow hD.comm hD.x_pow hD.y_pow, lineE_pow hD.comm hD.x_pow hD.y_pow] at h
  obtain ⟨h1, h2⟩ := planeMap_inj hD (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h
  revert h1 h2
  interval_cases j <;> interval_cases j' <;> interval_cases k <;> decide

variable (P R : Subgroup G)

structure RecHyp (x w a b : G) : Prop where
  hPR : P ≤ R
  x5 : x ^ 5 = 1
  x1 : x ≠ 1
  w2 : w * w = 1
  xP : x ∈ P
  aP : a ∈ P
  bP : b ∈ P
  wR : w ∈ R
  wP : w ∉ P
  Rw : ∀ g ∈ R, g ∉ P → w⁻¹ * g ∈ P
  ax : a * x = x * a
  bx : b * x = x * b
  wx : w * x = x * w
  aw : a * w = w * a
  bw : b * w = w * b
  bc : b = ⁅a * (b⁻¹ * b⁻¹), b⁻¹ * (b⁻¹ * (a * b⁻¹))⁆
  dCard : Nat.card (Subgroup.closure ({⁅a, b⁆, b} : Set G)) = 60
  dSimple : IsSimpleGroup (Subgroup.closure ({⁅a, b⁆, b} : Set G))
  nab : ⁅a, b⁆ * b ≠ b * ⁅a, b⁆
  cjA1 : a * ⁅a, b⁆ * a⁻¹ ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)
  cjA2 : a * b * a⁻¹ ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)
  cjB1 : b * ⁅a, b⁆ * b⁻¹ ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)
  notD : ∀ e < 5, a * x⁻¹ ^ e ∉ Subgroup.closure ({⁅a, b⁆, b} : Set G)
  cent : ∀ t ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G),
    a * t * ⁅a, b⁆ ≠ ⁅a, b⁆ * (a * t) ∨ a * t * b ≠ b * (a * t)
  bound : Nat.card (Subgroup.centralizer {x} ⊓ P : Subgroup G) ≤ 600

@[expose] def RecFacts (x w : G) (C : Subgroup G) : Prop :=
  C = Subgroup.centralizer {x} ⊓ R ∧ Nat.card C = 1200 ∧
    C ⊓ P = Subgroup.centralizer {x} ⊓ P ∧ Nat.card (C ⊓ P : Subgroup G) = 600 ∧
    (⁅C, C⁆ : Subgroup G) ≤ P ∧ IsSimpleGroup (⁅C, C⁆ : Subgroup G) ∧
    (∃ g ∈ (⁅C, C⁆ : Subgroup G), ∃ h ∈ (⁅C, C⁆ : Subgroup G), g * h ≠ h * g) ∧
    Nat.card (⁅C, C⁆ : Subgroup G) = 60 ∧ w ∈ (Subgroup.center C).map C.subtype ∧
    Subgroup.centralizer ((⁅C, C⁆ : Subgroup G) : Set G) ⊓ C =
      Subgroup.zpowers x ⊔ Subgroup.zpowers w ∧
    Subgroup.zpowers x ⊓ Subgroup.zpowers w = ⊥ ∧ Commute x w ∧
    Nat.card (Subgroup.centralizer ((⁅C, C⁆ : Subgroup G) : Set G) ⊓ C : Subgroup G) = 10 ∧
    Subgroup.centralizer ((⁅C, C⁆ : Subgroup G) : Set G) ⊓ (C ⊓ P) = Subgroup.zpowers x

variable {P R}

theorem RecHyp.map {x w a b : G} (H : RecHyp P R x w a b) (φ : G ≃* G)
    (hP : ∀ g, φ g ∈ P ↔ g ∈ P) (hw : φ w = w)
    (hb : Nat.card (Subgroup.centralizer {φ x} ⊓ P : Subgroup G) ≤ 600) :
    RecHyp P R (φ x) w (φ a) (φ b) := by
  have hD : Subgroup.closure ({⁅φ a, φ b⁆, φ b} : Set G) =
      (Subgroup.closure ({⁅a, b⁆, b} : Set G)).map φ.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp [map_commutatorElement]
  have hmem : ∀ t, φ t ∈ Subgroup.closure ({⁅φ a, φ b⁆, φ b} : Set G) ↔
      t ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G) := fun t => by
    rw [hD, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hs := H.dSimple
  refine
    { hPR := H.hPR
      x5 := by rw [← map_pow, H.x5, map_one]
      x1 := fun h => H.x1 (φ.injective (by rw [h, map_one]))
      w2 := H.w2
      xP := (hP x).2 H.xP
      aP := (hP a).2 H.aP
      bP := (hP b).2 H.bP
      wR := H.wR
      wP := H.wP
      Rw := H.Rw
      ax := by rw [← map_mul, ← map_mul, H.ax]
      bx := by rw [← map_mul, ← map_mul, H.bx]
      wx := by rw [← hw, ← map_mul, ← map_mul, H.wx]
      aw := by rw [← hw, ← map_mul, ← map_mul, H.aw]
      bw := by rw [← hw, ← map_mul, ← map_mul, H.bw]
      bc := by
        have := congrArg φ H.bc
        rw [map_commutatorElement] at this
        simp only [map_mul, map_inv] at this
        exact this
      dCard := by
        rw [hD, Subgroup.card_map_of_injective (by exact φ.injective)]
        exact H.dCard
      dSimple := by
        rw [hD]
        exact (Subgroup.equivMapOfInjective _ φ.toMonoidHom (by exact φ.injective)).symm.isSimpleGroup
      nab := fun h => H.nab (φ.injective (by
        rw [map_mul, map_mul, map_commutatorElement]
        exact h))
      cjA1 := by
        have e : φ (a * ⁅a, b⁆ * a⁻¹) = φ a * ⁅φ a, φ b⁆ * (φ a)⁻¹ := by
          simp [map_commutatorElement]
        rw [← e]
        exact (hmem _).2 H.cjA1
      cjA2 := by
        have e : φ (a * b * a⁻¹) = φ a * φ b * (φ a)⁻¹ := by simp
        rw [← e]
        exact (hmem _).2 H.cjA2
      cjB1 := by
        have e : φ (b * ⁅a, b⁆ * b⁻¹) = φ b * ⁅φ a, φ b⁆ * (φ b)⁻¹ := by
          simp [map_commutatorElement]
        rw [← e]
        exact (hmem _).2 H.cjB1
      notD := fun e he h => H.notD e he ((hmem (a * x⁻¹ ^ e)).1 (by
        rw [map_mul, map_pow, map_inv]
        exact h))
      cent := by
        intro t ht
        obtain ⟨t0, rfl⟩ : ∃ t0, t = φ t0 := ⟨φ.symm t, by simp⟩
        rcases H.cent t0 ((hmem t0).1 ht) with h | h
        · left
          intro h'
          apply h
          apply φ.injective
          simp only [map_mul, map_commutatorElement]
          exact h'
        · right
          intro h'
          apply h
          apply φ.injective
          simp only [map_mul]
          exact h'
      bound := hb }

section Facts

variable [Finite G] {x w a b : G} (H : RecHyp P R x w a b)
include H

theorem RecHyp.comm_d {y : G} (hya : a * y = y * a) (hyb : b * y = y * b) :
    ∀ d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G), d * y = y * d := by
  have hA : Commute a y := hya
  have hB : Commute b y := hyb
  have hc : Commute ⁅a, b⁆ y := by
    rw [commutatorElement_def]
    exact ((hA.mul_left hB).mul_left hA.inv_left).mul_left hB.inv_left
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    exacts [hc.eq, hB.eq]
  | one => simp
  | mul s t _ _ hs ht => exact (Commute.mul_left hs ht).eq
  | inv s _ hs => exact (Commute.inv_left hs).eq

theorem RecHyp.center_trivial {t : G} (ht : t ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G))
    (hc : ∀ d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G), d * t = t * d) : t = 1 := by
  set D := Subgroup.closure ({⁅a, b⁆, b} : Set G)
  have := H.dSimple
  have hZ := IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D)
  rcases hZ with hZ | hZ
  · have : (⟨t, ht⟩ : D) ∈ Subgroup.center D := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hc g.1 g.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have h1 : (⟨⁅a, b⁆, Subgroup.subset_closure (by simp)⟩ : D) ∈ Subgroup.center D := by
      rw [hZ]
      exact Subgroup.mem_top _
    have := Subgroup.mem_center_iff.1 h1 ⟨b, Subgroup.subset_closure (by simp)⟩
    exact H.nab (congrArg Subtype.val this).symm

theorem RecHyp.d_le_P : Subgroup.closure ({⁅a, b⁆, b} : Set G) ≤ P := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [SetLike.mem_coe, commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem H.aP H.bP) (P.inv_mem H.aP)) (P.inv_mem H.bP)
  · exact H.bP

theorem RecHyp.orderOf_w : orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [pow_two]; exact H.w2) fun h => H.wP ?_
  rw [h]
  exact P.one_mem

theorem RecHyp.orderOf_x : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime H.x5 H.x1

theorem RecHyp.xpow_inj {e e' : ℕ} (he : e < 5) (he' : e' < 5) (h : x ^ e = x ^ e') :
    e = e' := by
  have ho := H.orderOf_x
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.2 (by rw [ho]; exact he))
    (Set.mem_Iio.2 (by rw [ho]; exact he')) h

theorem RecHyp.zpow_form {z : G} (hz : z ∈ Subgroup.zpowers x) : ∃ k < 5, z = x⁻¹ ^ k := by
  classical
  have hz' : z ∈ Subgroup.zpowers x⁻¹ := by rwa [Subgroup.zpowers_inv]
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_inv, H.orderOf_x, Finset.mem_image] at hz'
  obtain ⟨k, hk, rfl⟩ := hz'
  exact ⟨k, Finset.mem_range.1 hk, rfl⟩

theorem RecHyp.comm_zx {d : G} (hd : d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)) {z : G}
    (hz : z ∈ Subgroup.zpowers x) : d * z = z * d := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_right (H.comm_d H.ax H.bx d hd) n).eq

theorem RecHyp.same {d d' : G} (hd : d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G))
    (hd' : d' ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)) {e e' : ℕ} (he : e < 5) (he' : e' < 5)
    (h : d * x ^ e = d' * x ^ e') : d = d' ∧ e = e' := by
  have e1 : d'⁻¹ * d = x ^ e' * (x ^ e)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hz : d'⁻¹ * d ∈ Subgroup.zpowers x := by
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x e')
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x e))
  have h1 : d'⁻¹ * d = 1 := H.center_trivial (Subgroup.mul_mem _ (Subgroup.inv_mem _ hd') hd)
    fun t ht => H.comm_zx ht hz
  rw [inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, H.xpow_inj he he' (mul_left_cancel h)⟩

theorem RecHyp.no_mix {d d' : G} (hd : d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G))
    (hd' : d' ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)) (e e' : ℕ)
    (h : a * d * x ^ e = d' * x ^ e') : False := by
  have hz : x ^ e * (x ^ e')⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers x e)
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x e'))
  have h1 : a * d = d' * (x ^ e' * (x ^ e)⁻¹) := by
    rw [← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : a * (x ^ e * (x ^ e')⁻¹) = d' * d⁻¹ := by
    calc a * (x ^ e * (x ^ e')⁻¹) = a * ((x ^ e * (x ^ e')⁻¹) * d) * d⁻¹ := by
          simp [mul_assoc]
      _ = a * d * (x ^ e * (x ^ e')⁻¹) * d⁻¹ := by
          rw [← H.comm_zx hd hz, mul_assoc a d]
      _ = d' * d⁻¹ := by
          rw [h1]
          simp [mul_assoc]
  obtain ⟨k, hk, hzk⟩ := H.zpow_form hz
  apply H.notD k hk
  rw [← hzk, h2]
  exact Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd)

theorem RecHyp.elt_inj {d d' : G} (hd : d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G))
    (hd' : d' ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G)) {e e' f f' s s' : ℕ}
    (he : e < 5) (he' : e' < 5) (hf : f < 2) (hf' : f' < 2) (hs : s < 2) (hs' : s' < 2)
    (h : a ^ s * d * x ^ e * w ^ f = a ^ s' * d' * x ^ e' * w ^ f') :
    d = d' ∧ e = e' ∧ f = f' ∧ s = s' := by
  have hDP := H.d_le_P
  have hu : ∀ {t : G}, t ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G) → ∀ (s e : ℕ),
      a ^ s * t * x ^ e ∈ P := fun ht s e =>
    P.mul_mem (P.mul_mem (P.pow_mem H.aP s) (hDP ht)) (P.pow_mem H.xP e)
  have hff : f = f' := by
    have e1 : (a ^ s' * d' * x ^ e')⁻¹ * (a ^ s * d * x ^ e) = w ^ f' * (w ^ f)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    have hm := P.mul_mem (P.inv_mem (hu hd' s' e')) (hu hd s e)
    rw [e1] at hm
    interval_cases f <;> interval_cases f'
    · rfl
    · simp only [pow_zero, pow_one, inv_one, mul_one] at hm
      exact absurd hm H.wP
    · simp only [pow_zero, pow_one, one_mul, inv_mem_iff] at hm
      exact absurd hm H.wP
    · rfl
  subst hff
  have h0 := mul_right_cancel h
  interval_cases s <;> interval_cases s'
  · simp only [pow_zero, one_mul] at h0
    obtain ⟨h1, h2⟩ := H.same hd hd' he he' h0
    exact ⟨h1, h2, rfl, rfl⟩
  · simp only [pow_zero, pow_one, one_mul] at h0
    exact (H.no_mix hd' hd e' e h0.symm).elim
  · simp only [pow_zero, pow_one, one_mul] at h0
    exact (H.no_mix hd hd' e e' h0).elim
  · simp only [pow_one] at h0
    rw [mul_assoc, mul_assoc] at h0
    obtain ⟨h1, h2⟩ := H.same hd hd' he he' (mul_left_cancel h0)
    exact ⟨h1, h2, rfl, rfl⟩

theorem RecHyp.C_le_cx :
    Subgroup.closure ({x, a, b, w} : Set G) ≤ Subgroup.centralizer {x} := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;>
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exacts [H.ax, H.bx, H.wx]

theorem RecHyp.C_le_cw :
    Subgroup.closure ({x, a, b, w} : Set G) ≤ Subgroup.centralizer {w} := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;>
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exacts [H.wx.symm, H.aw, H.bw]

theorem RecHyp.C_le_R : Subgroup.closure ({x, a, b, w} : Set G) ≤ R := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  exacts [H.hPR H.xP, H.hPR H.aP, H.hPR H.bP, H.wR]

theorem RecHyp.D_le_C :
    Subgroup.closure ({⁅a, b⁆, b} : Set G) ≤ Subgroup.closure ({x, a, b, w} : Set G) := by
  have haC : a ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  have hbC : b ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [SetLike.mem_coe, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haC hbC)
      (Subgroup.inv_mem _ haC)) (Subgroup.inv_mem _ hbC)
  · exact hbC

theorem RecHyp.card_CR_le :
    Nat.card (Subgroup.centralizer {x} ⊓ R : Subgroup G) ≤
      2 * Nat.card (Subgroup.centralizer {x} ⊓ P : Subgroup G) := by
  set A := (Subgroup.centralizer {x} ⊓ R : Subgroup G)
  set B := (Subgroup.centralizer {x} ⊓ P : Subgroup G)
  have hw' : w⁻¹ * x = x * w⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, H.wx, mul_assoc, mul_inv_cancel, mul_one]
  have hsub : (A : Set G) ⊆ (B : Set G) ∪ (fun g => w * g) '' (B : Set G) := by
    intro g hg
    obtain ⟨hgx, hgR⟩ := Subgroup.mem_inf.1 hg
    by_cases hgP : g ∈ P
    · exact Or.inl (Subgroup.mem_inf.2 ⟨hgx, hgP⟩)
    · right
      refine ⟨w⁻¹ * g, Subgroup.mem_inf.2 ⟨?_, H.Rw g hgR hgP⟩, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
      rw [mul_assoc, hgx, ← mul_assoc, hw', mul_assoc]
  have hfin : (B : Set G).Finite := Set.toFinite _
  calc Nat.card A = (A : Set G).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ((B : Set G) ∪ (fun g => w * g) '' (B : Set G)).ncard :=
        Set.ncard_le_ncard hsub (hfin.union (hfin.image _))
    _ ≤ (B : Set G).ncard + ((fun g => w * g) '' (B : Set G)).ncard := Set.ncard_union_le _ _
    _ = (B : Set G).ncard + (B : Set G).ncard := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective _)]
    _ = 2 * Nat.card B := by
        have hB : (B : Set G).ncard = Nat.card B := (Nat.card_coe_set_eq _).symm
        rw [hB]
        ring

theorem RecHyp.C_facts :
    Nat.card (Subgroup.closure ({x, a, b, w} : Set G)) = 1200 ∧
    ∀ g ∈ Subgroup.closure ({x, a, b, w} : Set G), ∃ d ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G),
      ∃ e < 5, ∃ f < 2, ∃ s < 2, g = a ^ s * d * x ^ e * w ^ f := by
  have hDC := H.D_le_C
  have hle0 := H.card_CR_le
  have hcx := H.C_le_cx
  have hcR := H.C_le_R
  set C := Subgroup.closure ({x, a, b, w} : Set G) with hC
  set D := Subgroup.closure ({⁅a, b⁆, b} : Set G) with hD
  have hxC : x ∈ C := Subgroup.subset_closure (by simp)
  have haC : a ∈ C := Subgroup.subset_closure (by simp)
  have hwC : w ∈ C := Subgroup.subset_closure (by simp)
  let F : D × Fin 5 × Fin 2 × Fin 2 → C := fun p =>
    ⟨a ^ (p.2.2.2 : ℕ) * p.1 * x ^ (p.2.1 : ℕ) * w ^ (p.2.2.1 : ℕ),
      C.mul_mem (C.mul_mem (C.mul_mem (C.pow_mem haC _) (hDC p.1.2)) (C.pow_mem hxC _))
        (C.pow_mem hwC _)⟩
  have hinj : Function.Injective F := by
    rintro ⟨⟨d, hd⟩, e, f, s⟩ ⟨⟨d', hd'⟩, e', f', s'⟩ h
    have h' := congrArg Subtype.val h
    obtain ⟨h1, h2, h3, h4⟩ := H.elt_inj hd hd' e.2 e'.2 f.2 f'.2 s.2 s'.2 h'
    subst h1
    rw [Fin.ext h2, Fin.ext h3, Fin.ext h4]
  have hcardD : Nat.card (D × Fin 5 × Fin 2 × Fin 2) = 1200 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, H.dCard,
      Nat.card_eq_fintype_card (α := Fin 5), Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin, Fintype.card_fin]
  have hle : Nat.card C ≤ 1200 :=
    calc Nat.card C ≤ Nat.card (Subgroup.centralizer {x} ⊓ R : Subgroup G) :=
          Subgroup.card_le_of_le (le_inf hcx hcR)
      _ ≤ 2 * Nat.card (Subgroup.centralizer {x} ⊓ P : Subgroup G) := hle0
      _ ≤ 2 * 600 := Nat.mul_le_mul_left _ H.bound
  have hge : 1200 ≤ Nat.card C := by
    rw [← hcardD]
    exact Nat.card_le_card_of_injective F hinj
  refine ⟨le_antisymm hle hge, fun g hg => ?_⟩
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcardD]; exact hle)
  obtain ⟨⟨⟨d, hd⟩, e, f, s⟩, hp⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨d, hd, e, e.2, f, f.2, s, s.2, (congrArg Subtype.val hp).symm⟩

theorem RecHyp.C_eq :
    Subgroup.closure ({x, a, b, w} : Set G) = Subgroup.centralizer {x} ⊓ R := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf H.C_le_cx H.C_le_R)
  rw [H.C_facts.1]
  calc _ ≤ 2 * Nat.card (Subgroup.centralizer {x} ⊓ P : Subgroup G) := H.card_CR_le
    _ ≤ 2 * 600 := Nat.mul_le_mul_left _ H.bound

theorem RecHyp.D_eq :
    ⁅Subgroup.closure ({x, a, b, w} : Set G), Subgroup.closure ({x, a, b, w} : Set G)⁆ =
      Subgroup.closure ({⁅a, b⁆, b} : Set G) := by
  have hxc : ∀ g ∈ ({x, a, b, w} : Set G), x * g = g * x := by
    rintro _ (rfl | rfl | rfl | rfl)
    exacts [rfl, H.ax.symm, H.bx.symm, H.wx.symm]
  have hwc : ∀ g ∈ ({x, a, b, w} : Set G), w * g = g * w := by
    rintro _ (rfl | rfl | rfl | rfl)
    exacts [H.wx, H.aw.symm, H.bw.symm, rfl]
  have hdx := H.comm_d H.ax H.bx
  have hdw := H.comm_d H.aw H.bw
  have cA1 := H.cjA1
  have cA2 := H.cjA2
  have cB1 := H.cjB1
  have hbc := H.bc
  have hab0 := H.ax
  have hbx0 := H.bx
  have haw0 := H.aw
  have hbw0 := H.bw
  set C := Subgroup.closure ({x, a, b, w} : Set G) with hC
  have haC : a ∈ C := Subgroup.subset_closure (by simp)
  have hbC : b ∈ C := Subgroup.subset_closure (by simp)
  apply commutator_closure_eq_closure
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht <;> rw [ht]
    · exact Subgroup.commutator_mem_commutator haC hbC
    · have h1 : a * (b⁻¹ * b⁻¹) ∈ C :=
        C.mul_mem haC (C.mul_mem (C.inv_mem hbC) (C.inv_mem hbC))
      have h2 : b⁻¹ * (b⁻¹ * (a * b⁻¹)) ∈ C :=
        C.mul_mem (C.inv_mem hbC) (C.mul_mem (C.inv_mem hbC) (C.mul_mem haC (C.inv_mem hbC)))
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [← hbc] at this
      exact this
  · intro s hs t ht
    have htD : t ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G) := Subgroup.subset_closure ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with hs | hs | hs | hs <;> rw [hs]
    · rw [← hdx t htD, mul_inv_cancel_right]
      exact htD
    · rcases ht with ht | ht <;> rw [ht]
      exacts [cA1, cA2]
    · rcases ht with ht | ht <;> rw [ht]
      · exact cB1
      · rw [mul_inv_cancel_right]
        exact Subgroup.subset_closure (by simp)
    · rw [← hdw t htD, mul_inv_cancel_right]
      exact htD
  · intro s hs s' hs'
    have h1 : ∀ g h : G, g * h = h * g →
        ⁅g, h⁆ ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G) := fun g h e => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 e]
      exact Subgroup.one_mem _
    have hab : ⁅a, b⁆ ∈ Subgroup.closure ({⁅a, b⁆, b} : Set G) := Subgroup.subset_closure (by simp)
    have hxs := hxc s' hs'
    have hws := hwc s' hs'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs'
    rcases hs with hs0 | hs0 | hs0 | hs0 <;> rw [hs0]
    · exact h1 _ _ hxs
    · rcases hs' with hs1 | hs1 | hs1 | hs1 <;> rw [hs1]
      · exact h1 _ _ hab0
      · exact h1 _ _ rfl
      · exact hab
      · exact h1 _ _ haw0
    · rcases hs' with hs1 | hs1 | hs1 | hs1 <;> rw [hs1]
      · exact h1 _ _ hbx0
      · have := Subgroup.inv_mem _ hab
        rwa [commutatorElement_inv] at this
      · exact h1 _ _ rfl
      · exact h1 _ _ hbw0
    · exact h1 _ _ hws

theorem RecHyp.mem_cent_iff (g : G) :
    g ∈ Subgroup.centralizer (Subgroup.closure ({⁅a, b⁆, b} : Set G) : Set G) ⊓
        Subgroup.closure ({x, a, b, w} : Set G) ↔
      ∃ e < 5, ∃ f < 2, g = x ^ e * w ^ f := by
  have hxw : ∀ e f : ℕ, x ^ e * w ^ f ∈
      Subgroup.centralizer (Subgroup.closure ({⁅a, b⁆, b} : Set G) : Set G) := fun e f => by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : Commute t x := H.comm_d H.ax H.bx t ht
    have h2 : Commute t w := H.comm_d H.aw H.bw t ht
    exact ((h1.pow_right e).mul_right (h2.pow_right f)).eq
  have hxC : x ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwC : w ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  constructor
  · rintro ⟨hgD, hgC⟩
    obtain ⟨d, hd, e, he, f, hf, s, hs, rfl⟩ := H.C_facts.2 g hgC
    have hu : a ^ s * d ∈
        Subgroup.centralizer (Subgroup.closure ({⁅a, b⁆, b} : Set G) : Set G) := by
      have := Subgroup.mul_mem _ hgD (Subgroup.inv_mem _ (hxw e f))
      rwa [mul_assoc (a ^ s * d), mul_inv_cancel_right] at this
    rw [Subgroup.mem_centralizer_iff] at hu
    interval_cases s
    · simp only [pow_zero, one_mul] at hu ⊢
      have hd1 : d = 1 := H.center_trivial hd fun t ht => hu t ht
      exact ⟨e, he, f, hf, by rw [hd1, one_mul]⟩
    · exfalso
      simp only [pow_one] at hu
      rcases H.cent d hd with h | h
      · exact h (hu _ (Subgroup.subset_closure (by simp))).symm
      · exact h (hu _ (Subgroup.subset_closure (by simp))).symm
  · rintro ⟨e, he, f, hf, rfl⟩
    exact ⟨hxw e f, Subgroup.mul_mem _ (Subgroup.pow_mem _ hxC e) (Subgroup.pow_mem _ hwC f)⟩

theorem RecHyp.facts : RecFacts P R x w (Subgroup.closure ({x, a, b, w} : Set G)) := by
  have hCD := H.D_eq
  have hcard := H.C_facts.1
  have hCeq := H.C_eq
  have hiff := H.mem_cent_iff
  have hCR := H.card_CR_le
  have hcw := H.C_le_cw
  have hDP := H.d_le_P
  have hxP := H.xP
  have hwP := H.wP
  have hox := H.orderOf_x
  have how := H.orderOf_w
  have hxC : x ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwC : w ∈ Subgroup.closure ({x, a, b, w} : Set G) := Subgroup.subset_closure (by simp)
  have hinj2 : ∀ {e e' f f' : ℕ}, e < 5 → e' < 5 → f < 2 → f' < 2 →
      x ^ e * w ^ f = x ^ e' * w ^ f' → e = e' ∧ f = f' := by
    intro e e' f f' he he' hf hf' h
    have h' : a ^ 0 * 1 * x ^ e * w ^ f = a ^ 0 * 1 * x ^ e' * w ^ f' := by
      simp only [pow_zero, one_mul]
      exact h
    obtain ⟨-, h2, h3, -⟩ := H.elt_inj (Subgroup.one_mem _) (Subgroup.one_mem _) he he' hf hf'
      (by norm_num) (by norm_num) h'
    exact ⟨h2, h3⟩
  set C := Subgroup.closure ({x, a, b, w} : Set G) with hC
  set D := Subgroup.closure ({⁅a, b⁆, b} : Set G) with hD
  have hCP : C ⊓ P = Subgroup.centralizer {x} ⊓ P := by
    rw [hCeq, inf_assoc, inf_eq_right.2 H.hPR]
  unfold RecFacts
  rw [hCD]
  refine ⟨hCeq, hcard, hCP, ?_, hDP, H.dSimple,
    ⟨_, Subgroup.subset_closure (by simp), _, Subgroup.subset_closure (by simp), H.nab⟩,
    H.dCard, ?_, ?_, ?_, H.wx.symm, ?_, ?_⟩
  · rw [hCP]
    apply le_antisymm H.bound
    rw [← hCeq, hcard] at hCR
    omega
  · exact ⟨⟨w, hwC⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.1 (hcw g.2)), rfl⟩
  · apply le_antisymm
    · intro g hg
      obtain ⟨e, -, f, -, rfl⟩ := (hiff g).1 hg
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers _ e))
        (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers _ f))
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact (hiff x).2 ⟨1, by norm_num, 0, by norm_num, by simp⟩
      · rw [Subgroup.zpowers_le]
        exact (hiff w).2 ⟨0, by norm_num, 1, by norm_num, by simp⟩
  · apply disjoint_iff.1
    apply Subgroup.disjoint_of_coprime_natCard
    rw [Nat.card_zpowers, Nat.card_zpowers, hox, how]
    norm_num
  · set φ : Fin 5 × Fin 2 → G := fun p => x ^ (p.1 : ℕ) * w ^ (p.2 : ℕ) with hφ
    have hinj : Function.Injective φ := by
      rintro ⟨e, f⟩ ⟨e', f'⟩ h
      obtain ⟨h2, h3⟩ := hinj2 e.2 e'.2 f.2 f'.2 h
      exact Prod.ext (Fin.ext h2) (Fin.ext h3)
    have hset : ((Subgroup.centralizer (D : Set G) ⊓ C : Subgroup G) : Set G) = Set.range φ := by
      ext g
      rw [SetLike.mem_coe, hiff]
      constructor
      · rintro ⟨e, he, f, hf, rfl⟩
        exact ⟨(⟨e, he⟩, ⟨f, hf⟩), rfl⟩
      · rintro ⟨⟨e, f⟩, rfl⟩
        exact ⟨e, e.2, f, f.2, rfl⟩
    rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective hinj]
    simp
  · apply le_antisymm
    · intro g hg
      rw [← inf_assoc] at hg
      obtain ⟨hgDC, hgP⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨e, he, f, hf, rfl⟩ := (hiff g).1 hgDC
      interval_cases f
      · rw [pow_zero, mul_one]
        exact Subgroup.npow_mem_zpowers _ e
      · exfalso
        apply hwP
        have := P.mul_mem (P.inv_mem (P.pow_mem hxP e)) hgP
        rwa [pow_one, inv_mul_cancel_left] at this
    · rw [Subgroup.zpowers_le, ← inf_assoc]
      exact Subgroup.mem_inf.2 ⟨(hiff x).2 ⟨1, by norm_num, 0, by norm_num, by simp⟩, hxP⟩

end Facts

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem card_centralizer_le_600
    {y : Equiv.Perm (Fin 3510)} (hyP : y ∈ fi22P) (hy : orderOf y = 5) :
    Nat.card (Subgroup.centralizer {y} ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) ≤ 600 := by
  obtain ⟨X, Y, hX, hY, hD, hN⟩ := orbit_part
  obtain ⟨L, hL, hLc, -⟩ := centralizer_facts hX hY hD
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set y' : fi22P := ⟨y, hyP⟩ with hy'_def
  have hy' : orderOf y' = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hy
  have hPy : IsPGroup 5 (Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy', pow_one])
  obtain ⟨T, hT⟩ := hPy.exists_le_sylow
  have hm : Nat.card fi22P = 5 ^ 2 * 2582470066176 := by norm_num [card_fi22P]
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hm (by norm_num) T
  have hyT : y' ∈ (T : Subgroup fi22P) := hT (Subgroup.mem_zpowers y')
  rw [← hg] at hyT
  have hmap := closure_pair_map X Y (MulAut.conj g)
  simp only [MulAut.conj_apply] at hmap
  rw [hmap] at hyT
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one] at hty
    have : orderOf y' = 1 := by rw [← hty, orderOf_one]
    omega
  obtain ⟨v, rfl⟩ := hD.closure_facts.2.2 t ht
  have hv : v ≠ 0 := by
    rintro rfl
    exact ht1 (by simp [planeMap])
  obtain ⟨n, -, hn⟩ := hN v hv
  have hconj : (g * n) * X * (g * n)⁻¹ = y' := by
    rw [← hty, ← hn]
    simp [MulAut.conj_apply, mul_assoc]
  have h2 : ((g * n : fi22P) : Equiv.Perm (Fin 3510)) * (X : Equiv.Perm (Fin 3510)) *
      ((g * n : fi22P) : Equiv.Perm (Fin 3510))⁻¹ = y := congrArg Subtype.val hconj
  rw [← CFSG.RankThree.Native.card_centralizer_inf_conj fi22P (g * n).2 h2]
  refine le_trans (Subgroup.card_le_of_le ?_) hL.le
  intro z hz
  obtain ⟨hzc, hzP⟩ := Subgroup.mem_inf.1 hz
  exact hLc ⟨z, hzP⟩ (Subgroup.mem_centralizer_singleton_iff.2
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hzc)))

end CFSG.KC.Fv8124
