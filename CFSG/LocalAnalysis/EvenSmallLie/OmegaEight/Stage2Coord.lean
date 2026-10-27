module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Fix
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix

abbrev Vec6 : Type := Fin 6 → ZMod 2

@[expose] def aPart (v : Vec12) : Vec6 := fun i => v ⟨2 * i, by omega⟩

@[expose] def bPart (v : Vec12) : Vec6 := fun i => v ⟨2 * i + 1, by omega⟩

@[expose] def join (a b : Vec6) : Vec12 := fun k =>
  if (k : ℕ) % 2 = 0 then a ⟨(k : ℕ) / 2, by omega⟩ else b ⟨(k : ℕ) / 2, by omega⟩

theorem aPart_join (a b : Vec6) : aPart (join a b) = a := by
  ext i
  simp only [aPart, join]
  rw [ite_eq_left (by omega)]
  congr 1
  ext
  simp only
  omega

theorem bPart_join (a b : Vec6) : bPart (join a b) = b := by
  ext i
  simp only [bPart, join]
  rw [ite_eq_right (by omega)]
  congr 1
  ext
  simp only
  omega

theorem join_parts (v : Vec12) : join (aPart v) (bPart v) = v := by
  ext k
  simp only [join, aPart, bPart]
  split_ifs with h
  · congr 1
    ext
    simp only
    omega
  · congr 1
    ext
    simp only
    omega

theorem aPart_add (v w : Vec12) : aPart (v + w) = aPart v + aPart w := rfl

theorem bPart_add (v w : Vec12) : bPart (v + w) = bPart v + bPart w := rfl

theorem aPart_zero : aPart 0 = 0 := rfl

theorem bPart_zero : bPart 0 = 0 := rfl

variable {G : Type*} [Group G]

structure CoordHyp (t : G) (Q R W : Subgroup G) (ψ : Vec6 → G) : Prop where
  comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  sq_eq_one : ∀ w ∈ W, w * w = 1
  card_eq : Nat.card W = 4096
  Q_le_W : Q ≤ W
  R_le_W : R ≤ W
  inf_eq : Q ⊓ R = ⊥
  sup_eq : Q ⊔ R = W
  t_mem : t ∈ Subgroup.normalizer (W : Set G)
  t_sq : t * t = 1
  Q_comm : ∀ q ∈ Q, q * t = t * q
  comm_mem : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ ∈ Q
  comm_eq_one : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ = 1 → r = 1
  ψ_add : ∀ v w, ψ (v + w) = ψ v * ψ w
  ψ_inj : Function.Injective ψ
  ψ_mem : ∀ v, ψ v ∈ Q
  mem_ψ : ∀ x ∈ Q, ∃ v, ψ v = x

@[expose] def cm (t r : G) : G := r * t * r⁻¹ * t⁻¹

namespace CoordHyp

variable {t : G} {Q R W : Subgroup G} {ψ : Vec6 → G}

theorem ψ_zero (h : CoordHyp t Q R W ψ) : ψ 0 = 1 := by
  have e := h.ψ_add 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

theorem cm_mul (h : CoordHyp t Q R W ψ) {r s : G} (hr : r ∈ W) (hs : s ∈ W) :
    cm t (r * s) = cm t r * cm t s := by
  have htW := Subgroup.mem_normalizer_iff.1 h.t_mem
  have hts : t * s⁻¹ * t⁻¹ ∈ W := (htW _).1 (W.inv_mem hs)
  have htr : t * r⁻¹ * t⁻¹ ∈ W := (htW _).1 (W.inv_mem hr)
  have hcs : cm t s ∈ W := by
    have : cm t s = s * (t * s⁻¹ * t⁻¹) := by unfold cm; group
    rw [this]
    exact W.mul_mem hs hts
  have hcr : cm t r ∈ W := by
    have : cm t r = r * (t * r⁻¹ * t⁻¹) := by unfold cm; group
    rw [this]
    exact W.mul_mem hr htr
  calc cm t (r * s) = r * cm t s * (t * r⁻¹ * t⁻¹) := by unfold cm; group
    _ = cm t s * r * (t * r⁻¹ * t⁻¹) := by rw [h.comm _ hr _ hcs]
    _ = cm t s * cm t r := by unfold cm; group
    _ = cm t r * cm t s := h.comm _ hcs _ hcr

theorem cm_one : cm t (1 : G) = 1 := by unfold cm; group

theorem cm_inv (h : CoordHyp t Q R W ψ) {r : G} (hr : r ∈ W) : cm t r⁻¹ = (cm t r)⁻¹ := by
  have e := h.cm_mul hr (W.inv_mem hr)
  rw [mul_inv_cancel, cm_one] at e
  exact (eq_inv_of_mul_eq_one_right e.symm)

theorem eq_of_cm_eq (h : CoordHyp t Q R W ψ) {r s : G} (hr : r ∈ R) (hs : s ∈ R)
    (e : cm t r = cm t s) : r = s := by
  have h1 : cm t (r * s⁻¹) = 1 := by
    rw [h.cm_mul (h.R_le_W hr) (W.inv_mem (h.R_le_W hs)), h.cm_inv (h.R_le_W hs), e,
      mul_inv_cancel]
  have := h.comm_eq_one _ (R.mul_mem hr (R.inv_mem hs)) h1
  exact mul_inv_eq_one.1 this

theorem card_Q [Finite G] (h : CoordHyp t Q R W ψ) : Nat.card Q = 64 := by
  have hb : Function.Bijective fun v : Vec6 => (⟨ψ v, h.ψ_mem v⟩ : Q) :=
    ⟨fun v w e => h.ψ_inj (congrArg Subtype.val e), fun x => by
      obtain ⟨v, hv⟩ := h.mem_ψ x x.2
      exact ⟨v, Subtype.ext hv⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb)]
  simp [Nat.card_eq_fintype_card]

theorem card_W_eq [Finite G] (h : CoordHyp t Q R W ψ) : Nat.card Q * Nat.card R = 4096 := by
  let μ : Q × R →* G :=
    { toFun := fun x => (x.1 : G) * x.2
      map_one' := by simp
      map_mul' := fun x y => by
        show ((x * y).1 : G) * (x * y).2 = (x.1 * x.2) * (y.1 * y.2)
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (x.1 : G) * y.1 * (x.2 * y.2) = x.1 * ((y.1 * x.2) * y.2) := by group
          _ = x.1 * ((x.2 * y.1) * y.2) := by
            rw [h.comm _ (h.Q_le_W y.1.2) _ (h.R_le_W x.2.2)]
          _ = x.1 * x.2 * (y.1 * y.2) := by group }
  have hW : W ≤ μ.range := by
    rw [← h.sup_eq]
    refine sup_le (fun q hq => ⟨(⟨q, hq⟩, 1), by simp [μ]⟩)
      (fun r hr => ⟨(1, ⟨r, hr⟩), by simp [μ]⟩)
  have hmem : ∀ x : Q × R, μ x ∈ W := fun x => W.mul_mem (h.Q_le_W x.1.2) (h.R_le_W x.2.2)
  have hb : Function.Bijective fun x : Q × R => (⟨μ x, hmem x⟩ : W) := by
    refine ⟨fun x y e => ?_, fun w => ?_⟩
    · have e' : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val e
      have h1 : (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
        calc (y.1 : G)⁻¹ * x.1 = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
          _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [e']
          _ = y.2 * (x.2 : G)⁻¹ := by group
      have h2 : (y.1 : G)⁻¹ * x.1 ∈ Q ⊓ R :=
        ⟨Q.mul_mem (Q.inv_mem y.1.2) x.1.2, h1 ▸ R.mul_mem y.2.2 (R.inv_mem x.2.2)⟩
      rw [h.inf_eq, Subgroup.mem_bot] at h2
      have hq : (x.1 : G) = y.1 := by
        have := congrArg (fun z => (y.1 : G) * z) h2
        simpa using this
      have hr : (x.2 : G) = y.2 := by
        rw [hq] at e'
        exact mul_left_cancel e'
      exact Prod.ext (Subtype.ext hq) (Subtype.ext hr)
    · obtain ⟨x, hx⟩ := hW w.2
      exact ⟨x, Subtype.ext hx⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective _ hb), h.card_eq]

theorem card_R [Finite G] (h : CoordHyp t Q R W ψ) : Nat.card R = 64 := by
  have := h.card_W_eq
  rw [h.card_Q] at this
  omega

theorem exists_cm [Finite G] (h : CoordHyp t Q R W ψ) (q : G) (hq : q ∈ Q) :
    ∃ r ∈ R, cm t r = q := by
  let c : R → Q := fun r => ⟨cm t r, h.comm_mem r r.2⟩
  have hinj : Function.Injective c := fun r s e =>
    Subtype.ext (h.eq_of_cm_eq r.2 s.2 (congrArg Subtype.val e))
  have hbij := hinj.bijective_of_nat_card_le (by rw [h.card_Q, h.card_R])
  obtain ⟨r, hr⟩ := hbij.2 ⟨q, hq⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

end CoordHyp

@[expose] noncomputable def rOf (t : G) (R : Subgroup G) (ψ : Vec6 → G) (b : Vec6) : G := by
  classical exact if hb : ∃ r ∈ R, cm t r = ψ b then hb.choose else 1

namespace CoordHyp

variable {t : G} {Q R W : Subgroup G} {ψ : Vec6 → G}

theorem rOf_spec [Finite G] (h : CoordHyp t Q R W ψ) (b : Vec6) :
    rOf t R ψ b ∈ R ∧ cm t (rOf t R ψ b) = ψ b := by
  have hb := h.exists_cm (ψ b) (h.ψ_mem b)
  unfold rOf
  rw [dite_eq_left hb]
  exact hb.choose_spec

theorem rOf_add [Finite G] (h : CoordHyp t Q R W ψ) (b b' : Vec6) :
    rOf t R ψ (b + b') = rOf t R ψ b * rOf t R ψ b' := by
  obtain ⟨h1, h2⟩ := h.rOf_spec b
  obtain ⟨h3, h4⟩ := h.rOf_spec b'
  obtain ⟨h5, h6⟩ := h.rOf_spec (b + b')
  refine h.eq_of_cm_eq h5 (R.mul_mem h1 h3) ?_
  rw [h6, h.cm_mul (h.R_le_W h1) (h.R_le_W h3), h2, h4, h.ψ_add]

end CoordHyp

@[expose] noncomputable def Phi (t : G) (R : Subgroup G) (ψ : Vec6 → G) (v : Vec12) : G :=
  ψ (aPart v) * rOf t R ψ (bPart v)

namespace CoordHyp

variable {t : G} {Q R W : Subgroup G} {ψ : Vec6 → G}

theorem Phi_mem [Finite G] (h : CoordHyp t Q R W ψ) (v : Vec12) : Phi t R ψ v ∈ W :=
  W.mul_mem (h.Q_le_W (h.ψ_mem _)) (h.R_le_W (h.rOf_spec _).1)

theorem Phi_add [Finite G] (h : CoordHyp t Q R W ψ) (v w : Vec12) :
    Phi t R ψ (v + w) = Phi t R ψ v * Phi t R ψ w := by
  unfold Phi
  rw [aPart_add, bPart_add, h.ψ_add, h.rOf_add]
  have e := h.comm _ (h.R_le_W (h.rOf_spec (bPart v)).1) _ (h.Q_le_W (h.ψ_mem (aPart w)))
  calc ψ (aPart v) * ψ (aPart w) * (rOf t R ψ (bPart v) * rOf t R ψ (bPart w)) =
      ψ (aPart v) * (ψ (aPart w) * rOf t R ψ (bPart v)) * rOf t R ψ (bPart w) := by group
    _ = ψ (aPart v) * (rOf t R ψ (bPart v) * ψ (aPart w)) * rOf t R ψ (bPart w) := by rw [e]
    _ = ψ (aPart v) * rOf t R ψ (bPart v) * (ψ (aPart w) * rOf t R ψ (bPart w)) := by group

theorem Phi_zero [Finite G] (h : CoordHyp t Q R W ψ) : Phi t R ψ 0 = 1 := by
  have e := h.Phi_add 0 0
  rw [add_zero] at e
  exact mul_eq_left.1 e.symm

theorem eq_zero_of_Phi_eq_one [Finite G] (h : CoordHyp t Q R W ψ) {v : Vec12}
    (hv : Phi t R ψ v = 1) : v = 0 := by
  obtain ⟨h1, h2⟩ := h.rOf_spec (bPart v)
  have hq : ψ (aPart v) = (rOf t R ψ (bPart v))⁻¹ := eq_inv_of_mul_eq_one_left hv
  have hm : ψ (aPart v) ∈ Q ⊓ R := ⟨h.ψ_mem _, hq ▸ R.inv_mem h1⟩
  rw [h.inf_eq, Subgroup.mem_bot] at hm
  have ha : aPart v = 0 := h.ψ_inj (hm.trans h.ψ_zero.symm)
  have hr : rOf t R ψ (bPart v) = 1 := by
    rw [hm] at hq
    exact (inv_eq_one.1 hq.symm)
  have hb : bPart v = 0 := by
    rw [hr, cm_one] at h2
    exact h.ψ_inj (h2.symm.trans h.ψ_zero.symm)
  rw [← join_parts v, ha, hb]
  ext k
  simp [join]

@[expose] noncomputable def PhiHom [Finite G] (h : CoordHyp t Q R W ψ) :
    Multiplicative Vec12 →* W where
  toFun v := ⟨Phi t R ψ (Multiplicative.toAdd v), h.Phi_mem _⟩
  map_one' := Subtype.ext h.Phi_zero
  map_mul' _ _ := Subtype.ext (h.Phi_add _ _)

theorem PhiHom_bijective [Finite G] (h : CoordHyp t Q R W ψ) : Function.Bijective h.PhiHom := by
  refine Function.Injective.bijective_of_nat_card_le (fun v w e => ?_) ?_
  · have e' : Phi t R ψ (Multiplicative.toAdd v) = Phi t R ψ (Multiplicative.toAdd w) :=
      congrArg Subtype.val e
    have h1 : Phi t R ψ (Multiplicative.toAdd v + Multiplicative.toAdd w) = 1 := by
      rw [h.Phi_add, e']
      exact h.sq_eq_one _ (h.Phi_mem _)
    have h2 := h.eq_zero_of_Phi_eq_one h1
    apply Multiplicative.toAdd.injective
    have hneg : ∀ y : Vec12, y + y = 0 := fun y => by
      ext i
      have : ∀ c : ZMod 2, c + c = 0 := by decide
      exact this _
    calc Multiplicative.toAdd v = Multiplicative.toAdd v + (Multiplicative.toAdd w +
          Multiplicative.toAdd w) := by rw [hneg, add_zero]
      _ = (Multiplicative.toAdd v + Multiplicative.toAdd w) + Multiplicative.toAdd w := by
          rw [add_assoc]
      _ = Multiplicative.toAdd w := by rw [h2, zero_add]
  · rw [h.card_eq]
    simp [Nat.card_eq_fintype_card]

@[expose] noncomputable def coordEquiv [Finite G] (h : CoordHyp t Q R W ψ) :
    W ≃* Multiplicative Vec12 :=
  (MulEquiv.ofBijective h.PhiHom h.PhiHom_bijective).symm

theorem coordEquiv_symm_apply [Finite G] (h : CoordHyp t Q R W ψ) (v : Vec12) :
    ((h.coordEquiv.symm (Multiplicative.ofAdd v) : W) : G) = Phi t R ψ v := rfl

theorem coordEquiv_Phi [Finite G] (h : CoordHyp t Q R W ψ) (v : Vec12) :
    h.coordEquiv ⟨Phi t R ψ v, h.Phi_mem v⟩ = Multiplicative.ofAdd v := by
  apply h.coordEquiv.symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact Subtype.ext (h.coordEquiv_symm_apply v).symm

theorem conj_t_Phi [Finite G] (h : CoordHyp t Q R W ψ) (v : Vec12) :
    t * Phi t R ψ v * t⁻¹ = Phi t R ψ (join (aPart v + bPart v) (bPart v)) := by
  obtain ⟨h1, h2⟩ := h.rOf_spec (bPart v)
  set r := rOf t R ψ (bPart v)
  have hq : t * ψ (aPart v) * t⁻¹ = ψ (aPart v) := by
    rw [← h.Q_comm _ (h.ψ_mem _)]
    group
  have hc2 : cm t r * cm t r = 1 := h.sq_eq_one _ (h.Q_le_W (h.comm_mem r h1))
  have hr : t * r * t⁻¹ = cm t r * r := by
    have hinv : (cm t r)⁻¹ = cm t r := inv_eq_of_mul_eq_one_right hc2
    calc t * r * t⁻¹ = (cm t r)⁻¹ * r := by unfold cm; group
      _ = cm t r * r := by rw [hinv]
  unfold Phi
  rw [aPart_join, bPart_join, h.ψ_add, ← h2]
  calc t * (ψ (aPart v) * r) * t⁻¹ = (t * ψ (aPart v) * t⁻¹) * (t * r * t⁻¹) := by group
    _ = ψ (aPart v) * cm t r * r := by rw [hq, hr, mul_assoc]

theorem conj_Phi_of_act [Finite G] (h : CoordHyp t Q R W ψ) {p : G} (hpt : p * t = t * p)
    (hpR : ∀ r ∈ R, p * r * p⁻¹ ∈ R) {A : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hA : ∀ x, p * ψ x * p⁻¹ = ψ (A *ᵥ x)) (v : Vec12) :
    p * Phi t R ψ v * p⁻¹ = Phi t R ψ (join (A *ᵥ aPart v) (A *ᵥ bPart v)) := by
  obtain ⟨h1, h2⟩ := h.rOf_spec (bPart v)
  obtain ⟨h3, h4⟩ := h.rOf_spec (A *ᵥ bPart v)
  have hcm : cm t (p * rOf t R ψ (bPart v) * p⁻¹) = p * cm t (rOf t R ψ (bPart v)) * p⁻¹ := by
    have hpt' : p⁻¹ * t = t * p⁻¹ := by
      calc p⁻¹ * t = p⁻¹ * (t * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * t) * p⁻¹ := by rw [hpt]
        _ = t * p⁻¹ := by group
    unfold cm
    calc p * rOf t R ψ (bPart v) * p⁻¹ * t * (p * rOf t R ψ (bPart v) * p⁻¹)⁻¹ * t⁻¹ =
        p * rOf t R ψ (bPart v) * (p⁻¹ * t) * p * (rOf t R ψ (bPart v))⁻¹ * p⁻¹ * t⁻¹ := by
          group
      _ = p * rOf t R ψ (bPart v) * (t * p⁻¹) * p * (rOf t R ψ (bPart v))⁻¹ * p⁻¹ * t⁻¹ := by
          rw [hpt']
      _ = p * (rOf t R ψ (bPart v) * t * (rOf t R ψ (bPart v))⁻¹ * t⁻¹) * (t * p⁻¹ * t⁻¹) := by
          group
      _ = p * (rOf t R ψ (bPart v) * t * (rOf t R ψ (bPart v))⁻¹ * t⁻¹) * p⁻¹ := by
          rw [← hpt']
          group
  have hr : p * rOf t R ψ (bPart v) * p⁻¹ = rOf t R ψ (A *ᵥ bPart v) :=
    h.eq_of_cm_eq (hpR _ h1) h3 (by rw [hcm, h2, hA, h4])
  unfold Phi
  rw [aPart_join, bPart_join, ← hA, ← hr]
  group

end CoordHyp

end CFSG.EvenSmallLie.OmegaEight.Stage2
