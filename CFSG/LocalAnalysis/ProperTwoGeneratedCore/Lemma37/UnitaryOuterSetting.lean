module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open CFSG.ProperTwoGeneratedCore.RootCenter

structure OuterSetting (X : Type*) [Group X] (J P : Subgroup X) (zb : X) (q : ℕ) : Prop where
  isPGroup : IsPGroup 2 P
  zb_mem : zb ∈ P
  zb_central : ∀ x : X, x * zb = zb * x
  zb_not_mem : zb ∉ J
  zb_sq : zb ^ 2 = 1
  involution : ∀ t : X, t ^ 2 = 1 → t ≠ 1 → t ∈ J ∨ zb * t ∈ J
  model : UnitaryOuterModel J (P.comap J.subtype) q

namespace OuterSetting

variable {X : Type*} [Group X] {J P : Subgroup X} [J.Normal] {zb : X} {q : ℕ}
  (hS : OuterSetting X J P zb q)

abbrev torusT (P J : Subgroup X) : Subgroup X := P ⊓ Subgroup.centralizer (J : Set X)

omit [J.Normal] in
theorem mem_rootJ {x : J} : x ∈ P.comap J.subtype ↔ (x : X) ∈ P := Iff.rfl

theorem conjNormal_eq_one {k : X} (hk : k ∈ Subgroup.centralizer (J : Set X)) :
    (MulAut.conjNormal k : MulAut J) = 1 := by
  ext j
  rw [MulAut.conjNormal_apply, MulAut.one_apply,
    ← Subgroup.mem_centralizer_iff.mp hk j j.2, mul_inv_cancel_right]

theorem coe_conjNormal_symm (m : X) (x : J) :
    (((MulAut.conjNormal m : MulAut J).symm x : J) : X) = m⁻¹ * x * m := by
  have h := MulAut.conjNormal_apply (H := J) m ((MulAut.conjNormal m : MulAut J).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

theorem map_rootJ {m : X} (hm : m ∈ P) :
    (P.comap J.subtype).map (MulAut.conjNormal m : MulAut J).toMonoidHom = P.comap J.subtype := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_rootJ, mem_rootJ, coe_conjNormal_symm]
  constructor
  · intro h
    have := P.mul_mem (P.mul_mem hm h) (P.inv_mem hm)
    simpa [mul_assoc] using this
  · intro h
    exact P.mul_mem (P.mul_mem (P.inv_mem hm) h) hm

@[expose] def InRT (P J : Subgroup X) (w : X) : Prop :=
  ∃ y ∈ P ⊓ J, ∃ t ∈ torusT P J, w = y * t

include hS in
theorem eq_one_of_mem_centralizer {x : X} (hxP : x ∈ P) (hxJ : x ∈ J)
    (hxK : x ∈ Subgroup.centralizer (J : Set X)) : x = 1 := by
  have h : MulAut.conj (⟨x, hxJ⟩ : J) = 1 := by
    rw [← MulAut.conjNormal_val]
    exact conjNormal_eq_one hxK
  exact congrArg Subtype.val (hS.model.conj_inj _ hxP h)

theorem inRT_of_conjNormal_mem {m : X} (hm : m ∈ P)
    (h : (MulAut.conjNormal m : MulAut J) ∈ (P.comap J.subtype).map MulAut.conj) :
    InRT P J m := by
  obtain ⟨r, hr, hrm⟩ := h
  refine ⟨r, Subgroup.mem_inf.mpr ⟨hr, r.2⟩, (r : X)⁻¹ * m,
    Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem hr) hm, ?_⟩, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hrm ⟨j, hj⟩)
  rw [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  calc j * ((r : X)⁻¹ * m) = (r : X)⁻¹ * ((r : X) * j * (r : X)⁻¹) * m := by group
    _ = (r : X)⁻¹ * (m * j * m⁻¹) * m := by rw [h1]
    _ = (r : X)⁻¹ * m * j := by group

include hS in
theorem eq_of_mul_eq {y y' t t' : X} (hy : y ∈ P ⊓ J) (hy' : y' ∈ P ⊓ J) (ht : t ∈ torusT P J)
    (ht' : t' ∈ torusT P J) (h : y * t = y' * t') : y = y' ∧ t = t' := by
  have hx : y'⁻¹ * y = t' * t⁻¹ := by
    calc y'⁻¹ * y = y'⁻¹ * (y * t) * t⁻¹ := by group
      _ = y'⁻¹ * (y' * t') * t⁻¹ := by rw [h]
      _ = t' * t⁻¹ := by group
  have h1 : y'⁻¹ * y = 1 := by
    refine hS.eq_one_of_mem_centralizer (P.mul_mem (P.inv_mem hy'.1) hy.1)
      (J.mul_mem (J.inv_mem hy'.2) hy.2) ?_
    rw [hx]
    exact Subgroup.mul_mem _ ht'.2 (Subgroup.inv_mem _ ht.2)
  have hyy : y = y' := (inv_mul_eq_one.mp h1).symm
  refine ⟨hyy, ?_⟩
  rw [hyy] at h
  exact mul_left_cancel h

omit [J.Normal] in
include hS in
theorem zb_mem_centralizer : zb ∈ Subgroup.centralizer (J : Set X) :=
  Subgroup.mem_centralizer_iff.mpr fun j _ => hS.zb_central j

include hS in
theorem eq_one_or_eq_zb {t : X} (ht : t ∈ torusT P J) (ht2 : t ^ 2 = 1) : t = 1 ∨ t = zb := by
  by_cases ht1 : t = 1
  · exact Or.inl ht1
  right
  rcases hS.involution t ht2 ht1 with htJ | htJ
  · exact absurd (hS.eq_one_of_mem_centralizer ht.1 htJ ht.2) ht1
  · have h := hS.eq_one_of_mem_centralizer (P.mul_mem hS.zb_mem ht.1) htJ
      (Subgroup.mul_mem _ hS.zb_mem_centralizer ht.2)
    have hzz : zb * zb = 1 := by rw [← pow_two]; exact hS.zb_sq
    calc t = zb * (zb * t) := by rw [← mul_assoc, hzz, one_mul]
      _ = zb := by rw [h, mul_one]

include hS in
theorem false_of_sq_eq {m : X} (hm : m ∈ P) (hmRT : ¬ InRT P J m) {u : X} (hu : u ∈ P ⊓ J)
    (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) (hsq : m ^ 2 = u ∨ m ^ 2 = u * zb) : False := by
  set ψ : MulAut J := MulAut.conjNormal m with hψ
  have hψR := map_rootJ (J := J) hm
  have hψ2 : ψ ^ 2 = MulAut.conj (⟨u, hu.2⟩ : J) := by
    rw [hψ, ← map_pow]
    rcases hsq with h | h
    · rw [h, ← MulAut.conjNormal_val]
    · rw [h, map_mul, conjNormal_eq_one hS.zb_mem_centralizer, mul_one, ← MulAut.conjNormal_val]
  have hψ2' : ψ ^ 2 ∈ (P.comap J.subtype).map MulAut.conj :=
    hψ2 ▸ Subgroup.mem_map_of_mem _ (show (⟨u, hu.2⟩ : J) ∈ P.comap J.subtype from hu.1)
  have hψU := hS.model.fix ψ hψR hψ2'
  rcases hS.model.aut_sq ψ hψR hψU ⟨u, hu.2⟩ hu.1 (Subtype.ext hu2) hψ2 with h | h
  · exact hmRT (inRT_of_conjNormal_mem hm h)
  · rw [hψ2] at h
    exact hu1 (congrArg Subtype.val (hS.model.conj_inj _ hu.1 h))

omit [J.Normal] in
theorem inRT_one : InRT P J 1 :=
  ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [mul_one]⟩

omit [J.Normal] in
include hS in
theorem exists_sq_inRT {s : X} (hs : s ∈ P) (hsRT : ¬ InRT P J s) :
    ∃ s₁ ∈ P, ¬ InRT P J s₁ ∧ InRT P J (s₁ ^ 2) := by
  classical
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
  have hp : ∃ i, InRT P J (s ^ 2 ^ i) :=
    ⟨k, by
      have : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact inRT_one⟩
  set i₀ := Nat.find hp with hi₀
  have hi₀0 : i₀ ≠ 0 := by
    intro h
    have := Nat.find_spec hp
    rw [← hi₀, h, pow_zero, pow_one] at this
    exact hsRT this
  refine ⟨s ^ 2 ^ (i₀ - 1), P.pow_mem hs _, Nat.find_min hp (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hi₀0)]
  exact Nat.find_spec hp

theorem conjNormal_mul_of_mem {y t : X} (hy : y ∈ J) (ht : t ∈ Subgroup.centralizer (J : Set X)) :
    (MulAut.conjNormal (y * t) : MulAut J) = MulAut.conj (⟨y, hy⟩ : J) := by
  rw [map_mul, conjNormal_eq_one ht, mul_one, ← MulAut.conjNormal_val]

theorem mem_centralizer_of_conjNormal_eq_one {w : X} (h : (MulAut.conjNormal w : MulAut J) = 1) :
    w ∈ Subgroup.centralizer (J : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨j, hj⟩)
  rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc j * w = w * j * w⁻¹ * w := by rw [h1]
    _ = w * j := by group

include hS in
theorem exists_outer_sq_mem_torus {s : X} (hs : s ∈ P) (hsRT : ¬ InRT P J s) :
    ∃ w₁ ∈ P, ¬ InRT P J w₁ ∧ w₁ ^ 2 ∈ torusT P J := by
  obtain ⟨s₁, hs₁, hs₁RT, y, hy, t, ht, hyt⟩ := hS.exists_sq_inRT hs hsRT
  set ψ : MulAut J := MulAut.conjNormal s₁ with hψ
  have hψR := map_rootJ (J := J) hs₁
  have hψ2 : ψ ^ 2 ∈ (P.comap J.subtype).map MulAut.conj := by
    rw [hψ, ← map_pow, hyt, conjNormal_mul_of_mem hy.2 ht.2]
    exact Subgroup.mem_map_of_mem _ (show (⟨y, hy.2⟩ : J) ∈ P.comap J.subtype from hy.1)
  obtain ⟨y', hy', hy'2⟩ := hS.model.exists_sq_eq_one ψ hψR hψ2
  have hw₁P : (y' : X)⁻¹ * s₁ ∈ P := P.mul_mem (P.inv_mem hy') hs₁
  refine ⟨(y' : X)⁻¹ * s₁, hw₁P, fun ⟨y'', hy'', t'', ht'', h⟩ => hs₁RT ?_, ?_⟩
  · refine ⟨y' * y'', ⟨P.mul_mem hy' hy''.1, J.mul_mem y'.2 hy''.2⟩, t'', ht'', ?_⟩
    rw [mul_assoc, ← h]
    group
  · refine ⟨P.pow_mem hw₁P 2, mem_centralizer_of_conjNormal_eq_one ?_⟩
    rw [map_pow, map_mul, ← hy'2, hψ]
    congr 2
    rw [← Subgroup.coe_inv, MulAut.conjNormal_val]

include hS in
theorem mem_coset_of_sq_eq_zb {w₁ w : X} (hw₁ : w₁ ∈ P) (hw₁RT : ¬ InRT P J w₁)
    (hw₁2 : w₁ ^ 2 ∈ torusT P J) (hw : w ∈ P) (hwRT : ¬ InRT P J w) (hw2 : w ^ 2 = zb) :
    ∃ y ∈ P ⊓ J, ∃ t ∈ torusT P J, w = y * t * w₁ := by
  set ψ : MulAut J := MulAut.conjNormal w with hψ
  set ψ₁ : MulAut J := MulAut.conjNormal w₁ with hψ₁
  have hY : IsPGroup 2 (P.map (MulAut.conjNormal : X →* MulAut J)) := hS.isPGroup.map _
  have h1 : ψ ^ 2 ∈ (P.comap J.subtype).map MulAut.conj := by
    rw [hψ, ← map_pow, hw2, conjNormal_eq_one hS.zb_mem_centralizer]
    exact Subgroup.one_mem _
  have h2 : ψ₁ ^ 2 ∈ (P.comap J.subtype).map MulAut.conj := by
    rw [hψ₁, ← map_pow, conjNormal_eq_one hw₁2.2]
    exact Subgroup.one_mem _
  have h := hS.model.mul_inv_mem _ hY ψ (Subgroup.mem_map_of_mem _ hw) ψ₁
    (Subgroup.mem_map_of_mem _ hw₁) (map_rootJ hw) (map_rootJ hw₁) h1 h2
    (fun h => hwRT (inRT_of_conjNormal_mem hw h)) (fun h => hw₁RT (inRT_of_conjNormal_mem hw₁ h))
  rw [hψ, hψ₁, ← map_inv, ← map_mul] at h
  obtain ⟨y, hy, t, ht, hyt⟩ := inRT_of_conjNormal_mem (P.mul_mem hw (P.inv_mem hw₁)) h
  exact ⟨y, hy, t, ht, by rw [← hyt]; group⟩

omit [J.Normal] in
include hS in
theorem card_sq_one_root : Nat.card {x : X // x ∈ P ⊓ J ∧ x ^ 2 = 1} = q := by
  rw [← hS.model.card_sq_one]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1.2⟩, x.2.1.1, Subtype.ext (by simpa using x.2.2)⟩
      invFun := fun y => ⟨y.1, ⟨y.2.1, y.1.2⟩, by simpa using congrArg Subtype.val y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [J.Normal] in
include hS in
theorem card_sq_root {u : X} (hu : u ∈ P ⊓ J) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) :
    Nat.card {x : X // x ∈ P ⊓ J ∧ x ^ 2 = u} = q * (q + 1) := by
  rw [← hS.model.card_sq ⟨u, hu.2⟩ hu.1 (fun h => hu1 (congrArg Subtype.val h))
    (Subtype.ext hu2)]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1.2⟩, x.2.1.1, Subtype.ext (by simpa using x.2.2)⟩
      invFun := fun y => ⟨y.1, ⟨y.2.1, y.1.2⟩, by simpa using congrArg Subtype.val y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

include hS in
theorem card_twist_root {w₁ : X} (hw₁ : w₁ ∈ P) (hw₁RT : ¬ InRT P J w₁)
    (hw₁2 : w₁ ^ 2 ∈ torusT P J) :
    Nat.card {x : X // x ∈ P ⊓ J ∧ x * (w₁ * x * w₁⁻¹) = 1} = q ^ 2 := by
  have h2 : (MulAut.conjNormal w₁ : MulAut J) ^ 2 = 1 := by
    rw [← map_pow, conjNormal_eq_one hw₁2.2]
  rw [← hS.model.card_twist _ (map_rootJ hw₁) (fun h => hw₁RT (inRT_of_conjNormal_mem hw₁ h))
    h2]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1.2⟩, x.2.1.1, Subtype.ext (by
        rw [Subgroup.coe_mul, MulAut.conjNormal_apply]
        exact x.2.2)⟩
      invFun := fun y => ⟨y.1, ⟨y.2.1, y.1.2⟩, by
        have h := congrArg Subtype.val y.2.2
        rwa [Subgroup.coe_mul, MulAut.conjNormal_apply] at h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end OuterSetting

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
