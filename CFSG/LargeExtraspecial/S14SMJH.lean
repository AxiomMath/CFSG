module

public import CFSG.LargeExtraspecial.S14SMJLoc
public import CFSG.LargeExtraspecial.S14SMHLevi
public import CFSG.LargeExtraspecial.S14SMJSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup CFSG.Open

variable {G : Type} [Group G]

structure Cfg (S : Setting G) (t u : G) : Prop where
  ht : IsConj S.z t
  hu : IsConj S.z u
  htM : t ∈ S.M
  huM : u ∈ S.M
  htQ : t ∉ S.QG
  huQ : u ∉ S.QG
  h3 : orderOf (t * u) = 3

structure Loc (S : Setting G) (t u : G) : Prop where
  card_ge : 2 ^ 9 ≤ Nat.card ↥(S.QG ⊓ cent2 t u)
  cent : ∀ c ∈ cent2 t u, c ∈ S.M → (∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) → c ∈ S.QG
  oTwo : ∀ P : Subgroup G, P ≤ cent2 t u ⊓ S.M →
    (∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) → IsPGroup 2 P → P ≤ S.QG
  irr : ∀ R : Subgroup G, S.z ∈ R → R ≤ S.QG ⊓ cent2 t u →
    (∀ c ∈ cent2 t u ⊓ S.M, ∀ r ∈ R, c * r * c⁻¹ ∈ R) → R = zpowers S.z ∨ S.QG ⊓ cent2 t u ≤ R
  exists_y : ∃ y : G, IsConj S.z y ∧ y ∈ S.M ∧ y ∉ S.QG ∧ y ∈ cent2 t u
  weak : ∀ c : G, IsConj S.z c → c ∈ S.QG → c ∈ cent2 t u → c = S.z

theorem commute_conj {a b : G} (k : G) (h : Commute a b) :
    Commute (k⁻¹ * a * k) (k⁻¹ * b * k) := by
  change k⁻¹ * a * k * (k⁻¹ * b * k) = k⁻¹ * b * k * (k⁻¹ * a * k)
  calc k⁻¹ * a * k * (k⁻¹ * b * k) = k⁻¹ * (a * b) * k := by group
    _ = k⁻¹ * (b * a) * k := by rw [h.eq]
    _ = k⁻¹ * b * k * (k⁻¹ * a * k) := by group

theorem commute_conj_iff {a b : G} (k : G) :
    Commute (k⁻¹ * a * k) (k⁻¹ * b * k) ↔ Commute a b := by
  refine ⟨fun h => ?_, commute_conj k⟩
  have h' := commute_conj k⁻¹ h
  simpa [mul_assoc] using h'

theorem conj_mem_cent2_iff {t u x : G} (k : G) :
    k⁻¹ * x * k ∈ cent2 (k⁻¹ * t * k) (k⁻¹ * u * k) ↔ x ∈ cent2 t u := by
  rw [mem_cent2, mem_cent2, commute_conj_iff, commute_conj_iff]

theorem orderOf_kconj (k x : G) : orderOf (k⁻¹ * x * k) = orderOf x := by
  rw [show k⁻¹ * x * k = MulAut.conj k⁻¹ x by rw [MulAut.conj_apply, inv_inv],
    MulEquiv.orderOf_eq]

theorem Cfg.conj [Finite G] {S : Setting G} {t u : G} (C : Cfg S t u) (k : G)
    (hyH : k * S.z * k⁻¹ ∈ cent2 t u) : Cfg S (k⁻¹ * t * k) (k⁻¹ * u * k) := by
  have hzk : k⁻¹ * (k * S.z * k⁻¹) * k = S.z := by group
  have hM : ∀ x : G, Commute (k * S.z * k⁻¹) x → k⁻¹ * x * k ∈ S.M := fun x hx => by
    have h := commute_conj k hx
    rw [hzk] at h
    exact S.mem_M_iff.mpr h.eq.symm
  have htt : t * t = 1 := SmithQ.mul_self_eq_one_of_isConj S C.ht
  have huu : u * u = 1 := SmithQ.mul_self_eq_one_of_isConj S C.hu
  have hsq : ∀ x : G, x * x = 1 → k⁻¹ * x * k * (k⁻¹ * x * k) = 1 := fun x hx => by
    calc k⁻¹ * x * k * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
      _ = 1 := by rw [hx]; group
  have h3' : orderOf (k⁻¹ * t * k * (k⁻¹ * u * k)) = 3 := by
    rw [show k⁻¹ * t * k * (k⁻¹ * u * k) = k⁻¹ * (t * u) * k by group, orderOf_kconj]
    exact C.h3
  have htuM := hM t (mem_cent2.mp hyH).1
  have huuM := hM u (mem_cent2.mp hyH).2
  refine ⟨C.ht.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩),
    C.hu.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩), htuM, huuM,
    SMH.not_mem_QG_of_orderOf_eq_three S (hsq u huu) huuM h3', ?_, h3'⟩
  refine SMH.not_mem_QG_of_orderOf_eq_three S (hsq t htt) htuM ?_
  rw [show k⁻¹ * u * k * (k⁻¹ * t * k) = (k⁻¹ * t * k)⁻¹ * (k⁻¹ * t * k * (k⁻¹ * u * k)) *
    (k⁻¹ * t * k) by group, orderOf_kconj]
  exact h3'

theorem Loc.cent_conj {S : Setting G} {t u : G} (k : G)
    (L : Loc S (k⁻¹ * t * k) (k⁻¹ * u * k)) {n : G} (hnH : n ∈ cent2 t u)
    (hny : n * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * n)
    (hnq : ∀ q ∈ cent2 t u, k⁻¹ * q * k ∈ S.QG → n * q = q * n) : k⁻¹ * n * k ∈ S.QG := by
  refine L.cent _ ((conj_mem_cent2_iff k).mpr hnH) ?_ fun q' hq' => ?_
  · rw [S.mem_M_iff]
    calc k⁻¹ * n * k * S.z = k⁻¹ * (n * (k * S.z * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * S.z * k⁻¹ * n) * k := by rw [hny]
      _ = S.z * (k⁻¹ * n * k) := by group
  · obtain ⟨hq'Q, hq'H⟩ := mem_inf.mp hq'
    have hqH : k * q' * k⁻¹ ∈ cent2 t u := by
      rw [← conj_mem_cent2_iff k]
      rwa [show k⁻¹ * (k * q' * k⁻¹) * k = q' by group]
    have h := hnq _ hqH (by rwa [show k⁻¹ * (k * q' * k⁻¹) * k = q' by group])
    calc k⁻¹ * n * k * q' = k⁻¹ * (n * (k * q' * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * q' * k⁻¹ * n) * k := by rw [h]
      _ = q' * (k⁻¹ * n * k) := by group

section SetH

variable {S : Setting G} {t u : G} (C : Cfg S t u) (L : Loc S t u)
  (hext : IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u))

@[expose] noncomputable def setH : Setting ↥(cent2 t u) :=
  subSetting S (cent2 t u) (z_mem_cent2 S C.htM C.huM) hext L.cent L.oTwo

theorem mem_setH_QG_iff {x : ↥(cent2 t u)} : x ∈ (setH C L hext).QG ↔ (x : G) ∈ S.QG :=
  mem_subSetting_QG_iff S _ _ _ _ _

theorem mem_setH_M_iff {x : ↥(cent2 t u)} : x ∈ (setH C L hext).M ↔ (x : G) ∈ S.M :=
  mem_subSetting_M_iff S _ _ _ _ _

theorem card_setH_Q : Nat.card (setH C L hext).Q = Nat.card ↥(S.QG ⊓ cent2 t u) :=
  card_subSetting_Q S _ _ _ _ _

theorem setH_weak (g : ↥(cent2 t u))
    (hg : g * (setH C L hext).z * g⁻¹ ∈ (setH C L hext).QG) :
    g * (setH C L hext).z * g⁻¹ = (setH C L hext).z := by
  rw [mem_setH_QG_iff] at hg
  apply Subtype.ext
  change (g : G) * S.z * (g : G)⁻¹ = S.z
  refine L.weak _ (isConj_iff.mpr ⟨g, rfl⟩) hg ?_
  exact mul_mem (mul_mem g.2 (z_mem_cent2 S C.htM C.huM)) (inv_mem g.2)

end SetH

end CFSG.LargeExtraspecial.S14.SMJ
