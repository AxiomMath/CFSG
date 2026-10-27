module

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup

section Pull

variable {G Gs : Type*} [Group G] [Group Gs] {X : Subgroup G} {X' : Subgroup Gs}

@[expose] def pull (ψ : ↥X ≃* ↥X') (E' : Subgroup Gs) : Subgroup G :=
  (E'.subgroupOf X').map (X.subtype.comp ψ.symm.toMonoidHom)

theorem mem_pull (ψ : ↥X ≃* ↥X') (E' : Subgroup Gs) {x : G} (hx : x ∈ X) :
    x ∈ pull ψ E' ↔ ((ψ ⟨x, hx⟩ : ↥X') : Gs) ∈ E' := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : ψ.symm y = ⟨x, hx⟩ := Subtype.ext hyx
    have h2 : ψ ⟨x, hx⟩ = y := by rw [← h1]; exact ψ.apply_symm_apply y
    rw [h2]; exact hy
  · intro h
    refine ⟨ψ ⟨x, hx⟩, h, ?_⟩
    simp

theorem pull_le (ψ : ↥X ≃* ↥X') (E' : Subgroup Gs) : pull ψ E' ≤ X := by
  rintro _ ⟨y, -, rfl⟩
  exact (ψ.symm y).2

theorem mem_pull_iff (ψ : ↥X ≃* ↥X') (E' : Subgroup Gs) {x : G} :
    x ∈ pull ψ E' ↔ ∃ hx : x ∈ X, ((ψ ⟨x, hx⟩ : ↥X') : Gs) ∈ E' := by
  constructor
  · intro h
    have hx := pull_le ψ E' h
    exact ⟨hx, (mem_pull ψ E' hx).mp h⟩
  · rintro ⟨hx, h⟩
    exact (mem_pull ψ E' hx).mpr h

theorem pull_mono (ψ : ↥X ≃* ↥X') {E₁ E₂ : Subgroup Gs} (h : E₁ ≤ E₂) : pull ψ E₁ ≤ pull ψ E₂ :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono X' h)

theorem pull_sup (ψ : ↥X ≃* ↥X') {E₁ E₂ : Subgroup Gs} (h₁ : E₁ ≤ X') (h₂ : E₂ ≤ X') :
    pull ψ (E₁ ⊔ E₂) = pull ψ E₁ ⊔ pull ψ E₂ := by
  unfold pull
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem pull_inf (ψ : ↥X ≃* ↥X') (E₁ E₂ : Subgroup Gs) :
    pull ψ (E₁ ⊓ E₂) = pull ψ E₁ ⊓ pull ψ E₂ := by
  ext x
  constructor
  · intro h
    have hx := pull_le ψ _ h
    have h' := (mem_pull ψ _ hx).mp h
    exact ⟨(mem_pull ψ _ hx).mpr h'.1, (mem_pull ψ _ hx).mpr h'.2⟩
  · rintro ⟨h1, h2⟩
    have hx := pull_le ψ _ h1
    exact (mem_pull ψ _ hx).mpr ⟨(mem_pull ψ _ hx).mp h1, (mem_pull ψ _ hx).mp h2⟩

theorem pull_inj {E₁ E₂ : Subgroup Gs} (ψ : ↥X ≃* ↥X') (h₁ : E₁ ≤ X') (h₂ : E₂ ≤ X')
    (h : pull ψ E₁ = pull ψ E₂) : E₁ = E₂ := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := ψ.surjective ⟨y, h₁ hy⟩
    have hyx : ((ψ x : ↥X') : Gs) = y := congrArg Subtype.val hx
    have h3 : (x : G) ∈ pull ψ E₁ := by
      rw [mem_pull ψ _ x.2]
      show ((ψ x : ↥X') : Gs) ∈ E₁
      rw [hyx]; exact hy
    rw [h, mem_pull ψ _ x.2] at h3
    rw [← hyx]; exact h3
  · intro y hy
    obtain ⟨x, hx⟩ := ψ.surjective ⟨y, h₂ hy⟩
    have hyx : ((ψ x : ↥X') : Gs) = y := congrArg Subtype.val hx
    have h3 : (x : G) ∈ pull ψ E₂ := by
      rw [mem_pull ψ _ x.2]
      show ((ψ x : ↥X') : Gs) ∈ E₂
      rw [hyx]; exact hy
    rw [← h, mem_pull ψ _ x.2] at h3
    rw [← hyx]; exact h3

@[expose] noncomputable def pullEquiv (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') :
    ↥(pull ψ E') ≃* ↥E' where
  toFun x := ⟨((ψ ⟨(x : G), pull_le ψ E' x.2⟩ : ↥X') : Gs),
    (mem_pull ψ E' (pull_le ψ E' x.2)).mp x.2⟩
  invFun y := ⟨((ψ.symm ⟨(y : Gs), hE y.2⟩ : ↥X) : G), by
    rw [mem_pull ψ E' (ψ.symm ⟨(y : Gs), hE y.2⟩).2]
    simp⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    show ((ψ (⟨(a : G), pull_le ψ E' a.2⟩ * ⟨(b : G), pull_le ψ E' b.2⟩) : ↥X') : Gs) = _
    rw [map_mul]
    rfl

theorem pullEquiv_apply (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') (x : ↥(pull ψ E')) :
    ((pullEquiv ψ hE x : ↥E') : Gs) = ((ψ ⟨(x : G), pull_le ψ E' x.2⟩ : ↥X') : Gs) := rfl

theorem card_pull (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') :
    Nat.card ↥(pull ψ E') = Nat.card ↥E' :=
  Nat.card_congr (pullEquiv ψ hE).toEquiv

theorem mem_map_conj {K : Subgroup G} {c x : G} :
    x ∈ K.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    simpa [MulAut.conj_apply, e] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem pull_map_conj (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} {t : G} (ht : t ∈ X) :
    (pull ψ E').map (MulAut.conj t).toMonoidHom =
      pull ψ (E'.map (MulAut.conj ((ψ ⟨t, ht⟩ : ↥X') : Gs)).toMonoidHom) := by
  ext x
  rw [mem_map_conj]
  constructor
  · intro h
    have hx1 : t⁻¹ * x * t ∈ X := pull_le ψ _ h
    have hx : x ∈ X := by
      have := X.mul_mem (X.mul_mem ht hx1) (X.inv_mem ht)
      simpa [mul_assoc] using this
    rw [mem_pull ψ _ hx, mem_map_conj]
    rw [mem_pull ψ _ hx1] at h
    have e : (ψ ⟨t⁻¹ * x * t, hx1⟩ : ↥X') = (ψ ⟨t, ht⟩)⁻¹ * ψ ⟨x, hx⟩ * ψ ⟨t, ht⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h
    simpa using h
  · intro h
    have hx : x ∈ X := pull_le ψ _ h
    have hx1 : t⁻¹ * x * t ∈ X := X.mul_mem (X.mul_mem (X.inv_mem ht) hx) ht
    rw [mem_pull ψ _ hx, mem_map_conj] at h
    rw [mem_pull ψ _ hx1]
    have e : (ψ ⟨t⁻¹ * x * t, hx1⟩ : ↥X') = (ψ ⟨t, ht⟩)⁻¹ * ψ ⟨x, hx⟩ * ψ ⟨t, ht⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    simpa using h

theorem mem_normalizer_pull (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') {t : G}
    (ht : t ∈ X) :
    t ∈ normalizer ((pull ψ E' : Subgroup G) : Set G) ↔
      ((ψ ⟨t, ht⟩ : ↥X') : Gs) ∈ normalizer (E' : Set Gs) := by
  have h1 := pull_map_conj ψ (E' := E') ht
  have ht' : ((ψ ⟨t, ht⟩ : ↥X') : Gs) ∈ X' := (ψ ⟨t, ht⟩).2
  constructor
  · intro h
    have h2 : (pull ψ E').map (MulAut.conj t).toMonoidHom = pull ψ E' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp h
    rw [h1] at h2
    have h3 : E'.map (MulAut.conj ((ψ ⟨t, ht⟩ : ↥X') : Gs)).toMonoidHom = E' := by
      refine pull_inj ψ ?_ hE h2
      rintro _ ⟨e, he, rfl⟩
      exact X'.mul_mem (X'.mul_mem ht' (hE he)) (X'.inv_mem ht')
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3
  · intro h
    have h3 : E'.map (MulAut.conj ((ψ ⟨t, ht⟩ : ↥X') : Gs)).toMonoidHom = E' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp h
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show (pull ψ E').map (MulAut.conj t).toMonoidHom = pull ψ E'
    rw [h1, h3]

theorem pull_subgroupOf (ψ : ↥X ≃* ↥X') (E' : Subgroup Gs) :
    (pull ψ E').subgroupOf X = (E'.subgroupOf X').map ψ.symm.toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_pull ψ E' x.2, Subgroup.mem_map_equiv]
  exact Iff.rfl

@[expose] def push (ψ : ↥X ≃* ↥X') (L : Subgroup G) : Subgroup Gs :=
  (L.subgroupOf X).map (X'.subtype.comp ψ.toMonoidHom)

theorem push_le (ψ : ↥X ≃* ↥X') (L : Subgroup G) : push ψ L ≤ X' := by
  rintro _ ⟨y, -, rfl⟩
  exact (ψ y).2

theorem mem_push (ψ : ↥X ≃* ↥X') (L : Subgroup G) {y : Gs} (hy : y ∈ X') :
    y ∈ push ψ L ↔ ((ψ.symm ⟨y, hy⟩ : ↥X) : G) ∈ L := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have : ψ x = ⟨y, hy⟩ := Subtype.ext hxy
    have h2 : ψ.symm ⟨y, hy⟩ = x := by rw [← this]; exact ψ.symm_apply_apply x
    rw [h2]; exact hx
  · intro h
    exact ⟨ψ.symm ⟨y, hy⟩, h, by simp⟩

theorem pull_push (ψ : ↥X ≃* ↥X') {L : Subgroup G} (hL : L ≤ X) : pull ψ (push ψ L) = L := by
  ext x
  constructor
  · intro h
    have hx := pull_le ψ _ h
    have h1 := (mem_pull ψ _ hx).mp h
    have h2 := (mem_push ψ L (ψ ⟨x, hx⟩).2).mp h1
    simpa using h2
  · intro h
    have hx := hL h
    rw [mem_pull ψ _ hx, mem_push ψ L (ψ ⟨x, hx⟩).2]
    simpa using h

theorem push_subgroupOf (ψ : ↥X ≃* ↥X') (L : Subgroup G) :
    (push ψ L).subgroupOf X' = (L.subgroupOf X).map ψ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_subgroupOf, mem_push ψ L y.2, Subgroup.mem_map_equiv]
  exact Iff.rfl

theorem mem_center_equiv_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A} :
    e a ∈ center B ↔ a ∈ center A := by
  rw [← Subgroup.map_center_eq e]
  constructor
  · rintro ⟨c, hc, hce⟩
    have : c = a := e.injective hce
    rwa [← this]
  · intro h
    exact ⟨a, h, rfl⟩

theorem center_pull (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') :
    (center ↥(pull ψ E')).map (pull ψ E').subtype = pull ψ ((center ↥E').map E'.subtype) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hxX : (c : G) ∈ X := pull_le ψ E' c.2
    show (c : G) ∈ pull ψ ((center ↥E').map E'.subtype)
    rw [mem_pull ψ _ hxX]
    refine ⟨pullEquiv ψ hE c, ?_, ?_⟩
    · exact (mem_center_equiv_iff (pullEquiv ψ hE)).mpr hc
    · exact pullEquiv_apply ψ hE c
  · intro hx
    have hxX : x ∈ X := pull_le ψ _ hx
    rw [mem_pull ψ _ hxX] at hx
    obtain ⟨d, hd, hdx⟩ := hx
    let c : ↥(pull ψ E') := (pullEquiv ψ hE).symm d
    have hc : c ∈ center ↥(pull ψ E') := by
      have : (pullEquiv ψ hE) c = d := (pullEquiv ψ hE).apply_symm_apply d
      rw [← mem_center_equiv_iff (pullEquiv ψ hE), this]
      exact hd
    refine ⟨c, hc, ?_⟩
    have h1 := pullEquiv_apply ψ hE c
    have h2 : (pullEquiv ψ hE) c = d := (pullEquiv ψ hE).apply_symm_apply d
    rw [h2] at h1
    have h3 : ψ ⟨(c : G), pull_le ψ E' c.2⟩ = ψ ⟨x, hxX⟩ := Subtype.ext (by rw [← h1]; exact hdx)
    have h4 := ψ.injective h3
    exact congrArg Subtype.val h4

theorem pull_zpowers (ψ : ↥X ≃* ↥X') {z : G} (hz : z ∈ X) {z' : Gs}
    (hzz : ((ψ ⟨z, hz⟩ : ↥X') : Gs) = z') : pull ψ (zpowers z') = zpowers z := by
  ext x
  constructor
  · intro h
    have hx := pull_le ψ _ h
    have h1 := (mem_pull ψ _ hx).mp h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hzk : z ^ k ∈ X := X.zpow_mem hz k
    have h2 : ψ ⟨x, hx⟩ = ψ ⟨z ^ k, hzk⟩ := by
      apply Subtype.ext
      show ((ψ ⟨x, hx⟩ : ↥X') : Gs) = ((ψ (⟨z, hz⟩ ^ k) : ↥X') : Gs)
      rw [map_zpow, Subgroup.coe_zpow, hzz, hk]
    have := ψ.injective h2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using (congrArg Subtype.val this).symm⟩
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have hzk : z ^ k ∈ X := X.zpow_mem hz k
    rw [mem_pull ψ _ hzk]
    have e : ((ψ ⟨z ^ k, hzk⟩ : ↥X') : Gs) = z' ^ k := by
      have : (⟨z ^ k, hzk⟩ : ↥X) = ⟨z, hz⟩ ^ k := rfl
      rw [this, map_zpow, Subgroup.coe_zpow, hzz]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z') k

theorem psi_mul (ψ : ↥X ≃* ↥X') {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    ((ψ ⟨x * y, X.mul_mem hx hy⟩ : ↥X') : Gs) =
      ((ψ ⟨x, hx⟩ : ↥X') : Gs) * ((ψ ⟨y, hy⟩ : ↥X') : Gs) := by
  have : (⟨x * y, X.mul_mem hx hy⟩ : ↥X) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]
  rfl

theorem psi_one (ψ : ↥X ≃* ↥X') : ((ψ ⟨1, X.one_mem⟩ : ↥X') : Gs) = 1 := by
  have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
  rw [this, map_one]
  rfl

theorem psi_inv (ψ : ↥X ≃* ↥X') {x : G} (hx : x ∈ X) :
    ((ψ ⟨x⁻¹, X.inv_mem hx⟩ : ↥X') : Gs) = ((ψ ⟨x, hx⟩ : ↥X') : Gs)⁻¹ := by
  have : (⟨x⁻¹, X.inv_mem hx⟩ : ↥X) = (⟨x, hx⟩ : ↥X)⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem psi_eq_iff (ψ : ↥X ≃* ↥X') {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    ((ψ ⟨x, hx⟩ : ↥X') : Gs) = ((ψ ⟨y, hy⟩ : ↥X') : Gs) ↔ x = y := by
  constructor
  · intro h
    have := ψ.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · rintro rfl
    rfl

theorem orderOf_psi (ψ : ↥X ≃* ↥X') {x : G} (hx : x ∈ X) :
    orderOf ((ψ ⟨x, hx⟩ : ↥X') : Gs) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact Subgroup.orderOf_mk x hx

theorem orderOf_eq_of_isConj {H : Type*} [Group H] {a b : H} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a).symm

theorem exists_psi_eq (ψ : ↥X ≃* ↥X') {y : Gs} (hy : y ∈ X') :
    ∃ (x : G) (hx : x ∈ X), ((ψ ⟨x, hx⟩ : ↥X') : Gs) = y := by
  refine ⟨((ψ.symm ⟨y, hy⟩ : ↥X) : G), (ψ.symm ⟨y, hy⟩).2, ?_⟩
  have : ψ ⟨((ψ.symm ⟨y, hy⟩ : ↥X) : G), (ψ.symm ⟨y, hy⟩).2⟩ = ⟨y, hy⟩ := ψ.apply_symm_apply _
  exact congrArg Subtype.val this

end Pull

end CFSG.GH74.GLS.LU.Local
