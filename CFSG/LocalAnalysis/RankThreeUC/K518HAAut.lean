module

public import CFSG.LocalAnalysis.RankThreeUC.K518HACore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

@[expose] def RKGood (Λ : Type) [Group Λ] [Finite Λ] (p : ℕ) : Prop :=
  ∀ ψ : MulAut Λ, (∃ k : ℕ, orderOf ψ = p ^ k) →
    ψ ∉ (MulAut.conj : Λ →* MulAut Λ).range →
    2 ≤ CFSG.Open.pRank p ((MulAut.conj : Λ →* MulAut Λ).range ⊔ Subgroup.zpowers ψ)

theorem congr_conj {Λ Λ' : Type*} [Group Λ] [Group Λ'] (e : Λ ≃* Λ') (g : Λ) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem RKGood.of_mulEquiv {Λ Λ' : Type} [Group Λ] [Finite Λ] [Group Λ'] [Finite Λ']
    (e : Λ ≃* Λ') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : RKGood Λ' p) : RKGood Λ p := by
  intro ψ hψp hψ
  set ψ' : MulAut Λ' := MulAut.congr e ψ with hψ'
  have hord : orderOf ψ' = orderOf ψ := MulEquiv.orderOf_eq (MulAut.congr e) ψ
  have hnot : ψ' ∉ (MulAut.conj : Λ' →* MulAut Λ').range := by
    rintro ⟨g', hg'⟩
    apply hψ
    refine ⟨e.symm g', ?_⟩
    apply (MulAut.congr e).injective
    rw [← hψ']
    change MulAut.conj g' = _ at hg'
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hg'
  have h2 := h ψ' (hord ▸ hψp) hnot
  refine CFSG.LocalAnalysis.RankThreeUC.S15.two_le_pRank_of_map (MulAut.congr e).toMonoidHom hp hp2
    _ ?_
  have hmap : ((MulAut.conj : Λ →* MulAut Λ).range ⊔ Subgroup.zpowers ψ).map
      (MulAut.congr e).toMonoidHom = (MulAut.conj : Λ' →* MulAut Λ').range ⊔
        Subgroup.zpowers ψ' := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
      exact ⟨e g, (congr_conj e g).symm⟩
    · rintro ⟨g', rfl⟩
      refine ⟨MulAut.conj (e.symm g'), ⟨e.symm g', rfl⟩, ?_⟩
      change MulAut.congr e (MulAut.conj (e.symm g')) = _
      rw [congr_conj, MulEquiv.apply_symm_apply]
  rwa [hmap]

section Act

variable {Y : Type} [Group Y]

@[expose] def stabSub (R : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {g | ∀ x, g x ∈ R ↔ x ∈ R}
  mul_mem' := fun {g h} hg hh x => by
    change g (h x) ∈ R ↔ x ∈ R
    rw [hg, hh]
  one_mem' := fun x => Iff.rfl
  inv_mem' := fun {g} hg x => by
    change g.symm x ∈ R ↔ x ∈ R
    rw [← hg (g.symm x), g.apply_symm_apply]

theorem map_eq_of_mem_stabSub {R : Subgroup Y} {g : MulAut Y} (hg : g ∈ stabSub R) :
    R.map g.toMonoidHom = R := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hg y).2 hy
  · intro hz
    exact ⟨g.symm z, (hg (g.symm z)).1 (by rw [g.apply_symm_apply]; exact hz), g.apply_symm_apply z⟩

theorem mem_stabSub_of_map_eq {R : Subgroup Y} {g : MulAut Y} (h : R.map g.toMonoidHom = R) :
    g ∈ stabSub R := by
  intro x
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := g.injective hyx
    rwa [this] at hy
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩

private def resAut (R : Subgroup Y) (g : MulAut Y) (hg : g ∈ stabSub R) : MulAut ↥R where
  toFun x := ⟨g (x : Y), (hg x).2 x.2⟩
  invFun x := ⟨g.symm (x : Y), (hg (g.symm (x : Y))).1 (by rw [g.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (g.symm_apply_apply (x : Y))
  right_inv x := Subtype.ext (g.apply_symm_apply (x : Y))
  map_mul' x y := Subtype.ext (map_mul g (x : Y) (y : Y))

variable (R W : Subgroup Y) [hWn : (W.subgroupOf R).Normal]

private def quotAut (g : MulAut Y) (hR : g ∈ stabSub R) (hW : g ∈ stabSub W) :
    MulAut (↥R ⧸ W.subgroupOf R) :=
  QuotientGroup.congr (W.subgroupOf R) (W.subgroupOf R) (resAut R g hR) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : Y) ∈ W := hy
      show g (y : Y) ∈ W
      exact (hW y).2 hy'
    · intro hx
      have hx' : (x : Y) ∈ W := hx
      refine ⟨(resAut R g hR).symm x, ?_, MulEquiv.apply_symm_apply _ x⟩
      show g.symm (x : Y) ∈ W
      exact (hW (g.symm (x : Y))).1 (by rw [g.apply_symm_apply]; exact hx'))

private def actQuot (J : Subgroup (MulAut Y)) (hJ : J ≤ stabSub R ⊓ stabSub W) :
    ↥J →* MulAut (↥R ⧸ W.subgroupOf R) where
  toFun g := quotAut R W g.1 (hJ g.2).1 (hJ g.2).2
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

private theorem actQuot_conj (J : Subgroup (MulAut Y)) (hJ : J ≤ stabSub R ⊓ stabSub W) {x : Y}
    (hx : x ∈ R) (hxJ : (MulAut.conj x : MulAut Y) ∈ J) :
    actQuot R W J hJ ⟨MulAut.conj x, hxJ⟩ = MulAut.conj (QuotientGroup.mk (⟨x, hx⟩ : ↥R)) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y => 
    show QuotientGroup.mk (resAut R (MulAut.conj x) _ y) =
      (MulAut.conj (QuotientGroup.mk (⟨x, hx⟩ : ↥R))) (QuotientGroup.mk y)
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

end Act

theorem mulAut_mul_conj_mul_inv {Y : Type*} [Group Y] (c : MulAut Y) (y : Y) :
    c * MulAut.conj y * c⁻¹ = MulAut.conj (c y) := by
  ext z
  change c (y * c.symm z * y⁻¹) = c y * z * (c y)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem autRK {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R W : Subgroup Y) (hWR : W ≤ R) [hWn : (W.subgroupOf R).Normal]
    (hRK : RKGood (↥R ⧸ W.subgroupOf R) p)
    (hpI : p ∣ Nat.card (MulAut.conj : (↥R ⧸ W.subgroupOf R) →*
      MulAut (↥R ⧸ W.subgroupOf R)).range)
    (c : MulAut Y) (hc : ∃ k : ℕ, orderOf c = p ^ k) (hcR : R.map c.toMonoidHom = R)
    (hcW : W.map c.toMonoidHom = W) (hcInn : c ∉ R.map (MulAut.conj : Y →* MulAut Y)) :
    2 ≤ CFSG.Open.pRank p (R.map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRn : R ≤ Subgroup.normalizer (W : Set Y) := 
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).1 hWn
  set Rh : Subgroup (MulAut Y) := R.map (MulAut.conj : Y →* MulAut Y) with hRh
  set J : Subgroup (MulAut Y) := Rh ⊔ Subgroup.zpowers c with hJdef
  have hcR' : c ∈ stabSub R := mem_stabSub_of_map_eq hcR
  have hcW' : c ∈ stabSub W := mem_stabSub_of_map_eq hcW
  have hRhstab : Rh ≤ stabSub R ⊓ stabSub W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun y => ?_, fun y => ?_⟩
    · change x * y * x⁻¹ ∈ R ↔ y ∈ R
      constructor
      · intro h
        have := R.mul_mem (R.mul_mem (R.inv_mem hx) h) hx
        simpa [mul_assoc] using this
      · intro h
        exact R.mul_mem (R.mul_mem hx h) (R.inv_mem hx)
    · change x * y * x⁻¹ ∈ W ↔ y ∈ W
      exact ((Subgroup.mem_normalizer_iff.1 (hRn hx) y).symm)
  have hJstab : J ≤ stabSub R ⊓ stabSub W :=
    sup_le hRhstab (Subgroup.zpowers_le.2 ⟨hcR', hcW'⟩)
  have hRhJ : Rh ≤ J := le_sup_left
  have hcJ : c ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hcnorm : c ∈ Subgroup.normalizer (Rh : Set (MulAut Y)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c y, (hcR' y).2 hy, (mulAut_mul_conj_mul_inv c y).symm⟩
    · rintro ⟨y, hy, hyg⟩
      have hcy : c⁻¹ y ∈ R := (((stabSub R).inv_mem hcR') y).2 hy
      refine ⟨c⁻¹ y, hcy, ?_⟩
      have h1 := mulAut_mul_conj_mul_inv c⁻¹ y
      change MulAut.conj (c⁻¹ y) = g
      rw [← h1]
      have h2 : MulAut.conj y = c * g * c⁻¹ := hyg
      rw [h2]
      group
  have hnorm : J ≤ Subgroup.normalizer (Rh : Set (MulAut Y)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hcnorm)
  haveI : (Rh.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRhJ).2 hnorm
  set φ := actQuot R W J hJstab with hφ
  have himage : (Rh.subgroupOf J).map φ =
      (MulAut.conj : (↥R ⧸ W.subgroupOf R) →* MulAut (↥R ⧸ W.subgroupOf R)).range := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, hxg⟩ := (Subgroup.mem_subgroupOf.1 hg)
      have hgx : g = ⟨MulAut.conj x, hRhJ ⟨x, hx, rfl⟩⟩ := Subtype.ext hxg.symm
      rw [hgx, hφ, actQuot_conj R W J hJstab hx]
      exact ⟨_, rfl⟩
    · rintro ⟨lam, rfl⟩
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective lam
      exact ⟨⟨MulAut.conj x, hRhJ ⟨x, hx, rfl⟩⟩, Subgroup.mem_subgroupOf.2 ⟨x, hx, rfl⟩,
        by rw [hφ, actQuot_conj R W J hJstab hx]⟩
  obtain ⟨k, hk⟩ := hc
  have hr : ∃ k : ℕ, orderOf (⟨c, hcJ⟩ : ↥J) = p ^ k :=
    ⟨k, by rw [Subgroup.orderOf_mk, hk]⟩
  have hrR : (⟨c, hcJ⟩ : ↥J) ∉ Rh.subgroupOf J := fun h => hcInn (Subgroup.mem_subgroupOf.1 h)
  have hgen : Rh.subgroupOf J ⊔ Subgroup.zpowers (⟨c, hcJ⟩ : ↥J) = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup hRhJ (Subgroup.zpowers_le.2 hcJ)
    rw [← hJdef, Subgroup.subgroupOf_self] at h1
    rw [eq_top_iff, h1]
    refine sup_le_sup_left ?_ _
    rintro x ⟨m, hm⟩
    exact ⟨m, Subtype.ext hm⟩
  have hz : ∃ z ∈ (Rh.subgroupOf J).map φ, z ≠ 1 ∧ ∃ k : ℕ, orderOf z = p ^ k := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpI
    refine ⟨z.1, by rw [himage]; exact z.2, ?_, 1, ?_⟩
    · intro h1
      have : orderOf (z : MulAut (↥R ⧸ W.subgroupOf R)) = p := (Subgroup.orderOf_coe z).trans hz
      rw [h1, orderOf_one] at this
      exact hp.one_lt.ne this
    · rw [pow_one]
      exact (Subgroup.orderOf_coe z).trans hz
  have hRK' : ∀ ψ : MulAut (↥R ⧸ W.subgroupOf R), (∃ k : ℕ, orderOf ψ = p ^ k) →
      ψ ∉ (Rh.subgroupOf J).map φ →
      2 ≤ CFSG.Open.pRank p ((Rh.subgroupOf J).map φ ⊔ Subgroup.zpowers ψ) := by
    rw [himage]
    exact hRK
  have h2 := lambda_pRank hp hp2 (Rh.subgroupOf J) φ hr hrR hgen hz hRK'
  have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt J.subtype J.subtype_injective ⊤
  rw [Subgroup.map_top, Subgroup.range_subtype] at h3
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
