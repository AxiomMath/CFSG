module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219A
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev CQ (Q : Subgroup G) (x : G) : Subgroup ↥Q := (centralizer ({x} : Set G)).subgroupOf Q

abbrev Lay (Q : Subgroup G) (x : G) : Subgroup G := GSThmB.layerIn (Q ⊓ centralizer ({x} : Set G))

abbrev LQ (Q : Subgroup G) (x : G) : Subgroup ↥Q := (Lay Q x).subgroupOf Q

theorem Lay_le {Q : Subgroup G} {x : G} : Lay Q x ≤ Q ⊓ centralizer ({x} : Set G) :=
  map_subtype_le _

theorem LQ_le_CQ {Q : Subgroup G} {x : G} : LQ Q x ≤ CQ Q x := fun _ hq => (Lay_le hq).2

theorem eq_one_of_mem_Lay {Q : Subgroup G} {x : G} (hLZ : center ↥(Lay Q x) = ⊥) {q : ↥Q}
    (hqL : (q : G) ∈ Lay Q x) (hqZ : q ∈ center ↥Q) : q = 1 := by
  have hc : (⟨q, hqL⟩ : ↥(Lay Q x)) ∈ center ↥(Lay Q x) := by
    rw [mem_center_iff]
    rintro ⟨l, hl⟩
    apply Subtype.ext
    have h := mem_center_iff.mp hqZ ⟨l, (Lay_le hl).1⟩
    have h' := congrArg Subtype.val h
    exact h'
  rw [hLZ, mem_bot] at hc
  have h' := congrArg Subtype.val hc
  exact Subtype.ext h'

theorem isSubnormal_map_subtype {Q : Subgroup G} {x : G} {K : Subgroup ↥Q}
    (h : (K.subgroupOf (CQ Q x)).IsSubnormal) :
    ((K.map Q.subtype).subgroupOf (Q ⊓ centralizer ({x} : Set G))).IsSubnormal := by
  let f : ↥(CQ Q x) →* ↥(Q ⊓ centralizer ({x} : Set G)) :=
    { toFun := fun c => ⟨((c : ↥Q) : G), ⟨(c : ↥Q).2, c.2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨g, hgQ, hgx⟩
    exact ⟨⟨⟨g, hgQ⟩, hgx⟩, rfl⟩
  have hmap : (K.subgroupOf (CQ Q x)).map f =
      (K.map Q.subtype).subgroupOf (Q ⊓ centralizer ({x} : Set G)) := by
    ext ⟨g, hgQ, hgx⟩
    constructor
    · rintro ⟨c, hc, hcg⟩
      exact ⟨c, hc, congrArg Subtype.val hcg⟩
    · rintro ⟨q, hq, hqg⟩
      have hqx : (q : G) ∈ centralizer ({x} : Set G) := by
        rw [show (q : G) = g from hqg]
        exact hgx
      exact ⟨⟨q, hqx⟩, hq, Subtype.ext hqg⟩
  rw [← hmap]
  exact h.map hf

section Pi

variable {Q : Subgroup G} {P : Type*} [Group P] (e : ↥Q ⧸ center ↥Q ≃* P)

@[expose] def piQ : ↥Q →* P := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥Q))

theorem piQ_apply (q : ↥Q) : piQ e q = e (QuotientGroup.mk q) := rfl

theorem piQ_surjective : Function.Surjective (piQ e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piQ_eq_one_iff (q : ↥Q) : piQ e q = 1 ↔ q ∈ center ↥Q := by
  rw [piQ_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem ker_piQ : (piQ e).ker = center ↥Q := by
  ext q
  exact piQ_eq_one_iff e q

theorem piQ_eq_iff (a b : ↥Q) : piQ e a = piQ e b ↔ a⁻¹ * b ∈ center ↥Q := by
  rw [piQ_apply, piQ_apply, e.injective.eq_iff, QuotientGroup.eq]

abbrev Jp (x : G) : Subgroup P := (LQ Q x).map (piQ e)

theorem piQ_injOn {x : G} (hLZ : center ↥(Lay Q x) = ⊥) {a b : ↥Q} (ha : a ∈ LQ Q x)
    (hb : b ∈ LQ Q x) (hab : piQ e a = piQ e b) : a = b := by
  have h := (piQ_eq_iff e a b).mp hab
  have h1 := eq_one_of_mem_Lay (q := a⁻¹ * b) hLZ (mul_mem (inv_mem ha) hb) h
  rw [← mul_inv_cancel_left a b, h1, mul_one]

theorem injective_piQ_comp {x : G} (hLZ : center ↥(Lay Q x) = ⊥) :
    Function.Injective ((piQ e).comp (LQ Q x).subtype) := fun a b hab =>
  Subtype.ext (piQ_injOn e hLZ a.2 b.2 hab)

@[expose] def equivJp {x : G} (hLZ : center ↥(Lay Q x) = ⊥) : ↥(Lay Q x) ≃* ↥(Jp e x) :=
  (subgroupOfEquivOfLe (Lay_le.trans inf_le_left)).symm.trans
    ((MonoidHom.ofInjective (injective_piQ_comp e hLZ)).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))

theorem le_LQ_of_perfect {x : G} {K : Subgroup ↥Q} (hK : ⁅K, K⁆ = K)
    (hKJ : K.map (piQ e) ≤ Jp e x) : K ≤ LQ Q x := by
  have hle : K ≤ LQ Q x ⊔ center ↥Q := by
    rw [← ker_piQ e, ← comap_map_eq]
    exact map_le_iff_le_comap.mp hKJ
  rw [← hK, commutator_le]
  intro a ha b hb
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := mem_sup_of_normal_right.mp (hle ha)
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := mem_sup_of_normal_right.mp (hle hb)
  have c1 : z₁ * m₂ = m₂ * z₁ := (mem_center_iff.mp hz₁ m₂).symm
  have c2 : z₂ * m₁⁻¹ = m₁⁻¹ * z₂ := (mem_center_iff.mp hz₂ m₁⁻¹).symm
  have c12 : z₁ * z₂ = z₂ * z₁ := (mem_center_iff.mp hz₁ z₂).symm
  have h : ⁅m₁ * z₁, m₂ * z₂⁆ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
    rw [commutatorElement_def]
    calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹
        = m₁ * (z₁ * m₂) * z₂ * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
      _ = m₁ * m₂ * (z₁ * z₂) * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by rw [c1]; group
      _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by rw [c12]; group
      _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by rw [c2]; group
  rw [h]
  exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)

end Pi

variable {Q : Subgroup G} {x : G} (hx : x ∈ normalizer (Q : Set G))

abbrev xAut : MulAut ↥Q := normalizerConj Q ⟨x, hx⟩

theorem coe_xAut (q : ↥Q) : ((xAut hx q : ↥Q) : G) = x * q * x⁻¹ := rfl

theorem xAut_eq_iff (q : ↥Q) : xAut hx q = q ↔ (q : G) ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, coe_xAut]
  constructor
  · intro h
    calc (q : G) * x = x * q * x⁻¹ * x := by rw [h]
      _ = x * q := by group
  · intro h
    rw [← h]
    group

variable {P : Type*} [Group P] (e : ↥Q ⧸ center ↥Q ≃* P)

@[expose] def phi : MulAut P := MulAut.congr e (GSThmB.Cent516.barAut (xAut hx))

theorem phi_piQ (q : ↥Q) : phi hx e (piQ e q) = piQ e (xAut hx q) := by
  simp only [phi, piQ_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, GSThmB.Cent516.barAut_mk]

theorem phi_phi (hx2 : x * x = 1) (y : P) : phi hx e (phi hx e y) = y := by
  obtain ⟨q, rfl⟩ := piQ_surjective e y
  rw [phi_piQ, phi_piQ]
  congr 1
  apply Subtype.ext
  rw [coe_xAut, coe_xAut]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hxi]
  calc x * (x * (q : G) * x) * x = (x * x) * q * (x * x) := by group
    _ = q := by rw [hx2, one_mul, mul_one]

theorem phi_sq (hx2 : x * x = 1) : phi hx e ^ 2 = 1 := by
  ext y
  rw [pow_two, MulAut.mul_apply, phi_phi hx e hx2, MulAut.one_apply]

theorem fixed_of_perfect {K : Subgroup ↥Q} (hK : ⁅K, K⁆ = K)
    (hKφ : ∀ q ∈ K, phi hx e (piQ e q) = piQ e q) : ∀ q ∈ K, xAut hx q = q :=
  GSThmB.Cent516.fix_of_perfect (xAut hx) K hK fun q hq => by
    have h := hKφ q hq
    rw [phi_piQ, piQ_eq_iff] at h
    have h' := inv_mem h
    rwa [mul_inv_rev, inv_inv] at h'

theorem phi_ne_one (hQ : Group.IsPerfect ↥Q) (hxQ : x ∉ centralizer (Q : Set G)) :
    phi hx e ≠ 1 := by
  intro h1
  apply hxQ
  have htop : ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ = (⊤ : Subgroup ↥Q) := by
    rw [← _root_.commutator_def]
    exact hQ.commutator_eq_top
  have hall := fixed_of_perfect hx e htop fun q _ => by rw [h1]; rfl
  rw [mem_centralizer_iff]
  intro g hg
  exact mem_centralizer_singleton_iff.mp ((xAut_eq_iff hx ⟨g, hg⟩).mp (hall ⟨g, hg⟩ (mem_top _)))

theorem piQ_mem_fixSub {q : ↥Q} (hq : (q : G) ∈ centralizer ({x} : Set G)) :
    piQ e q ∈ fixSub (phi hx e) := by
  rw [mem_fixSub, phi_piQ, (xAut_eq_iff hx q).mpr hq]

theorem conj_mem_centralizer {q c : ↥Q} (hq : piQ e q ∈ fixSub (phi hx e))
    (hc : (c : G) ∈ centralizer ({x} : Set G)) :
    ((q * c * q⁻¹ : ↥Q) : G) ∈ centralizer ({x} : Set G) := by
  rw [← xAut_eq_iff hx]
  have hc' := (xAut_eq_iff hx c).mpr hc
  rw [map_mul, map_mul, map_inv, hc']
  have hz : q⁻¹ * xAut hx q ∈ center ↥Q := by
    have h := hq
    rw [mem_fixSub, phi_piQ, piQ_eq_iff] at h
    have h' := inv_mem h
    rwa [mul_inv_rev, inv_inv] at h'
  obtain ⟨z, hzc, hqz⟩ : ∃ z ∈ center ↥Q, xAut hx q = q * z := ⟨_, hz, by group⟩
  rw [hqz]
  have hzc' : z * c = c * z := (mem_center_iff.mp hzc c).symm
  calc q * z * c * (q * z)⁻¹ = q * (z * c) * z⁻¹ * q⁻¹ := by group
    _ = q * c * q⁻¹ := by rw [hzc']; group

theorem fixSub_le_normalizer :
    fixSub (phi hx e) ≤ normalizer (((CQ Q x).map (piQ e) : Subgroup P) : Set P) := by
  apply Sol76.le_normalizer_of_forall_conj_mem
  rintro y hy _ ⟨c, hc, rfl⟩
  obtain ⟨q, rfl⟩ := piQ_surjective e y
  refine ⟨q * c * q⁻¹, conj_mem_centralizer hx e hy hc, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem map_CQ_le_fixSub : (CQ Q x).map (piQ e) ≤ fixSub (phi hx e) := by
  rintro _ ⟨c, hc, rfl⟩
  exact piQ_mem_fixSub hx e hc

theorem Jp_le_fixSub : Jp e x ≤ fixSub (phi hx e) :=
  (map_mono LQ_le_CQ).trans (map_CQ_le_fixSub hx e)

theorem Jp_le_map_CQ : Jp e x ≤ (CQ Q x).map (piQ e) :=
  map_mono LQ_le_CQ


variable [Finite G]

theorem le_normalizer_Lay :
    Q ⊓ centralizer ({x} : Set G) ≤ normalizer ((Lay Q x : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : (pLayer ↥(Q ⊓ centralizer ({x} : Set G)) 2).Characteristic :=
    CatalogueBPrimeJoin.pLayer_characteristic
  have hN : ((Lay Q x).subgroupOf (Q ⊓ centralizer ({x} : Set G))).Normal := by
    change (((pLayer ↥(Q ⊓ centralizer ({x} : Set G)) 2).map
      (Q ⊓ centralizer ({x} : Set G)).subtype).subgroupOf _).Normal
    have heq : ((pLayer ↥(Q ⊓ centralizer ({x} : Set G)) 2).map
        (Q ⊓ centralizer ({x} : Set G)).subtype).subgroupOf (Q ⊓ centralizer ({x} : Set G)) =
        pLayer ↥(Q ⊓ centralizer ({x} : Set G)) 2 :=
      comap_map_eq_self_of_injective (Q ⊓ centralizer ({x} : Set G)).subtype_injective _
    rw [heq]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer Lay_le).mp hN

theorem le_Lay {K : Subgroup G} (hK : K ≤ Q ⊓ centralizer ({x} : Set G)) (hq : IsQuasisimple K)
    (hs : (K.subgroupOf (Q ⊓ centralizer ({x} : Set G))).IsSubnormal) : K ≤ Lay Q x :=
  Sol76.le_pLayer_of_isQuasisimple hK hq hs

theorem map_CQ_le_normalizer :
    (CQ Q x).map (piQ e) ≤ normalizer ((Jp e x : Subgroup P) : Set P) := by
  apply Sol76.le_normalizer_of_forall_conj_mem
  rintro _ ⟨c, hc, rfl⟩ _ ⟨l, hl, rfl⟩
  refine ⟨c * l * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have hcN := le_normalizer_Lay (Q := Q) (x := x) ⟨c.2, hc⟩
  exact (mem_normalizer_iff.mp hcN (l : G)).mp hl

theorem isSubnormal_Jp : ((Jp e x).subgroupOf (fixSub (phi hx e))).IsSubnormal :=
  Sol76.isSubnormal_subgroupOf_of_le_normalizer (Jp_le_map_CQ e) (map_CQ_le_fixSub hx e)
    (map_CQ_le_normalizer e) (fixSub_le_normalizer hx e)

theorem isComponent_Jp [IsSimpleGroup ↥(Lay Q x)] (hLna : ∃ a b : ↥(Lay Q x), a * b ≠ b * a) :
    IsComponent ((Jp e x).subgroupOf (fixSub (phi hx e))) := by
  have hLZ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hLq : IsQuasisimple ↥(Lay Q x) :=
    LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hLna
  refine ⟨?_, isSubnormal_Jp hx e⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((equivJp e hLZ).trans (subgroupOfEquivOfLe (Jp_le_fixSub hx e)).symm) hLq

theorem le_Jp_of_isComponent {R : Subgroup P} (hRφ : R ≤ fixSub (phi hx e))
    (hR : IsComponent (R.subgroupOf (fixSub (phi hx e)))) : R ≤ Jp e x := by
  obtain ⟨hRq, hRs⟩ := hR
  have hRq' : IsQuasisimple ↥R :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hRφ) hRq
  have hRp : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.mp hRq'.1
  have hker : (piQ e).ker ≤ center ↥Q := (ker_piQ e).le
  have hRr : R ≤ (piQ e).range := by
    rw [MonoidHom.range_eq_top.mpr (piQ_surjective e)]
    exact le_top
  set Rh := GSThmB.Cent516.liftN (piQ e) R with hRh
  have hRhp : ⁅Rh, Rh⁆ = Rh := GSThmB.Cent516.liftN_perfect hker hRp hRr
  have hRhmap : Rh.map (piQ e) = R := GSThmB.Cent516.map_liftN hRp hRr
  have hRhle : Rh ≤ R.comap (piQ e) := GSThmB.Cent516.liftN_le (piQ e) R
  have hfix := fixed_of_perfect hx e hRhp fun q hq => hRφ (hRhle hq)
  have hRhC : Rh ≤ CQ Q x := fun q hq => (xAut_eq_iff hx q).mp (hfix q hq)
  set D := (fixSub (phi hx e)).comap (piQ e) with hD
  let f : ↥D →* ↥(fixSub (phi hx e)) :=
    ((piQ e).comp D.subtype).codRestrict _ (fun d => d.2)
  have h1 : ((R.comap (piQ e)).subgroupOf D).IsSubnormal := by
    have h := hRs.comap f
    have heq : (R.subgroupOf (fixSub (phi hx e))).comap f = (R.comap (piQ e)).subgroupOf D := by
      ext d
      exact Iff.rfl
    rwa [heq] at h
  have hCD : CQ Q x ≤ D := fun q hq => piQ_mem_fixSub hx e hq
  have h2 : ((R.comap (piQ e)).subgroupOf (CQ Q x)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCD h1
  have hRhM : Rh ≤ R.comap (piQ e) ⊓ CQ Q x := le_inf hRhle hRhC
  have h3 : (Rh.subgroupOf (CQ Q x)).IsSubnormal := by
    refine CFSG.GroupTheory.isSubnormal_subgroupOf_trans hRhM inf_le_right ?_ ?_
    · apply Subgroup.Normal.isSubnormal
      rw [normal_subgroupOf_iff_le_normalizer hRhM]
      exact inf_le_left.trans (L219.le_normalizer_commutator _ _)
    · rwa [inf_subgroupOf_right]
  have hRhq : IsQuasisimple ↥Rh := by
    let g : ↥Rh →* ↥R := ((piQ e).comp Rh.subtype).codRestrict R (fun r => hRhle r.2)
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      rw [← hRhmap] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      exact ⟨⟨r, hr⟩, rfl⟩
    have hgker : g.ker ≤ center ↥Rh := by
      intro r hr
      have hr' : (r : ↥Q) ∈ center ↥Q := hker (by
        rw [MonoidHom.mem_ker] at hr ⊢
        exact congrArg Subtype.val hr)
      rw [mem_center_iff]
      intro s
      exact Subtype.ext (mem_center_iff.mp hr' s)
    exact (LocalCores.isQuasisimple_iff_of_surjective (Subgroup.isPerfect_iff.mpr hRhp) g hg
      hgker).mpr hRq'
  have hRhG : Rh.map Q.subtype ≤ Lay Q x := by
    refine le_Lay (fun g hg => ?_)
      (LocalCores.isQuasisimple_of_mulEquiv (Rh.equivMapOfInjective _ Q.subtype_injective) hRhq)
      (isSubnormal_map_subtype h3)
    obtain ⟨q, hq, rfl⟩ := hg
    exact ⟨q.2, hRhC hq⟩
  have hRhL : Rh ≤ LQ Q x := fun q hq => hRhG ⟨q, hq, rfl⟩
  rw [← hRhmap]
  exact map_mono hRhL

end CFSG.ComponentClassification.HarrisLit.C3
