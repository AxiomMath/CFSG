module

public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupCentralizer
public import CFSG.CharacterTheory.Semidihedral.MatrixFourGroupNormalizer
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers

public noncomputable section

namespace CFSG.Semidihedral.ActualFourGroupNormalizer

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.ActualFourGroupCentralizer

universe u v

section Kernel

variable {E : Type u} [Group E]

theorem normalizer_centralizes_of_disjoint (N V : Subgroup E) [N.Normal]
    (hdis : Disjoint N V) (n : E) (hn : n ∈ N ⊓ Subgroup.normalizer (V : Set E)) :
    n ∈ Subgroup.centralizer (V : Set E) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro v hv
  have hnv : n * v * n⁻¹ ∈ V :=
    Subgroup.le_normalizer_iff.mp le_rfl n hn.2 v hv
  have hcommV : n * v * n⁻¹ * v⁻¹ ∈ V := V.mul_mem hnv (V.inv_mem hv)
  have hnq : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn.1
  have hcommN : n * v * n⁻¹ * v⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (n * v * n⁻¹ * v⁻¹) = 1
    simp only [map_mul, map_inv, hnq, one_mul, inv_one, mul_one, mul_inv_cancel]
  have hcomm := Subgroup.disjoint_def.mp hdis hcommN hcommV
  have h : n * v * n⁻¹ = v := mul_inv_eq_one.mp hcomm
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem normalizer_kernel_four [Finite E] (N : Subgroup E) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : E) (hc : t ∈ Subgroup.center E)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hne : t ≠ s) :
    N ⊓ Subgroup.normalizer (KleinFourOddKernel.fourSubgroup t s : Set E) =
      N ⊓ Subgroup.centralizer {s} := by
  have hdis := KleinFourOddKernel.normalOdd_disjoint_four N hN t s hc ht hs hne
  have hcent : Subgroup.centralizer (KleinFourOddKernel.fourSubgroup t s : Set E) =
      Subgroup.centralizer {s} :=
    MatrixFourGroupNormalizer.centralizer_kleinGenerated t s hc
  apply le_antisymm
  · intro n hn
    exact ⟨hn.1, hcent ▸ normalizer_centralizes_of_disjoint N _ hdis n hn⟩
  · intro n hn
    exact ⟨hn.1, Subgroup.centralizer_le_normalizer _ (hcent ▸ hn.2)⟩

end Kernel

section OrderFourLift

variable {E : Type u} {Q : Type v} [Group E] [Group Q]

theorem pgroup_embedding_injective {P : Type*} [Group P]
    (f : E →* Q) (i : P →* E) (hi : Function.Injective i)
    (hP : IsPGroup 2 P) (hker : Nat.Coprime 2 (Nat.card f.ker)) :
    Function.Injective (f.comp i) := by
  apply (f.comp i).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow x
  have hdiv : orderOf x ∣ Nat.card f.ker := by
    rw [← orderOf_injective i hi x]
    exact Subgroup.orderOf_dvd_natCard f.ker hx
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hker.pow_left k) hk hdiv)

theorem odd_kernel_order_four_lift [Finite E] (f : E →* Q)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (t : E) (ht : orderOf t = 2) (hc : t ∈ Subgroup.center E)
    (v : Q) (hv : orderOf v = 4) (hsquare : v ^ 2 = f t) :
    ∃ d : E, orderOf d = 4 ∧ d ^ 2 = t ∧ f d = v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B := Subgroup.zpowers v
  let P := B.comap f
  let g : P →* B := (f.comp P.subtype).codRestrict B (fun x => x.property)
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨x, hx⟩ := hf b
    exact ⟨⟨x, by change f x ∈ B; rw [hx]; exact b.property⟩, Subtype.ext hx⟩
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers, hv]; rfl)
  let U : Sylow 2 P := Sylow.nonempty.some
  have hmap : (U : Subgroup P).map g = ⊤ :=
    ((U.mapSurjective hg).is_maximal'
      (hB.of_injective (⊤ : Subgroup B).subtype Subtype.val_injective) le_top).symm
  let vb : B := ⟨v, Subgroup.mem_zpowers v⟩
  have hvb : vb ∈ (U : Subgroup P).map g := hmap ▸ Subgroup.mem_top vb
  obtain ⟨d0, hd0, hgd⟩ := hvb
  let du : U := ⟨d0, hd0⟩
  let i : U →* E := P.subtype.comp (U : Subgroup P).subtype
  have hi : Function.Injective i :=
    P.subtype_injective.comp (U : Subgroup P).subtype_injective
  have hfi : Function.Injective (f.comp i) :=
    pgroup_embedding_injective f i hi U.isPGroup' hker.coprime_two_left
  have hdu : (f.comp i) du = v := congrArg Subtype.val hgd
  have hduorder : orderOf du = 4 := by
    rw [← orderOf_injective (f.comp i) hfi du, hdu]
    exact hv
  have htP : t ∈ P := by
    change f t ∈ B
    rw [← hsquare]
    exact Subgroup.pow_mem B (Subgroup.mem_zpowers v) 2
  let tp : P := ⟨t, htP⟩
  have htp : orderOf tp = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have htc : tp ∈ Subgroup.center P := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc x)
  let T := Subgroup.zpowers tp
  let : T.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htc)
  have hT : IsPGroup 2 T := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, htp]; rfl)
  have htU : tp ∈ (U : Subgroup P) := hT.le_sylow_of_normal U (Subgroup.mem_zpowers tp)
  let tu : U := ⟨tp, htU⟩
  have hsqu : du ^ 2 = tu := by
    apply hfi
    rw [map_pow, hdu]
    exact hsquare
  refine ⟨i du, ?_, ?_, hdu⟩
  · exact (orderOf_injective i hi du).trans hduorder
  · have h := congrArg i hsqu
    change i (du ^ 2) = t at h
    simpa only [map_pow] using h

end OrderFourLift

variable {G : Type u} [Group G]

abbrev K {t : G} (s : C t) := Subgroup.normalizer (V s : Set (C t))

abbrev N0InK {t : G} (s : C t) := (N t).subgroupOf (K s)

abbrev DInK {t : G} (s : C t) := (D s).subgroupOf (K s)

theorem D_eq_centralizer_V {t : G} (s : C t) :
    D s = Subgroup.centralizer (V s : Set (C t)) :=
  (MatrixFourGroupNormalizer.centralizer_kleinGenerated (tInC t) s
    (tInC_central t)).symm

theorem D_le_K {t : G} (s : C t) : D s ≤ K s := by
  rw [D_eq_centralizer_V s]
  exact Subgroup.centralizer_le_normalizer _

instance DInK_normal {t : G} (s : C t) : (DInK s).Normal := by
  change ((D s).subgroupOf (K s)).Normal
  rw [D_eq_centralizer_V s]
  exact Subgroup.normal_subgroupOf_centralizer_normalizer _

instance N0InK_normal {t : G} (s : C t) : (N0InK s).Normal := inferInstance

theorem actual_kernel_intersection [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    N t ⊓ K s = N t ⊓ D s := by
  have htC : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  exact normalizer_kernel_four (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
    (tInC t) s (tInC_central t) htC hs hst.symm

theorem N0InK_map_ambient [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    (N0InK s).map (K s).subtype = N t ⊓ D s := by
  rw [Subgroup.subgroupOf_map_subtype]
  exact actual_kernel_intersection ht s hs hst

@[expose] def N0EquivK [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) : N0 s ≃* N0InK s where
  toFun x := ⟨⟨x.val.val, D_le_K s x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩,
    (actual_kernel_intersection ht s hs hst ▸
      (show x.val.val ∈ N t ⊓ K s from ⟨x.property, x.val.property⟩)).2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem N0EquivK_value [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) (x : N0 s) :
    (N0EquivK ht s hs hst x).val.val = x.val.val := rfl

theorem N0InK_card [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Nat.card (N0InK s) = Nat.card (N0 s) :=
  (Nat.card_congr (N0EquivK ht s hs hst).toEquiv).symm

theorem N0InK_odd [Finite G] {t : G} (s : C t) : Odd (Nat.card (N0InK s)) := by
  apply Nat.coprime_two_left.mp
  exact CFSG.pPrimeCore_coprime_card.of_dvd_right
    (Subgroup.card_comap_dvd_of_injective (N t) (K s).subtype (K s).subtype_injective)

theorem V_le_K {t : G} (s : C t) : V s ≤ K s := Subgroup.le_normalizer

theorem t_mem_V {t : G} (s : C t) : tInC t ∈ V s :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem s_mem_V {t : G} (s : C t) : s ∈ V s :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

@[expose] def tInK {t : G} (s : C t) : K s := ⟨tInC t, V_le_K s (t_mem_V s)⟩

theorem tInK_central {t : G} (s : C t) : tInK s ∈ Subgroup.center (K s) := by
  apply Subgroup.mem_center_iff.mpr
  intro k
  exact Subtype.ext (Subgroup.mem_center_iff.mp (tInC_central t) k)

@[expose] def sInK {t : G} (s : C t) : K s := ⟨s, V_le_K s (s_mem_V s)⟩

@[expose] def onNormalizer {t : G} (s : C t) :
    K s →* Subgroup.normalizer ((V s).map (nu t) : Set (H t)) :=
  ((nu t).comp (K s).subtype).codRestrict _ (fun k =>
    Subgroup.le_normalizer_map (nu t) (Subgroup.mem_map_of_mem (nu t) k.property))

theorem onNormalizer_value {t : G} (s : C t) (k : K s) :
    (onNormalizer s k : H t) = nu t (k : C t) := rfl

theorem onNormalizer_kernel {t : G} (s : C t) :
    (onNormalizer s).ker = N0InK s := by
  ext k
  change (onNormalizer s k = 1) ↔ (k : C t) ∈ N t
  rw [← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff _

theorem actual_normalizer_image [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    (K s).map (nu t) = Subgroup.normalizer ((V s).map (nu t) : Set (H t)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hV : IsPGroup 2 (V s) := IsPGroup.iff_card.mpr
    ⟨2, KleinFourOddKernel.fourSubgroup_card (tInC t) s (tInC_central t)
      htC hs hst.symm⟩
  exact CFSG.SignalizerFunctor.Helpers.coprime_quotient_normalizer_image 2
    Nat.prime_two (N t) (V s) CFSG.pPrimeCore_coprime_card hV

theorem onNormalizer_surjective [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Function.Surjective (onNormalizer s) := by
  intro q
  have hq : (q : H t) ∈ (K s).map (nu t) := by
    simpa only [actual_normalizer_image ht s hs hst] using q.property
  obtain ⟨k, hk, heq⟩ := hq
  exact ⟨⟨k, hk⟩, Subtype.ext heq⟩

@[expose] def normalizerQuotientEquiv [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    K s ⧸ N0InK s ≃* Subgroup.normalizer ((V s).map (nu t) : Set (H t)) :=
  (QuotientGroup.quotientMulEquivOfEq (onNormalizer_kernel s).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (onNormalizer s)
      (onNormalizer_surjective ht s hs hst))

theorem normalizerQuotientEquiv_mk [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) (k : K s) :
    (normalizerQuotientEquiv ht s hs hst (QuotientGroup.mk' (N0InK s) k) : H t) =
      nu t (k : C t) := rfl

theorem actual_order_four_lift [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (v : Subgroup.normalizer ((V s).map (nu t) : Set (H t)))
    (hv : orderOf v = 4) (hsquare : v ^ 2 = onNormalizer s (tInK s)) :
    ∃ d : K s, orderOf d = 4 ∧ d ^ 2 = tInK s ∧ onNormalizer s d = v := by
  have htK : orderOf (tInK s) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact ht
  have hker : Odd (Nat.card (onNormalizer s).ker) := by
    rw [onNormalizer_kernel]
    exact N0InK_odd s
  exact odd_kernel_order_four_lift (onNormalizer s)
    (onNormalizer_surjective ht s hs hst) hker (tInK s) htK (tInK_central s)
    v hv hsquare

theorem quotient_on_V_injective [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Function.Injective ((nu t).subgroupMap (V s)) := by
  have htC : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  exact KleinFourOddKernel.quotient_onFour_injective (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
    (tInC t) s (tInC_central t) htC hs hst.symm

theorem conjugation_lifts_on_V [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) (d : K s)
    (hquot : nu t ((d : C t) * s * (d : C t)⁻¹) = nu t (tInC t * s)) :
    (d : C t) * s * (d : C t)⁻¹ = tInC t * s := by
  have hconj : (d : C t) * s * (d : C t)⁻¹ ∈ V s :=
    Subgroup.le_normalizer_iff.mp le_rfl (d : C t) d.property s (s_mem_V s)
  have hprod : tInC t * s ∈ V s := (V s).mul_mem (t_mem_V s) (s_mem_V s)
  have h := quotient_on_V_injective ht s hs hst
    (a₁ := ⟨_, hconj⟩) (a₂ := ⟨_, hprod⟩) (Subtype.ext hquot)
  exact congrArg Subtype.val h

@[expose] def DToK {t : G} (s : C t) : D s →* K s := Subgroup.inclusion (D_le_K s)

abbrev RInK {t : G} (s : C t) := (R s).map (DToK s)

theorem RInK_eq_core {t : G} (s : C t) :
    RInK s = (CFSG.pPrimeCore 2 (DInK s)).map (DInK s).subtype := by
  let e : D s ≃* DInK s := (Subgroup.subgroupOfEquivOfLe (D_le_K s)).symm
  have hcomp : (DInK s).subtype.comp e.toMonoidHom = DToK s := rfl
  rw [← CFSG.pPrimeCore_map_iso 2 e, Subgroup.map_map, hcomp]
  change (R s).map (DToK s) = _
  rw [show R s = CFSG.pPrimeCore 2 (D s) from
    KleinFourOddKernel.piCore_odd_eq_pPrimeCore]

instance RInK_normal {t : G} (s : C t) : (RInK s).Normal := by
  rw [RInK_eq_core s]
  exact ConjAct.normal_of_characteristic_of_normal

@[expose] def REquivK {t : G} (s : C t) : R s ≃* RInK s :=
  Subgroup.equivMapOfInjective _ (DToK s) (Subgroup.inclusion_injective _)

theorem REquivK_value {t : G} (s : C t) (r : R s) :
    (REquivK s r).val.val = r.val.val := rfl

theorem N0InK_le_RInK [Finite G] {t : G} (ht : orderOf t = 2)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) : N0InK s ≤ RInK s := by
  intro k hk
  have hD : (k : C t) ∈ D s :=
    (actual_kernel_intersection ht s hs hst ▸
      (show (k : C t) ∈ N t ⊓ K s from ⟨hk, k.property⟩)).2
  let dk : D s := ⟨k, hD⟩
  have hR : dk ∈ R s :=
    KleinFourOddKernel.centralizerKernel_le_oddKernel (N t)
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) s hk
  exact ⟨dk, hR, Subtype.ext rfl⟩

@[expose] def conjugationOnR {t : G} (s : C t) (d : K s) : MulAut (R s) :=
  (REquivK s).trans ((MulAut.conjNormal (H := RInK s) d).trans (REquivK s).symm)

theorem conjugationOnR_value {t : G} (s : C t) (d : K s) (r : R s) :
    ((conjugationOnR s d r : D s) : C t) =
      (d : C t) * ((r : D s) : C t) * (d : C t)⁻¹ := by
  calc
    ((conjugationOnR s d r : D s) : C t) =
        (REquivK s (conjugationOnR s d r)).val.val :=
      (REquivK_value s _).symm
    _ = ((MulAut.conjNormal (H := RInK s) d) (REquivK s r)).val.val := by
      change ((REquivK s) ((REquivK s).symm
        ((MulAut.conjNormal (H := RInK s) d) (REquivK s r)))).val.val = _
      rw [MulEquiv.apply_symm_apply]
    _ = (d : C t) * ((r : D s) : C t) * (d : C t)⁻¹ := rfl

theorem conjugationOnR_kernel {t : G} (s : C t) (d : K s) :
    N0InR s ≤ (N0InR s).comap (conjugationOnR s d).toMonoidHom := by
  intro r hr
  change ((conjugationOnR s d r : D s) : C t) ∈ N t
  rw [conjugationOnR_value s d r]
  exact Subgroup.Normal.conj_mem (inferInstance : (N t).Normal)
    ((r : D s) : C t) hr (d : C t)

@[expose] def conjugationOnOddQuotient {t : G} (s : C t) (d : K s) :
    R s ⧸ N0InR s →* R s ⧸ N0InR s :=
  QuotientGroup.map (N0InR s) (N0InR s) (conjugationOnR s d).toMonoidHom
    (conjugationOnR_kernel s d)

theorem conjugationOnOddQuotient_mk {t : G} (s : C t) (d : K s) (r : R s) :
    conjugationOnOddQuotient s d (QuotientGroup.mk' (N0InR s) r) =
      QuotientGroup.mk' (N0InR s) (conjugationOnR s d r) := rfl

section OriginalModel

variable (F : Type v) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
variable (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
variable {t : G} (s : C t) (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)

theorem original_V_image
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    (MatrixTorus.originalV0 F a A hfix).map Psi.toMonoidHom = (V s).map (nu t) := by
  change (Subgroup.zpowers (MatrixTorus.originalZ F a A hfix) ⊔
    Subgroup.zpowers (MatrixTorus.originalU F a A hfix)).map Psi.toMonoidHom =
      (Subgroup.zpowers (tInC t) ⊔ Subgroup.zpowers s).map (nu t)
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change Subgroup.zpowers (Psi (MatrixTorus.originalZ F a A hfix)) ⊔
    Subgroup.zpowers (Psi (MatrixTorus.originalU F a A hfix)) = _
  rw [hz, hu]

@[expose] def toOriginalModel : K s →* MatrixTorus.OriginalH F a A hfix :=
  Psi.symm.toMonoidHom.comp ((nu t).comp (K s).subtype)

@[expose] def quotientToOriginalModel : K s ⧸ N0InK s →* MatrixTorus.OriginalH F a A hfix :=
  QuotientGroup.lift (N0InK s) (toOriginalModel F a A hfix s Psi) (by
    intro k hk
    change Psi.symm (nu t (k : C t)) = 1
    have hn : nu t (k : C t) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [hn, map_one])

theorem quotientToOriginalModel_mk (k : K s) :
    quotientToOriginalModel F a A hfix s Psi (QuotientGroup.mk' (N0InK s) k) =
      Psi.symm (nu t (k : C t)) := rfl

theorem original_D_image [Finite G] (hs : orderOf s = 2)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    (D s).map (Psi.symm.toMonoidHom.comp (nu t)) =
      Subgroup.centralizer {MatrixTorus.originalU F a A hfix} := by
  ext m
  constructor
  · rintro ⟨d, hd, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Psi.injective
    have h := congrArg (nu t) (Subgroup.mem_centralizer_singleton_iff.mp hd)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      MulEquiv.apply_symm_apply, hu] using h
  · intro hm
    have hq : Psi m ∈ Subgroup.centralizer {nu t s} := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h := congrArg Psi (Subgroup.mem_centralizer_singleton_iff.mp hm)
      simpa only [map_mul, hu] using h
    obtain ⟨d, hqd, hd⟩ := KleinFourOddKernel.quotient_centralizer_lift (N t)
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) s hs _ hq
    exact ⟨d, hd, by change Psi.symm (nu t d) = m; rw [hqd, MulEquiv.symm_apply_apply]⟩

theorem original_DInK_image [Finite G] (hs : orderOf s = 2)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    (DInK s).map (toOriginalModel F a A hfix s Psi) =
      Subgroup.centralizer {MatrixTorus.originalU F a A hfix} := by
  change (DInK s).map
    ((Psi.symm.toMonoidHom.comp (nu t)).comp (K s).subtype) = _
  rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (D_le_K s), original_D_image F a A hfix s Psi hs hu]

abbrev OriginalOddImage :=
  (MatrixTorus.originalOddSemilinear F a A hfix).map Psi.toMonoidHom

theorem original_B_odd [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hA : Odd (Nat.card A)) : Odd (Nat.card (OriginalOddImage F a A hfix Psi)) := by
  have hcard : Nat.card (OriginalOddImage F a A hfix Psi) =
      Nat.card (MatrixTorus.originalOddSemilinear F a A hfix) :=
    (Nat.card_congr (Psi.subgroupMap (MatrixTorus.originalOddSemilinear F a A hfix)).toEquiv).symm
  rw [hcard]
  exact original_odd_odd F A a hfix hF ha hA

theorem original_model_lifted [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    KleinFourOddKernel.LiftedCentralizerConclusion (N t) (tInC t) s (OriginalOddImage F a A hfix Psi) := by
  have hN : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe _).symm.trans ht
  have hB : OriginalOddImage F a A hfix Psi ≤ Subgroup.centralizer {nu t s} := by
    rintro q ⟨m, hm, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg Psi (Subgroup.mem_centralizer_singleton_iff.mp
      (original_odd_le_centralizer F A a hfix hm))
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, hu] using h
  have hBo := original_B_odd F a A hfix Psi hF ha hA
  have hcardB : Nat.card (OriginalOddImage F a A hfix Psi) =
      Nat.card A * (MatrixTorus.torusSize (Nat.card F) / 2) := by
    rw [show Nat.card (OriginalOddImage F a A hfix Psi) =
      Nat.card (MatrixTorus.originalOddSemilinear F a A hfix) from
        (Nat.card_congr (Psi.subgroupMap _).toEquiv).symm]
    exact original_odd_card F A a hfix hF ha
  have hcardQ : Nat.card (Subgroup.centralizer {nu t s}) =
      2 * Nat.card A * MatrixTorus.torusSize (Nat.card F) :=
    (Nat.card_congr (centralizerEquiv Psi (MatrixTorus.originalU F a A hfix)
      (nu t s) hu).toEquiv).symm.trans (original_centralizer_card F A a hfix hF ha)
  have hdir : KleinFourOddKernel.IsInternalDirectProduct
      (KleinFourOddKernel.quotientFourInCentralizer (N t) (tInC t) s)
      (KleinFourOddKernel.quotientOddInCentralizer (N t) s (OriginalOddImage F a A hfix Psi)) := by
    have hfour := KleinFourOddKernel.quotientFourInCentralizer_card
      (N t) hN (tInC t) s (tInC_central t) htC hs hst.symm
    have hoddcard := KleinFourOddKernel.quotientOddInCentralizer_card (N t) s _ hB
    refine ⟨Subgroup.isComplement'_of_coprime ?_ ?_, ?_⟩
    · rw [hfour, hoddcard, hcardB, hcardQ]
      nth_rw 2 [MatrixTorus.torusSize_two_mul_half hF]
      ring
    · rw [hfour, hoddcard]
      exact (show Nat.Coprime (2 ^ 2) (Nat.card (OriginalOddImage F a A hfix Psi)) from
        hBo.coprime_two_left.pow_left 2)
    · intro v b
      exact (Subgroup.mem_center_iff.mp
        (KleinFourOddKernel.quotientFourInCentralizer_central (N t) hN (tInC t) s
          (tInC_central t) htC hs v.property) b).symm
  exact KleinFourOddKernel.odd_kernel_central_Klein_four_centralizer_lifting (N t)
    hN (tInC t) s (tInC_central t) htC hs hst.symm _ hB hBo hdir

theorem original_RInK_image [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    (RInK s).map (toOriginalModel F a A hfix s Psi) =
      MatrixTorus.originalOddSemilinear F a A hfix := by
  have h := (original_model_lifted F a A hfix s Psi ht hs hst hu hF ha hA).original_range
  have hnu : (R s).map ((nu t).comp (D s).subtype) = OriginalOddImage F a A hfix Psi := by
    change (((nu t).comp (D s).subtype).comp (R s).subtype).range = _ at h
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    exact h
  have hcomp : (toOriginalModel F a A hfix s Psi).comp (DToK s) =
      Psi.symm.toMonoidHom.comp ((nu t).comp (D s).subtype) := rfl
  rw [RInK, Subgroup.map_map, hcomp, ← Subgroup.map_map, hnu]
  change ((MatrixTorus.originalOddSemilinear F a A hfix).map Psi.toMonoidHom).map
    Psi.symm.toMonoidHom = _
  rw [Subgroup.map_map, show Psi.symm.toMonoidHom.comp Psi.toMonoidHom =
    MonoidHom.id _ from MonoidHom.ext (fun m => Psi.symm_apply_apply m), Subgroup.map_id]

@[expose] def actualOddModelEquiv [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    R s ⧸ N0InR s ≃* MatrixTorus.originalOddSemilinear F a A hfix :=
  (Classical.choose
    (original_model_lifted F a A hfix s Psi ht hs hst hu hF ha hA).first_isomorphism).trans
      (Psi.subgroupMap (MatrixTorus.originalOddSemilinear F a A hfix)).symm

theorem actualOddModelEquiv_mk [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) (r : R s) :
    Psi (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
      (QuotientGroup.mk' (N0InR s) r)) = nu t ((r : D s) : C t) := by
  let e := Classical.choose
    (original_model_lifted F a A hfix s Psi ht hs hst hu hF ha hA).first_isomorphism
  have he := Classical.choose_spec
    (original_model_lifted F a A hfix s Psi ht hs hst hu hF ha hA).first_isomorphism r
  change Psi ((Psi.subgroupMap _).symm (e (QuotientGroup.mk' (N0InR s) r))) = _
  have h := congrArg Subtype.val ((Psi.subgroupMap _).apply_symm_apply
    (e (QuotientGroup.mk' (N0InR s) r)))
  exact h.trans he

@[expose] def originalOddCoordinateEquiv :
    OriginalWProduct F A a hfix ≃* MatrixTorus.originalOddSemilinear F a A hfix :=
  (MulEquiv.ofBijective (originalOddInclusion F A a hfix).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
      (originalOddInclusion_injective F A a hfix),
      MonoidHom.rangeRestrict_surjective _⟩).trans
        (MulEquiv.subgroupCongr (originalOddInclusion_range F A a hfix))

theorem originalOddCoordinateEquiv_value (w : OriginalWProduct F A a hfix) :
    (originalOddCoordinateEquiv F a A hfix w : MatrixTorus.OriginalH F a A hfix) =
      originalOddInclusion F A a hfix w := rfl

@[expose] def actualOddProductEquiv [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    R s ⧸ N0InR s ≃* OriginalWProduct F A a hfix :=
  (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA).trans
    (originalOddCoordinateEquiv F a A hfix).symm

theorem actualOddProductEquiv_mk [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) (r : R s) :
    Psi (originalOddInclusion F A a hfix
      (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
        (QuotientGroup.mk' (N0InR s) r))) = nu t ((r : D s) : C t) := by
  rw [← originalOddCoordinateEquiv_value]
  change Psi ((originalOddCoordinateEquiv F a A hfix)
    ((originalOddCoordinateEquiv F a A hfix).symm
      (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
        (QuotientGroup.mk' (N0InR s) r)))) = _
  rw [MulEquiv.apply_symm_apply, actualOddModelEquiv_mk]

theorem actualOddModelEquiv_conjugation [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (d : K s) (q : R s ⧸ N0InR s) :
    (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
      (conjugationOnOddQuotient s d q) : MatrixTorus.OriginalH F a A hfix) =
      toOriginalModel F a A hfix s Psi d *
        (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA q :
          MatrixTorus.OriginalH F a A hfix) *
        (toOriginalModel F a A hfix s Psi d)⁻¹ := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N0InR s) q
  apply Psi.injective
  calc
    Psi (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
        (conjugationOnOddQuotient s d (QuotientGroup.mk' (N0InR s) r))) =
        Psi (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
          (QuotientGroup.mk' (N0InR s) (conjugationOnR s d r))) :=
      congrArg (fun q => Psi (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA q))
        (conjugationOnOddQuotient_mk s d r)
    _ = nu t ((conjugationOnR s d r : D s) : C t) :=
      actualOddModelEquiv_mk F a A hfix s Psi ht hs hst hu hF ha hA _
    _ = nu t (d : C t) * nu t ((r : D s) : C t) * (nu t (d : C t))⁻¹ :=
      (congrArg (nu t) (conjugationOnR_value s d r)).trans (by
        rw [map_mul, map_mul, map_inv])
    _ = Psi (toOriginalModel F a A hfix s Psi d *
        (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA
          (QuotientGroup.mk' (N0InR s) r) : MatrixTorus.OriginalH F a A hfix) *
        (toOriginalModel F a A hfix s Psi d)⁻¹) := by
      have hd : Psi (toOriginalModel F a A hfix s Psi d) = nu t (d : C t) :=
        Psi.apply_symm_apply _
      have hr := actualOddModelEquiv_mk F a A hfix s Psi ht hs hst hu hF ha hA r
      exact (Psi.map_mul _ _).trans
        (congrArg₂ (fun b c => b * c)
          ((Psi.map_mul _ _).trans (congrArg₂ (fun b c => b * c) hd hr))
          ((Psi.map_inv _).trans (congrArg Inv.inv hd))) |>.symm

theorem actualOddProductEquiv_coordinates [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (q : R s ⧸ N0InR s) :
    originalOddInclusion F A a hfix
      (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA q) =
      (actualOddModelEquiv F a A hfix s Psi ht hs hst hu hF ha hA q :
        MatrixTorus.OriginalH F a A hfix) :=
  congrArg Subtype.val ((originalOddCoordinateEquiv F a A hfix).apply_symm_apply _)

theorem actualOddProductEquiv_conjugation [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (d : K s) (q : R s ⧸ N0InR s) :
    originalOddInclusion F A a hfix
      (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
        (conjugationOnOddQuotient s d q)) =
      toOriginalModel F a A hfix s Psi d *
        originalOddInclusion F A a hfix
          (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA q) *
        (toOriginalModel F a A hfix s Psi d)⁻¹ :=
  (actualOddProductEquiv_coordinates F a A hfix s Psi ht hs hst hu hF ha hA _).trans
    ((actualOddModelEquiv_conjugation F a A hfix s Psi ht hs hst hu hF ha hA d q).trans
      (congrArg (fun m => toOriginalModel F a A hfix s Psi d * m *
        (toOriginalModel F a A hfix s Psi d)⁻¹)
          (actualOddProductEquiv_coordinates F a A hfix s Psi ht hs hst hu hF ha hA q).symm))

theorem quotient_conjugation_inverts_W [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) (d : K s)
    (himage : nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy))
    (w : MatrixTorus.W F a) :
    let e := actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
    e (conjugationOnOddQuotient s d (e.symm (SemidirectProduct.inl w))) =
      SemidirectProduct.inl w⁻¹ := by
  dsimp only
  let e := actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
  have hd : toOriginalModel F a A hfix s Psi d =
      MatrixFourGroupNormalizer.X F a A hfix x y hxy := by
    change Psi.symm (nu t (d : C t)) = _
    rw [himage, MulEquiv.symm_apply_apply]
  apply originalOddInclusion_injective F A a hfix
  calc
    originalOddInclusion F A a hfix (e (conjugationOnOddQuotient s d
        (e.symm (SemidirectProduct.inl w)))) =
        toOriginalModel F a A hfix s Psi d *
          originalOddInclusion F A a hfix (e (e.symm (SemidirectProduct.inl w))) *
          (toOriginalModel F a A hfix s Psi d)⁻¹ :=
      actualOddProductEquiv_conjugation F a A hfix s Psi ht hs hst hu hF ha hA d _
    _ = MatrixFourGroupNormalizer.X F a A hfix x y hxy *
        MatrixFourGroupNormalizer.WInH F a A hfix w *
        (MatrixFourGroupNormalizer.X F a A hfix x y hxy)⁻¹ := by
      rw [hd, e.apply_symm_apply]
      rfl
    _ = MatrixFourGroupNormalizer.WInH F a A hfix w⁻¹ :=
      MatrixFourGroupNormalizer.W_X_action F a A hfix x y hxy w
    _ = originalOddInclusion F A a hfix (SemidirectProduct.inl w⁻¹) := rfl

theorem quotient_conjugation_fixes_A [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (d : K s)
    (himage : nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy))
    (sigma : A) :
    let e := actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
    e (conjugationOnOddQuotient s d (e.symm (SemidirectProduct.inr sigma))) =
      SemidirectProduct.inr sigma := by
  dsimp only
  let e := actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
  have hd : toOriginalModel F a A hfix s Psi d =
      MatrixFourGroupNormalizer.X F a A hfix x y hxy := by
    change Psi.symm (nu t (d : C t)) = _
    rw [himage, MulEquiv.symm_apply_apply]
  apply originalOddInclusion_injective F A a hfix
  calc
    originalOddInclusion F A a hfix (e (conjugationOnOddQuotient s d
        (e.symm (SemidirectProduct.inr sigma)))) =
        toOriginalModel F a A hfix s Psi d *
          originalOddInclusion F A a hfix (e (e.symm (SemidirectProduct.inr sigma))) *
          (toOriginalModel F a A hfix s Psi d)⁻¹ :=
      actualOddProductEquiv_conjugation F a A hfix s Psi ht hs hst hu hF ha hA d _
    _ = MatrixFourGroupNormalizer.X F a A hfix x y hxy *
        MatrixTorus.originalFieldInH F a A hfix sigma *
        (MatrixFourGroupNormalizer.X F a A hfix x y hxy)⁻¹ := by
      rw [hd, e.apply_symm_apply]
      rfl
    _ = MatrixTorus.originalFieldInH F a A hfix sigma :=
      (congrArg (fun m => m * (MatrixFourGroupNormalizer.X F a A hfix x y hxy)⁻¹)
        (MatrixFourGroupNormalizer.field_commutes_X F a A hfix x y hxy sigma).eq.symm).trans
          (by group)
    _ = originalOddInclusion F A a hfix (SemidirectProduct.inr sigma) := rfl

@[expose] def originalNormalizerImageEquiv
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    MatrixFourGroupNormalizer.Normalizer F a A hfix ≃*
      Subgroup.normalizer ((V s).map (nu t) : Set (H t)) :=
  (Psi.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    change (Subgroup.normalizer (MatrixTorus.originalV0 F a A hfix :
      Set (MatrixTorus.OriginalH F a A hfix))).map Psi.toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq, original_V_image F a A hfix s Psi hz hu]))

theorem originalNormalizerImageEquiv_value
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (m : MatrixFourGroupNormalizer.Normalizer F a A hfix) :
    (originalNormalizerImageEquiv F a A hfix s Psi hz hu m : H t) = Psi m := rfl

@[expose] def actualModelNormalizerEquiv [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    K s ⧸ N0InK s ≃* MatrixFourGroupNormalizer.Normalizer F a A hfix :=
  (normalizerQuotientEquiv ht s hs hst).trans
    (originalNormalizerImageEquiv F a A hfix s Psi hz hu).symm

theorem actualModelNormalizerEquiv_mk [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) (k : K s) :
    (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu
      (QuotientGroup.mk' (N0InK s) k) : MatrixTorus.OriginalH F a A hfix) =
        Psi.symm (nu t (k : C t)) := rfl

theorem actualModelNormalizerEquiv_value [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (q : K s ⧸ N0InK s) :
    (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu q :
      MatrixTorus.OriginalH F a A hfix) = quotientToOriginalModel F a A hfix s Psi q := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N0InK s) q
  rfl

abbrev DInNormalizerQuotient := (DInK s).map (QuotientGroup.mk' (N0InK s))

abbrev RInNormalizerQuotient := (RInK s).map (QuotientGroup.mk' (N0InK s))

abbrev ModelCentralizer :=
  (Subgroup.centralizer {MatrixTorus.originalU F a A hfix}).subgroupOf
    (MatrixFourGroupNormalizer.Normalizer F a A hfix)

abbrev ModelOdd := (MatrixTorus.originalOddSemilinear F a A hfix).subgroupOf
  (MatrixFourGroupNormalizer.Normalizer F a A hfix)

theorem actualModelNormalizerEquiv_D_image [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    (DInNormalizerQuotient s).map
      (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).toMonoidHom =
        ModelCentralizer F a A hfix := by
  apply Subgroup.map_injective
    (MatrixFourGroupNormalizer.Normalizer F a A hfix).subtype_injective
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (MatrixFourGroupNormalizer.centralizer_le_normalizer_original F a A hfix)]
  have hc : ((MatrixFourGroupNormalizer.Normalizer F a A hfix).subtype.comp
      (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).toMonoidHom).comp
        (QuotientGroup.mk' (N0InK s)) = toOriginalModel F a A hfix s Psi :=
    MonoidHom.ext (actualModelNormalizerEquiv_mk F a A hfix s Psi ht hs hst hz hu)
  rw [hc]
  exact original_DInK_image F a A hfix s Psi hs hu

theorem actualModelNormalizerEquiv_R_image [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    (RInNormalizerQuotient s).map
      (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).toMonoidHom =
        ModelOdd F a A hfix := by
  apply Subgroup.map_injective
    (MatrixFourGroupNormalizer.Normalizer F a A hfix).subtype_injective
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((original_odd_le_centralizer F A a hfix).trans
      (MatrixFourGroupNormalizer.centralizer_le_normalizer_original F a A hfix))]
  have hc : ((MatrixFourGroupNormalizer.Normalizer F a A hfix).subtype.comp
      (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).toMonoidHom).comp
        (QuotientGroup.mk' (N0InK s)) = toOriginalModel F a A hfix s Psi :=
    MonoidHom.ext (actualModelNormalizerEquiv_mk F a A hfix s Psi ht hs hst hz hu)
  rw [hc]
  exact original_RInK_image F a A hfix s Psi ht hs hst hu hF ha hA

@[expose] def modelCentralizerDirectEquiv [Finite F]
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    MatrixTorus.originalV0 F a A hfix × MatrixTorus.originalOddSemilinear F a A hfix ≃*
      ModelCentralizer F a A hfix :=
  (MatrixTorus.originalDirectEquiv F a A hfix hF ha).trans
    (Subgroup.subgroupOfEquivOfLe
      (MatrixFourGroupNormalizer.centralizer_le_normalizer_original F a A hfix)).symm

theorem modelCentralizerDirectEquiv_value [Finite F]
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (v : MatrixTorus.originalV0 F a A hfix)
    (b : MatrixTorus.originalOddSemilinear F a A hfix) :
    ((modelCentralizerDirectEquiv F a A hfix hF ha (v, b) :
      MatrixFourGroupNormalizer.Normalizer F a A hfix) :
        MatrixTorus.OriginalH F a A hfix) = (v : MatrixTorus.OriginalH F a A hfix) * b :=
  MatrixTorus.originalDirectEquiv_apply F a A hfix hF ha (v, b)

abbrev ModelNormalProduct [Finite F] (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :=
  SemidirectProduct (MatrixTorus.W F a)
    (MatrixFourGroupNormalizer.S0 F a A hfix x y hxy × A)
    (MatrixFourGroupNormalizer.normalizerAction F a A hfix x y hxy)

@[expose] def actualNormalizerProductEquiv [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    K s ⧸ N0InK s ≃* ModelNormalProduct F a A hfix x y hxy :=
  (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).trans
    (MatrixFourGroupNormalizer.NormalizerEquiv F a A hfix
      hF ha x y hxy).symm

theorem actualNormalizerProductEquiv_mk [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (k : K s) :
    let p := actualNormalizerProductEquiv F a A hfix s Psi ht hs hst hz hu
      hF ha x y hxy (QuotientGroup.mk' (N0InK s) k)
    Psi (MatrixFourGroupNormalizer.WInH F a A hfix p.left *
      p.right.1.val * MatrixTorus.originalFieldInH F a A hfix p.right.2) =
        nu t (k : C t) := by
  dsimp only
  rw [← MatrixFourGroupNormalizer.NormalizerEquiv_coe
    F a A hfix hF ha x y hxy]
  change Psi ((MatrixFourGroupNormalizer.NormalizerEquiv F a A hfix
    hF ha x y hxy) ((MatrixFourGroupNormalizer.NormalizerEquiv
      F a A hfix hF ha x y hxy).symm
        (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu
          (QuotientGroup.mk' (N0InK s) k)))) = _
  rw [MulEquiv.apply_symm_apply, actualModelNormalizerEquiv_mk, MulEquiv.apply_symm_apply]

theorem actual_original_X_lift [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    ∃ d : K s, orderOf d = 4 ∧ d ^ 2 = tInK s ∧
      (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
      nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) := by
  let X0 : MatrixFourGroupNormalizer.Normalizer F a A hfix :=
    ⟨MatrixFourGroupNormalizer.X F a A hfix x y hxy,
      MatrixFourGroupNormalizer.S0_le_normalizer F a A hfix x y hxy
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))⟩
  let v := originalNormalizerImageEquiv F a A hfix s Psi hz hu X0
  have hv : orderOf v = 4 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact MatrixFourGroupNormalizer.X_order F a A hfix hF x y hxy
  have hv2 : v ^ 2 = onNormalizer s (tInK s) := by
    apply Subtype.ext
    change Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) ^ 2 = nu t (tInC t)
    rw [← map_pow, MatrixFourGroupNormalizer.X_square, hz]
  obtain ⟨d, hd, hd2, hdv⟩ := actual_order_four_lift ht s hs hst v hv hv2
  have himage : nu t (d : C t) =
      Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) :=
    congrArg Subtype.val hdv
  refine ⟨d, hd, hd2, conjugation_lifts_on_V ht s hs hst d ?_, himage⟩
  calc
    nu t ((d : C t) * s * (d : C t)⁻¹) =
        Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) *
          Psi (MatrixTorus.originalU F a A hfix) *
          (Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy))⁻¹ := by
      rw [map_mul, map_mul, map_inv, himage, ← hu]
    _ = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy *
        MatrixTorus.originalU F a A hfix *
        (MatrixFourGroupNormalizer.X F a A hfix x y hxy)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    _ = Psi (MatrixTorus.originalZ F a A hfix * MatrixTorus.originalU F a A hfix) :=
      congrArg Psi (MatrixFourGroupNormalizer.X_conjugates_U F a A hfix x y hxy)
    _ = nu t (tInC t * s) := by rw [map_mul, hz, hu, map_mul]

theorem original_s_not_mem_rotation
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) (d : K s)
    (himage : nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy)) :
    sInK s ∉ Subgroup.zpowers d := by
  intro h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  have hq : Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy ^ i) =
      Psi (MatrixTorus.originalU F a A hfix) := by
    rw [map_zpow, ← himage, hu, ← map_zpow]
    exact congrArg (nu t) (congrArg Subtype.val hi)
  exact MatrixFourGroupNormalizer.U_not_mem_X_zpowers F a A hfix x y hxy
    (Subgroup.mem_zpowers_iff.mpr ⟨i, Psi.injective hq⟩)

theorem rotation_inverted_by_s (d : K s) (hd2 : d ^ 2 = tInK s)
    (hconj : (d : C t) * s * (d : C t)⁻¹ = tInC t * s) :
    sInK s * d * (sInK s)⁻¹ = d⁻¹ := by
  have h : d * sInK s * d⁻¹ = d ^ 2 * sInK s := by
    rw [hd2]
    exact Subtype.ext hconj
  have h1 : sInK s * d⁻¹ = d * sInK s := by
    calc
      sInK s * d⁻¹ = d⁻¹ * (d * sInK s * d⁻¹) := by group
      _ = d⁻¹ * (d ^ 2 * sInK s) := by rw [h]
      _ = d * sInK s := by group
  calc
    sInK s * d * (sInK s)⁻¹ =
        d⁻¹ * (d * sInK s) * d * (sInK s)⁻¹ := by group
    _ = d⁻¹ * (sInK s * d⁻¹) * d * (sInK s)⁻¹ := by rw [← h1]
    _ = d⁻¹ := by group

theorem actual_dihedral_lift [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    ∃ d : K s, orderOf d = 4 ∧ d ^ 2 = tInK s ∧
      (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
      nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) ∧
      Nonempty (MatrixFourGroupNormalizer.generatedDihedral d (sInK s) ≃* DihedralGroup 4) ∧
      Nat.card (MatrixFourGroupNormalizer.generatedDihedral d (sInK s)) = 8 := by
  obtain ⟨d, hd, hd2, hconj, himage⟩ :=
    actual_original_X_lift F a A hfix s Psi ht hs hst hz hu hF x y hxy
  have hs2 : sInK s ^ 2 = 1 := by
    apply Subtype.ext
    exact hs ▸ pow_orderOf_eq_one s
  have he := MatrixFourGroupNormalizer.generatedDihedral_equiv d (sInK s) hd hs2
    (rotation_inverted_by_s s d hd2 hconj)
    (original_s_not_mem_rotation F a A hfix s Psi hu x y hxy d himage)
  refine ⟨d, hd, hd2, hconj, himage, he, ?_⟩
  obtain ⟨e⟩ := he
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem actual_K_card [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Nat.card (K s) =
      4 * Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (Nat.card F) := by
  rw [← (N0InK s).card_mul_index, (N0InK s).index_eq_card,
    Nat.card_congr (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).toEquiv,
    N0InK_card ht s hs hst, MatrixFourGroupNormalizer.Normalizer_card F a A hfix hF ha x y hxy]
  ring

theorem original_actual_D_card [Finite G] [Finite F]
    (hs : orderOf s = 2)
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (D s) = 2 * Nat.card (N0 s) * Nat.card A *
      MatrixTorus.torusSize (Nat.card F) := by
  have hcard := (KleinFourOddKernel.onCentralizer (N t) s).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    (KleinFourOddKernel.onCentralizer_surjective (N t)
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) s hs),
    Subgroup.card_top, KleinFourOddKernel.onCentralizer_ker] at hcard
  have hN0 : Nat.card (KleinFourOddKernel.centralizerKernel (N t) s) =
      Nat.card (N0 s) :=
    Nat.card_congr (intersectionSwapEquiv (N t) (D s)).toEquiv
  have hquot : Nat.card (Subgroup.centralizer {nu t s}) =
      2 * Nat.card A * MatrixTorus.torusSize (Nat.card F) :=
    (Nat.card_congr (centralizerEquiv Psi (MatrixTorus.originalU F a A hfix)
      (nu t s) hu).toEquiv).symm.trans
        (original_centralizer_card F A a hfix hF ha)
  rw [hN0, hquot] at hcard
  change _ = Nat.card (D s) at hcard
  rw [← hcard]
  ring

theorem actual_K_card_twice_D [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Nat.card (K s) = 2 * Nat.card (D s) := by
  rw [actual_K_card F a A hfix s Psi ht hs hst hz hu hF ha x y hxy,
    original_actual_D_card F a A hfix s Psi hs hu hF ha]
  ring

theorem actual_dihedral_sylow [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ∃ d : K s, orderOf d = 4 ∧ d ^ 2 = tInK s ∧
      (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
      nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) ∧
      Nonempty (MatrixFourGroupNormalizer.generatedDihedral d (sInK s) ≃* DihedralGroup 4) ∧
      Nat.card (MatrixFourGroupNormalizer.generatedDihedral d (sInK s)) = 8 ∧
      ∃ P : Sylow 2 (K s), (P : Subgroup (K s)) =
        MatrixFourGroupNormalizer.generatedDihedral d (sInK s) := by
  obtain ⟨d, hd, hd2, hconj, himage, he, hcard⟩ :=
    actual_dihedral_lift F a A hfix s Psi ht hs hst hz hu hF x y hxy
  refine ⟨d, hd, hd2, hconj, himage, he, hcard, ?_⟩
  apply MatrixFourGroupNormalizer.sylow_two_of_card_eight _
    (Nat.card (N0 s) * Nat.card A * (MatrixTorus.torusSize (Nat.card F) / 2)) hcard
  · rw [actual_K_card F a A hfix s Psi ht hs hst hz hu hF ha x y hxy]
    nth_rw 1 [MatrixTorus.torusSize_two_mul_half hF]
    ring
  · have hN0 : Odd (Nat.card (N0 s)) := by
      rw [← N0InK_card ht s hs hst]
      exact N0InK_odd s
    exact (hN0.mul hA).mul (MatrixTorus.torusSize_half_odd hF)

end OriginalModel

abbrev N0InD {t : G} (s : C t) := (N t).subgroupOf (D s)

instance N0InD_normal {t : G} (s : C t) : (N0InD s).Normal := inferInstance

@[expose] def DQuotientInclusion {t : G} (s : C t) :
    D s ⧸ N0InD s →* K s ⧸ N0InK s :=
  QuotientGroup.quotientMapSubgroupOfOfLe (A' := N t) (B' := N t) le_rfl (D_le_K s)

theorem DQuotientInclusion_mk {t : G} (s : C t) (d : D s) :
    DQuotientInclusion s (QuotientGroup.mk' (N0InD s) d) =
      QuotientGroup.mk' (N0InK s) (DToK s d) := rfl

theorem DQuotientInclusion_injective {t : G} (s : C t) :
    Function.Injective (DQuotientInclusion s) := by
  let f := (QuotientGroup.mk' (N0InK s)).comp (DToK s)
  have hf : N0InD s ≤ f.ker := fun _ h => (QuotientGroup.eq_one_iff _).mpr h
  change Function.Injective (QuotientGroup.lift (N0InD s) f hf)
  apply (QuotientGroup.injective_lift_iff _ _ hf).mpr
  ext d
  change (d : C t) ∈ N t ↔ QuotientGroup.mk' (N0InK s) (DToK s d) = 1
  exact (QuotientGroup.eq_one_iff (N := N0InK s) (DToK s d)).symm

theorem DQuotientInclusion_range {t : G} (s : C t) :
    (DQuotientInclusion s).range = DInNormalizerQuotient s := by
  have hc : (DQuotientInclusion s).comp (QuotientGroup.mk' (N0InD s)) =
      (QuotientGroup.mk' (N0InK s)).comp (DToK s) := rfl
  have h := MonoidHom.range_comp (DQuotientInclusion s)
    (QuotientGroup.mk' (N0InD s))
  rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    Subgroup.map_top, hc, MonoidHom.range_comp] at h
  have hi : (DToK s).range = DInK s := by
    ext k
    constructor
    · rintro ⟨d, rfl⟩
      exact d.property
    · intro hk
      exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩
  exact h.symm.trans (congrArg (Subgroup.map (QuotientGroup.mk' (N0InK s))) hi)

@[expose] def RQuotientInclusion {t : G} (s : C t) :
    R s ⧸ N0InR s →* K s ⧸ N0InK s :=
  QuotientGroup.map (N0InR s) (N0InK s)
    ((DToK s).comp (R s).subtype) (fun _ h => h)

theorem RQuotientInclusion_mk {t : G} (s : C t) (r : R s) :
    RQuotientInclusion s (QuotientGroup.mk' (N0InR s) r) =
      QuotientGroup.mk' (N0InK s) (DToK s r) := rfl

theorem RQuotientInclusion_injective {t : G} (s : C t) :
    Function.Injective (RQuotientInclusion s) := by
  let f := (QuotientGroup.mk' (N0InK s)).comp ((DToK s).comp (R s).subtype)
  have hf : N0InR s ≤ f.ker := fun _ h => (QuotientGroup.eq_one_iff _).mpr h
  change Function.Injective (QuotientGroup.lift (N0InR s) f hf)
  apply (QuotientGroup.injective_lift_iff _ _ hf).mpr
  ext r
  change ((r : D s) : C t) ∈ N t ↔
    QuotientGroup.mk' (N0InK s) (DToK s r) = 1
  exact (QuotientGroup.eq_one_iff (N := N0InK s) (DToK s r)).symm

theorem RQuotientInclusion_range {t : G} (s : C t) :
    (RQuotientInclusion s).range = RInNormalizerQuotient s := by
  have hc : (RQuotientInclusion s).comp (QuotientGroup.mk' (N0InR s)) =
      (QuotientGroup.mk' (N0InK s)).comp ((DToK s).comp (R s).subtype) := rfl
  have h := MonoidHom.range_comp (RQuotientInclusion s)
    (QuotientGroup.mk' (N0InR s))
  have hs : (QuotientGroup.mk' (N0InR s)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hleft : ((RQuotientInclusion s).comp (QuotientGroup.mk' (N0InR s))).range =
      (RQuotientInclusion s).range :=
    h.trans ((congrArg (Subgroup.map (RQuotientInclusion s)) hs).trans
      (Subgroup.map_top _))
  have hright := MonoidHom.range_comp (QuotientGroup.mk' (N0InK s))
    ((DToK s).comp (R s).subtype)
  have hi : ((DToK s).comp (R s).subtype).range = RInK s :=
    (MonoidHom.range_comp (DToK s) (R s).subtype).trans
      (congrArg (Subgroup.map (DToK s)) (Subgroup.range_subtype (R s)))
  exact hleft.symm.trans ((congrArg MonoidHom.range hc).trans
    (hright.trans (congrArg (Subgroup.map (QuotientGroup.mk' (N0InK s))) hi)))

@[expose] def DQuotientImageEquiv {t : G} (s : C t) :
    D s ⧸ N0InD s ≃* DInNormalizerQuotient s :=
  (MulEquiv.ofBijective (DQuotientInclusion s).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (DQuotientInclusion_injective s),
      MonoidHom.rangeRestrict_surjective _⟩).trans
        (MulEquiv.subgroupCongr (DQuotientInclusion_range s))

theorem DQuotientImageEquiv_mk {t : G} (s : C t) (d : D s) :
    (DQuotientImageEquiv s (QuotientGroup.mk' (N0InD s) d) : K s ⧸ N0InK s) =
      QuotientGroup.mk' (N0InK s) (DToK s d) := rfl

@[expose] def RQuotientImageEquiv {t : G} (s : C t) :
    R s ⧸ N0InR s ≃* RInNormalizerQuotient s :=
  (MulEquiv.ofBijective (RQuotientInclusion s).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (RQuotientInclusion_injective s),
      MonoidHom.rangeRestrict_surjective _⟩).trans
        (MulEquiv.subgroupCongr (RQuotientInclusion_range s))

theorem RQuotientImageEquiv_mk {t : G} (s : C t) (r : R s) :
    (RQuotientImageEquiv s (QuotientGroup.mk' (N0InR s) r) : K s ⧸ N0InK s) =
      QuotientGroup.mk' (N0InK s) (DToK s r) := rfl

section ModelEmbeddings
variable (F : Type v) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
variable (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
variable {t : G} (s : C t) (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)

@[expose] def modelCentralizerProductEquiv [Finite F]
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    MatrixTorus.originalV0 F a A hfix × OriginalWProduct F A a hfix ≃*
      ModelCentralizer F a A hfix :=
  ((MulEquiv.refl _).prodCongr (originalOddCoordinateEquiv F a A hfix)).trans
    (modelCentralizerDirectEquiv F a A hfix hF ha)

theorem modelCentralizerProductEquiv_value [Finite F]
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (v : MatrixTorus.originalV0 F a A hfix) (w : OriginalWProduct F A a hfix) :
    ((modelCentralizerProductEquiv F a A hfix hF ha (v, w) :
      MatrixFourGroupNormalizer.Normalizer F a A hfix) : MatrixTorus.OriginalH F a A hfix) =
        (v : MatrixTorus.OriginalH F a A hfix) * originalOddInclusion F A a hfix w :=
  modelCentralizerDirectEquiv_value F a A hfix hF ha v
    (originalOddCoordinateEquiv F a A hfix w)

@[expose] def actualDModelEquiv [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    D s ⧸ N0InD s ≃* ModelCentralizer F a A hfix :=
  (DQuotientImageEquiv s).trans
    (((actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu).subgroupMap
      (DInNormalizerQuotient s)).trans (MulEquiv.subgroupCongr
        (actualModelNormalizerEquiv_D_image F a A hfix s Psi ht hs hst hz hu)))

theorem actualDModelEquiv_mk [Finite G]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s) (d : D s) :
    ((actualDModelEquiv F a A hfix s Psi ht hs hst hz hu
      (QuotientGroup.mk' (N0InD s) d) : MatrixFourGroupNormalizer.Normalizer F a A hfix) :
        MatrixTorus.OriginalH F a A hfix) = Psi.symm (nu t (d : C t)) := rfl

@[expose] def actualDProductEquiv [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    D s ⧸ N0InD s ≃* MatrixTorus.originalV0 F a A hfix × OriginalWProduct F A a hfix :=
  (actualDModelEquiv F a A hfix s Psi ht hs hst hz hu).trans
    (modelCentralizerProductEquiv F a A hfix hF ha).symm

theorem actualDProductEquiv_mk [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (d : D s) :
    let p := actualDProductEquiv F a A hfix s Psi ht hs hst hz hu hF ha
      (QuotientGroup.mk' (N0InD s) d)
    Psi ((p.1 : MatrixTorus.OriginalH F a A hfix) * originalOddInclusion F A a hfix p.2) =
      nu t (d : C t) := by
  dsimp only
  rw [← modelCentralizerProductEquiv_value F a A hfix hF ha]
  change Psi ((modelCentralizerProductEquiv F a A hfix hF ha)
    ((modelCentralizerProductEquiv F a A hfix hF ha).symm
      (actualDModelEquiv F a A hfix s Psi ht hs hst hz hu
        (QuotientGroup.mk' (N0InD s) d)))) = _
  rw [MulEquiv.apply_symm_apply, actualDModelEquiv_mk, MulEquiv.apply_symm_apply]

theorem RQuotientInclusion_model [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (q : R s ⧸ N0InR s) :
    (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu
      (RQuotientInclusion s q) : MatrixTorus.OriginalH F a A hfix) =
      originalOddInclusion F A a hfix
        (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA q) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N0InR s) q
  apply Psi.injective
  calc
    Psi (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu
      (RQuotientInclusion s (QuotientGroup.mk' (N0InR s) r))) =
        Psi (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu
          (QuotientGroup.mk' (N0InK s) (DToK s r))) :=
      congrArg (fun q => Psi (actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu q))
        (RQuotientInclusion_mk s r)
    _ = nu t ((r : D s) : C t) :=
      (congrArg Psi (actualModelNormalizerEquiv_mk F a A hfix s Psi ht hs hst hz hu
        (DToK s r))).trans (Psi.apply_symm_apply _)
    _ = Psi (originalOddInclusion F A a hfix
        (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA
          (QuotientGroup.mk' (N0InR s) r))) :=
      (actualOddProductEquiv_mk F a A hfix s Psi ht hs hst hu hF ha hA r).symm

theorem RQuotientInclusion_originalMap [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (q : R s ⧸ N0InR s) :
    quotientToOriginalModel F a A hfix s Psi (RQuotientInclusion s q) =
      originalOddInclusion F A a hfix
        (actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA q) :=
  (actualModelNormalizerEquiv_value F a A hfix s Psi ht hs hst hz hu _).symm.trans
    (RQuotientInclusion_model F a A hfix s Psi ht hs hst hz hu hF ha hA q)

theorem actual_K_card_signed [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    (Nat.card (K s) : ℤ) = 4 * Nat.card (N0 s) * Nat.card A *
      ((Nat.card F : ℤ) + torusSign (Nat.card F)) := by
  rw [actual_K_card F a A hfix s Psi ht hs hst hz hu hF ha x y hxy]
  push_cast
  rw [MatrixFourGroupNormalizer.torusSize_eq_signed hF]
  rfl

structure OriginalNormalizerData [Finite G] [Finite F]
    (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) : Prop where
  kernel_normal : (N0InK s).Normal
  kernel_original : (N0InK s).map (K s).subtype = N t ⊓ D s
  kernel_equiv : ∃ e : N0 s ≃* N0InK s, ∀ k, (e k).val.val = k.val.val
  D_embedding : Function.Injective (DQuotientInclusion s) ∧
    (DQuotientInclusion s).range = DInNormalizerQuotient s
  R_embedding : Function.Injective (RQuotientInclusion s) ∧
    (RQuotientInclusion s).range = RInNormalizerQuotient s
  quotient_normalizer : (K s).map (nu t) =
    Subgroup.normalizer ((V s).map (nu t) : Set (H t))
  model_quotient : ∃ e : K s ⧸ N0InK s ≃* MatrixFourGroupNormalizer.Normalizer F a A hfix,
    (∀ k : K s, (e (QuotientGroup.mk' (N0InK s) k) : MatrixTorus.OriginalH F a A hfix) =
      Psi.symm (nu t (k : C t))) ∧
    (∀ q : K s ⧸ N0InK s, (e q : MatrixTorus.OriginalH F a A hfix) =
      quotientToOriginalModel F a A hfix s Psi q) ∧
    (DInNormalizerQuotient s).map e.toMonoidHom = ModelCentralizer F a A hfix ∧
    (RInNormalizerQuotient s).map e.toMonoidHom = ModelOdd F a A hfix
  product_quotient : ∃ e : K s ⧸ N0InK s ≃* ModelNormalProduct F a A hfix x y hxy,
    ∀ k : K s,
      let p := e (QuotientGroup.mk' (N0InK s) k)
      Psi (MatrixFourGroupNormalizer.WInH F a A hfix p.left * p.right.1.val *
        MatrixTorus.originalFieldInH F a A hfix p.right.2) = nu t (k : C t)
  dihedral_model : Nonempty (MatrixFourGroupNormalizer.S0 F a A hfix x y hxy ≃* DihedralGroup 4)
  dihedral_model_card : Nat.card (MatrixFourGroupNormalizer.S0 F a A hfix x y hxy) = 8
  D_quotient : ∃ e : D s ⧸ N0InD s ≃*
    MatrixTorus.originalV0 F a A hfix × OriginalWProduct F A a hfix,
    ∀ d : D s,
      let p := e (QuotientGroup.mk' (N0InD s) d)
      Psi ((p.1 : MatrixTorus.OriginalH F a A hfix) * originalOddInclusion F A a hfix p.2) =
        nu t (d : C t)
  R_normal : (RInK s).Normal
  actual_lift_and_action : ∃ d : K s, orderOf d = 4 ∧ d ^ 2 = tInK s ∧
    (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
    nu t (d : C t) = Psi (MatrixFourGroupNormalizer.X F a A hfix x y hxy) ∧
    Nonempty (MatrixFourGroupNormalizer.generatedDihedral d (sInK s) ≃* DihedralGroup 4) ∧
    Nat.card (MatrixFourGroupNormalizer.generatedDihedral d (sInK s)) = 8 ∧
    (∃ P : Sylow 2 (K s), (P : Subgroup (K s)) =
      MatrixFourGroupNormalizer.generatedDihedral d (sInK s)) ∧
    ∃ e : R s ⧸ N0InR s ≃* OriginalWProduct F A a hfix,
      (∀ r : R s, Psi (originalOddInclusion F A a hfix
        (e (QuotientGroup.mk' (N0InR s) r))) = nu t ((r : D s) : C t)) ∧
      (∀ q : R s ⧸ N0InR s,
        quotientToOriginalModel F a A hfix s Psi (RQuotientInclusion s q) =
          originalOddInclusion F A a hfix (e q)) ∧
      (∀ w : MatrixTorus.W F a,
        e (conjugationOnOddQuotient s d (e.symm (SemidirectProduct.inl w))) =
          SemidirectProduct.inl w⁻¹) ∧
      (∀ sigma : A,
        e (conjugationOnOddQuotient s d (e.symm (SemidirectProduct.inr sigma))) =
          SemidirectProduct.inr sigma)
  K_card : Nat.card (K s) = 4 * Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (Nat.card F)
  K_card_signed : (Nat.card (K s) : ℤ) = 4 * Nat.card (N0 s) * Nat.card A *
    ((Nat.card F : ℤ) + torusSign (Nat.card F))
  twice_D_card : Nat.card (K s) = 2 * Nat.card (D s)

theorem original_normalizer_data [Finite G] [Finite F]
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hz : Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t))
    (hu : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (x y : MatrixCover.FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    OriginalNormalizerData F a A hfix s Psi x y hxy := by
  refine
    { kernel_normal := inferInstance
      kernel_original := N0InK_map_ambient ht s hs hst
      kernel_equiv := ⟨N0EquivK ht s hs hst, N0EquivK_value ht s hs hst⟩
      D_embedding := ⟨DQuotientInclusion_injective s, DQuotientInclusion_range s⟩
      R_embedding := ⟨RQuotientInclusion_injective s, RQuotientInclusion_range s⟩
      quotient_normalizer := actual_normalizer_image ht s hs hst
      model_quotient := ⟨actualModelNormalizerEquiv F a A hfix s Psi ht hs hst hz hu,
        actualModelNormalizerEquiv_mk F a A hfix s Psi ht hs hst hz hu,
        actualModelNormalizerEquiv_value F a A hfix s Psi ht hs hst hz hu,
        actualModelNormalizerEquiv_D_image F a A hfix s Psi ht hs hst hz hu,
        actualModelNormalizerEquiv_R_image F a A hfix s Psi ht hs hst hz hu hF ha hA⟩
      product_quotient := ⟨actualNormalizerProductEquiv F a A hfix s Psi ht hs hst hz hu hF ha x y hxy,
        actualNormalizerProductEquiv_mk F a A hfix s Psi ht hs hst hz hu hF ha x y hxy⟩
      dihedral_model := ⟨MatrixFourGroupNormalizer.S0Equiv F a A hfix hF x y hxy⟩
      dihedral_model_card := MatrixFourGroupNormalizer.S0_card F a A hfix hF x y hxy
      D_quotient := ⟨actualDProductEquiv F a A hfix s Psi ht hs hst hz hu hF ha,
        actualDProductEquiv_mk F a A hfix s Psi ht hs hst hz hu hF ha⟩
      R_normal := inferInstance
      actual_lift_and_action := ?_
      K_card := actual_K_card F a A hfix s Psi ht hs hst hz hu hF ha x y hxy
      K_card_signed := actual_K_card_signed F a A hfix s Psi ht hs hst hz hu hF ha x y hxy
      twice_D_card := actual_K_card_twice_D F a A hfix s Psi ht hs hst hz hu hF ha x y hxy }
  obtain ⟨d, hd, hd2, hc, hi, he, hcard, hP⟩ :=
    actual_dihedral_sylow F a A hfix s Psi ht hs hst hz hu hF ha hA x y hxy
  exact ⟨d, hd, hd2, hc, hi, he, hcard, hP,
    actualOddProductEquiv F a A hfix s Psi ht hs hst hu hF ha hA,
    actualOddProductEquiv_mk F a A hfix s Psi ht hs hst hu hF ha hA,
    RQuotientInclusion_originalMap F a A hfix s Psi ht hs hst hz hu hF ha hA,
    quotient_conjugation_inverts_W F a A hfix s Psi ht hs hst hu hF ha hA x y hxy d hi,
    quotient_conjugation_fixes_A F a A hfix s Psi ht hs hst hu hF ha hA x y hxy d hi⟩

end ModelEmbeddings


theorem actual_simple_layer_four_group_normalizer_action
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ((∃ s : C t, orderOf s = 2 ∧ s ≠ tInC t) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (a : (MatrixCover.FixedField F A)ˣ),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ Nat.card A ∣ f ∧
      Nat.card (MatrixCover.FixedField F A) = p ^ (f / Nat.card A) ∧
      Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A ∧
      (∀ x : (MatrixCover.FixedField F A)ˣ, x ∈ Subgroup.zpowers a) ∧
      ¬IsSquare a ∧ ¬IsSquare (MatrixCover.fixedUnit F A a) ∧
      (∀ (sigma : A) (x : MatrixCoverData.M F (MatrixCover.fixedUnit F A a)),
        MatrixTorus.originalFieldAction F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) sigma x =
            ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩) ∧
      (∀ sigma : A,
        MatrixTorus.originalFieldAction F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) sigma (MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) =
            MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) ∧
      OriginalTorusData F A (MatrixCover.fixedUnit F A a) (fixed_coefficient_action F A a) ∧
      ∀ (s : C t), orderOf s = 2 → s ≠ tInC t →
        ∃ Psi : MatrixTorus.OriginalH F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) ≃* H t,
          Psi (MatrixTorus.originalZ F (MatrixCover.fixedUnit F A a) A
            (fixed_coefficient_action F A a)) = nu t (tInC t) ∧
          Psi (MatrixTorus.originalU F (MatrixCover.fixedUnit F A a) A
            (fixed_coefficient_action F A a)) = nu t s ∧
          OriginalCentralizerData F A s p f (MatrixCover.fixedUnit F A a)
            (fixed_coefficient_action F A a) Psi ∧
          SignedOrderData F A s p f (MatrixCover.fixedUnit F A a) ∧
          (D s).map (C t).subtype = C t ⊓ Subgroup.centralizer {(s : G)} ∧
          (V s).map (C t).subtype = Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) ∧
          ∀ x : N t, x ∈ N0 s ↔ s * (x : C t) = (x : C t) * s) ∧
    ∀ (F : Type v) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) (a : Fˣ)
      (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
      (s : C t), orderOf s = 2 → s ≠ tInC t →
      ∀ (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t),
        Psi (MatrixTorus.originalZ F a A hfix) = nu t (tInC t) →
        Psi (MatrixTorus.originalU F a A hfix) = nu t s →
        Nat.card F = p ^ f → Odd (Nat.card A) → ¬IsSquare a →
        (∃ x y : MatrixCover.FixedField F A,
          (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) ∧
        ∀ (x y : MatrixCover.FixedField F A)
          (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1),
          OriginalNormalizerData F a A hfix s Psi x y hxy := by
  refine ⟨actual_simple_layer_four_group_centralizer_odd_core n hn S0 f0 hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel, ?_⟩
  intro F hfield hfinite A a hfix s hs hst Psi hz hu hcard hA ha
  have hF : Odd (Nat.card F) := hcard.symm ▸ hpodd.pow
  refine ⟨MatrixFourGroupNormalizer.original_fixed_pair_exists F a A hfix hF hA, ?_⟩
  intro x y hxy
  exact original_normalizer_data F a A hfix s Psi ht hs hst hz hu hF ha hA x y hxy

end CFSG.Semidihedral.ActualFourGroupNormalizer
