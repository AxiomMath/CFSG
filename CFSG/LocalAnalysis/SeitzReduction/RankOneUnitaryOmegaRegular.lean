module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaCartan
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmega

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

section QuotConj

variable {G : Type*} [Group G] {R K : Subgroup G}

theorem map_normalizerMonoidHom_subgroupOf {y : normalizer (R : Set G)}
    (hy : (y : G) ∈ normalizer (K : Set G)) :
    (K.subgroupOf R).map (R.normalizerMonoidHom y : R →* R) = K.subgroupOf R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ K := hz
    show (y : G) * z * (y : G)⁻¹ ∈ K
    exact (mem_normalizer_iff.mp hy z).mp hz'
  · intro hx
    rw [mem_subgroupOf] at hx
    refine ⟨⟨(y : G)⁻¹ * x * y, (mem_normalizer_iff''.mp y.2 x).mp x.2⟩,
      mem_subgroupOf.mpr ((mem_normalizer_iff''.mp hy x).mp hx), Subtype.ext ?_⟩
    change (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ = x
    group

variable [(K.subgroupOf R).Normal]

@[expose] noncomputable def quotConj (Y : Subgroup G) (hYR : Y ≤ normalizer (R : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) : Y →* MulAut (R ⧸ K.subgroupOf R) where
  toFun y := QuotientGroup.congr (K.subgroupOf R) (K.subgroupOf R)
    (R.normalizerMonoidHom ⟨y, hYR y.2⟩) (map_normalizerMonoidHom_subgroupOf (hYK y.2))
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [QuotientGroup.congr_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change ((1 : Y) : G) * x * ((1 : Y) : G)⁻¹ = x
    simp
  map_mul' y y' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    change ((y * y' : Y) : G) * x * ((y * y' : Y) : G)⁻¹ =
      (y : G) * ((y' : G) * x * (y' : G)⁻¹) * (y : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

theorem quotConj_mk (Y : Subgroup G) (hYR : Y ≤ normalizer (R : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) (y : Y) (x : R) :
    quotConj Y hYR hYK y (x : R ⧸ K.subgroupOf R) =
      ((⟨(y : G) * x * (y : G)⁻¹, (mem_normalizer_iff.mp (hYR y.2) x).mp x.2⟩ : R) :
        R ⧸ K.subgroupOf R) :=
  rfl

end QuotConj

section OmegaAction

variable {G : Type*} [Group G] {L T R₂ : Subgroup G} {t : G}

theorem map_conj_mem_u3Omega {y : G}
    (hy : y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) {X : Subgroup G}
    (hX : X ∈ u3Omega L T R₂ t) : X.map (MulAut.conj y).toMonoidHom ∈ u3Omega L T R₂ t := by
  obtain ⟨y₀, hy₀, rfl⟩ := hX
  refine ⟨y * y₀, mul_mem hy hy₀, ?_⟩
  rw [Subgroup.map_map, map_mul]
  rfl

variable (L T R₂ t) in
@[expose] noncomputable def u3OmegaAction :
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) →*
      Equiv.Perm (u3Omega L T R₂ t) where
  toFun y :=
    { toFun := fun X => ⟨X.1.map (MulAut.conj (y : G)).toMonoidHom, map_conj_mem_u3Omega y.2 X.2⟩
      invFun := fun X => ⟨X.1.map (MulAut.conj (y : G)⁻¹).toMonoidHom,
        map_conj_mem_u3Omega (inv_mem y.2) X.2⟩
      left_inv := fun X => Subtype.ext (by
        change (X.1.map (MulAut.conj (y : G)).toMonoidHom).map
          (MulAut.conj (y : G)⁻¹).toMonoidHom = X.1
        rw [Subgroup.map_map]
        convert Subgroup.map_id X.1
        ext x
        simp [MulAut.conj_apply, mul_assoc])
      right_inv := fun X => Subtype.ext (by
        change (X.1.map (MulAut.conj (y : G)⁻¹).toMonoidHom).map
          (MulAut.conj (y : G)).toMonoidHom = X.1
        rw [Subgroup.map_map]
        convert Subgroup.map_id X.1
        ext x
        simp [MulAut.conj_apply, mul_assoc]) }
  map_one' := by
    refine Equiv.ext fun X => Subtype.ext ?_
    change X.1.map (MulAut.conj (1 : G)).toMonoidHom = X.1
    convert Subgroup.map_id X.1
    ext x
    simp
  map_mul' y y' := by
    refine Equiv.ext fun X => Subtype.ext ?_
    change X.1.map (MulAut.conj ((y : G) * (y' : G))).toMonoidHom =
      (X.1.map (MulAut.conj (y' : G)).toMonoidHom).map (MulAut.conj (y : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

theorem u3OmegaAction_apply
    (y : normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G))
    (X : u3Omega L T R₂ t) :
    ((u3OmegaAction L T R₂ t y X : u3Omega L T R₂ t) : Subgroup G) =
      (X : Subgroup G).map (MulAut.conj (y : G)).toMonoidHom :=
  rfl

end OmegaAction

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_cartan_data_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ D : Subgroup G, IsCyclic D ∧ D ≤ L ⊓ normalizer (szT₁ L T : Set G) ∧
      (∀ b ∈ L ⊓ normalizer (szT₁ L T : Set G), ∃ p ∈ szT₁ L T, ∃ d ∈ D, b = p * d) ∧
      (∀ d ∈ D, d ≠ 1 → ∀ x ∈ szT₁ L T, d * x * d⁻¹ * x⁻¹ ∈ szA₁ (szT₁ L T) →
        x ∈ szA₁ (szT₁ L T)) ∧
      (Even f → ∀ w ∈ szT₁ L T, w ∉ szA₁ (szT₁ L T) → ∀ w' ∈ szT₁ L T,
        w' ∉ szA₁ (szT₁ L T) → ∃ d ∈ D, (d * w * d⁻¹)⁻¹ * w' ∈ szA₁ (szT₁ L T)) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hT₁L : szT₁ L T ≤ L := szT₁_le_right L T
  have hcart : ∀ d ∈ cartan (Q : Subgroup L) t₀,
      ((d : L) : G) ∈ L ⊓ normalizer (szT₁ L T : Set G) :=
    fun d hd => mem_inf.mpr ⟨d.2, (mem_borel_iff_mem_normalizer hmemQ hT₁L d).mp
      (cartan_le_borel _ _ hd)⟩
  refine ⟨(cartan (Q : Subgroup L) t₀).map L.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · have := hc.isCyclic
    exact isCyclic_of_surjective ((cartan (Q : Subgroup L) t₀).equivMapOfInjective L.subtype
      L.subtype_injective).toMonoidHom (MulEquiv.surjective _)
  · rintro _ ⟨d, hd, rfl⟩
    exact hcart d hd
  · intro b hb
    obtain ⟨hbL, hbT⟩ := mem_inf.mp hb
    have hbB : (⟨b, hbL⟩ : L) ∈ borel (Q : Subgroup L) :=
      (mem_borel_iff_mem_normalizer hmemQ hT₁L _).mpr hbT
    rw [← hc.sup_eq] at hbB
    have hbB' : (⟨b, hbL⟩ : L) ∈
        ((Q : Subgroup L) : Set L) * (cartan (Q : Subgroup L) t₀ : Set L) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (cartan_le_borel _ _)]
      exact hbB
    obtain ⟨p, hp, d, hd, hpd⟩ := Set.mem_mul.mp hbB'
    refine ⟨p, (hmemQ p).mp hp, d, ⟨d, hd, rfl⟩, ?_⟩
    have := congrArg Subtype.val hpd
    simpa using this.symm
  · rintro _ ⟨d, hd, rfl⟩ hd1 x hx hdx
    have hxL : x ∈ L := hT₁L hx
    have hd1' : d ≠ 1 := fun h1 => hd1 (by rw [h1]; rfl)
    have := hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hd hd1' ((hmemQ ⟨x, hxL⟩).mpr hx)
      ((hmemZ _).mpr (by simpa using hdx))
    exact (hmemZ _).mp this
  · intro heven w hw hwA w' hw' hw'A
    have hwL : w ∈ L := hT₁L hw
    have hwL' : w' ∈ L := hT₁L hw'
    obtain ⟨d, hd, hdd⟩ := BenderType.exists_cartan_conj_quot_of_even hB heven Q hc
      ((hmemQ ⟨w, hwL⟩).mpr hw) (fun h1 => hwA ((hmemZ _).mp h1))
      ((hmemQ ⟨w', hwL'⟩).mpr hw') (fun h1 => hw'A ((hmemZ _).mp h1))
    refine ⟨d, ⟨d, hd, rfl⟩, ?_⟩
    have := (hmemZ _).mp hdd
    simpa using this

theorem normal_subgroupOf_szR {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    (R₂.subgroupOf (szR (szT₁ L T) R₂ t)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_szR_mid _ _ _)).mpr
    (sup_le (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer)
      (zpowers_le.mpr hR.t_mem_normalizer))

theorem normalizer_sup_le_normalizer_szA₁_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ≤
      normalizer (szA₁ (szT₁ L T) : Set G) := by
  intro x hxH
  rw [h.szA₁_eq_commutator_sup_of_card_sylow hS2 hR]
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun a ha => ?_
  have hle : ⁅szT₁ L T ⊔ R₂, szT₁ L T ⊔ R₂⁆ ≤
      ⁅szT₁ L T ⊔ R₂, szT₁ L T ⊔ R₂⁆.comap (MulAut.conj x⁻¹).toMonoidHom := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : x⁻¹ * ⁅g₁, g₂⁆ * x = ⁅x⁻¹ * g₁ * x, x⁻¹ * g₂ * x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator ((mem_normalizer_iff''.mp hxH _).mp hg₁)
      ((mem_normalizer_iff''.mp hxH _).mp hg₂)
  have := hle ha
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

end U3Start

end CFSG.SeitzReduction.RankOne
