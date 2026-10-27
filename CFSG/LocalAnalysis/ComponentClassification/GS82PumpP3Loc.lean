module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219D
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace FixedLoc

theorem nonempty_fusionZStar_equiv_of_surjective_quot {A B : Type*} [Group A] [Group B]
    (hA : CFSG.IsQuasisimple (A ⧸ pPrimeCore 2 A)) (hB : CFSG.IsQuasisimple (B ⧸ pPrimeCore 2 B))
    (φ : B ⧸ pPrimeCore 2 B →* A ⧸ pPrimeCore 2 A) (hφ : Function.Surjective φ) :
    Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) := by
  have hker : φ.ker ≤ center (B ⧸ pPrimeCore 2 B) := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hB φ.normal_ker with h | h
    · exfalso
      have h1 : ∀ y : A ⧸ pPrimeCore 2 A, y = 1 := fun y => by
        obtain ⟨x, rfl⟩ := hφ y
        exact φ.mem_ker.mp (h ▸ mem_top x)
      obtain ⟨-, -, a, b, hab⟩ := hA
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (by rw [h1 a, h1 b])
    · exact h
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hB φ hφ hker
  obtain ⟨eA⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar A
  obtain ⟨eB⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar B
  exact ⟨eA.symm.trans (e.symm.trans eB)⟩

variable {X : Type} [Group X] (β : MulAut X)

abbrev Ext : Type := X ⋊[(zpowers β).subtype] ↥(zpowers β)

instance [Finite X] : Finite (Ext β) :=
  Finite.of_equiv (X × ↥(zpowers β)) (SemidirectProduct.equivProd (φ := (zpowers β).subtype)).symm

abbrev gen : Ext β := SemidirectProduct.inr ⟨β, mem_zpowers β⟩

theorem gen_mul_inl (x : X) :
    gen β * SemidirectProduct.inl x * (gen β)⁻¹ = (SemidirectProduct.inl (β x) : Ext β) := by
  have h := SemidirectProduct.inl_aut (φ := (zpowers β).subtype) ⟨β, mem_zpowers β⟩ x
  rw [map_inv] at h
  exact h.symm

theorem map_map_inl (H : Subgroup X) :
    (H.map β.toMonoidHom).map (SemidirectProduct.inl : X →* Ext β) =
      (H.map (SemidirectProduct.inl : X →* Ext β)).map (MulAut.conj (gen β)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (gen_mul_inl β x).symm

theorem gen_mul_gen (hβ : ∀ x, β (β x) = x) : gen β * gen β = 1 := by
  have h2 : (⟨β, mem_zpowers β⟩ : zpowers β) * ⟨β, mem_zpowers β⟩ = 1 :=
    Subtype.ext (MulEquiv.ext fun x => hβ x)
  change SemidirectProduct.inr _ * SemidirectProduct.inr _ = (1 : Ext β)
  rw [← map_mul, h2, map_one]

theorem gen_ne_one (hβ1 : β ≠ 1) : gen β ≠ 1 := by
  intro h
  have h' : (SemidirectProduct.inr (⟨β, mem_zpowers β⟩ : zpowers β) : Ext β) =
      SemidirectProduct.inr 1 := by
    rw [map_one]
    exact h
  exact hβ1 (congrArg Subtype.val (SemidirectProduct.inr_injective h'))

theorem orderOf_gen (hβ : ∀ x, β (β x) = x) (hβ1 : β ≠ 1) : orderOf (gen β) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact gen_mul_gen β hβ) (gen_ne_one β hβ1)

theorem map_inl_fixedSubgroup :
    (fixedSubgroup β).map (SemidirectProduct.inl : X →* Ext β) =
      (SemidirectProduct.inl : X →* Ext β).range ⊓ centralizer {gen β} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hx' : β x = x := hx
    have h := gen_mul_inl β x
    rw [hx'] at h
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h).symm
  · rintro ⟨⟨x, rfl⟩, hc⟩
    refine ⟨x, ?_, rfl⟩
    have h2 : gen β * SemidirectProduct.inl x * (gen β)⁻¹ = SemidirectProduct.inl x :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc).symm
    exact SemidirectProduct.inl_injective ((gen_mul_inl β x).symm.trans h2)

theorem normal_range_inl : (SemidirectProduct.inl : X →* Ext β).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem le_range_inl {K : Subgroup (Ext β)} (hK : ⁅K, K⁆ = K) :
    K ≤ (SemidirectProduct.inl : X →* Ext β).range := by
  rw [← hK, SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

variable [Finite X]

theorem isTwoComponentIn_map_inl {T : Subgroup X} (hTC : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) :
    HarrisLit.IsTwoComponentIn (T.map (SemidirectProduct.inl : X →* Ext β))
      (centralizer {gen β}) := by
  have hN := map_inl_fixedSubgroup β
  have hJN : T.map (SemidirectProduct.inl : X →* Ext β) ≤
      (fixedSubgroup β).map (SemidirectProduct.inl : X →* Ext β) := map_mono hTC
  have hNC : (fixedSubgroup β).map (SemidirectProduct.inl : X →* Ext β) ≤
      centralizer {gen β} := by
    rw [hN]
    exact inf_le_right
  rw [HarrisLit.isTwoComponentIn_iff (hJN.trans hNC)]
  have hNsub : (((fixedSubgroup β).map (SemidirectProduct.inl : X →* Ext β)).subgroupOf
      (centralizer {gen β})).IsSubnormal := by
    rw [hN, inf_subgroupOf_right]
    exact ((normal_range_inl β).subgroupOf _).isSubnormal
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJN hNC hNsub]
  let e := (fixedSubgroup β).equivMapOfInjective (SemidirectProduct.inl : X →* Ext β)
    SemidirectProduct.inl_injective
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hT
  have heq : (T.subgroupOf (fixedSubgroup β)).map e.toMonoidHom =
      (T.map (SemidirectProduct.inl : X →* Ext β)).subgroupOf
        ((fixedSubgroup β).map (SemidirectProduct.inl : X →* Ext β)) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc, hce⟩
      refine ⟨c, hc, ?_⟩
      have h1 := congrArg Subtype.val hce
      rwa [MulEquiv.coe_toMonoidHom, coe_equivMapOfInjective_apply] at h1
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hTC hx⟩, hx, Subtype.ext (coe_equivMapOfInjective_apply _ _ _ _)⟩
  rwa [heq] at h

private noncomputable def comapEquiv {K : Subgroup (Ext β)}
    (hKX : K ≤ (SemidirectProduct.inl : X →* Ext β).range) :
    ↥(K.comap (SemidirectProduct.inl : X →* Ext β)) ≃* ↥K :=
  ((K.comap (SemidirectProduct.inl : X →* Ext β)).equivMapOfInjective _
    SemidirectProduct.inl_injective).trans (MulEquiv.subgroupCongr (map_comap_eq_self hKX))

theorem isPComponent_comap_inl {K : Subgroup (Ext β)} (hK : HarrisLit.IsTwoComponent K)
    (hKX : K ≤ (SemidirectProduct.inl : X →* Ext β).range) :
    IsPComponent 2 (K.comap (SemidirectProduct.inl : X →* Ext β)) := by
  rw [← HarrisLit.isTwoComponent_iff_isPComponent]
  exact ⟨hK.1.comap _, HarrisLit.isTwoQuasisimple_of_mulEquiv (comapEquiv β hKX).symm hK.2⟩

theorem card_pPrimeCore_quotient_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ pPrimeCore 2 A) = Nat.card (B ⧸ pPrimeCore 2 B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).toEquiv

end FixedLoc

open FixedLoc

theorem fixedTwoComponentLocation_holds : FixedTwoComponentLocation := by
  intro X _ _ β hβ T hTC hT
  by_cases hβ1 : β = 1
  · subst hβ1
    refine ⟨T, ?_, Or.inl ⟨?_, le_rfl⟩⟩
    · have htop : fixedSubgroup (1 : MulAut X) = ⊤ := by
        ext x
        exact ⟨fun _ => mem_top x, fun _ => rfl⟩
      rw [htop, CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T ⊤ le_top] at hT
      exact (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 T).2
        ⟨Subgroup.IsSubnormal.trans le_top hT.1 Subgroup.IsSubnormal.top, hT.2⟩
    · have h1 : (1 : MulAut X).toMonoidHom = MonoidHom.id X := MonoidHom.ext fun _ => rfl
      rw [h1, Subgroup.map_id]
  have ht := orderOf_gen β hβ hβ1
  have hJ := isTwoComponentIn_map_inl β hTC hT
  have h219 := HarrisLit.harris82Lemma219Input_holds (Ext β) (gen β) ht
  obtain ⟨K, hK, hcases, -⟩ := h219.2 _ hJ
  have hKX : K ≤ (SemidirectProduct.inl : X →* Ext β).range :=
    le_range_inl β (Subgroup.isPerfect_iff.mp hK.2.1)
  have hX₁K : (K.comap (SemidirectProduct.inl : X →* Ext β)).map
      (SemidirectProduct.inl : X →* Ext β) = K := map_comap_eq_self hKX
  have hinv : (K.comap (SemidirectProduct.inl : X →* Ext β)).map β.toMonoidHom =
      K.comap (SemidirectProduct.inl : X →* Ext β) ↔
      K.map (MulAut.conj (gen β)).toMonoidHom = K := by
    rw [← (Subgroup.map_injective
      (SemidirectProduct.inl_injective (φ := (zpowers β).subtype))).eq_iff,
      map_map_inl, hX₁K]
  refine ⟨K.comap SemidirectProduct.inl, isPComponent_comap_inl β hK hKX, ?_⟩
  rcases hcases with ⟨hKt, hJK⟩ | ⟨hKt, hJeq⟩
  · exact Or.inl ⟨hinv.mpr hKt, map_le_iff_le_comap.mp (hJK.1.trans inf_le_left)⟩
  · refine Or.inr ⟨fun h => hKt (hinv.mp h), ?_⟩
    have hφ : ∃ φ : ↥K ⧸ pPrimeCore 2 ↥K →*
        ↥(T.map (SemidirectProduct.inl : X →* Ext β)) ⧸
          pPrimeCore 2 ↥(T.map (SemidirectProduct.inl : X →* Ext β)),
        Function.Surjective φ := by
      obtain ⟨-, -, hφ⟩ := (h219.1 K hK).2 hKt
      rw [hJeq]
      exact hφ
    obtain ⟨φ, hφ⟩ := hφ
    let eT := T.equivMapOfInjective (SemidirectProduct.inl : X →* Ext β)
      SemidirectProduct.inl_injective
    let eK := comapEquiv β hKX
    obtain ⟨e₁⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eT
    obtain ⟨e₂⟩ := nonempty_fusionZStar_equiv_of_surjective_quot hJ.2.2.2 hK.2.2 φ hφ
    obtain ⟨e₃⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eK
    refine ⟨⟨e₁.trans (e₂.trans e₃.symm)⟩, ?_⟩
    rw [card_pPrimeCore_quotient_congr eT, card_pPrimeCore_quotient_congr eK]
    exact Subgroup.card_dvd_of_surjective hφ

end CFSG.ComponentClassification.GS82PumpInputs
