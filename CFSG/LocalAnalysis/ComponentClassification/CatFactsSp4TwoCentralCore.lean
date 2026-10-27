module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag CFSG.Assembly.LowTwoRank

section Lift

variable {G G' : Type*} [Group G] [Group G']

theorem isPComponent_map_subgroupOf_iff (p : ℕ) (f : G →* G') (hf : Function.Injective f)
    {C M : Subgroup G} (hMC : M ≤ C) :
    CFSG.IsPComponent p ((M.map f).subgroupOf (C.map f)) ↔
      CFSG.IsPComponent p (M.subgroupOf C) := by
  let ψ : C ≃* C.map f := C.equivMapOfInjective f hf
  have key : (M.subgroupOf C).map ψ.toMonoidHom = (M.map f).subgroupOf (C.map f) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨c, hc⟩, hcM, hceq⟩
      refine ⟨c, hcM, ?_⟩
      exact congrArg Subtype.val hceq
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hMC hm⟩, hm, rfl⟩
  rw [← key]
  constructor
  · intro h
    have h2 := isPComponent_map_of_isPComponent p ψ.symm h
    rwa [Subgroup.map_map, show ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ from by
      ext x; simp, Subgroup.map_id] at h2
  · exact isPComponent_map_of_isPComponent p ψ

theorem isComponent_map_subgroupOf_of_injective (f : G →* G') (hf : Function.Injective f)
    {M C : Subgroup G} (hMC : M ≤ C) (hM : IsComponent (M.subgroupOf C)) :
    IsComponent ((M.map f).subgroupOf (C.map f)) := by
  let ψ : C ≃* C.map f := C.equivMapOfInjective f hf
  have hmap : (M.subgroupOf C).map ψ.toMonoidHom = (M.map f).subgroupOf (C.map f) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨m, hmC⟩, hm, hmx⟩
      exact ⟨m, hm, congrArg Subtype.val hmx⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hMC hm⟩, hm, rfl⟩
  rw [← hmap]
  obtain ⟨hq, hs⟩ := hM
  refine ⟨?_, hs.map ψ.surjective⟩
  exact (isQuasisimple_congr ((M.subgroupOf C).equivMapOfInjective ψ.toMonoidHom ψ.injective)).mp hq

theorem isComponent_subgroupOf_of_inf {Y C M : Subgroup G} [hY : Y.Normal] (hMN : M ≤ Y ⊓ C)
    (hM : IsComponent (M.subgroupOf (Y ⊓ C))) : IsComponent (M.subgroupOf C) := by
  have hNC : Y ⊓ C ≤ C := inf_le_right
  have hNn : ((Y ⊓ C).subgroupOf C).Normal := by
    rw [inf_subgroupOf_right]
    infer_instance
  obtain ⟨hq, hs⟩ := hM
  refine ⟨?_, (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hMN hNC hNn.isSubnormal).mpr hs⟩
  exact (isQuasisimple_congr ((subgroupOfEquivOfLe hMN).trans
    (subgroupOfEquivOfLe (hMN.trans hNC)).symm)).mp hq

end Lift

theorem twoCentral_main (H : Type) [Group H] [Finite H] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hsimple : IsSimpleGroup ↥(generalizedFitting H))
    (hY : Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f)
    (a : H) (ha : orderOf a = 2) (J : Subgroup H) (hJY : J ≤ generalizedFitting H)
    (hJa : J ≤ centralizer ({a} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))))
    (hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f)
    (R : Subgroup H) (_hR2 : IsPGroup 2 R)
    (_hRle : R ≤ centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J)
    (hRs : GSThmB.Seven.IsSylowIn (R ⊓ generalizedFitting H) (generalizedFitting H ⊓
      centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J)) :
    ∃ t ∈ R ⊓ generalizedFitting H, orderOf t = 2 ∧ ∃ M : Subgroup H,
      M ≤ centralizer ({t} : Set H) ∧ IsComponent (M.subgroupOf (centralizer ({t} : Set H))) ∧
      conjugate M a ≠ M ∧ J ≤ M ⊔ conjugate M a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := generalizedFitting H with hYdef
  have hYn : Y.Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hY
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) := e.isSimpleGroup_congr.mp hsimple
  set φ : MulAut Y := MulAut.conjNormal a with hφdef
  have hφ : ∀ y : Y, ((φ y : Y) : H) = a * y * a⁻¹ := fun y => MulAut.conjNormal_apply a y
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hφφ : ∀ y, φ (φ y) = y := fun y => Subtype.ext (by
    rw [hφ, hφ, hainv]
    calc a * (a * (y : H) * a) * a = (a * a) * y * (a * a) := by group
      _ = y := by rw [ha2, one_mul, mul_one])
  set α : MulAut (StatedProj (StatedSp 2 K)) := e.symm.trans (φ.trans e) with hαdef
  have hcomm : ∀ y, e (φ y) = α (e y) := fun y => by
    simp only [hαdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα2 : α * α = 1 := by
    ext x
    simp only [hαdef, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      hφφ, MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hα1 : α ≠ 1 := by
    intro h
    have hφ1 : ∀ y, φ y = y := fun y => by
      apply e.injective
      rw [hcomm, h, MulAut.one_apply]
    have hac : a ∈ centralizer (Y : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      have := congrArg Subtype.val (hφ1 ⟨y, hy⟩)
      rw [hφ] at this
      calc y * a = a * y * a⁻¹ * a := by rw [this]
        _ = a * y := by group
    have haY : a ∈ Y := centralizer_generalizedFitting_le H hac
    have hcen : e ⟨a, haY⟩ ∈ center (StatedProj (StatedSp 2 K)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_iff.mp hac y y.2
    have h1 := eq_one_of_mem_center_P h2 h4 hs hcen
    have : a = 1 := by
      have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      exact this
    rw [this, orderOf_one] at ha
    omega
  set J₀ : Subgroup Y := J.subgroupOf Y with hJ₀def
  have hJ₀map : J₀.map Y.subtype = J := by
    rw [hJ₀def, subgroupOf_map_subtype, inf_of_le_left hJY]
  have hfix : (fixOf φ).map Y.subtype = Y ⊓ centralizer ({a} : Set H) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : H) ∈ centralizer ({a} : Set H)
      rw [mem_centralizer_singleton_iff]
      have := congrArg Subtype.val (show φ y = y from hy)
      rw [hφ] at this
      calc (y : H) * a = a * y * a⁻¹ * a := by rw [this]
        _ = a * y := by group
    · rintro ⟨hxY, hxa⟩
      have hxa' : x * a = a * x := mem_centralizer_singleton_iff.mp hxa
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      change φ ⟨x, hxY⟩ = ⟨x, hxY⟩
      apply Subtype.ext
      rw [hφ]
      change a * x * a⁻¹ = x
      rw [← hxa', mul_inv_cancel_right]
  have hJ₀X : J₀ ≤ fixOf φ := by
    intro y hy
    change φ y = y
    apply Subtype.ext
    rw [hφ]
    have hya : (y : H) * a = a * y := mem_centralizer_singleton_iff.mp (hJa hy)
    rw [← hya, mul_inv_cancel_right]
  have hJ₀ : IsPComponent 2 (J₀.subgroupOf (fixOf φ)) := by
    have h1 := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJY hJa)
      (inf_le_right : Y ⊓ centralizer ({a} : Set H) ≤ _) hJ
    rw [← hJ₀map, ← hfix] at h1
    exact (isPComponent_map_subgroupOf_iff 2 Y.subtype Y.subtype_injective hJ₀X).mp h1
  obtain ⟨hJ'X, hJ'⟩ := isPComponent_map_fixOf hcomm hJ₀X hJ₀
  have hJcard : ∃ o, Odd o ∧ Nat.card (J₀.map e.toMonoidHom) =
      o * (p ^ f * ((p ^ f) ^ 2 - 1) / 2) := by
    obtain ⟨-, -, F, _, _, hF, ⟨eJ⟩⟩ := GH74.Generic.lieModel_psl_data hJm
    have hFodd : Odd (Nat.card F) := odd_card_of_card_eq hp hp2 hF
    refine ⟨Nat.card (pPrimeCore 2 J), Nat.coprime_two_left.mp pPrimeCore_coprime_card, ?_⟩
    have c1 : Nat.card (J₀.map e.toMonoidHom) = Nat.card J := by
      rw [← Nat.card_congr (J₀.equivMapOfInjective _ e.injective).toEquiv, ← hJ₀map]
      exact Nat.card_congr (J₀.equivMapOfInjective _ Y.subtype_injective).toEquiv
    rw [c1, (pPrimeCore 2 J).card_eq_card_quotient_mul_card_subgroup, mul_comm,
      Nat.card_congr eJ.toEquiv, card_statedProj_statedSL_two_odd hFodd, hF]
  have hw := tcWitness_of_involution hp hp2 hf hK h5 hs α hα2 hα1 hJ'X hJ' hJcard
  obtain ⟨t₀, ht₀2, ht₀1, ht₀φ, ht₀J, M₀, hM₀t, hM₀, hM₀φ, hJM₀⟩ :=
    TCWitness.of_comm hcomm hw
  set t : H := (t₀ : H) with htdef
  set M : Subgroup H := M₀.map Y.subtype with hMdef
  have hmapφ : (M₀.map φ.toMonoidHom).map Y.subtype = conjugate M a := by
    rw [conjugate_eq_map, hMdef, Subgroup.map_map, Subgroup.map_map, hainv]
    congr 1
  have hcentY : (centralizer ({t₀} : Set Y)).map Y.subtype = Y ⊓ centralizer ({t} : Set H) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : H) ∈ centralizer ({t} : Set H)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hxY, hxt⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      show (⟨x, hxY⟩ : Y) ∈ centralizer ({t₀} : Set Y)
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxt)
  refine twoCentral_of_witness hRs (t₀ := t) t₀.2 (congrArg Subtype.val ht₀2)
    (fun h => ht₀1 (Subtype.ext h)) ?_ ?_ (M₀ := M) ?_ ?_ ?_ ?_
  · have := congrArg Subtype.val ht₀φ
    rw [hφ] at this
    calc t * a = a * t * a⁻¹ * a := by rw [this]
      _ = a * t := by group
  · intro j hj
    have := ht₀J ⟨j, hJY hj⟩ hj
    exact congrArg Subtype.val this
  · rintro _ ⟨m, hm, rfl⟩
    have := hM₀t hm
    rw [mem_centralizer_singleton_iff] at this ⊢
    exact congrArg Subtype.val this
  · have hMN : M ≤ Y ⊓ centralizer ({t} : Set H) := by
      rw [← hcentY]
      exact map_mono hM₀t
    apply isComponent_subgroupOf_of_inf hMN
    rw [← hcentY]
    exact isComponent_map_subgroupOf_of_injective Y.subtype Y.subtype_injective hM₀t hM₀
  · rw [← hmapφ]
    intro h
    exact hM₀φ (Subgroup.map_injective Y.subtype_injective h)
  · rw [← hmapφ, ← Subgroup.map_sup, ← hJ₀map]
    exact map_mono hJM₀

end CFSG.ComponentClassification.CatFactsSp4
