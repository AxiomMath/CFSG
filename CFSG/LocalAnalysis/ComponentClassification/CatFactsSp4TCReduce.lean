module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4D

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG Subgroup

variable {H : Type} [Group H]

theorem mem_coreActionKernel_of_commute {J : Subgroup H} {g : H}
    (hg : ∀ j ∈ J, g * j = j * g) : g ∈ UnbalancedLayer.coreActionKernel J := by
  have hconj : ∀ j ∈ J, g * j * g⁻¹ = j := fun j hj => by rw [hg j hj, mul_inv_cancel_right]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      rw [hconj j hj]
      exact hj
    · intro hj
      have h1 := hg _ hj
      have h2 : g * j * g⁻¹ = j := by
        apply mul_left_cancel (a := g)
        calc g * (g * j * g⁻¹) = g * j * g⁻¹ * g := h1
          _ = g * j := by group
      rwa [h2] at hj
  · have : j⁻¹ * g⁻¹ * j * g = 1 := by
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * (j * g)) := by group
        _ = j⁻¹ * (g⁻¹ * (g * j)) := by rw [hg j hj]
        _ = 1 := by group
    rw [this]
    exact one_mem _

theorem map_conj_centralizer (c t₀ : H) :
    (centralizer {t₀}).map (MulAut.conj c).toMonoidHom = centralizer {c * t₀ * c⁻¹} :=
  map_centralizer_singleton (MulAut.conj c) t₀

theorem isComponent_map_subgroupOf (φ : H ≃* H) {M C : Subgroup H} (hMC : M ≤ C)
    (hM : IsComponent (M.subgroupOf C)) :
    IsComponent ((M.map φ.toMonoidHom).subgroupOf (C.map φ.toMonoidHom)) := by
  let ψ : C ≃* C.map φ.toMonoidHom := C.equivMapOfInjective φ.toMonoidHom φ.injective
  have hmap : (M.subgroupOf C).map ψ.toMonoidHom =
      (M.map φ.toMonoidHom).subgroupOf (C.map φ.toMonoidHom) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨m, hmC⟩, hm, hmx⟩
      have := congrArg Subtype.val hmx
      exact ⟨m, hm, this⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hMC hm⟩, hm, rfl⟩
  rw [← hmap]
  obtain ⟨hq, hs⟩ := hM
  refine ⟨?_, hs.map ψ.surjective⟩
  exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((M.subgroupOf C).equivMapOfInjective ψ.toMonoidHom ψ.injective) |>.mp hq

theorem conjugate_eq_map (M : Subgroup H) (a : H) :
    conjugate M a = M.map (MulAut.conj a⁻¹).toMonoidHom := rfl

theorem conjugate_map_conj_comm {M : Subgroup H} {a c : H} (hca : c * a = a * c) :
    conjugate (M.map (MulAut.conj c).toMonoidHom) a =
      (conjugate M a).map (MulAut.conj c).toMonoidHom := by
  rw [conjugate_eq_map, conjugate_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have : a⁻¹ * c = c * a⁻¹ := by
    calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * c) * a⁻¹ := by rw [hca]
      _ = c * a⁻¹ := by group
  calc a⁻¹ * (c * x * c⁻¹) * a⁻¹⁻¹ = (a⁻¹ * c) * x * (a⁻¹ * c)⁻¹ := by group
    _ = (c * a⁻¹) * x * (c * a⁻¹)⁻¹ := by rw [this]
    _ = c * (a⁻¹ * x * a⁻¹⁻¹) * c⁻¹ := by group

variable [Finite H]

theorem twoCentral_of_witness {Y : Subgroup H} {a : H} {J R : Subgroup H}
    (hR : GSThmB.Seven.IsSylowIn (R ⊓ Y)
      (Y ⊓ centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J))
    {t₀ : H} (ht₀Y : t₀ ∈ Y) (ht₀2 : t₀ * t₀ = 1) (ht₀1 : t₀ ≠ 1) (ht₀a : t₀ * a = a * t₀)
    (ht₀J : ∀ j ∈ J, t₀ * j = j * t₀) {M₀ : Subgroup H}
    (hM₀t : M₀ ≤ centralizer ({t₀} : Set H))
    (hM₀ : IsComponent (M₀.subgroupOf (centralizer ({t₀} : Set H))))
    (hM₀a : conjugate M₀ a ≠ M₀) (hJM : J ≤ M₀ ⊔ conjugate M₀ a) :
    ∃ t ∈ R ⊓ Y, orderOf t = 2 ∧ ∃ M : Subgroup H, M ≤ centralizer ({t} : Set H) ∧
      IsComponent (M.subgroupOf (centralizer ({t} : Set H))) ∧ conjugate M a ≠ M ∧
        J ≤ M ⊔ conjugate M a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := Y ⊓ centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J with hD
  have ht₀D : t₀ ∈ D :=
    ⟨⟨ht₀Y, mem_centralizer_singleton_iff.mpr ht₀a⟩, mem_coreActionKernel_of_commute ht₀J⟩
  have ho : orderOf t₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht₀2) ht₀1
  have hP : IsPGroup 2 (zpowers t₀) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ho, pow_one]
  obtain ⟨c, hcD, hcR⟩ := exists_conj_le_of_isSylowIn (zpowers_le.mpr ht₀D) hP hR
  have hca : c * a = a * c := mem_centralizer_singleton_iff.mp hcD.1.2
  have hcJ : c ∈ normalizer (J : Set H) := hcD.2.1
  set t := c * t₀ * c⁻¹ with ht
  have htR : t ∈ R ⊓ Y := hcR ⟨t₀, mem_zpowers t₀, rfl⟩
  refine ⟨t, htR, by rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ho],
    M₀.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← map_conj_centralizer]
    exact map_mono hM₀t
  · rw [← map_conj_centralizer]
    exact isComponent_map_subgroupOf (MulAut.conj c) hM₀t hM₀
  · rw [conjugate_map_conj_comm hca]
    intro h
    exact hM₀a (Subgroup.map_injective (MulAut.conj c).injective h)
  · rw [conjugate_map_conj_comm hca, ← Subgroup.map_sup]
    intro j hj
    refine ⟨c⁻¹ * j * c, hJM ?_, by simp [MulAut.conj_apply]; group⟩
    have := (mem_normalizer_iff.mp (inv_mem hcJ) j).mp hj
    simpa using this

@[expose] def TCWitness {G : Type*} [Group G] (α : MulAut G) (J : Subgroup G) : Prop :=
  ∃ t₀ : G, t₀ * t₀ = 1 ∧ t₀ ≠ 1 ∧ α t₀ = t₀ ∧ (∀ j ∈ J, t₀ * j = j * t₀) ∧
    ∃ M₀ : Subgroup G, M₀ ≤ centralizer ({t₀} : Set G) ∧
      IsComponent (M₀.subgroupOf (centralizer ({t₀} : Set G))) ∧
      M₀.map α.toMonoidHom ≠ M₀ ∧ J ≤ M₀ ⊔ M₀.map α.toMonoidHom

theorem TCWitness.map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {α : MulAut G}
    {J : Subgroup G} (h : TCWitness α J) :
    TCWitness (φ.symm.trans (α.trans φ)) (J.map φ.toMonoidHom) := by
  obtain ⟨t₀, h2, h1, hα, hJ, M₀, hMt, hM, hMα, hJM⟩ := h
  have hmapα : ∀ N : Subgroup G, (N.map φ.toMonoidHom).map (φ.symm.trans (α.trans φ)).toMonoidHom
      = (N.map α.toMonoidHom).map φ.toMonoidHom := by
    intro N
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  refine ⟨φ t₀, by rw [← map_mul, h2, map_one], fun h => h1 (φ.injective (h.trans
    (map_one φ).symm)), by simp [hα], ?_, M₀.map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    change φ t₀ * φ j = φ j * φ t₀
    rw [← map_mul, ← map_mul, hJ j hj]
  · rw [← map_centralizer_singleton]
    exact map_mono hMt
  · have hC := map_centralizer_singleton φ t₀
    let ψ : centralizer ({t₀} : Set G) ≃* (centralizer ({t₀} : Set G)).map φ.toMonoidHom :=
      (centralizer ({t₀} : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective
    have hmap : (M₀.subgroupOf (centralizer ({t₀} : Set G))).map
        ((ψ.trans (MulEquiv.subgroupCongr hC)).toMonoidHom) =
        (M₀.map φ.toMonoidHom).subgroupOf (centralizer ({φ t₀} : Set G')) := by
      ext ⟨x, hx⟩
      rw [mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨⟨m, hmC⟩, hm, hmx⟩
        have := congrArg Subtype.val hmx
        exact ⟨m, hm, this⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hMt hm⟩, hm, rfl⟩
    rw [← hmap]
    obtain ⟨hq, hs⟩ := hM
    refine ⟨?_, hs.map (ψ.trans (MulEquiv.subgroupCongr hC)).surjective⟩
    exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((M₀.subgroupOf _).equivMapOfInjective _ (ψ.trans (MulEquiv.subgroupCongr hC)).injective)
      |>.mp hq
  · rw [hmapα]
    intro h
    exact hMα (Subgroup.map_injective φ.injective h)
  · rw [hmapα, ← Subgroup.map_sup]
    exact map_mono hJM

end CFSG.ComponentClassification.CatFactsSp4
