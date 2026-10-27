module

public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

instance fstarCenter_normal (Y : Type) [Group Y] : (fstarCenter Y).Normal := by
  have hFn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  refine ⟨fun z hz y => ?_⟩
  obtain ⟨c, hc'', rfl⟩ := hz
  have hc' : c ∈ Subgroup.center ↥(genFittingFStar Y) := hc''
  refine ⟨⟨y * c * y⁻¹, hFn.conj_mem _ c.2 y⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro f
  apply Subtype.ext
  have hf : y⁻¹ * (f : Y) * y ∈ genFittingFStar Y := by simpa using hFn.conj_mem _ f.2 y⁻¹
  have h' : y⁻¹ * (f : Y) * y * (c : Y) = (c : Y) * (y⁻¹ * (f : Y) * y) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨_, hf⟩)
  show (f : Y) * (y * c * y⁻¹) = y * c * y⁻¹ * f
  calc (f : Y) * (y * c * y⁻¹) = y * ((y⁻¹ * f * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * f * y)) * y⁻¹ := by rw [h']
    _ = y * c * y⁻¹ * f := by group

theorem fstarCenter_le_fitting (Y : Type) [Group Y] : fstarCenter Y ≤ genFittingFitting Y := by
  have hZcomm : ∀ a b : ↥(fstarCenter Y), a * b = b * a := by
    rintro ⟨a, c₁, hc₁, rfl⟩ ⟨b, c₂, hc₂, rfl⟩
    apply Subtype.ext
    show (c₁ : Y) * c₂ = c₂ * c₁
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₁ c₂).symm
  have hZnil : Group.IsNilpotent ↥(fstarCenter Y) := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥(fstarCenter Y) →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hZcomm w z
  exact le_sSup ⟨inferInstance, hZnil⟩

theorem twoSubgroupsFourGenerated_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A →* B) (hφ : Function.Surjective φ) (h : TwoSubgroupsFourGenerated A) :
    TwoSubgroupsFourGenerated B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  set M : Subgroup A := P.comap φ with hM
  let g : ↥M →* ↥P := (φ.comp M.subtype).codRestrict P fun m => m.2
  have hg : Function.Surjective g := by
    rintro ⟨p, hp⟩
    obtain ⟨a, rfl⟩ := hφ p
    exact ⟨⟨a, hp⟩, rfl⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  have hQP : (Q : Subgroup ↥M).map g = ⊤ := by
    have hP' : IsPGroup 2 (⊤ : Subgroup ↥P) := hP.of_equiv Subgroup.topEquiv.symm
    exact ((Q.mapSurjective hg).is_maximal' hP' le_top).symm
  obtain ⟨s, hs, hcl⟩ := h ((Q : Subgroup ↥M).map M.subtype) (Q.isPGroup'.map M.subtype)
  refine ⟨s.image φ, (Finset.card_image_le).trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hcl]
  refine le_antisymm ?_ fun p hp => ?_
  · rintro _ ⟨_, ⟨q, -, rfl⟩, rfl⟩
    exact q.2
  · have hmem : (⟨p, hp⟩ : ↥P) ∈ (Q : Subgroup ↥M).map g := by
      rw [hQP]
      exact Subgroup.mem_top _
    obtain ⟨q, hq, hqp⟩ := hmem
    exact ⟨(q : A), ⟨q, hq, rfl⟩, congrArg Subtype.val hqp⟩

theorem exists_ne_comm_of_commutator_eq_top {K : Type*} [Group K] [Nontrivial K]
    (h : commutator K = ⊤) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hcomm : commutator K = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  obtain ⟨x, y, hxy⟩ := exists_pair_ne K
  have h1 : ∀ z : K, z = 1 := fun z => by
    have : z ∈ commutator K := by rw [h]; exact Subgroup.mem_top z
    rwa [hcomm, Subgroup.mem_bot] at this
  exact hxy ((h1 x).trans (h1 y).symm)

section Quotient

variable (Y : Type) [Group Y]

theorem nonempty_fstarBar_equiv :
    Nonempty (↥((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y))) ≃*
      ↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) := by
  have hker : ((QuotientGroup.mk' (fstarCenter Y)).domRestrict (genFittingFStar Y)).ker =
      Subgroup.center ↥(genFittingFStar Y) := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange _)).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))).symm⟩

theorem isSimpleGroup_fstarBar (hQ : TightFStarQuasisimple Y) :
    IsSimpleGroup ↥((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y))) := by
  obtain ⟨e⟩ := nonempty_fstarBar_equiv Y
  have := hQ.2
  exact e.isSimpleGroup

theorem exists_ne_comm_fstarBar (hQ : TightFStarQuasisimple Y) :
    ∃ a b : ↥((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y))), a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_fstarBar_equiv Y
  have := hQ.2
  have hs := QuotientGroup.mk'_surjective (Subgroup.center ↥(genFittingFStar Y))
  have hperf : commutator (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) = ⊤ := by
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator,
      ← _root_.commutator_def, hQ.1, Subgroup.map_top_of_surjective _ hs]
  obtain ⟨a, b, hab⟩ := exists_ne_comm_of_commutator_eq_top hperf
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

variable [Finite Y]

theorem centralizer_fstarBar_eq_bot (hQ : TightFStarQuasisimple Y)
    (hNc : fstarCenter Y ≤ Subgroup.center Y) :
    Subgroup.centralizer (((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y)) :
      Subgroup (Y ⧸ fstarCenter Y)) : Set (Y ⧸ fstarCenter Y)) = ⊥ := by
  set L := genFittingFStar Y with hL
  set N := fstarCenter Y with hN
  rw [eq_bot_iff]
  intro ybar hy
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N ybar
  have hcomm : ∀ ℓ ∈ L, y * ℓ * y⁻¹ * ℓ⁻¹ ∈ N := by
    intro ℓ hℓ
    have h1 := Subgroup.mem_centralizer_iff.mp hy (QuotientGroup.mk' N ℓ)
      (Subgroup.mem_map_of_mem _ hℓ)
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h1]
    group
  have hcen : ∀ ℓ : ↥L, y * ℓ * y⁻¹ * (ℓ : Y)⁻¹ ∈ Subgroup.center Y := fun ℓ =>
    hNc (hcomm ℓ ℓ.2)
  let ψ : ↥L →* ↥(Subgroup.center Y) :=
    { toFun := fun ℓ => ⟨y * ℓ * y⁻¹ * (ℓ : Y)⁻¹, hcen ℓ⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.mp (hcen b) ((a : Y)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc y * ((a : Y) * b) * y⁻¹ * ((b : Y)⁻¹ * (a : Y)⁻¹)
            = y * a * y⁻¹ * ((y * b * y⁻¹ * (b : Y)⁻¹) * (a : Y)⁻¹) := by group
          _ = y * a * y⁻¹ * ((a : Y)⁻¹ * (y * b * y⁻¹ * (b : Y)⁻¹)) := by rw [hb]
          _ = y * a * y⁻¹ * (a : Y)⁻¹ * (y * b * y⁻¹ * (b : Y)⁻¹) := by group }
  have hker : commutator ↥L ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [hQ.1] at hker
  have hyC : y ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have h1 : ψ ⟨ℓ, hℓ⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
    have h2 : y * ℓ * y⁻¹ * ℓ⁻¹ = 1 := congrArg Subtype.val h1
    calc ℓ * y = (y * ℓ * y⁻¹ * ℓ⁻¹)⁻¹ * (y * ℓ) := by group
      _ = y * ℓ := by rw [h2, inv_one, one_mul]
  have hyL : y ∈ L := CFSG.Adapters.generalized_fitting_self_centralizing Y hyC
  have hyZ : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro ℓ
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC ℓ ℓ.2)
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  show y ∈ (Subgroup.center ↥L).map L.subtype
  exact ⟨⟨y, hyL⟩, hyZ, rfl⟩

theorem genFittingFStar_quotient_fstarCenter (hQ : TightFStarQuasisimple Y)
    (hNc : fstarCenter Y ≤ Subgroup.center Y) :
    genFittingFStar (Y ⧸ fstarCenter Y) =
      (genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y)) := by
  have : ((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y))).Normal :=
    (genFittingFStar_normal Y).map _ (QuotientGroup.mk'_surjective _)
  have := isSimpleGroup_fstarBar Y hQ
  exact genFittingFStar_eq_of_normal_simple _ (exists_ne_comm_fstarBar Y hQ)
    (centralizer_fstarBar_eq_bot Y hQ hNc)

theorem twoSubgroupsFourGenerated_fstarBar (h : TwoSubgroupsFourGenerated ↥(genFittingFStar Y)) :
    TwoSubgroupsFourGenerated ↥((genFittingFStar Y).map (QuotientGroup.mk' (fstarCenter Y))) := by
  set π := QuotientGroup.mk' (fstarCenter Y)
  refine twoSubgroupsFourGenerated_of_surjective
    ((π.domRestrict (genFittingFStar Y)).codRestrict _
      fun x => Subgroup.mem_map_of_mem π x.2) (fun z => ?_) h
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩

end Quotient

end CFSG.ClassicalInvolution.Q3.TA3
