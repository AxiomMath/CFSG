module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG
open scoped commutatorElement

theorem not_isQuasisimple_of_comm {Q : Type*} [Group Q] (h : ∀ a b : Q, a * b = b * a) :
    ¬ IsQuasisimple Q := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a b])

section Cover

variable {H X : Type*} [Group H] [Group X] (π : H →* X)

@[expose] def centralizerMap (h : H) :
    centralizer ({h} : Set H) →* centralizer ({π h} : Set X) :=
  ((π.comp (centralizer ({h} : Set H)).subtype).codRestrict _ fun c => by
    have hc := mem_centralizer_singleton_iff.1 c.2
    exact mem_centralizer_singleton_iff.2 (by
      show π c * π h = π h * π c
      rw [← map_mul, ← map_mul, hc]))

variable {π}

theorem commutator_lift_mem_ker (h ĝ : H) (hg : π ĝ ∈ centralizer ({π h} : Set X)) :
    ĝ * h * ĝ⁻¹ * h⁻¹ ∈ π.ker := by
  have := mem_centralizer_singleton_iff.1 hg
  rw [MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact this

theorem conj_mem_centralizer_of_lift (hker : π.ker ≤ center H) (h ĝ c : H)
    (hg : π ĝ ∈ centralizer ({π h} : Set X)) (hc : c ∈ centralizer ({h} : Set H)) :
    ĝ * c * ĝ⁻¹ ∈ centralizer ({h} : Set H) := by
  have hcomm := mem_centralizer_singleton_iff.1 hc
  have hg' : π ĝ⁻¹ ∈ centralizer ({π h} : Set X) := by
    rw [map_inv]
    exact inv_mem hg
  have hu : ∀ y : H, y * (ĝ⁻¹ * h * ĝ * h⁻¹) = (ĝ⁻¹ * h * ĝ * h⁻¹) * y := by
    simpa only [inv_inv] using
      mem_center_iff.1 (hker (commutator_lift_mem_ker (π := π) h ĝ⁻¹ hg'))
  rw [mem_centralizer_singleton_iff]
  have key : ĝ⁻¹ * h * ĝ = (ĝ⁻¹ * h * ĝ * h⁻¹) * h := by group
  have key2 : h * ĝ = ĝ * ((ĝ⁻¹ * h * ĝ * h⁻¹) * h) := by rw [← key]; group
  calc ĝ * c * ĝ⁻¹ * h = ĝ * c * (ĝ⁻¹ * h * ĝ) * ĝ⁻¹ := by group
    _ = ĝ * c * ((ĝ⁻¹ * h * ĝ * h⁻¹) * h) * ĝ⁻¹ := by rw [← key]
    _ = ĝ * (c * (ĝ⁻¹ * h * ĝ * h⁻¹)) * h * ĝ⁻¹ := by group
    _ = ĝ * ((ĝ⁻¹ * h * ĝ * h⁻¹) * c) * h * ĝ⁻¹ := by rw [hu c]
    _ = ĝ * (ĝ⁻¹ * h * ĝ * h⁻¹) * (c * h) * ĝ⁻¹ := by group
    _ = ĝ * (ĝ⁻¹ * h * ĝ * h⁻¹) * (h * c) * ĝ⁻¹ := by rw [hcomm]
    _ = (ĝ * ((ĝ⁻¹ * h * ĝ * h⁻¹) * h)) * c * ĝ⁻¹ := by group
    _ = (h * ĝ) * c * ĝ⁻¹ := by rw [← key2]
    _ = h * (ĝ * c * ĝ⁻¹) := by group

@[expose] def liftComm (hker : π.ker ≤ center H) (h : H) :
    ((centralizer ({π h} : Set X)).comap π) →* center H where
  toFun x := ⟨x * h * x⁻¹ * h⁻¹, hker (commutator_lift_mem_ker h x x.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hx := mem_center_iff.1 (hker (commutator_lift_mem_ker (π := π) h x x.2))
    have hy := mem_center_iff.1 (hker (commutator_lift_mem_ker (π := π) h y y.2))
    show (x * y : H) * h * (x * y : H)⁻¹ * h⁻¹ = ((x : H) * h * (x : H)⁻¹ * h⁻¹) *
      ((y : H) * h * (y : H)⁻¹ * h⁻¹)
    have e : (x : H) * (y : H) * h * ((y : H)⁻¹ * (x : H)⁻¹) * h⁻¹ =
        (x : H) * (((y : H) * h * (y : H)⁻¹ * h⁻¹) * h) * (x : H)⁻¹ * h⁻¹ := by group
    calc (x * y : H) * h * (x * y : H)⁻¹ * h⁻¹
        = (x : H) * (((y : H) * h * (y : H)⁻¹ * h⁻¹) * h) * (x : H)⁻¹ * h⁻¹ := by
          rw [← e]; simp [mul_assoc]
      _ = (((y : H) * h * (y : H)⁻¹ * h⁻¹) * ((x : H) * h * (x : H)⁻¹ * h⁻¹)) := by
          have := hy (x : H)
          calc (x : H) * (((y : H) * h * (y : H)⁻¹ * h⁻¹) * h) * (x : H)⁻¹ * h⁻¹
              = ((x : H) * ((y : H) * h * (y : H)⁻¹ * h⁻¹)) * h * (x : H)⁻¹ * h⁻¹ := by group
            _ = (((y : H) * h * (y : H)⁻¹ * h⁻¹) * (x : H)) * h * (x : H)⁻¹ * h⁻¹ := by rw [this]
            _ = _ := by group
      _ = _ := hx _

variable (hπ : Function.Surjective π) (hker : π.ker ≤ center H) (h : H)
include hπ hker

theorem centralizerMap_range_normal : (centralizerMap π h).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  obtain ⟨ĝ, hĝ⟩ := hπ (g : X)
  have hg : π ĝ ∈ centralizer ({π h} : Set X) := by rw [hĝ]; exact g.2
  refine ⟨⟨ĝ * (c : H) * ĝ⁻¹, conj_mem_centralizer_of_lift hker h ĝ c hg c.2⟩, ?_⟩
  apply Subtype.ext
  change π (ĝ * (c : H) * ĝ⁻¹) = (g : X) * π (c : H) * (g : X)⁻¹
  rw [map_mul, map_mul, map_inv, hĝ]

theorem commutator_le_range :
    commutator (centralizer ({π h} : Set X)) ≤ (centralizerMap π h).range := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨a, ha⟩ := hπ (g₁ : X)
  obtain ⟨b, hb⟩ := hπ (g₂ : X)
  have ha' : a ∈ (centralizer ({π h} : Set X)).comap π := by
    rw [Subgroup.mem_comap, ha]; exact g₁.2
  have hb' : b ∈ (centralizer ({π h} : Set X)).comap π := by
    rw [Subgroup.mem_comap, hb]; exact g₂.2
  have hz : liftComm hker h (⁅(⟨a, ha'⟩ : (centralizer ({π h} : Set X)).comap π),
      (⟨b, hb'⟩ : (centralizer ({π h} : Set X)).comap π)⁆) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (mem_center_iff.1 (liftComm hker h ⟨b, hb'⟩).2 _))
  have hz' := congrArg Subtype.val hz
  have hx : ⁅a, b⁆ ∈ centralizer ({h} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    have : ⁅a, b⁆ * h * (⁅a, b⁆)⁻¹ * h⁻¹ = 1 := hz'
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this.symm ▸ (by simp [mul_assoc])
  refine ⟨⟨⁅a, b⁆, hx⟩, ?_⟩
  apply Subtype.ext
  show π ⁅a, b⁆ = ⁅(g₁ : X), (g₂ : X)⁆
  rw [map_commutatorElement, ha, hb]

theorem isSolvable_centralizer_of_cover
    (hs : Group.IsSolvable (centralizer ({h} : Set H))) :
    Group.IsSolvable (centralizer ({π h} : Set X)) := by
  haveI := centralizerMap_range_normal hπ hker h
  have hcomm : ∀ a b : centralizer ({π h} : Set X) ⧸ (centralizerMap π h).range,
      a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [hxy]
        exact commutator_le_range hπ hker h (by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
  haveI : Group.IsSolvable (centralizer ({π h} : Set X) ⧸ (centralizerMap π h).range) :=
    isSolvable_of_comm hcomm
  haveI := hs
  exact solvable_of_ker_le_range (centralizerMap π h)
    (QuotientGroup.mk' (centralizerMap π h).range) (by rw [QuotientGroup.ker_mk'])

theorem exists_isComponent_of_cover {M : Subgroup (centralizer ({h} : Set H))}
    (hM : IsComponent M) : ∃ K : Subgroup (centralizer ({π h} : Set X)), IsComponent K := by
  haveI := centralizerMap_range_normal hπ hker h
  set ρ := centralizerMap π h with hρ
  have hker' : ρ.ker ≤ center (centralizer ({h} : Set H)) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro d
    have hc1 : π (c : H) = 1 := by
      have := MonoidHom.mem_ker.1 hc
      exact congrArg Subtype.val this
    have hcc := mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hc1)) (d : H)
    exact Subtype.ext hcc
  have hnle : ¬ M ≤ ρ.rangeRestrict.ker := by
    intro hle
    have hle' : M ≤ center (centralizer ({h} : Set H)) := fun m hm => hker' (by
      have := hle hm
      rwa [MonoidHom.ker_rangeRestrict] at this)
    have hcomm : ∀ a b : M, a * b = b * a := fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hle' a.2) b.1).symm
    exact not_isQuasisimple_of_comm hcomm hM.1
  have hq := LocalCores.isQuasisimple_map hM.1 ρ.rangeRestrict hnle
  have hsn : (M.map ρ.rangeRestrict).IsSubnormal := hM.2.map ρ.rangeRestrict_surjective
  exact ⟨(M.map ρ.rangeRestrict).map ρ.range.subtype,
    CatLeafProof.isComponent_map_subtype_of_normal ⟨hq, hsn⟩⟩

end Cover

theorem solvableOrComponent_of_cover {H X : Type} [Group H] [Group X] (π : H →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center H) (h : H)
    (hs : SolvableOrComponent H h) : SolvableOrComponent X (π h) := by
  rcases hs with hs | ⟨M, hM⟩
  · exact Or.inl (isSolvable_centralizer_of_cover hπ hker h hs)
  · exact Or.inr (exists_isComponent_of_cover hπ hker h hM)

end CFSG.ComponentClassification.CatFC.DS81
