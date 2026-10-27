module

public import CFSG.LinearAlgebra.RootGroupSL.AutSemidirect
public import CFSG.LinearAlgebra.RootGroupSL.ModelAction
public import CFSG.LinearAlgebra.RootGroupSL.ModelPCore
public import CFSG.LinearAlgebra.RootGroupSL.AutK1
public import CFSG.LinearAlgebra.RootGroupSL.CocycleModel
public import CFSG.LinearAlgebra.RootGroupSL.EndModel
public import CFSG.LinearAlgebra.RootGroupSL.EndModelDual

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private instance finite_sl : Finite (SpecialLinearGroup k (VJ × V₀)) := by
  haveI : Finite VJ := Module.finite_of_finite k
  haveI : Finite V₀ := Module.finite_of_finite k
  haveI : Finite (VJ × V₀) := inferInstance
  haveI : Finite ((VJ × V₀) ≃ₗ[k] (VJ × V₀)) :=
    Finite.of_injective (fun e : (VJ × V₀) ≃ₗ[k] (VJ × V₀) => e.toEquiv.toFun)
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  exact Subtype.finite

private noncomputable def transportAutOf {A P : Subgroup (SpecialLinearGroup k (VJ × V₀))}
    (h : A ⊔ modelK1 k VJ V₀ = P) (α : MulAut ↥P) : MulAut ↥(A ⊔ modelK1 k VJ V₀) :=
  (MulEquiv.subgroupCongr h).trans (α.trans (MulEquiv.subgroupCongr h).symm)

private lemma subgroupCongr_transportAutOf {A P : Subgroup (SpecialLinearGroup k (VJ × V₀))}
    (h : A ⊔ modelK1 k VJ V₀ = P) (α : MulAut ↥P)
    (x : ↥(A ⊔ modelK1 k VJ V₀)) :
    MulEquiv.subgroupCongr h (transportAutOf h α x) = α (MulEquiv.subgroupCongr h x) := by
  simp [transportAutOf, MulEquiv.trans_apply]

private lemma mem_pCoreOf_iff {G : Type*} [Group G] (p : ℕ) (H : Subgroup G)
    (x : ↥H) : ((x : G) ∈ CFSG.Open.pCoreOf p H) ↔ x ∈ CFSG.pCore p ↥H := by
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private lemma characteristic_mem_iff {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.Characteristic) (φ : G ≃* G) (x : G) : x ∈ H ↔ φ x ∈ H := by
  have h := Subgroup.characteristic_iff_comap_eq.mp hH φ
  constructor
  · intro hx
    have hh : x ∈ H.comap φ.toMonoidHom := by rwa [h]
    exact (Subgroup.mem_comap).mp hh
  · intro hx
    have hh : x ∈ H.comap φ.toMonoidHom := (Subgroup.mem_comap).mpr hx
    rwa [h] at hh

private lemma mem_of_eq_pCoreOf {G : Type*} [Group G] {A P : Subgroup G} {p : ℕ}
    (hA : A = CFSG.Open.pCoreOf p P) (x : G) :
    x ∈ A ↔ x ∈ CFSG.Open.pCoreOf p P := by
  rw [hA]

private lemma alpha_preserves_pCore {A P : Subgroup (SpecialLinearGroup k (VJ × V₀))}
    (h : A ⊔ modelK1 k VJ V₀ = P) (hA : A = CFSG.Open.pCoreOf 2 P)
    (α : MulAut ↥P) :
    ∀ x : ↥(A ⊔ modelK1 k VJ V₀),
      (x : SpecialLinearGroup k (VJ × V₀)) ∈ A ↔
      (((transportAutOf h α x : ↥(A ⊔ modelK1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) ∈ A) := by
  intro x
  rw [mem_of_eq_pCoreOf hA (x : SpecialLinearGroup k (VJ × V₀))]
  rw [mem_of_eq_pCoreOf hA
    (((transportAutOf h α x : ↥(A ⊔ modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)))]
  rw [← MulEquiv.subgroupCongr_apply h x,
    mem_pCoreOf_iff 2 P (MulEquiv.subgroupCongr h x)]
  rw [← MulEquiv.subgroupCongr_apply h (transportAutOf h α x),
    mem_pCoreOf_iff 2 P (MulEquiv.subgroupCongr h (transportAutOf h α x))]
  rw [subgroupCongr_transportAutOf]
  exact characteristic_mem_iff (CFSG.pCore_characteristic (p := 2) (G := ↥P)) α
    (MulEquiv.subgroupCongr h x)

theorem exists_conj_of_mulAut_modelP1 (hm : 3 ≤ Module.finrank E VJ)
    (hc : 2 ≤ Module.finrank k E) (α : MulAut ↥(modelP1 k VJ V₀))
    (hα : ∀ j : ↥(modelP1 k VJ V₀),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α j = j) :
    ∃ z : (VJ × V₀) ≃ₗ[k] (VJ × V₀), ∀ p : ↥(modelP1 k VJ V₀),
      SpecialLinearGroup.toLinearEquiv ((α p : ↥(modelP1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) =
        z * SpecialLinearGroup.toLinearEquiv (p : SpecialLinearGroup k (VJ × V₀)) * z⁻¹ := by
  have hVJ4 : 4 ≤ Module.finrank k VJ := by
    rw [← Module.finrank_mul_finrank k E VJ]
    have h := Nat.mul_le_mul hc hm
    omega
  have hVJ3 : 3 ≤ Module.finrank k VJ := by omega
  have hVJ2 : 2 ≤ Module.finrank k VJ := by omega
  have hAK : modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀ = modelP1 k VJ V₀ :=
    modelA1_sup_modelK1 (k := k) (VJ := VJ) (V₀ := V₀)
  have hαJ : ∀ j : ↥(modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ →
        transportAutOf hAK α j = j := by
    intro j hj
    apply (MulEquiv.subgroupCongr hAK).injective
    rw [subgroupCongr_transportAutOf]
    exact hα (MulEquiv.subgroupCongr hAK j) (by
      rw [MulEquiv.subgroupCongr_apply]
      exact hj)
  obtain ⟨s, hs, y, hy, hconj⟩ :=
    exists_conj_of_aut_semidirect
      (ε := SpecialLinearGroup.toLinearEquiv (R := k) (V := VJ × V₀))
      (hε := SpecialLinearGroup.toLinearEquiv_injective (R := k) (V := VJ × V₀))
      (A := modelA1 k VJ V₀) (K := modelK1 k VJ V₀) (J := modelJ k E VJ V₀)
      (Sg := (diagEHom k E VJ V₀).range) (Yg := (diagYHom k VJ V₀).range)
      (hAK := modelA1_inf_modelK1 (k := k) (VJ := VJ) (V₀ := V₀))
      (hAc := fun a ha b hb => modelA1_mul_comm (k := k) (VJ := VJ) (V₀ := V₀) ha hb)
      (hKA := fun g hg a ha => modelK1_conj_mem_modelA1 (k := k) (VJ := VJ) (V₀ := V₀) hg ha)
      (hJK := modelJ_le_modelK1 (k := k) (E := E) (VJ := VJ) (V₀ := V₀))
      (hCA := fun a ha h => modelA1_eq_one_of_commute_modelJ (k := k) (E := E) (VJ := VJ)
        (V₀ := V₀) (by omega) ha h)
      (hSA := fun s hs a ha => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        obtain ⟨a', ha', h⟩ :=
          diagE_conj_mem_modelA1 (k := k) (VJ := VJ) (V₀ := V₀) u ha
        exact ⟨a', ha', h⟩)
      (hSK := fun s hs g hg => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        obtain ⟨g', hg', h⟩ :=
          diagE_conj_mem_modelK1 (k := k) (VJ := VJ) (V₀ := V₀) u hg
        exact ⟨g', hg', h⟩)
      (hSJ := fun s hs j hj => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        exact diagE_comm_modelJ (k := k) (VJ := VJ) (V₀ := V₀) u hj)
      (hYA := fun y hy a ha => by
        obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
        obtain ⟨a', ha', h⟩ :=
          diagY_conj_mem_modelA1 (k := k) (VJ := VJ) (V₀ := V₀) v ha
        exact ⟨a', ha', h⟩)
      (hYK := fun y hy g hg => by
        obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
        exact diagY_comm_modelK1 (k := k) (VJ := VJ) (V₀ := V₀) v hg)
      (H12 := fun β hβ => by
        obtain ⟨u, hu⟩ := exists_diagE_of_mulAut_modelK1 (k := k) (E := E) (VJ := VJ)
          (V₀ := V₀) hm β hβ
        exact ⟨diagEHom k E VJ V₀ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩, fun g => hu g⟩)
      (EndA := fun γ hγ => by
        obtain ⟨v, hv⟩ := modelA1_end (k := k) (VJ := VJ) (V₀ := V₀) hVJ3 γ hγ
        exact ⟨diagYHom k VJ V₀ v, MonoidHom.mem_range.mpr ⟨v, rfl⟩, fun a => hv a⟩)
      (H1 := fun δ hδ => modelA1_h1 (k := k) (VJ := VJ) (V₀ := V₀) hVJ4 δ hδ)
      (α := transportAutOf hAK α) (hαJ := hαJ)
      (hαA := alpha_preserves_pCore hAK
        ((pCoreOf_modelP1 (k := k) (VJ := VJ) (V₀ := V₀) hVJ2).symm) α)
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
  refine ⟨diagE u * diagY v, ?_⟩
  intro p
  have htrans_eq : transportAutOf hAK α ((MulEquiv.subgroupCongr hAK).symm p) =
      (MulEquiv.subgroupCongr hAK).symm (α p) := by
    simp [transportAutOf, MulEquiv.trans_apply]
  have htrans_coe : (((transportAutOf hAK α ((MulEquiv.subgroupCongr hAK).symm p) :
      ↥(modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀))) =
      ((α p : ↥(modelP1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) := by
    rw [htrans_eq, MulEquiv.subgroupCongr_symm_apply]
  have hp_coe : ((((MulEquiv.subgroupCongr hAK).symm p :
      ↥(modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀))) =
      (p : SpecialLinearGroup k (VJ × V₀)) :=
    MulEquiv.subgroupCongr_symm_apply hAK p
  have h := hconj ((MulEquiv.subgroupCongr hAK).symm p)
  rw [htrans_coe, hp_coe] at h
  exact h

theorem exists_conj_of_mulAut_modelP2 (hm : 3 ≤ Module.finrank E VJ)
    (hc : 2 ≤ Module.finrank k E) (α : MulAut ↥(modelP2 k VJ V₀))
    (hα : ∀ j : ↥(modelP2 k VJ V₀),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α j = j) :
    ∃ z : (VJ × V₀) ≃ₗ[k] (VJ × V₀), ∀ p : ↥(modelP2 k VJ V₀),
      SpecialLinearGroup.toLinearEquiv ((α p : ↥(modelP2 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) =
        z * SpecialLinearGroup.toLinearEquiv (p : SpecialLinearGroup k (VJ × V₀)) * z⁻¹ := by
  have hVJ4 : 4 ≤ Module.finrank k VJ := by
    rw [← Module.finrank_mul_finrank k E VJ]
    have h := Nat.mul_le_mul hc hm
    omega
  have hVJ3 : 3 ≤ Module.finrank k VJ := by omega
  have hVJ2 : 2 ≤ Module.finrank k VJ := by omega
  have hAK : modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀ = modelP2 k VJ V₀ :=
    modelA2_sup_modelK1 (k := k) (VJ := VJ) (V₀ := V₀)
  have hαJ : ∀ j : ↥(modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ →
        transportAutOf hAK α j = j := by
    intro j hj
    apply (MulEquiv.subgroupCongr hAK).injective
    rw [subgroupCongr_transportAutOf]
    exact hα (MulEquiv.subgroupCongr hAK j) (by
      rw [MulEquiv.subgroupCongr_apply]
      exact hj)
  obtain ⟨s, hs, y, hy, hconj⟩ :=
    exists_conj_of_aut_semidirect
      (ε := SpecialLinearGroup.toLinearEquiv (R := k) (V := VJ × V₀))
      (hε := SpecialLinearGroup.toLinearEquiv_injective (R := k) (V := VJ × V₀))
      (A := modelA2 k VJ V₀) (K := modelK1 k VJ V₀) (J := modelJ k E VJ V₀)
      (Sg := (diagEHom k E VJ V₀).range) (Yg := (diagYHom k VJ V₀).range)
      (hAK := modelA2_inf_modelK1 (k := k) (VJ := VJ) (V₀ := V₀))
      (hAc := fun a ha b hb => modelA2_mul_comm (k := k) (VJ := VJ) (V₀ := V₀) ha hb)
      (hKA := fun g hg a ha => modelK1_conj_mem_modelA2 (k := k) (VJ := VJ) (V₀ := V₀) hg ha)
      (hJK := modelJ_le_modelK1 (k := k) (E := E) (VJ := VJ) (V₀ := V₀))
      (hCA := fun a ha h => modelA2_eq_one_of_commute_modelJ (k := k) (E := E) (VJ := VJ)
        (V₀ := V₀) (by omega) ha h)
      (hSA := fun s hs a ha => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        obtain ⟨a', ha', h⟩ :=
          diagE_conj_mem_modelA2 (k := k) (VJ := VJ) (V₀ := V₀) u ha
        exact ⟨a', ha', h⟩)
      (hSK := fun s hs g hg => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        obtain ⟨g', hg', h⟩ :=
          diagE_conj_mem_modelK1 (k := k) (VJ := VJ) (V₀ := V₀) u hg
        exact ⟨g', hg', h⟩)
      (hSJ := fun s hs j hj => by
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
        exact diagE_comm_modelJ (k := k) (VJ := VJ) (V₀ := V₀) u hj)
      (hYA := fun y hy a ha => by
        obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
        obtain ⟨a', ha', h⟩ :=
          diagY_conj_mem_modelA2 (k := k) (VJ := VJ) (V₀ := V₀) v ha
        exact ⟨a', ha', h⟩)
      (hYK := fun y hy g hg => by
        obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
        exact diagY_comm_modelK1 (k := k) (VJ := VJ) (V₀ := V₀) v hg)
      (H12 := fun β hβ => by
        obtain ⟨u, hu⟩ := exists_diagE_of_mulAut_modelK1 (k := k) (E := E) (VJ := VJ)
          (V₀ := V₀) hm β hβ
        exact ⟨diagEHom k E VJ V₀ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩, fun g => hu g⟩)
      (EndA := fun γ hγ => by
        obtain ⟨v, hv⟩ := modelA2_end (k := k) (VJ := VJ) (V₀ := V₀) hVJ3 γ hγ
        exact ⟨diagYHom k VJ V₀ v, MonoidHom.mem_range.mpr ⟨v, rfl⟩, fun a => hv a⟩)
      (H1 := fun δ hδ => modelA2_h1 (k := k) (VJ := VJ) (V₀ := V₀) hVJ4 δ hδ)
      (α := transportAutOf hAK α) (hαJ := hαJ)
      (hαA := alpha_preserves_pCore hAK
        ((pCoreOf_modelP2 (k := k) (VJ := VJ) (V₀ := V₀) hVJ2).symm) α)
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
  refine ⟨diagE u * diagY v, ?_⟩
  intro p
  have htrans_eq : transportAutOf hAK α ((MulEquiv.subgroupCongr hAK).symm p) =
      (MulEquiv.subgroupCongr hAK).symm (α p) := by
    simp [transportAutOf, MulEquiv.trans_apply]
  have htrans_coe : (((transportAutOf hAK α ((MulEquiv.subgroupCongr hAK).symm p) :
      ↥(modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀))) =
      ((α p : ↥(modelP2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) := by
    rw [htrans_eq, MulEquiv.subgroupCongr_symm_apply]
  have hp_coe : ((((MulEquiv.subgroupCongr hAK).symm p :
      ↥(modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀))) =
      (p : SpecialLinearGroup k (VJ × V₀)) :=
    MulEquiv.subgroupCongr_symm_apply hAK p
  have h := hconj ((MulEquiv.subgroupCongr hAK).symm p)
  rw [htrans_coe, hp_coe] at h
  exact h

end CFSG.LinearAlgebra.RootGroupSL
