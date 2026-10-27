module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG
open scoped commutatorElement

universe u

@[expose] def HasCompOrSolv (G : Type*) [Group G] : Prop :=
  Group.IsSolvable G ∨ ∃ K : Subgroup G, IsComponent K

theorem solvableOrComponent_iff (X : Type) [Group X] (τ : X) :
    SolvableOrComponent X τ ↔ HasCompOrSolv (centralizer ({τ} : Set X)) := Iff.rfl

theorem HasCompOrSolv.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : HasCompOrSolv G) : HasCompOrSolv G' := by
  rcases h with hs | ⟨K, hK⟩
  · exact Or.inl (solvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · exact Or.inr ⟨K.map e.toMonoidHom, LocalCores.isComponent_map_mulEquiv e hK⟩

theorem isComponent_map_of_normal_range {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) [f.range.Normal] {K : Subgroup G} (hK : IsComponent K) :
    IsComponent (K.map f) := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  have h1 : IsComponent (K.map e.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e hK
  have h2 := CatLeafProof.isComponent_map_subtype_of_normal (N := f.range) h1
  have : (K.map e.toMonoidHom).map f.range.subtype = K.map f := by
    rw [Subgroup.map_map]
    rfl
  rwa [this] at h2

theorem range_inl_eq_ker_snd (G₁ G₂ : Type*) [Group G₁] [Group G₂] :
    (MonoidHom.inl G₁ G₂).range = (MonoidHom.snd G₁ G₂).ker := by
  ext ⟨a, b⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.inl_apply, MonoidHom.coe_snd,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, -, rfl⟩
    rfl
  · intro h
    exact ⟨a, rfl, h.symm⟩

theorem range_inr_eq_ker_fst (G₁ G₂ : Type*) [Group G₁] [Group G₂] :
    (MonoidHom.inr G₁ G₂).range = (MonoidHom.fst G₁ G₂).ker := by
  ext ⟨a, b⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.inr_apply, MonoidHom.coe_fst,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, rfl, -⟩
    rfl
  · intro h
    exact ⟨b, h.symm, rfl⟩

theorem HasCompOrSolv.prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] (h₁ : HasCompOrSolv G₁)
    (h₂ : HasCompOrSolv G₂) : HasCompOrSolv (G₁ × G₂) := by
  rcases h₁ with hs₁ | ⟨K, hK⟩
  · rcases h₂ with hs₂ | ⟨K, hK⟩
    · exact Or.inl (inferInstance)
    · haveI : (MonoidHom.inr G₁ G₂).range.Normal := by
        rw [range_inr_eq_ker_fst]; infer_instance
      exact Or.inr ⟨_, isComponent_map_of_normal_range (MonoidHom.inr G₁ G₂)
        (fun a b h => (Prod.ext_iff.1 h).2) hK⟩
  · haveI : (MonoidHom.inl G₁ G₂).range.Normal := by
      rw [range_inl_eq_ker_snd]; infer_instance
    exact Or.inr ⟨_, isComponent_map_of_normal_range (MonoidHom.inl G₁ G₂)
      (fun a b h => (Prod.ext_iff.1 h).1) hK⟩

theorem hasCompOrSolv_GL (n : ℕ) (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n) :
    HasCompOrSolv (Matrix.GeneralLinearGroup (Fin n) K) := by
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
  · exact Or.inl (CatalogueBGeneralLinear.generalLinear_small_solvable n K hsmall)
  · refine Or.inr ⟨CatalogueBGeneralLinear.specialLinearRange n K,
      (CatalogueBGeneralLinear.retained_quasisimple_and_pComponents n K hn hsmall).2.1, ?_⟩
    exact Subgroup.Normal.isSubnormal inferInstance

theorem HasCompOrSolv.of_inj {H G : Type*} [Group H] [Group G] (ρ : H →* G)
    (hρ : Function.Injective ρ) [hn : ρ.range.Normal] (hc : commutator G ≤ ρ.range)
    (h : HasCompOrSolv G) : HasCompOrSolv H := by
  rcases h with hs | ⟨K, hK⟩
  · haveI := hs
    exact Or.inl (solvable_of_solvable_injective hρ)
  · have hKr : K ≤ ρ.range := by
      calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.mp hK.1.1).symm
        _ ≤ commutator G := Subgroup.commutator_mono le_top le_top
        _ ≤ ρ.range := hc
    have h1 : IsComponent (K.subgroupOf ρ.range) :=
      ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKr).symm hK.1,
        hK.2.subgroupOf⟩
    exact Or.inr ⟨_, LocalCores.isComponent_map_mulEquiv (MonoidHom.ofInjective hρ).symm h1⟩

section Descent

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)

@[expose] def centralizerInjMap (h : H) :
    centralizer ({h} : Set H) →* centralizer ({ι h} : Set G) :=
  ((ι.comp (centralizer ({h} : Set H)).subtype).codRestrict _ fun c => by
    have hc := mem_centralizer_singleton_iff.1 c.2
    exact mem_centralizer_singleton_iff.2 (by
      show ι c * ι h = ι h * ι c
      rw [← map_mul, ← map_mul, hc]))

variable {ι}

theorem centralizerInjMap_injective (hι : Function.Injective ι) (h : H) :
    Function.Injective (centralizerInjMap ι h) := by
  intro a b hab
  apply Subtype.ext
  apply hι
  exact congrArg Subtype.val hab

theorem exists_mem_centralizer_of_range (hι : Function.Injective ι) (h : H) {g : G}
    (hg : g ∈ centralizer ({ι h} : Set G)) (hr : g ∈ ι.range) :
    ∃ c : centralizer ({h} : Set H), centralizerInjMap ι h c = ⟨g, hg⟩ := by
  obtain ⟨c, rfl⟩ := hr
  have hc := mem_centralizer_singleton_iff.1 hg
  have : c * h = h * c := hι (by rw [map_mul, map_mul]; exact hc)
  exact ⟨⟨c, mem_centralizer_singleton_iff.2 this⟩, rfl⟩

theorem solvableOrComponent_of_inj {H G : Type} [Group H] [Group G] (ι : H →* G)
    (hι : Function.Injective ι) (hn : ι.range.Normal) (hc : commutator G ≤ ι.range) (h : H)
    (hs : SolvableOrComponent G (ι h)) : SolvableOrComponent H h := by
  set ρ := centralizerInjMap ι h with hρ
  have hρinj : Function.Injective ρ := centralizerInjMap_injective hι h
  have hρn : ρ.range.Normal := by
    refine ⟨fun n hn' g => ?_⟩
    obtain ⟨c, rfl⟩ := hn'
    have hg1 : (g : G) * ι c * (g : G)⁻¹ ∈ ι.range := hn.conj_mem _ ⟨c, rfl⟩ g
    have hgc' : Commute (g : G) (ι h) := mem_centralizer_singleton_iff.1 g.2
    have hcc' : Commute (ι (c : H)) (ι h) := mem_centralizer_singleton_iff.1 (ρ c).2
    have hg2 : (g : G) * ι c * (g : G)⁻¹ ∈ centralizer ({ι h} : Set G) :=
      mem_centralizer_singleton_iff.2 ((hgc'.mul_left hcc').mul_left hgc'.inv_left)
    obtain ⟨c', hc'⟩ := exists_mem_centralizer_of_range hι h hg2 hg1
    exact ⟨c', Subtype.ext (congrArg Subtype.val hc')⟩
  have hcomm : commutator (centralizer ({ι h} : Set G)) ≤ ρ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : ((⁅a, b⁆ : centralizer ({ι h} : Set G)) : G) ∈ ι.range := by
      apply hc
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top (a : G)) (mem_top (b : G))
    obtain ⟨c', hc'⟩ := exists_mem_centralizer_of_range hι h (⁅a, b⁆ : centralizer ({ι h} : Set G)).2 h1
    exact ⟨c', hc'⟩
  haveI := hρn
  exact HasCompOrSolv.of_inj ρ hρinj hcomm hs

end Descent

end CFSG.ComponentClassification.CatFC.DS81
