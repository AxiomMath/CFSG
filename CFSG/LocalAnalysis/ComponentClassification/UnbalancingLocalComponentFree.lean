module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.LocalCores CFSG.ComponentClassification.OuterAutomorphisms

namespace ComponentFree

theorem not_isComponent_of_pow {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsComponent B) (h2 : ∀ x ∈ B, ∃ k : ℕ, x ^ 2 ^ k = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 B := fun x => by
    obtain ⟨k, hk⟩ := h2 x x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have : Nontrivial B := isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect B := hB.1.1
  exact Group.IsPerfect.not_isNilpotent B hP.isNilpotent

theorem no_component_of_two_radical {M : Type*} [Group M] [Finite M] {X R : Subgroup M}
    (hRX : R ≤ X) (hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ X, x ∈ Subgroup.centralizer (R : Set M) → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (B : Subgroup X) : ¬ IsComponent B := by
  intro hB
  have hRn : (R.subgroupOf X).Normal := ⟨fun r hr x => by
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hnorm x x.2) r).mp hr⟩
  rcases component_normal_subgroup hB hRn with hle | hcomm
  · refine not_isComponent_of_pow hB fun b hb => ?_
    obtain ⟨k, hk⟩ := hR _ (Subgroup.mem_subgroupOf.mp (hle hb))
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · refine not_isComponent_of_pow hB fun b hb => ?_
    have hbc : (b : M) ∈ Subgroup.centralizer (R : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hb) ⟨r, hRX hr⟩
        (Subgroup.mem_subgroupOf.mpr hr)
      exact congrArg Subtype.val h1
    obtain ⟨k, hk⟩ := hcent _ b.2 hbc
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem no_component_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ B : Subgroup Y, ¬ IsComponent B) (B : Subgroup X) : ¬ IsComponent B := fun hB =>
  hY _ ((component_isomorphism e).1 B |>.mp hB)

theorem map_centralizer_eq {G M : Type*} [Group G] [Group M] {φ : G →* M}
    (hφ : Function.Injective φ) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map φ =
      φ.range ⊓ Subgroup.centralizer ({φ g} : Set M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · intro hy
    obtain ⟨⟨x, rfl⟩, hxc⟩ := Subgroup.mem_inf.mp hy
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hxc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hφ hxc

@[expose] noncomputable def centralizerRangeEquiv {G M : Type*} [Group G] [Group M] {φ : G →* M}
    (hφ : Function.Injective φ) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃*
      ↥(φ.range ⊓ Subgroup.centralizer ({φ g} : Set M)) :=
  ((Subgroup.centralizer ({g} : Set G)).equivMapOfInjective φ hφ).trans
    (MulEquiv.subgroupCongr (map_centralizer_eq hφ g))

theorem no_component_centralizer {T P : Type*} [Group T] [Group P] (e : T ≃* P)
    (hconj : Function.Injective (MulAut.conj : P →* MulAut P)) (t : T)
    (h : ∀ B : Subgroup ↥(inner P ⊓ Subgroup.centralizer ({MulAut.conj (e t)} : Set (MulAut P))),
      ¬ IsComponent B) :
    ∀ B : Subgroup (Subgroup.centralizer ({t} : Set T)), ¬ IsComponent B := by
  have hφ : Function.Injective ((MulAut.conj : P →* MulAut P).comp e.toMonoidHom) :=
    hconj.comp e.injective
  have hrange : ((MulAut.conj : P →* MulAut P).comp e.toMonoidHom).range = inner P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
    rfl
  have hX : ((MulAut.conj : P →* MulAut P).comp e.toMonoidHom).range ⊓
      Subgroup.centralizer ({((MulAut.conj : P →* MulAut P).comp e.toMonoidHom) t} :
        Set (MulAut P)) =
      inner P ⊓ Subgroup.centralizer ({MulAut.conj (e t)} : Set (MulAut P)) := by
    rw [hrange]
    rfl
  exact no_component_of_mulEquiv
    ((centralizerRangeEquiv hφ t).trans (MulEquiv.subgroupCongr hX)) h

end ComponentFree

end CFSG.ComponentClassification.UnbalancingLocal
