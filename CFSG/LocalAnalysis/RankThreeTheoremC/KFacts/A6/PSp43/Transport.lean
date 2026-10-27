module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

section Inj

variable {G G' : Type*} [Group G] [Group G'] {ι : G →* G'}

theorem map_centralizer_singleton (hι : Function.Injective ι) (z : G) :
    (centralizer ({z} : Set G)).map ι = ι.range ⊓ centralizer ({ι z} : Set G') := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hι (by rw [map_mul, map_mul]; exact hy), rfl⟩

theorem comm_of_map {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ A.map ι, ∀ y ∈ A.map ι, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hA a ha b hb]

end Inj

theorem comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  have := (isMulCommutative_iff.1 hA.1) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem pCoreOf_le_self {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    CFSG.Open.pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

section Model

variable {T : Type*} [Group T] {L : Subgroup T}

noncomputable abbrev modelHom (e : L ≃* PSp43) : L →* Equiv.Perm (Fin 45) :=
  P.subtype.comp (psiEquiv.toMonoidHom.comp e.toMonoidHom)

theorem modelHom_injective (e : L ≃* PSp43) : Function.Injective (modelHom e) :=
  P.subtype_injective.comp (psiEquiv.injective.comp e.injective)

theorem range_modelHom (e : L ≃* PSp43) : (modelHom e).range = P := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (psiEquiv (e y)).2
  · intro hx
    refine ⟨e.symm (psiEquiv.symm ⟨x, hx⟩), ?_⟩
    simp

theorem modelHom_mem (e : L ≃* PSp43) (y : L) : modelHom e y ∈ P :=
  (range_modelHom e) ▸ ⟨y, rfl⟩

theorem map_subtype_centralizer (z : L) :
    (centralizer ({z} : Set L)).map L.subtype = L ⊓ centralizer ({(z : T)} : Set T) := by
  rw [map_centralizer_singleton L.subtype_injective, L.range_subtype]
  rfl

theorem map_model_centralizer (e : L ≃* PSp43) (z : L) :
    (centralizer ({z} : Set L)).map (modelHom e) =
      P ⊓ centralizer ({modelHom e z} : Set (Equiv.Perm (Fin 45))) := by
  rw [map_centralizer_singleton (modelHom_injective e), range_modelHom]

theorem card_model_centralizer (e : L ≃* PSp43) (z : L) :
    Nat.card ↥(P ⊓ centralizer ({modelHom e z} : Set (Equiv.Perm (Fin 45)))) =
      Nat.card ↥(L ⊓ centralizer ({(z : T)} : Set T)) := by
  rw [← map_model_centralizer, ← map_subtype_centralizer,
    Subgroup.card_map_of_injective (modelHom_injective e),
    Subgroup.card_map_of_injective L.subtype_injective]

theorem map_comap_subtype {A : Subgroup T} (hAL : A ≤ L) :
    (A.comap L.subtype).map L.subtype = A := by
  rw [Subgroup.map_comap_eq, L.range_subtype]
  exact inf_of_le_right hAL

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
