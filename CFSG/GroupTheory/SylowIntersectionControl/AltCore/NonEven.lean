module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.StarOrbit
import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α] {H : Subgroup (Perm α)}

omit [DecidableEq α] in
theorem not_isEvenSet_compl (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) :
    ¬ IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ := by
  intro hc
  classical
  have hrad := isRadical_of_isPIsolatedOver hH hiso
  have hO : normalizer (H : Set (Perm α)) ≤
      setStab (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ := by
    rw [setStab_compl]
    exact orbit_mem_setStab x₀
  obtain ⟨z, hz, hze⟩ := exists_isEvenSet_orbit hH hrad _ _ rfl hO hc
  exact hz (orbit_eq_iff.mp (orbit_eq_of_isEvenSet hH hiso hze he))

omit [DecidableEq α] in
theorem eq_restrSub_of_isPGroup (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    [DecidablePred (· ∈ (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ)]
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) {Q : Subgroup (Perm α)}
    (hQ : IsPGroup 2 Q) (hQO : Q ≤ fixOutside (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ)
    (hPQ : restrSub (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ H ≤ Q) :
    Q = restrSub (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrad := isRadical_of_isPIsolatedOver hH hiso
  have hO : normalizer (H : Set (Perm α)) ≤
      setStab (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ := by
    rw [setStab_compl]
    exact orbit_mem_setStab x₀
  refine le_antisymm (le_of_inf_normalizer_le_of_isPGroup hQ hPQ fun y hy => ?_) hPQ
  obtain ⟨hyQ, hyN⟩ := mem_inf.mp hy
  have hyH : y ∈ normalizer (H : Set (Perm α)) :=
    mem_normalizer_of_mem_fixOutside hH hrad hO (hQO hyQ) hyN
  by_cases hyH' : y ∈ H
  · rw [← restrHom_eq_self (hQO hyQ) (fixOutside_le_setStab _ (hQO hyQ))]
    exact restrHom_mem_restrSub hyH'
  · exfalso
    obtain ⟨m, hm⟩ := hQ ⟨y, hyQ⟩
    obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem (m := m)
      (by simpa using congrArg Subtype.val hm) hyH'
    exact not_isEvenSet_compl hH hiso he ⟨_, pow_mem hyH _, pow_mem (hQO hyQ) _, hk, hk2⟩

private theorem map_comap_ofSubtype {C : Set α} [DecidablePred (· ∈ C)] {P : Subgroup (Perm α)}
    (hP : P ≤ fixOutside C) : (P.comap (ofSubtype : Perm C →* Perm α)).map ofSubtype = P := by
  refine le_antisymm (map_comap_le _ _) fun g hg => ?_
  have hr : g ∈ (ofSubtype : Perm C →* Perm α).range := mem_range_ofSubtype_iff.mpr fun z hz => by
    by_contra h
    exact (mem_support.mp hz) (hP hg z h)
  obtain ⟨g', rfl⟩ := hr
  exact ⟨g', hg, rfl⟩

private theorem fusionIsSylowIn_comap (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    [DecidablePred (· ∈ (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ)]
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) :
    CFSG.Open.fusionIsSylowIn 2 ((restrSub (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ H).comap
      (ofSubtype : Perm ↥(orbit (normalizer (H : Set (Perm α))) x₀)ᶜ →* Perm α)) ⊤ := by
  refine ⟨le_top, (isPGroup_restrSub hH).comap_of_injective _ ofSubtype_injective,
    fun Q _ hQ hPQ => ?_⟩
  have hmap := eq_restrSub_of_isPGroup hH hiso he (hQ.map _)
    (by rintro _ ⟨g', -, rfl⟩ z hz; exact ofSubtype_apply_of_not_mem g' hz)
    (by rw [← map_comap_ofSubtype restrSub_le_fixOutside]; exact map_mono hPQ)
  rw [← hmap, comap_map_eq_self_of_injective ofSubtype_injective]

private theorem image_orbit_comap {C : Set α} [DecidablePred (· ∈ C)]
    (hC : normalizer (H : Set (Perm α)) ≤ setStab C) {x : α} (hx : x ∈ C) :
    Subtype.val '' orbit ((restrSub C H).comap (ofSubtype : Perm C →* Perm α)) (⟨x, hx⟩ : C) =
      orbit H x := by
  ext y
  constructor
  · rintro ⟨_, ⟨⟨g', ⟨⟨h, hs⟩, hh, he⟩⟩, rfl⟩, rfl⟩
    refine ⟨⟨h, mem_subgroupOf.mp hh⟩, ?_⟩
    change h x = (g' ⟨x, hx⟩ : α)
    rw [← ofSubtype_apply_of_mem g' hx, ← he, restrHom_apply_of_mem _ hx]
  · rintro ⟨⟨h, hh⟩, rfl⟩
    have hr := restrHom_mem_restrSub (O := C) (h := ⟨h, hC (le_normalizer hh)⟩) hh
    rw [← map_comap_ofSubtype restrSub_le_fixOutside] at hr
    obtain ⟨g', hg', hge⟩ := hr
    refine ⟨g' • ⟨x, hx⟩, ⟨⟨g', hg'⟩, rfl⟩, ?_⟩
    change (g' ⟨x, hx⟩ : α) = h x
    rw [← ofSubtype_apply_of_mem g' hx, hge, restrHom_apply_of_mem _ hx]

theorem orbit_eq_of_card_orbit_eq (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) {x y : α}
    (hx : x ∉ orbit (normalizer (H : Set (Perm α))) x₀)
    (hy : y ∉ orbit (normalizer (H : Set (Perm α))) x₀)
    (hxy : Nat.card (orbit H x) = Nat.card (orbit H y)) : orbit H x = orbit H y := by
  classical
  have hC : normalizer (H : Set (Perm α)) ≤
      setStab (orbit (normalizer (H : Set (Perm α))) x₀)ᶜ := by
    rw [setStab_compl]
    exact orbit_mem_setStab x₀
  have h1 := image_orbit_comap hC (x := x) hx
  have h2 := image_orbit_comap hC (x := y) hy
  have heq := CFSG.Holt.H78.orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_top
    (fusionIsSylowIn_comap hH hiso he) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (by
      rw [← Nat.card_image_of_injective Subtype.val_injective,
        ← Nat.card_image_of_injective Subtype.val_injective (orbit _ (⟨y, hy⟩ : _)), h1, h2]
      exact hxy)
  rw [← h1, ← h2, heq]

theorem orbit_normalizer_eq_orbit (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) {x : α}
    (hx : x ∉ orbit (normalizer (H : Set (Perm α))) x₀) :
    orbit (normalizer (H : Set (Perm α))) x = orbit H x := by
  refine le_antisymm ?_ fun y ⟨⟨h, hh⟩, hy⟩ => ⟨⟨h, le_normalizer hh⟩, hy⟩
  rintro _ ⟨⟨n, hn⟩, rfl⟩
  have hnx : n x ∉ orbit (normalizer (H : Set (Perm α))) x₀ := fun h =>
    hx ((orbit_mem_setStab x₀ hn x).mp h)
  have heq := orbit_eq_of_card_orbit_eq hH hiso he hnx hx (card_orbit_eq_of_normalizer hn x)
  rw [← heq]
  exact mem_orbit_self _

end CFSG.GroupTheory.AltCore
