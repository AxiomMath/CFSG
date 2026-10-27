module

public import CFSG.LieType.SeitzGeneration.ExcTorusSylow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem isMulCommutative_map {G H : Type*} [Group G] [Group H] (f : G →* H) {T : Subgroup G}
    (hT : IsMulCommutative T) : IsMulCommutative (T.map f) := by
  refine IsMulCommutative.of_comm fun a b => ?_
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
  apply Subtype.ext
  show (a : H) * b = b * a
  have := hT
  rw [← hxa, ← hyb, ← map_mul, ← map_mul, setLike_mul_comm hx hy]

theorem isMulCommutative_of_mulEquiv_prod {G A B : Type*} [Group G] [CommGroup A] [CommGroup B]
    (e : G ≃* A × B) : IsMulCommutative G :=
  IsMulCommutative.of_comm fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])

theorem SylowTorus.of_embedding {C G : Type*} [Group C] [Group G] (ι : C →* G)
    (hι : Function.Injective ι) {p m : ℕ} {T E : Subgroup G} (hT : IsMulCommutative T)
    (hTr : T ≤ ι.range)
    (hconj : ∀ P : Subgroup C, IsPGroup p P →
      ∃ c : C, (P.map (MulAut.conj c).toMonoidHom).map ι ≤ T)
    (hE : ∀ x, x ∈ E ↔ x ∈ T ∧ x ^ p = 1) (hEcard : Nat.card E = p ^ m) : SylowTorus C p m := by
  have hET : E ≤ T := fun x hx => ((hE x).1 hx).1
  have hcomm : ∀ a b : C, ι a ∈ T → ι b ∈ T → a * b = b * a := fun a b ha hb => by
    have := hT
    apply hι
    rw [map_mul, map_mul]
    exact setLike_mul_comm ha hb
  refine ⟨⟨T.comap ι, E.comap ι, ?_, ?_, Subgroup.comap_mono hET, ?_, ?_, ?_⟩⟩
  · exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b a.2 b.2)
  · intro P hP
    obtain ⟨c, hc⟩ := hconj P hP
    refine ⟨c⁻¹, fun x hx => ?_⟩
    refine Subgroup.mem_map.2 ⟨(MulAut.conj c).toMonoidHom x, ?_, ?_⟩
    · exact hc ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
      group
  · intro x hx hxp
    refine (hE (ι x)).2 ⟨hx, ?_⟩
    rw [← map_pow, hxp, map_one]
  · refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b (hET a.2) (hET b.2)), ?_⟩
    intro x hx
    have hxp := ((hE (ι x)).1 hx).2
    apply hι
    rw [map_pow, hxp, map_one]
  · have hmap : (E.comap ι).map ι = E := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 (hET.trans hTr)
    rw [← Subgroup.card_map_of_injective hι, hmap, hEcard]

end CFSG.LieType.SeitzGeneration
