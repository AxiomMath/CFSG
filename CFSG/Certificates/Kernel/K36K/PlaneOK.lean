module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporExc

public section

namespace CFSG.KD.K36K

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UCK.Spor

variable {X : Type*} [Group X] {G : Subgroup X}

theorem mem_closure_subtype {S : Set X} (hS : S ⊆ G) {x : ↥G}
    (hx : (x : X) ∈ Subgroup.closure S) : x ∈ Subgroup.closure {y : ↥G | (y : X) ∈ S} := by
  have hmap : (Subgroup.closure {y : ↥G | (y : X) ∈ S}).map G.subtype = Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hz
      exact ⟨⟨z, hS hz⟩, hz, rfl⟩
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← Subtype.ext hyx]

theorem planeOK_of_gen_facts {A : Subgroup ↥G} {Y : Subgroup X}
    (hAY : ∀ x : ↥G, x ∈ A ↔ (x : X) ∈ Y) (hYG : Y ≤ G) {Γ : Set X} (hΓG : Γ ⊆ G)
    (hGΓ : G ≤ Subgroup.closure Γ) (hΓ : ∀ g ∈ Γ, ∃ u ∈ Y, u ≠ 1 ∧ u * g = g * u) :
    PlaneOK A := by
  refine planeOK_of_gens (Γ := {x : ↥G | (x : X) ∈ Γ}) (fun x hx => ?_) ?_
  · obtain ⟨u, hu, hu1, hux⟩ := hΓ _ hx
    exact ⟨⟨u, hYG hu⟩, (hAY _).2 hu, fun h1 => hu1 (congrArg Subtype.val h1), Subtype.ext hux⟩
  · rw [eq_top_iff]
    intro x _
    exact mem_closure_subtype hΓG (hGΓ x.2)

theorem planeOK_of_exc_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup ↥G}
    {Y : Subgroup X} (hAY : ∀ x : ↥G, x ∈ A ↔ (x : X) ∈ Y) (hYG : Y ≤ G)
    (hAe : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hnorm : ∀ k ∈ G, (∃ u ∈ Y, u ≠ 1 ∧ u * k = k * u) → ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hcent : ∀ k ∈ G, (∀ y ∈ Y, k * y = y * k) → k ∈ Y) {cs : List X} {y : X} {f f' : ℕ → X}
    (hcs : ∀ c ∈ cs, c ∈ G ∧ ∃ u ∈ Y, u ≠ 1 ∧ u * c = c * u) (hy : y ∈ G)
    (hf : ∀ k < 2, f k ∈ Subgroup.closure {c | c ∈ cs} ∧ f' k ∈ Subgroup.closure {c | c ∈ cs} ∧
      y * f k = f' k * y)
    (hgen : G ≤ Subgroup.closure ({c | c ∈ cs} ∪ {y}))
    (hcen : ∀ t ∈ G, t * f 0 = f 0 * t → t * f 1 = f 1 * t → t = 1) : PlaneOK A := by
  have hcsG : {c | c ∈ cs} ⊆ (G : Set X) := fun c hc => (hcs c hc).1
  have hclG : Subgroup.closure {c | c ∈ cs} ≤ G := (Subgroup.closure_le G).2 hcsG
  set C : Set ↥G := {x | (x : X) ∈ cs} with hCdef
  have hC : C ⊆ centSet A := fun x hx => by
    obtain ⟨-, u, hu, hu1, hux⟩ := hcs _ hx
    exact ⟨⟨u, hYG hu⟩, (hAY _).2 hu, fun h1 => hu1 (congrArg Subtype.val h1), Subtype.ext hux⟩
  have hmemC : ∀ {x : X} (hx : x ∈ Subgroup.closure {c | c ∈ cs}),
      (⟨x, hclG hx⟩ : ↥G) ∈ Subgroup.closure C := fun hx => mem_closure_subtype hcsG hx
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  set yG : ↥G := ⟨y, hy⟩ with hyG
  have hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hAp : IsPGroup p A := IsPGroup.of_card hAc
  refine planeOK_of_exc hp hp2 hAcomm hAp ?_ ?_ hC (hmemC h0.1) (hmemC h1.1) (hmemC h0.2.1)
    (hmemC h1.2.1) (y := yG) (Subtype.ext h0.2.2) (Subtype.ext h1.2.2) ?_ ?_
  · rintro k ⟨a, haA, ha1, hak⟩ x hx
    rw [hAY] at hx ⊢
    have := hnorm k k.2 ⟨a, (hAY a).1 haA, fun h => ha1 (Subtype.ext h),
      congrArg Subtype.val hak⟩ x hx
    simpa using this
  · intro k hk
    rw [hAY]
    refine hcent k k.2 fun y hy => ?_
    exact congrArg Subtype.val (hk ⟨y, hYG hy⟩ ((hAY _).2 hy))
  · intro k hk0 hk1
    exact Subtype.ext (hcen k k.2 (congrArg Subtype.val hk0) (congrArg Subtype.val hk1))
  · have hS : ({c | c ∈ cs} ∪ {y} : Set X) ⊆ G := by
      rintro c (hc | hc)
      · exact hcsG hc
      · rw [Set.mem_singleton_iff] at hc
        rw [hc]
        exact hy
    have hset : {z : ↥G | (z : X) ∈ ({c | c ∈ cs} ∪ {y} : Set X)} = C ∪ {yG} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, hCdef, hyG,
        Subtype.ext_iff]
    rw [eq_top_iff, ← hset]
    intro x _
    exact mem_closure_subtype hS (hgen x.2)

end CFSG.KD.K36K

end
