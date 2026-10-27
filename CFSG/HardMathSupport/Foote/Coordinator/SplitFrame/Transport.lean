module

public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Open CFSG.LieType.SeitzGeneration

theorem planeGen_of_native_closure {C N : Type*} [Group C] [Group N] (e : C ≃* N)
    (hZ : Subgroup.center N = ⊥) {p : ℕ}
    (hnat : ∀ E₀ : Subgroup N, (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range) : PlaneGen E := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  set E₀C : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hE₀C
  have hmap : E₀C.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hin
  set E₀ : Subgroup N := E₀C.map e.toMonoidHom with hE₀
  have hE₀p : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : (MulAut.conj : C →* MulAut C) (c ^ p) = 1 := by
      rw [map_pow]
      exact hE.2 _ hc
    have h2 : c ^ p = 1 := hinj (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, ← hcard, ← hmap,
      Subgroup.card_map_of_injective hinj]
  have htop := hnat E₀ hE₀p hE₀c
  set T : Set C := {k | ∃ c ∈ E₀C, c ≠ 1 ∧ Commute k c} with hT
  have himage : e.toMonoidHom '' T = {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} := by
    ext k
    constructor
    · rintro ⟨k₀, ⟨c, hc, hc1, hkc⟩, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, fun h => hc1 (e.injective (h.trans (map_one e).symm)),
        hkc.map e.toMonoidHom⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hx1, hkx⟩
      refine ⟨e.symm k, ⟨c, hc, fun h => hx1 (by rw [h]; exact map_one e.toMonoidHom), ?_⟩, ?_⟩
      · have := hkx.map e.symm.toMonoidHom
        simpa using this
      · simp
  have hT : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e.toMonoidHom k ∈ Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [← himage, ← MonoidHom.map_closure] at hk
    obtain ⟨k₀, hk₀, hk₀e⟩ := hk
    have : k₀ = k := e.injective hk₀e
    rw [← this]
    exact hk₀
  have hle : Subgroup.closure T ≤ planeClosure E := by
    rw [Subgroup.closure_le]
    rintro k ⟨c, hc, hc1, hkc⟩
    refine Subgroup.subset_closure ⟨MulAut.conj c, hc, fun h => hc1 ?_, ?_⟩
    · exact hinj (h.trans (map_one _).symm)
    · rw [MulAut.conj_apply, ← hkc.eq]
      group
  rw [PlaneGen, eq_top_iff, ← hT]
  exact hle

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
