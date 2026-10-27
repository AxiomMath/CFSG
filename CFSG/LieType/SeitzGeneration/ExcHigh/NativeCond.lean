module

public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.LieType.SeitzGeneration

@[expose] def NormalizesRGroup {G : Type*} [Group G] (r : ℕ) (E₀ : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup r U ∧ ∀ x ∈ E₀, U.map (MulAut.conj x).toMonoidHom = U

theorem planeGen_of_native_closure_cond {C N : Type*} [Group C] [Group N] (e : C ≃* N)
    (hZ : Subgroup.center N = ⊥) {p r : ℕ}
    (hnat : ∀ E₀ : Subgroup N, (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ¬ NormalizesRGroup r E₀ →
      Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range)
    (hn : ¬ ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    PlaneGen E := by
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
  have hnE₀ : ¬ NormalizesRGroup r E₀ := by
    rintro ⟨U, hU1, hUp, hUn⟩
    apply hn
    refine ⟨U.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · intro h
      apply hU1
      have h' := congrArg (fun S : Subgroup C => S.map e.toMonoidHom) h
      simp only [Subgroup.map_map, Subgroup.map_bot] at h'
      have : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id N := by
        ext x
        simp
      rwa [this, Subgroup.map_id] at h'
    · exact hUp.map e.symm.toMonoidHom
    · intro ε hε
      obtain ⟨c, rfl⟩ := hin hε
      have hc : c ∈ E₀C := hε
      have hxn := hUn (e c) ⟨c, hc, rfl⟩
      rw [Subgroup.map_map]
      have hcomp : ((MulAut.conj c).toMonoidHom).comp e.symm.toMonoidHom =
          e.symm.toMonoidHom.comp (MulAut.conj (e c)).toMonoidHom := by
        ext x
        simp
      rw [hcomp, ← Subgroup.map_map, hxn]
  have htop := hnat E₀ hE₀p hE₀c hnE₀
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

end CFSG.LieType.SeitzGeneration.ExcHigh
