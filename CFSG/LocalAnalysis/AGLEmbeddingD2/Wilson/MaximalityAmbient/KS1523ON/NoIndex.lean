module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open Subgroup Equiv

theorem mem_of_index_two_perm8 {G' : Subgroup (Perm (Fin 8))} (h : G'.index = 2) :
    List.formPerm [0, 1, 2] ∈ G' ∧ List.formPerm [3, 4, 5, 6, 7] ∈ G' := by
  have hn : G'.Normal := Subgroup.normal_of_index_eq_two h
  have hsq : ∀ τ : Perm (Fin 8), τ ^ 2 ∈ G' := fun τ => by
    simpa [h] using Subgroup.pow_index_mem G' τ
  have hA : alternatingGroup (Fin 8) ≤ G' := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      have := Equiv.Perm.lcm_cycleType σ
      rw [hσ.cycleType] at this
      have h' : orderOf σ = 3 := by rw [← this]; simp
      rw [← h']
      exact pow_orderOf_eq_one σ
    have : σ = (σ ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc σ = σ ^ 3 * σ := by rw [h3, one_mul]
        _ = σ ^ 4 := by rw [← pow_succ]
    rw [this]
    exact G'.pow_mem (hsq σ) 2
  refine ⟨hA ?_, hA ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel

theorem no_injective_hom_perm8 {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 20160)
    (hno : ∀ g h : G, g * h = h * g → g ^ 3 = 1 → g ≠ 1 → h ^ 5 = 1 → h ≠ 1 → False)
    (σ : G →* Perm (Fin 8)) (hσ : Function.Injective σ) : False := by
  have hcr : Nat.card σ.range = 20160 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hσ).toEquiv.symm, hcard]
  have hidx : σ.range.index = 2 := by
    have h := σ.range.card_mul_index
    rw [hcr, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have : (Nat.factorial 8) = 40320 := by decide
    rw [this] at h
    omega
  obtain ⟨h3, h5⟩ := mem_of_index_two_perm8 hidx
  obtain ⟨g, hg⟩ := h3
  obtain ⟨h, hh⟩ := h5
  refine hno g h (hσ ?_) (hσ ?_) ?_ (hσ ?_) ?_
  · rw [map_mul, map_mul, hg, hh]; decide +kernel
  · rw [map_pow, hg, map_one]; decide +kernel
  · intro hg1; rw [hg1, map_one] at hg; revert hg; decide +kernel
  · rw [map_pow, hh, map_one]; decide +kernel
  · intro hh1; rw [hh1, map_one] at hh; revert hh; decide +kernel

theorem no_index_le_eight {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 20160)
    (hno : ∀ g h : G, g * h = h * g → g ^ 3 = 1 → g ≠ 1 → h ^ 5 = 1 → h ≠ 1 → False)
    (V : Subgroup G) (hV : V ≠ ⊤) (hi : V.index ≤ 8) : False := by
  classical
  let φ : G →* Perm (G ⧸ V) := MulAction.toPermHom G (G ⧸ V)
  have hker : φ.ker = ⊥ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker) with h | h
    · exact h
    · exfalso
      apply hV
      rw [eq_top_iff]
      intro g _
      have h1 : g ∈ φ.ker := by rw [h]; trivial
      have h2 := congrArg (fun p : Perm (G ⧸ V) => p ((1 : G) : G ⧸ V)) (MonoidHom.mem_ker.1 h1)
      simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.coe_one] at h2
      have : ((g : G) : G ⧸ V) = ((1 : G) : G ⧸ V) := by
        have h3 : ((g * 1 : G) : G ⧸ V) = ((1 : G) : G ⧸ V) := h2
        simpa using h3
      rw [QuotientGroup.eq] at this
      simpa using this
  have hφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hQ : Nat.card (G ⧸ V) ≤ 8 := by rw [← Subgroup.index]; exact hi
  have : Fintype (G ⧸ V) := Fintype.ofFinite _
  have hQc : Fintype.card (G ⧸ V) ≤ 8 := by rw [← Nat.card_eq_fintype_card]; exact hQ
  by_cases h8 : Fintype.card (G ⧸ V) = 8
  · let e : (G ⧸ V) ≃ Fin 8 := Fintype.equivFinOfCardEq h8
    exact no_injective_hom_perm8 hcard hno (e.permCongrHom.toMonoidHom.comp φ)
      (e.permCongrHom.injective.comp hφ)
  · exfalso
    have hlt : Fintype.card (G ⧸ V) < 8 := lt_of_le_of_ne hQc h8
    have hle := Nat.card_le_card_of_injective φ hφ
    rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card] at hle
    have : Nat.factorial (Fintype.card (G ⧸ V)) ≤ Nat.factorial 7 :=
      Nat.factorial_le (by omega)
    have h7 : Nat.factorial 7 = 5040 := by decide
    omega


theorem no_surj_from_group {G S V : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [Group S] [Finite S] [IsSimpleGroup S] [Group V] [Finite V]
    (hG : Nat.card G = 20160) (hS : Nat.card S = 2520)
    (hno : ∀ g h : G, g * h = h * g → g ^ 3 = 1 → g ≠ 1 → h ^ 5 = 1 → h ≠ 1 → False)
    (ι : V →* G) (hι : Function.Injective ι) (g : V →* S) (hg : Function.Surjective g) :
    False := by
  have hSV : Nat.card S ∣ Nat.card V := Subgroup.card_dvd_of_surjective hg
  have hVr : Nat.card ι.range = Nat.card V := by
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm]
  have hVd : Nat.card ι.range ∣ 20160 := hG ▸ Subgroup.card_subgroup_dvd_card ι.range
  by_cases htop : ι.range = ⊤
  ·
    have hbij : Function.Bijective ι := ⟨hι, fun y => by
      have : y ∈ ι.range := by rw [htop]; trivial
      exact this⟩
    let e : V ≃* G := MulEquiv.ofBijective ι hbij
    have : IsSimpleGroup V := e.isSimpleGroup
    have hVc : Nat.card V = 20160 := by rw [Nat.card_congr e.toEquiv, hG]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with h | h
    · have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).1 h
      have : Nat.card V = Nat.card S :=
        Nat.card_congr (MulEquiv.ofBijective g ⟨hinj, hg⟩).toEquiv
      omega
    · have : Nat.card S = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
        obtain ⟨va, rfl⟩ := hg a
        obtain ⟨vb, rfl⟩ := hg b
        have h1 : va ∈ g.ker := by rw [h]; trivial
        have h2 : vb ∈ g.ker := by rw [h]; trivial
        rw [MonoidHom.mem_ker.1 h1, MonoidHom.mem_ker.1 h2]
      omega
  · apply no_index_le_eight hG hno ι.range htop
    have h := ι.range.card_mul_index
    rw [hG] at h
    have h1 : 2520 ∣ Nat.card ι.range := by rw [hVr]; exact hS ▸ hSV
    obtain ⟨k, hk⟩ := h1
    rw [hk] at h
    have h2 : 2520 * (k * ι.range.index) = 20160 := by rw [← h]; ring
    have h3 : k * ι.range.index = 8 := by omega
    exact Nat.le_of_dvd (by norm_num) ⟨k, by rw [mul_comm]; exact h3.symm⟩

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
