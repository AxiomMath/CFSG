module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_three_twins (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N : Subgroup G}
    (hN : N ∈ conjClass K) :
    ∃ T₂ T₃ T₄ : Subgroup G, T₂ ≠ T₃ ∧ T₂ ≠ T₄ ∧ T₃ ≠ T₄ ∧ T₂ ≠ N ∧ T₃ ≠ N ∧ T₄ ≠ N ∧
      ∀ T, (T ∈ conjClass K ∧ cnbhd (conjClass K) T = cnbhd (conjClass K) N) ↔
        (T = N ∨ T = T₂ ∨ T = T₃ ∨ T = T₄) := by
  classical
  let 𝒯 : Set (Subgroup G) := {T | T ∈ conjClass K ∧ cnbhd (conjClass K) T = cnbhd (conjClass K) N}
  have h𝒯 : 𝒯.ncard = 4 := ncard_twins_of_shape S hloc hN
  have hN𝒯 : N ∈ 𝒯 := ⟨hN, rfl⟩
  have h3 : (𝒯 \ {N}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hN𝒯, h𝒯]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, hset⟩ := Set.ncard_eq_three.mp h3
  have hT : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ 𝒯 ∧ T ≠ N := by
    intro T hT
    have : T ∈ 𝒯 \ {N} := by
      rw [hset]
      rcases hT with rfl | rfl | rfl <;> simp
    exact ⟨this.1, this.2⟩
  refine ⟨T₂, T₃, T₄, h23, h24, h34, (hT T₂ (Or.inl rfl)).2, (hT T₃ (Or.inr (Or.inl rfl))).2,
    (hT T₄ (Or.inr (Or.inr rfl))).2, fun T => ⟨fun hTm => ?_, fun h => ?_⟩⟩
  · by_cases hTN : T = N
    · exact Or.inl hTN
    · have : T ∈ 𝒯 \ {N} := ⟨hTm, hTN⟩
      rw [hset] at this
      simpa using Or.inr this
  · rcases h with rfl | h
    · exact hN𝒯
    · exact (hT T h).1

omit [Finite G] in
theorem mem_outerNbhd_iff {Ω : Set (Subgroup G)} {M L : Subgroup G} (hM : M ∈ Ω) (hL : L ∈ Ω) :
    (⟨L, hL⟩ : ↥Ω) ∈ outerNbhd (commAdj Ω) (⟨M, hM⟩ : ↥Ω) ↔ L ∈ outerSet Ω M := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hL, mem_closedNbhd_iff.mp h1⟩,
      fun h => h2 ((cnbhd_eq_iff_closedNbhd_eq (u := ⟨L, hL⟩) (v := ⟨M, hM⟩)).mp h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_closedNbhd_iff.mpr h1.2,
      fun h => h2 ((cnbhd_eq_iff_closedNbhd_eq (u := ⟨L, hL⟩) (v := ⟨M, hM⟩)).mpr h)⟩

omit [Finite G] in
theorem twin_mem_outerSet {Ω : Set (Subgroup G)} {N M T : Subgroup G} (hT : T ∈ Ω)
    (hTN : cnbhd Ω T = cnbhd Ω N) (hM : M ∈ outerSet Ω N) : T ∈ outerSet Ω M := by
  have hMT : M ∈ outerSet Ω T := by
    rw [outerSet_eq_of_cnbhd_eq hTN]
    exact hM
  exact mem_outerSet_symm hT hMT

theorem commutes_outer_eq_twin (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N M L : Subgroup G}
    (hN : N ∈ conjClass K) (hM : M ∈ outerSet (conjClass K) N)
    (hL : L ∈ outerSet (conjClass K) M) (hLN : Commutes L N) :
    cnbhd (conjClass K) L = cnbhd (conjClass K) N := by
  classical
  set Ω := conjClass K with hΩdef
  have hΩ : InClass p f Ω := S.inClass
  have hex : ExactMembers Ω := S.exact
  have hf : 0 < f := routeD_f_pos S
  have hMΩ : M ∈ Ω := hM.1.1
  have hLΩ : L ∈ Ω := hL.1.1
  by_cases hLeqN : L = N
  · rw [hLeqN]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, h2N, h3N, h4N, hT⟩ := exists_three_twins S hloc hN
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hMΩ
  obtain ⟨-, F, fadj, hCF, -, e, he⟩ := exists_localData S.odd S.five hf hΩ hex hw hMΩ hP1
    (single_class_of_mem hMΩ) D hcard ht hr hrest
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hTmem : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ Ω ∧ cnbhd Ω T = cnbhd Ω N := fun T h =>
    (hT T).mpr (Or.inr h)
  have hTout : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ outerSet Ω M := fun T h =>
    twin_mem_outerSet (hTmem T h).1 (hTmem T h).2 hM
  let v : ∀ T, T ∈ outerSet Ω M → ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω)) := fun T hT' =>
    ⟨⟨T, hT'.1.1⟩, (mem_outerNbhd_iff hMΩ hT'.1.1).mpr hT'⟩
  have hcomm : ∀ T T', (T = N ∨ T = T₂ ∨ T = T₃ ∨ T = T₄) → (T' = N ∨ T' = T₂ ∨ T' = T₃ ∨ T' = T₄) →
      T ≠ T' → Commutes T T' := by
    intro T T' hT1 hT2 hne
    have hT1' := (hT T).mpr hT1
    have hT2' := (hT T').mpr hT2
    have : T ∈ cnbhd Ω T' := by
      rw [hT2'.2, ← hT1'.2]
      exact self_mem_cnbhd hT1'.1
    exact this.2.resolve_left hne
  have hadjF : ∀ (a b : ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω))), a ≠ b →
      (Commutes a.1.1 b.1.1 ↔ fadj (e a) (e b)) := fun a b hab => he a b hab
  set vN := v N hNM with hvN
  set v₂ := v T₂ (hTout T₂ (Or.inl rfl)) with hv₂
  set v₃ := v T₃ (hTout T₃ (Or.inr (Or.inl rfl))) with hv₃
  set v₄ := v T₄ (hTout T₄ (Or.inr (Or.inr rfl))) with hv₄
  set vL := v L hL with hvL
  have hne : ∀ {a b : ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω))}, a.1.1 ≠ b.1.1 → a ≠ b :=
    fun h hab => h (by rw [hab])
  have hf12 : fadj (e vN) (e v₂) := (hadjF vN v₂ (hne h2N.symm)).mp
    (hcomm N T₂ (Or.inl rfl) (Or.inr (Or.inl rfl)) h2N.symm)
  have hf13 : fadj (e vN) (e v₃) := (hadjF vN v₃ (hne h3N.symm)).mp
    (hcomm N T₃ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) h3N.symm)
  have hf14 : fadj (e vN) (e v₄) := (hadjF vN v₄ (hne h4N.symm)).mp
    (hcomm N T₄ (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) h4N.symm)
  have hf23 : fadj (e v₂) (e v₃) := (hadjF v₂ v₃ (hne h23)).mp
    (hcomm T₂ T₃ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) h23)
  have he12 : e vN ≠ e v₂ := fun h => h2N.symm (congrArg (fun a => a.1.1) (e.injective h))
  have he13 : e vN ≠ e v₃ := fun h => h3N.symm (congrArg (fun a => a.1.1) (e.injective h))
  have he23 : e v₂ ≠ e v₃ := fun h => h23 (congrArg (fun a => a.1.1) (e.injective h))
  obtain ⟨F₄, hF4₁, hF4₂, hF4₃, -, -, -, hF4⟩ := hCF (e vN) (e v₂) (e v₃) he12 he13 he23 hf12 hf13
    hf23
  have hv4 : e v₄ = F₄ := by
    rcases hF4 (e v₄) hf14 with h | h | h
    · exact absurd (e.injective h) (fun h' => h24 (congrArg (fun a => a.1.1) h').symm)
    · exact absurd (e.injective h) (fun h' => h34 (congrArg (fun a => a.1.1) h').symm)
    · exact h
  have hLN' : fadj (e vN) (e vL) := (hadjF vN vL (hne (fun h => hLeqN h.symm))).mp hLN.symm
  have hLcases := hF4 (e vL) hLN'
  have hLT : L = T₂ ∨ L = T₃ ∨ L = T₄ := by
    rcases hLcases with h | h | h
    · exact Or.inl (congrArg (fun a => a.1.1) (e.injective h))
    · exact Or.inr (Or.inl (congrArg (fun a => a.1.1) (e.injective h)))
    · exact Or.inr (Or.inr (congrArg (fun a => a.1.1) (e.injective (h.trans hv4.symm))))
  exact (hTmem L hLT).2

theorem exists_noncommuting_outer (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N M : Subgroup G}
    (hN : N ∈ conjClass K) (hM : M ∈ outerSet (conjClass K) N) :
    ∃ L ∈ outerSet (conjClass K) N, L ≠ M ∧ ¬ Commutes M L := by
  classical
  set Ω := conjClass K with hΩdef
  have hΩ : InClass p f Ω := S.inClass
  have hex : ExactMembers Ω := S.exact
  have hf : 0 < f := routeD_f_pos S
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hN
  have hout := outerSet_eq_compMembers S.odd hf S.five hΩ hex hw hN hP1
    (single_class_of_mem hN) D ht hr hrest
  have hq4 : 4 ≤ p ^ f := by
    have := S.five
    omega
  have hperf := D.fundPerfect S.odd hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  have hMc : M ∈ compMembers Ω w D i₁ := hout ▸ hM
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hMc
  obtain ⟨S', hS, hSne, hSnc⟩ := exists_fund_not_commuting (D.isFundTag i₁) (D.admissible i₁)
    (by rw [ht, hr]; decide) hR.2.1
  obtain ⟨L', hL'⟩ := exists_corr_right hΩ D hsc hS
  refine ⟨L', hout ▸ ⟨hL'.1, hL'.2.2 ▸ Subgroup.map_le_range _ _⟩,
    fun h => hSne (corr_unique_left hperf hL' (h ▸ hR)), fun h => hSnc ?_⟩
  exact (corr_commutes hΩ hP1 hperf hL' hR).mp (commutes_symm h)

omit [Finite G] in
theorem commutes_of_twin {Ω : Set (Subgroup G)} {N T L : Subgroup G}
    (hTN : cnbhd Ω T = cnbhd Ω N) (hL : L ∈ cnbhd Ω N) (hLT : L ≠ T) : Commutes L T := by
  have : L ∈ cnbhd Ω T := by
    rw [hTN]
    exact hL
  exact this.2.resolve_left hLT

omit [Finite G] in
theorem ne_of_mem_outerSet {Ω : Set (Subgroup G)} {N T L : Subgroup G}
    (hTN : cnbhd Ω T = cnbhd Ω N) (hL : L ∈ outerSet Ω N) : L ≠ T := fun h =>
  hL.2 (by rw [h, hTN])

omit [Finite G] in
theorem commutes_of_twins {Ω : Set (Subgroup G)} {N T T' : Subgroup G} (hT : T ∈ Ω)
    (hTN : cnbhd Ω T = cnbhd Ω N) (hT'N : cnbhd Ω T' = cnbhd Ω N) (hne : T ≠ T') :
    Commutes T T' := by
  refine commutes_of_twin hT'N ?_ hne
  rw [← hTN]
  exact self_mem_cnbhd hT

end CFSG.ClassicalInvolution.RouteD.Exotic
