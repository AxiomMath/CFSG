module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem mem_dComp_conjSub (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ dComp Ω K) (g : G) :
    conjSub g J ∈ dComp Ω (conjSub g K) := by
  have h' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    h
  clear h
  show Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) _ _
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine Relation.ReflTransGen.tail ih ⟨hΩ g c hbc.1, ?_⟩
    rcases hbc.2 with h | h
    · exact Or.inl (omegaNbr_conj hΩ h g)
    · exact Or.inr (omegaNbr_conj hΩ h g)

end Conj

section Existence

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem mem_DSet_of_le_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) {R : Subgroup G}
    (hR : R ∈ RSet Ω) (hRS : R ≤ (S : Subgroup G)) : R ∈ DSet Ω W := by
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  refine ⟨hR, ?_⟩
  have := le_normalizer_biSup_of_acts ((l6_10_proved p f hp hq G Ω hΩ S η hηG hηS).1 R hR hRS)
  rwa [← hWη] at this

theorem exists_conj_mem_DSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) (S : Sylow 2 G) :
    ∃ g : G, ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → conjSub g R ∈ DSet Ω W := by
  obtain ⟨S', hWS'⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S'
  refine ⟨g, fun R hR hRS => ?_⟩
  refine mem_DSet_of_le_sylow hp hq hΩ hW hWS' (RSet.conj hΩ.conjInvariant hR g) ?_
  rw [← hg]
  exact conjSub_mono hRS

theorem exists_sylow_mem_DSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) {J U : Subgroup G}
    (hJ : J ∈ Ω) (hU : U ∈ USet Ω) (hUJ : U ≤ J) (hUS : U ≤ (S : Subgroup G)) :
    ∃ T ∈ DSet Ω W, IsSylow2In T J := by
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := hΩ.exists_data_of_mem_USet hp hU
  obtain ⟨η, hηG, hWη⟩ := id hW
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hWle : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hWle V hV).trans hWS
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (hU4.trans (Subgroup.card_le_of_le (le_inf hUJ hUS)))
  have hV₀ : J ⊓ W ∈ η := by
    have := l6_11_proved p f hp hq G Ω hΩ S η hηG hηS J hJ hJS
    rwa [← hWη] at this
  have hV₀U : J ⊓ W ∈ USet Ω := (hη.1 hV₀).1
  have hV₀2 : IsPGroup 2 ↥(J ⊓ W) := hΩ.isPGroup_of_mem_USet hp hV₀U
  obtain ⟨-, -, -, -, -, -, -, -, hV₀4⟩ := hΩ.exists_data_of_mem_USet hp hV₀U
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hzV₀ : zJ ∈ J ⊓ W := T3.mem_of_isPGroup hzJ inf_le_left hV₀2 (by omega)
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hWJ' : (⨆ V ∈ η, V : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := by
    refine iSup₂_le fun V hV => ?_
    by_cases hVeq : V = J ⊓ W
    · rw [hVeq]
      exact inf_le_left.trans Subgroup.le_normalizer
    · obtain ⟨Rv, -, J', hJ', hRvJ', hVRv, -, -, hV4⟩ :=
        hΩ.exists_data_of_mem_USet hp (hη.1 hV).1
      have hVJ' : V ≤ J' := hVRv.trans hRvJ'.1
      have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hp (hη.1 hV).1
      have hJJ' : J ≠ J' := by
        intro hJJ'
        rw [← hJJ'] at hVJ'
        exact hη.2.1 V hV (J ⊓ W) hV₀ hVeq J hJ ⟨hVJ', inf_le_left⟩
      refine hΩ.le_normalizer_of_le_centralizer hp hq hJ hJ' hJJ' hzJ hVJ' hV2 (by omega) ?_
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hWab v (hWle V hV hv) zJ hzV₀.2
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) := hWη.le.trans hWJ'
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨T, hTJ, hTW⟩ := T3.exists_sylow_normalized hW2 hWJ
  have hWT : W ≤ Subgroup.normalizer (T : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hTW w hw)
  obtain ⟨S', hS'⟩ := (hW2.to_sup_of_normal_right' hTJ.2.1 hWT).exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hTS' : T ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  exact ⟨T, mem_DSet_of_le_sylow hp hq hΩ hW hWS' (mem_RSet_of_isSylow2In hJ hTJ) hTS', hTJ⟩

theorem not_connected_of_dComp_ne (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K : Subgroup G} (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W := by
  intro hconn
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := exists_boundary_of_dComp_ne hp hq hΩ hK hne
  have hK₁ : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨hJ₁Ω, -, U, hU, hUJ₁, hUN⟩ := hJ₁
  have hU2 : IsPGroup 2 U := hΩ.isPGroup_of_mem_USet hp hU
  obtain ⟨R, hRK, hRU⟩ := T3.exists_sylow_normalized hU2 hUN
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S₁, hS₁⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S
  have hUS : conjSub g U ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_left.trans hS₁)
    rwa [hg] at this
  have hRS : conjSub g R ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_right.trans hS₁)
    rwa [hg] at this
  have hK' : conjSub g K₁ ∈ Ω := hΩ.conjInvariant g K₁ hK₁
  have hJ' : conjSub g J₁ ∈ Ω := hΩ.conjInvariant g J₁ hJ₁Ω
  have hR'K' : IsSylow2In (conjSub g R) (conjSub g K₁) := hRK.conj g
  have hR'D : conjSub g R ∈ DSet Ω W :=
    mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'K') hRS
  obtain ⟨T, hTD, hTJ⟩ := exists_sylow_mem_DSet hp hq hΩ hW hWS hJ'
    (USet.conj hΩ.conjInvariant hU g) (conjSub_mono hUJ₁) hUS
  let c : Ctx p f Ω W := ⟨hp, hq, hΩ, hW, hkey, hA⟩
  have hmem := c.mem_dComp_of_connected hconn hK' hJ' hR'D hTD hR'K' hTJ
  have h1 : conjSub g K₁ ∈ dComp Ω (conjSub g K) := mem_dComp_conjSub hΩ.conjInvariant hK₁d g
  have h2 : conjSub g J₁ ∈ dComp Ω (conjSub g K) := dComp_trans' h1 hmem
  have h3 := mem_dComp_conjSub hΩ.conjInvariant h2 g⁻¹
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h3
  exact hJ₁n h3

end Existence

end Thompson

end CFSG.ClassicalInvolution.Asc77
