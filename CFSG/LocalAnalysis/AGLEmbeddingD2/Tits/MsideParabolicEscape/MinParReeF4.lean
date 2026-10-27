module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieF4
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley

section Transfer

variable {G : Type*} [Group G] {Γ : Subgroup G}

theorem subgroupOf_atom {B P : Subgroup G} (hB : B ≤ Γ) (hP : P ≤ Γ)
    (h : ∀ Q : Subgroup G, B ≤ Q → Q ≤ P → Q = B ∨ Q = P) :
    ∀ Q : Subgroup ↥Γ, B.subgroupOf Γ ≤ Q → Q ≤ P.subgroupOf Γ →
      Q = B.subgroupOf Γ ∨ Q = P.subgroupOf Γ := by
  intro Q hQ1 hQ2
  have h1 : B ≤ Q.map Γ.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hB]; exact Subgroup.map_mono hQ1
  have h2 : Q.map Γ.subtype ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hP]; exact Subgroup.map_mono hQ2
  rcases h _ h1 h2 with e | e
  · exact Or.inl ((Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective Q).symm.trans
      (by rw [e]; rfl))
  · exact Or.inr ((Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective Q).symm.trans
      (by rw [e]; rfl))

end Transfer

section Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem reeF4_borel_facts :
    F4.reeFixedBorel K a = F4.reeFixedTorus K a ⊔ F4.reeFixedPosUnipotent K a ∧
    F4.reeFixedBorel K a ≤ F4.reeGamma K a ∧
    F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a ∧
    F4.reeFixedTorus K a ≤ F4.reeGamma K a ∧
    F4.reeFixedTorus K a ≤ Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) ∧
    F4.reeGamma K a ⊓ Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) =
      F4.reeFixedBorel K a := by
  have h1 := reeFixedBorel_eq_sup (t := F4) (K := K) (a := a)
  have hN := reeGamma_inf_normalizer_reeFixedPosUnipotent (t := F4) (K := K) (a := a)
  refine ⟨h1, reeFixedBorel_le_reeGamma, reeFixedPosUnipotent_le_reeGamma, ?_, ?_, hN⟩
  · exact reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  · have : F4.reeFixedBorel K a ≤ Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) :=
      hN.symm.le.trans inf_le_right
    exact reeFixedTorus_le_reeFixedBorel.trans this

theorem reeF4_cell_facts
    (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ F4.reeGamma K a ∧
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∉ F4.reeFixedBorel K a ∧
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      Subgroup.normalizer (torusGroup F4.tag K : Set (ModGL F4.tag K)) ∧
    (∀ g ∈ F4.reeLocalParabolic K a j, g ∈ F4.reeFixedBorel K a ∨
      ∃ b ∈ F4.reeFixedBorel K a, ∃ b' ∈ F4.reeFixedBorel K a,
        g = b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * b') := by
  have hmon := canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem j)
  refine ⟨hmon.2, canonicalRep_fixedOrbitElement_not_mem_reeFixedBorel (K := K) (a := a) j, ?_, ?_⟩
  · exact mem_normalizer_torusGroup_of_mem_monomialSubgroup hmon.1
  · intro g hg
    have hg' : g ∈ ((F4.reeGamma K a ⊓ parabolicSubgroup F4.tag K (F4.fixedOrbitSet j) :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := hg
    rw [coe_reeGamma_inf_parabolicSubgroup j] at hg'
    rcases hg' with hB | hD
    · exact Or.inl hB
    · obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hD
      exact Or.inr ⟨b, hb, b', hb', rfl⟩

theorem twoPar_reeF4
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TwoPar ↥(F4.reeGamma K a) ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
  classical
  have : Finite (ModGL F4.tag K) := finite_modGL
  have pd := CFSG.QuasithinUnique.B113Lie.LargeRee.parabolicData ha hK
  obtain ⟨hBsup, hBΓ, hUΓ, hHΓ, hHN, hNU⟩ := reeF4_borel_facts (K := K) (a := a)
  set Γ := F4.reeGamma K a with hΓ
  set U₀ := F4.reeFixedPosUnipotent K a with hU₀
  set H₀ := F4.reeFixedTorus K a with hH₀
  set B₀ := F4.reeFixedBorel K a with hB₀
  have hPΓ : ∀ j, F4.reeLocalParabolic K a j ≤ Γ := fun j => inf_le_left
  have hBP : ∀ j, B₀ ≤ F4.reeLocalParabolic K a j := fun j =>
    (reeFixedBorel_lt_reeLocalParabolic j).le
  have hB : B₀.subgroupOf Γ = H₀.subgroupOf Γ ⊔ U₀.subgroupOf Γ := by
    rw [hBsup, Subgroup.subgroupOf_sup hHΓ hUΓ]
  have hNB : Subgroup.normalizer ((U₀.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) =
      H₀.subgroupOf Γ ⊔ U₀.subgroupOf Γ := by
    rw [← hB]
    apply Subgroup.map_injective Γ.subtype_injective
    rw [map_normalizer_eq_inf', Subgroup.map_subgroupOf_eq_of_le hUΓ,
      Subgroup.map_subgroupOf_eq_of_le hBΓ, inf_comm, hNU]
  have hcell : ∀ j, TwoCell (U₀.subgroupOf Γ) (H₀.subgroupOf Γ)
      (⟨canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j),
        (reeF4_cell_facts j).1⟩ : ↥Γ) ((F4.reeLocalParabolic K a j).subgroupOf Γ) := by
    intro j
    obtain ⟨hnΓ, hnB, hnT, hPcell⟩ := reeF4_cell_facts (K := K) (a := a) j
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hNB]; exact le_sup_left
    · refine Subgroup.mem_normalizer_iff.2 fun x => ?_
      show (x : ModGL F4.tag K) ∈ H₀ ↔
        (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * (x : ModGL F4.tag K) *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))⁻¹) ∈ H₀
      have hxΓ : (x : ModGL F4.tag K) ∈ Γ := x.2
      have hnxΓ : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) *
          (x : ModGL F4.tag K) *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))⁻¹ ∈ Γ :=
        Γ.mul_mem (Γ.mul_mem hnΓ hxΓ) (Γ.inv_mem hnΓ)
      have := Subgroup.mem_normalizer_iff.1 hnT (x : ModGL F4.tag K)
      have hH : ∀ y, y ∈ H₀ ↔ y ∈ torusGroup F4.tag K ∧ y ∈ Γ := fun y => Subgroup.mem_inf
      rw [hH, hH]
      exact ⟨fun h => ⟨this.1 h.1, hnxΓ⟩, fun h => ⟨this.2 h.1, hxΓ⟩⟩
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hBP j (reeFixedPosUnipotent_le_reeFixedBorel
        (Subgroup.mem_subgroupOf.1 hx)))
    · intro g hg
      rcases hPcell _ (Subgroup.mem_subgroupOf.1 hg) with hb | ⟨b, hb, b', hb', e⟩
      · left
        rw [← hB]; exact Subgroup.mem_subgroupOf.2 hb
      · right
        refine ⟨⟨b, hBΓ hb⟩, ?_, ⟨b', hBΓ hb'⟩, ?_, Subtype.ext e⟩
        · rw [← hB]; exact Subgroup.mem_subgroupOf.2 hb
        · rw [← hB]; exact Subgroup.mem_subgroupOf.2 hb'
  have atomA : ∀ j, ∀ Q : Subgroup (ModGL F4.tag K), B₀ ≤ Q → Q ≤ F4.reeLocalParabolic K a j →
      Q = B₀ ∨ Q = F4.reeLocalParabolic K a j := by
    intro j Q hBQ hQP
    by_cases hQB : Q = B₀
    · exact Or.inl hQB
    right
    have hmin := (minimal_reeFixedBorel_iff (t := F4) (K := K) (a := a)
      (A := F4.reeLocalParabolic K a j)).2 ⟨j, rfl⟩
    exact le_antisymm hQP (hmin.2 ⟨lt_of_le_of_ne hBQ (Ne.symm hQB), hQP.trans (hPΓ j)⟩ hQP)
  have atomS : ∀ j, ∀ Q : Subgroup ↥Γ, B₀.subgroupOf Γ ≤ Q →
      Q ≤ (F4.reeLocalParabolic K a j).subgroupOf Γ →
      Q = B₀.subgroupOf Γ ∨ Q = (F4.reeLocalParabolic K a j).subgroupOf Γ :=
    fun j => subgroupOf_atom hBΓ (hPΓ j) (atomA j)
  have hBPS : ∀ j, B₀.subgroupOf Γ ≤ (F4.reeLocalParabolic K a j).subgroupOf Γ := fun j x hx =>
    Subgroup.mem_subgroupOf.2 (hBP j (Subgroup.mem_subgroupOf.1 hx))
  have hltS : ∀ j, B₀.subgroupOf Γ < (F4.reeLocalParabolic K a j).subgroupOf Γ := by
    intro j
    refine lt_of_le_of_ne (hBPS j) fun e => ?_
    have := congrArg (Subgroup.map Γ.subtype) e
    rw [Subgroup.map_subgroupOf_eq_of_le hBΓ, Subgroup.map_subgroupOf_eq_of_le (hPΓ j)] at this
    exact (reeFixedBorel_lt_reeLocalParabolic (K := K) (a := a) j).ne this
  have hmin : ∀ Y : Subgroup ↥Γ, B₀.subgroupOf Γ ≤ Y → Y ≠ B₀.subgroupOf Γ →
      (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf Γ ≤ Y ∨
        (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf Γ ≤ Y := by
    intro Y hBY hYB
    have h1 : B₀ ≤ Y.map Γ.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hBΓ]; exact Subgroup.map_mono hBY
    have h2 : Y.map Γ.subtype ≤ Γ := by
      rintro _ ⟨y, -, rfl⟩; exact y.2
    have hlt : B₀ < Y.map Γ.subtype := by
      refine lt_of_le_of_ne h1 fun e => hYB ?_
      refine (Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective Y).symm.trans ?_
      rw [← e]; rfl
    obtain ⟨j, hj⟩ := exists_canonicalRep_mem_of_lt hlt h2
    have hPj := reeLocalParabolic_le_of_mem hlt.le hj
    have hle : (F4.reeLocalParabolic K a j).subgroupOf Γ ≤ Y := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hPj (Subgroup.mem_subgroupOf.1 hx)
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    have hcases : ∀ j : Fin F4.fixedOrbitCount, j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
      decide
    rcases hcases j with rfl | rfl
    · exact Or.inl hle
    · exact Or.inr hle
  have hcover : ∀ X : Subgroup ↥Γ, U₀.subgroupOf Γ ≤ X → X ≠ ⊤ →
      X ≤ (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf Γ ∨
        X ≤ (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf Γ := by
    intro X hUX hXt
    obtain ⟨P, hP, hXP⟩ := pd.cover X hUX hXt
    rcases hP with rfl | hP
    · exact Or.inl hXP
    · rw [Set.mem_singleton_iff] at hP
      exact Or.inr (hP ▸ hXP)
  have hUB : U₀.subgroupOf Γ ≤ B₀.subgroupOf Γ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (reeFixedPosUnipotent_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hx))
  have hover := hover_of_minimal hUB (hltS ⟨0, by decide⟩) (hltS ⟨1, by decide⟩)
    (atomS ⟨0, by decide⟩) (atomS ⟨1, by decide⟩) hcover hmin
  have hne : (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf Γ ≠
      (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf Γ := fun e => by
    have := congrArg (Subgroup.map Γ.subtype) e
    rw [Subgroup.map_subgroupOf_eq_of_le (hPΓ _), Subgroup.map_subgroupOf_eq_of_le (hPΓ _)] at this
    have h01 := reeLocalParabolic_injective (t := F4) (K := K) (a := a) this
    exact absurd (congrArg Fin.val h01) (by decide)
  have hnP : ∀ j, (⟨canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j),
        (reeF4_cell_facts j).1⟩ : ↥Γ) ∈ (F4.reeLocalParabolic K a j).subgroupOf Γ := fun j =>
    Subgroup.mem_subgroupOf.2 (canonicalRep_fixedOrbitElement_mem_reeGamma_inf j)
  have hnB : ∀ j, (⟨canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j),
        (reeF4_cell_facts j).1⟩ : ↥Γ) ∉ H₀.subgroupOf Γ ⊔ U₀.subgroupOf Γ := fun j h => by
    rw [← hB] at h
    exact (reeF4_cell_facts (K := K) (a := a) j).2.1 (Subgroup.mem_subgroupOf.1 h)
  refine twoPar_of_twoCell pd.sylow hNB (hcell ⟨0, by decide⟩) (hcell ⟨1, by decide⟩)
    (hnP _) (hnP _) (hnB _) (hnB _) (hB ▸ hBPS _) (hB ▸ hBPS _) ?_ ?_ hne
    (pd.le _ (by simp)).2 (pd.le _ (by simp)).2 ?_ hcover
    (pd.charTwo _ (by simp)) (pd.charTwo _ (by simp))
  · rw [← hB]; exact atomS _
  · rw [← hB]; exact atomS _
  · rw [← hB]; exact hover

end Ree

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
