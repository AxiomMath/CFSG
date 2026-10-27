module

public import CFSG.LargeExtraspecial.O62Basic
public import CFSG.LargeExtraspecial.S45QOmega

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem eichler_mem_omegaGroup (hQ : Q.polarBilin.Nondegenerate) (u w : V) :
    eichler Q u w ∈ omegaGroup Q hQ := by
  refine ⟨eichler_mem_orthogonalGroup Q u w, ?_⟩
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · by_cases hli : LinearIndependent (ZMod 2) ![u, w]
    · rw [commSpace_eichler hQ h.1 h.2 hli, OrthoF2.finrank_span_pair hli]
      exact ⟨1, rfl⟩
    · have h1 : eichler Q u w = 1 := by
        rw [OrthoF2.linearIndependent_pair_iff] at hli
        by_cases hu : u = 0
        · rw [hu, eichler_zero_left]
        by_cases hw : w = 0
        · rw [hw, eichler_zero_right]
        have huw : u = w := by
          by_contra hne
          exact hli ⟨hu, hw, hne⟩
        rw [← huw, ← eichler_zero_right Q u]
        simpa using eichler_add_smul_self (Q := Q) h.1 0 1
      rw [h1, OrthoF2.commSpace_one, finrank_bot]
      exact ⟨0, rfl⟩
  · rw [eichler_of_not h, OrthoF2.commSpace_one, finrank_bot]
    exact ⟨0, rfl⟩

theorem elementaryGroup_le_omegaGroup (hQ : Q.polarBilin.Nondegenerate) :
    elementaryGroup Q ≤ omegaGroup Q hQ :=
  elementaryGroup_le_of_eichler_mem fun u w _ _ => eichler_mem_omegaGroup hQ u w

theorem exists_mem_omegaGroup_apply_eq (hQ : Q.polarBilin.Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q x = Q y) :
    ∃ g ∈ omegaGroup Q hQ, g x = y := by
  obtain ⟨P₁, P₂, h₁₂, -, -⟩ := S45Q.exists_two_hypPairs hQ h5
  obtain ⟨g, hg, hgx⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ hx hy hxy
  exact ⟨g, elementaryGroup_le_omegaGroup hQ hg, hgx⟩

theorem map_apply_eq_of_normalizes (hQ : Q.polarBilin.Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ x ∈ omegaGroup Q hQ, g * x * g⁻¹ ∈ omegaGroup Q hQ) {x y : V} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : Q x = Q y) : Q (g y) = Q (g x) := by
  obtain ⟨ω, hω, rfl⟩ := exists_mem_omegaGroup_apply_eq hQ h5 hx hy hxy
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hg ω hω).1 (g x)
  rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.inv_apply_apply'] at h

theorem ncard_singular_nonsingular (hV : finrank (ZMod 2) V = 6)
    (hQ : Q.polarBilin.Nondegenerate) :
    ({v | v ≠ 0 ∧ Q v = 0}.ncard = 35 ∧ {v | Q v = 1}.ncard = 28) ∨
      ({v | v ≠ 0 ∧ Q v = 0}.ncard = 27 ∧ {v | Q v = 1}.ncard = 36) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard := natCard_eq_sixtyFour hV
  have hc : {v | Q v = 0} = {v | Q v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (Q v) with h | h <;> simp [h]
  have hsum := Set.ncard_add_ncard_compl {v | Q v = 1}
  rw [← hc, hcard] at hsum
  have hS : {v | v ≠ 0 ∧ Q v = 0} = {v | Q v = 0} \ {0} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  have h0 : (0 : V) ∈ {v | Q v = 0} := by simp
  have hS' : {v | v ≠ 0 ∧ Q v = 0}.ncard + 1 = {v | Q v = 0}.ncard := by
    rw [hS, Set.ncard_sdiff_singleton_add_one h0]
  rcases ncard_map_eq_zero hV hQ with h | h
  · left
    omega
  · right
    omega

theorem mem_orthogonalGroup_of_normalizes (hV : finrank (ZMod 2) V = 6)
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ x ∈ omegaGroup Q hQ, g * x * g⁻¹ ∈ omegaGroup Q hQ) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h5 : 5 ≤ finrank (ZMod 2) V := by omega
  have hcounts := ncard_singular_nonsingular hV hQ
  set S : Set V := {v | v ≠ 0 ∧ Q v = 0} with hSdef
  set N : Set V := {v | Q v = 1} with hNdef
  have hSN : Disjoint S N := by
    rw [Set.disjoint_left]
    rintro v ⟨-, hv⟩ hv'
    rw [Set.mem_ofPred_eq] at hv'
    rw [hv] at hv'
    exact zero_ne_one hv'
  have hN0 : ∀ v ∈ N, v ≠ 0 := by
    rintro v hv rfl
    rw [Set.mem_ofPred_eq, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have himg : ∀ A : Set V, (g '' A).ncard = A.ncard :=
    fun A => Set.ncard_image_of_injective A g.injective
  have hinto : ∀ v, v ≠ 0 → (Q (g v) = 0 → g v ∈ S) ∧ (Q (g v) = 1 → g v ∈ N) := by
    intro v hv
    refine ⟨fun h => ⟨fun h0 => hv (g.injective (by rw [h0, map_zero])), h⟩, fun h => h⟩
  have hS : ∀ s ∈ S, Q (g s) = 0 := by
    by_contra! hcon
    obtain ⟨s₀, hs₀, hne⟩ := hcon
    have hs₀1 : Q (g s₀) = 1 := (zmod2_eq_zero_or_eq_one _).resolve_left hne
    have hSN' : g '' S ⊆ N := by
      rintro _ ⟨s, hs, rfl⟩
      have := map_apply_eq_of_normalizes hQ h5 hg hs₀.1 hs.1 (hs₀.2.trans hs.2.symm)
      exact (hinto s hs.1).2 (this.trans hs₀1)
    have h1 := Set.ncard_le_ncard hSN'
    rw [himg] at h1
    obtain ⟨n₀, hn₀⟩ : N.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      rcases hcounts with h | h <;> omega
    rcases zmod2_eq_zero_or_eq_one (Q (g n₀)) with hb | hb
    · have hNS : g '' N ⊆ S := by
        rintro _ ⟨n, hn, rfl⟩
        have := map_apply_eq_of_normalizes hQ h5 hg (hN0 n₀ hn₀) (hN0 n hn)
          (hn₀.trans hn.symm)
        exact (hinto n (hN0 n hn)).1 (this.trans hb)
      have h2 := Set.ncard_le_ncard hNS
      rw [himg] at h2
      rcases hcounts with h | h <;> omega
    · have hNN : g '' (S ∪ N) ⊆ N := by
        rw [Set.image_union]
        refine Set.union_subset hSN' ?_
        rintro _ ⟨n, hn, rfl⟩
        have := map_apply_eq_of_normalizes hQ h5 hg (hN0 n₀ hn₀) (hN0 n hn)
          (hn₀.trans hn.symm)
        exact (hinto n (hN0 n hn)).2 (this.trans hb)
      have h2 := Set.ncard_le_ncard hNN
      rw [himg, Set.ncard_union_eq hSN] at h2
      rcases hcounts with h | h <;> omega
  have hN : ∀ n ∈ N, Q (g n) = 1 := by
    by_contra! hcon
    obtain ⟨n₀, hn₀, hne⟩ := hcon
    have hn₀0 : Q (g n₀) = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hne
    have hSS : g '' (S ∪ N) ⊆ S := by
      rw [Set.image_union]
      refine Set.union_subset ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩
        exact (hinto s hs.1).1 (hS s hs)
      · rintro _ ⟨n, hn, rfl⟩
        have := map_apply_eq_of_normalizes hQ h5 hg (hN0 n₀ hn₀) (hN0 n hn)
          (hn₀.trans hn.symm)
        exact (hinto n (hN0 n hn)).1 (this.trans hn₀0)
    have h2 := Set.ncard_le_ncard hSS
    rw [himg, Set.ncard_union_eq hSN] at h2
    rcases hcounts with h | h <;> omega
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  by_cases hv : v = 0
  · rw [hv, map_zero]
  rcases zmod2_eq_zero_or_eq_one (Q v) with h | h
  · rw [h]
    exact hS v ⟨hv, h⟩
  · rw [h]
    exact hN v h

end CFSG.LargeExtraspecial.O62
