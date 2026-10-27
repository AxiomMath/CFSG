module

public import CFSG.ClassicalInvolution.Q3.TL3T55
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim7
public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Q3.TL3T43
public import CFSG.ClassicalInvolution.Q3.TL3T54
public import CFSG.ClassicalInvolution.Q3.TL4AECoverB

public section

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
  (FourSetPrim fourSetPrim_five fourSetPrim_six fourSetPrim_seven conj_memBar_vec_even)

namespace CFSG.ClassicalInvolution.Q3.AE.Block4

variable {n : ℕ} {S : Set (Finset (Fin n))}

private theorem fourSetPrim_small (hn5 : 5 ≤ n) (hn7 : n ≤ 7) : FourSetPrim n := by
  interval_cases n
  exacts [fourSetPrim_five, fourSetPrim_six, fourSetPrim_seven]

theorem eq_singleton_or_univ_of_prim (hP : FourSetPrim n) (hS4 : ∀ γ ∈ S, γ.card = 4)
    (hS : IsBlock4 S) {α : Finset (Fin n)} (hα : α ∈ S) :
    S = {α} ∨ ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ S := by
  by_cases h : ∀ β ∈ S, β = α
  · left
    ext β
    rw [Set.mem_singleton_iff]
    exact ⟨h β, fun e => e ▸ hα⟩
  · right
    push Not at h
    obtain ⟨β, hβ, hne⟩ := h
    exact hP S hS4 α hα ⟨β, hβ, hne⟩ fun x hx y hy p hp hxp =>
      hS p (Equiv.Perm.mem_alternatingGroup.mpr hp) x hx hxp y hy

theorem eq_singleton_or_univ_of_le_seven (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (hS4 : ∀ γ ∈ S, γ.card = 4) (hS : IsBlock4 S) {α : Finset (Fin n)} (hα : α ∈ S) :
    S = {α} ∨ ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ S :=
  eq_singleton_or_univ_of_prim (fourSetPrim_small hn5 hn7) hS4 hS hα

theorem eq_singleton_or_univ' (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n) (hS4 : ∀ γ ∈ S, γ.card = 4)
    (hS : IsBlock4 S) {α : Finset (Fin n)} (hα : α ∈ S) :
    S = {α} ∨ ∀ γ : Finset (Fin n), γ.card = 4 → γ ∈ S := by
  rcases hn with ⟨h5, h7⟩ | h9
  · exact eq_singleton_or_univ_of_le_seven h5 h7 hS4 hS hα
  · exact eq_singleton_or_univ h9 hS4 hS hα

end CFSG.ClassicalInvolution.Q3.AE.Block4

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

private theorem sum_pairVec_eq (α : Finset (Fin n)) (a c : Fin n) :
    ∑ x ∈ α, pairVec a c x = (if a ∈ α then 1 else 0) + (if c ∈ α then 1 else 0) := by
  classical
  simp only [pairVec_apply, Finset.sum_add_distrib, Finset.sum_ite_eq']

private theorem sum_pairVec_of_iff {α : Finset (Fin n)} {a c : Fin n} (h : a ∈ α ↔ c ∈ α) :
    ∑ x ∈ α, pairVec a c x = 0 := by
  rw [sum_pairVec_eq]
  by_cases ha : a ∈ α
  · rw [if_pos ha, if_pos (h.mp ha)]
    exact zmod_two_add_self _
  · rw [if_neg ha, if_neg fun hc => ha (h.mpr hc)]
    exact zero_add _

private theorem exists_pair_odd_even (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n) {α γ : Finset (Fin n)}
    (hα : α.card = 4) (hγ : γ.card = 4) (hne : γ ≠ α) :
    ∃ a c : Fin n, a ∈ γ ∧ c ∉ γ ∧ (a ∈ α ↔ c ∈ α) := by
  classical
  rcases hn with ⟨-, h7⟩ | h9
  ·
    obtain ⟨c, hcα, hcγ⟩ : ∃ c ∈ α, c ∉ γ := by
      by_contra h'
      push Not at h'
      exact hne (Finset.eq_of_subset_of_card_le h' (by omega)).symm
    have hpos : 0 < (α ∩ γ).card := by
      have h3 := Finset.card_union_add_card_inter α γ
      have h4 : (α ∪ γ).card ≤ n := by
        have := Finset.card_le_univ (α ∪ γ)
        simpa using this
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_inter] at ha
    exact ⟨a, c, ha.2, hcγ, iff_of_true ha.1 hcα⟩
  ·
    obtain ⟨a, haγ, haα⟩ : ∃ a ∈ γ, a ∉ α := by
      by_contra h'
      push Not at h'
      exact hne (Finset.eq_of_subset_of_card_le h' (by omega))
    obtain ⟨c, hc⟩ := AE.Block4.exists_not_mem (s := γ ∪ α) (by
      have := Finset.card_union_le γ α
      omega)
    rw [Finset.mem_union, not_or] at hc
    exact ⟨a, c, haγ, hc.1, iff_of_false haα hc.2⟩

end CFSG.ClassicalInvolution.Q3.TL4.AECov

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.twins_or_all' (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n) (I : AEIdent P n)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {B : Set (Subgroup G)} (hBP : B ⊆ P)
    (hblock : ∀ x ∈ pSpan P, (∃ M ∈ B, conjSub x M ∈ B) → ∀ M ∈ B, conjSub x M ∈ B)
    {K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ B) (hK₁ : K₁ ∈ B) {α : Finset (Fin n)} (hα : α.card = 4)
    {b₀ : Bool} (hlab₀ : (K₀.subgroupOf (pSpan P)).map I.φ = memBar α hα b₀)
    (hlab₁ : (K₁.subgroupOf (pSpan P)).map I.φ = memBar α hα (!b₀)) :
    (∀ M ∈ B, M = K₀ ∨ M = K₁) ∨ ∀ M ∈ P, M ∈ B := by
  classical
  have hn5 : 5 ≤ n := by rcases hn with ⟨h5, -⟩ | h9 <;> omega
  have hrange : ∀ w ∈ TL4.aeModel n, ∃ x : ↥(pSpan P), I.φ x = w := by
    intro w hw
    rw [show TL4.aeModel n = (aeSub n).map (mkQ n) from rfl, ← I.range_eq] at hw
    exact hw
  have hlabc : ∀ {L : Subgroup G} (_ : L ∈ P) (x : ↥(pSpan P)),
      ((conjSub (x : G) L).subgroupOf (pSpan P)).map I.φ =
        conjSub (I.φ x) ((L.subgroupOf (pSpan P)).map I.φ) :=
    fun _ x => TL4.AECov.map_conjSub_eq I _ x
  have hα₀ : ∀ {M : Subgroup G} (_ : M ∈ P) {c : Bool}
      (_ : (M.subgroupOf (pSpan P)).map I.φ = memBar α hα c), M = K₀ ∨ M = K₁ := by
    intro M hM c hlab
    by_cases hc : c = b₀
    · subst hc
      exact Or.inl (hinj M hM K₀ (hBP hK₀) (hlab.trans hlab₀.symm))
    · have hc' : c = !b₀ := by cases c <;> cases b₀ <;> simp_all
      subst hc'
      exact Or.inr (hinj M hM K₁ (hBP hK₁) (hlab.trans hlab₁.symm))
  have htwin : ∀ M ∈ B, ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c : Bool),
      (M.subgroupOf (pSpan P)).map I.φ = memBar γ hγ c → ∀ M' ∈ P,
      (M'.subgroupOf (pSpan P)).map I.φ = memBar γ hγ (!c) → M' ∈ B := by
    intro M hM γ hγ c hlab M' hM' hlab'
    by_cases hγα : γ = α
    · subst hγα
      rcases hα₀ hM' hlab' with rfl | rfl
      · exact hK₀
      · exact hK₁
    obtain ⟨a, c₀, haγ, hc₀γ, hac⟩ := TL4.AECov.exists_pair_odd_even hn hα hγ hγα
    obtain ⟨x, hx⟩ := hrange _ (vbar_pairVec_mem_aeModel a c₀)
    have hxK₀ : conjSub (x : G) K₀ = K₀ := by
      refine hinj _ (hconj K₀ (hBP hK₀) x x.2) K₀ (hBP hK₀) ?_
      rw [hlabc (hBP hK₀) x, hlab₀, hx]
      refine conj_memBar_vec_even hn5 α hα b₀ (TL4.pairVec a c₀) ?_
      rw [Fin.sum_univ_four, TL4.AECov.sum_emb α hα (TL4.pairVec a c₀)]
      exact TL4.AECov.sum_pairVec_of_iff hac
    have hall := hblock x x.2 ⟨K₀, hK₀, by rw [hxK₀]; exact hK₀⟩
    have hxM := hall M hM
    have hlabx : ((conjSub (x : G) M).subgroupOf (pSpan P)).map I.φ = memBar γ hγ (!c) := by
      rw [hlabc (hBP hM) x, hlab, hx]
      exact TL4.AECov.conjSub_memBar_of_odd rfl γ hγ c (TL4.AECov.sum_pairVec_of_mem haγ hc₀γ)
    rw [hinj M' hM' _ (hconj M (hBP hM) x x.2) (hlab'.trans hlabx.symm)]
    exact hxM
  set S : Set (Finset (Fin n)) := {γ | ∃ (hγ : γ.card = 4), ∃ M ∈ B, ∃ c : Bool,
    (M.subgroupOf (pSpan P)).map I.φ = memBar γ hγ c} with hSdef
  have hmemB : ∀ M ∈ P, ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c : Bool),
      (M.subgroupOf (pSpan P)).map I.φ = memBar γ hγ c → γ ∈ S → M ∈ B := by
    intro M hM γ hγ c hlab hγS
    simp only [hSdef, Set.mem_ofPred_eq] at hγS
    obtain ⟨hγ', M₂, hM₂, c₂, hlab₂⟩ := hγS
    by_cases hcc : c = c₂
    · subst hcc
      rw [hinj M hM M₂ (hBP hM₂) (hlab.trans hlab₂.symm)]
      exact hM₂
    · have hc' : c = !c₂ := by cases c <;> cases c₂ <;> simp_all
      subst hc'
      exact htwin M₂ hM₂ γ hγ c₂ hlab₂ M hM hlab
  have hS4 : ∀ γ ∈ S, γ.card = 4 := fun γ hγ => hγ.1
  have hblock4 : AE.IsBlock4 S := by
    rintro σ hσ γ ⟨hγ, M, hM, c, hlab⟩ hσγ δ ⟨hδ, M', hM', c', hlab'⟩
    obtain ⟨x, hx⟩ := hrange _ (mem_aeModel_ofPerm hσ)
    obtain ⟨c₁, hc₁⟩ := exists_conj_ofPerm_memBar σ γ hγ c
    have hxM : conjSub (x : G) M ∈ B := by
      refine hmemB _ (hconj M (hBP hM) x x.2) (γ.map σ.toEmbedding)
        (by rw [Finset.card_map]; exact hγ) c₁ ?_ hσγ
      rw [hlabc (hBP hM) x, hlab, hx]
      exact hc₁
    have hxM' := hblock x x.2 ⟨M, hM, hxM⟩ M' hM'
    obtain ⟨c₂, hc₂⟩ := exists_conj_ofPerm_memBar σ δ hδ c'
    refine ⟨by rw [Finset.card_map]; exact hδ, _, hxM', c₂, ?_⟩
    rw [hlabc (hBP hM') x, hlab', hx]
    exact hc₂
  have hαS : α ∈ S := ⟨hα, K₀, hK₀, b₀, hlab₀⟩
  rcases AE.Block4.eq_singleton_or_univ' hn hS4 hblock4 hαS with hS1 | hSall
  · left
    intro M hM
    obtain ⟨γ, hγ, c, hlab⟩ := I.label M (hBP hM)
    have hγS : γ ∈ S := ⟨hγ, M, hM, c, hlab⟩
    rw [hS1, Set.mem_singleton_iff] at hγS
    subst hγS
    exact hα₀ (hBP hM) hlab
  · right
    intro M hM
    obtain ⟨γ, hγ, c, hlab⟩ := I.label M hM
    exact hmemB M hM γ hγ c hlab (hSall γ hγ)

end CFSG.ClassicalInvolution.Q3.TC.Thin
