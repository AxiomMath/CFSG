module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem exists_mem_swap_of_odd_index {K Γ : Type*} [Group K] [Group Γ] (ρ : K →* Γ)
    {A B : Subgroup Γ} (hAB : A ≠ B)
    (hA : ∀ k : K, A.map (MulAut.conj (ρ k)).toMonoidHom = A ∨
      A.map (MulAut.conj (ρ k)).toMonoidHom = B)
    {T : Subgroup K} (hT : ¬ 2 ∣ T.index) {g : K}
    (hg : A.map (MulAut.conj (ρ g)).toMonoidHom = B) :
    ∃ t ∈ T, A.map (MulAut.conj (ρ t)).toMonoidHom = B := by
  let c : K → Subgroup Γ → Subgroup Γ := fun k X => X.map (MulAut.conj (ρ k)).toMonoidHom
  have hc_mul : ∀ k₁ k₂ X, c (k₁ * k₂) X = c k₁ (c k₂ X) := by
    intro k₁ k₂ X
    simp only [c, map_mul, Subgroup.map_map]
    congr 1
  have hc_one : ∀ X, c 1 X = X := by
    intro X
    simp only [c, map_one]
    ext x
    simp
  have hc_inj : ∀ k X Y, c k X = c k Y → X = Y := fun k X Y h =>
    Subgroup.map_injective (MulAut.conj (ρ k)).injective h
  let N : Subgroup K :=
    { carrier := {k | c k A = A}
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) A = A
        rw [hc_mul]; show c a (c b A) = A
        have hb' : c b A = A := hb
        have ha' : c a A = A := ha
        rw [hb', ha']
      one_mem' := hc_one A
      inv_mem' := fun {a} ha => by
        have ha' : c a A = A := ha
        have h := hc_mul a⁻¹ a A
        rw [inv_mul_cancel, hc_one, ha'] at h
        show c a⁻¹ A = A
        exact h.symm }
  have hgB : c g A = B := hg
  have hmem : ∀ k, k ∈ N ↔ c k A = A := fun k => Iff.rfl
  have hBA : ∀ b, c b B = A ∨ c b B = B := by
    intro b
    have h := hA (b * g)
    have e : c (b * g) A = c b B := by rw [hc_mul, hgB]
    have h' : c (b * g) A = A ∨ c (b * g) A = B := h
    rw [e] at h'
    exact h'
  have hindex : N.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨g, fun b => ?_⟩
    have hbg : b * g ∈ N ↔ c b B = A := by
      rw [hmem, hc_mul, hgB]
    rw [hbg, hmem]
    have hAb : c b A = A ∨ c b A = B := hA b
    rcases hAb with h | h
    · have h2 : c b B ≠ A := fun h2 => hAB (hc_inj b _ _ (h2.trans h.symm)).symm
      simp [h, h2]
    · have hb3 : c b A ≠ A := by rw [h]; exact hAB.symm
      have h2 : c b B = A := by
        rcases hBA b with h2 | h2
        · exact h2
        · exact absurd (hc_inj b _ _ (h.trans h2.symm)) hAB
      simp [h, h2, hAB.symm]
  by_contra hcon
  push Not at hcon
  have hTN : T ≤ N := by
    intro t ht
    have hAt : c t A = A ∨ c t A = B := hA t
    rcases hAt with h | h
    · exact h
    · exact absurd h (hcon t ht)
  exact hT (hindex ▸ Subgroup.index_dvd_of_le hTN)

variable {G : Type} [Group G]

theorem exists_swap_mem_sylow {M H L₁ L₂ T : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT : IsSylowTwoOf T (H ⊓ M))
    (hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    {g : G} (hgK : g ∈ H ⊓ M)
    (hg : barM M (L₁.map (MulAut.conj g).toMonoidHom) = barM M L₂) :
    ∃ t ∈ T, barM M (L₁.map (MulAut.conj t).toMonoidHom) = barM M L₂ := by
  have hKM : H ⊓ M ≤ M := inf_le_right
  let ρ : ↥(H ⊓ M) →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)
  have hconj : ∀ k : ↥(H ⊓ M), (barM M L₁).map (MulAut.conj (ρ k)).toMonoidHom =
      barM M (L₁.map (MulAut.conj (k : G)).toMonoidHom) := fun k =>
    (barM_map_conj (hKM k.2) L₁).symm
  have hA : ∀ k : ↥(H ⊓ M), (barM M L₁).map (MulAut.conj (ρ k)).toMonoidHom = barM M L₁ ∨
      (barM M L₁).map (MulAut.conj (ρ k)).toMonoidHom = barM M L₂ := by
    intro k
    rw [hconj]
    have hkS : (k : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
      rw [hNH]; exact k.2.1
    exact hk2 _ (isWeakSBlock_map_conj_of_normalizer h₁ (hKM k.2) hkS)
  obtain ⟨t, ht, ht'⟩ := exists_mem_swap_of_odd_index ρ hne hA
    (T := T.subgroupOf (H ⊓ M)) hT.2.2 (g := ⟨g, hgK⟩) (by rw [hconj]; exact hg)
  refine ⟨(t : G), Subgroup.mem_subgroupOf.mp ht, ?_⟩
  rw [← hconj]
  exact ht'

end CFSG.AGLEmbeddingD2.McLaughlin
