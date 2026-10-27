module

public import CFSG.ClassicalInvolution.Asc77.AscT7NA
public import CFSG.ClassicalInvolution.Asc77.AscT7FG

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Abstract

variable {Q : Type*} [Group Q] [Finite Q] {Δ : Set Q}

theorem eq_of_mem_cent_of_ncard_le {x : Q} (h4 : (Star3T.cent Δ x).ncard ≤ 4) {a b c d e : Q}
    (ha : a ∈ Star3T.cent Δ x) (hb : b ∈ Star3T.cent Δ x) (hc : c ∈ Star3T.cent Δ x)
    (hd : d ∈ Star3T.cent Δ x) (he : e ∈ Star3T.cent Δ x) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    e = a ∨ e = b ∨ e = c ∨ e = d := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hea, heb, hec, hed⟩ := hcon
  have hsub : (↑({a, b, c, d, e} : Finset Q) : Set Q) ⊆ Star3T.cent Δ x := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have h5 : ({a, b, c, d, e} : Finset Q).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, Ne.symm hea]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, Ne.symm heb]),
      Finset.card_insert_of_notMem (by simp [hcd, Ne.symm hec]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hed]), Finset.card_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, h5] at this
  omega

end Abstract

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.mem_omegaNbr_of_mem_omegaStarNbr (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {A B : Subgroup G} (hA : A ∈ dComp Ω K)
    (hB : B ∈ dComp Ω K) (hAB : B ∈ omegaStarNbr Ω A) : B ∈ omegaNbr Ω A := by
  have hst := h.std.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have c : Ctx p f Ω W := MuTab.muTabCtx hP h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ₀, -, hρ₀, -, -⟩ := h.exists_reps
  have hAΩ : A ∈ Ω := mem_of_mem_dComp' hK hA
  obtain ⟨g, ρ_A, ρ_B, hρA, hρB⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hAΩ hAB
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hnc ρ₀ ρ_A
  rw [hρ₀, hρA] at hmK
  have hmN : m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inv_mem _ (MGrp_le_normalizer Ω W hm)
  have hxA : conjSub (m⁻¹ * g) A = K := by
    rw [conjSub_mul, ← hmK, conjSub_inv_conjSub]
  have hxσ : m⁻¹ * g ∈ sigmaNorm Ω K :=
    T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hA
      (by rw [hxA]; exact Relation.ReflTransGen.refl)
  have hxB : conjSub (m⁻¹ * g) B ∈ dComp Ω K := (hxσ B).mp hB
  have hLK : (T7D.conjRep hΩ hmN ρ_B).K = conjSub (m⁻¹ * g) B := by
    show conjSub m⁻¹ ρ_B.K = _
    rw [hρB, conjSub_mul]
  have hrc := rep_comm_of_mem_dComp hP h.hW hK hne ρ₀ (T7D.conjRep hΩ hmN ρ_B)
    (by rw [hρ₀]; exact Relation.ReflTransGen.refl) (by rw [hLK]; exact hxB)
  rw [hρ₀, hLK] at hrc
  have hstar : conjSub (m⁻¹ * g) B ∈ omegaStarNbr Ω K := by
    have := omegaStarNbr_conj hΩ.conjInvariant hAB (m⁻¹ * g)
    rwa [hxA] at this
  have hxK : conjSub (m⁻¹ * g)⁻¹ K = A := by
    rw [← hxA, conjSub_inv_conjSub]
  rcases hrc with h1 | h1
  · exact absurd h1 hstar.2.1
  · have := omegaNbr_conj hΩ.conjInvariant h1 (m⁻¹ * g)⁻¹
    rwa [conjSub_inv_conjSub, hxK] at this

theorem Hyp21.exists_clique_conj (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ J' ∈ Ω, IsUniqueInvolution J' t ∧ J' ≠ J ∧ J' ≠ K ∧ J' ≠ K' ∧
      ∀ M ∈ omegaNbr Ω K, ∃ n ∈ Subgroup.normalizer (K : Set G),
        conjSub n M = K' ∨ conjSub n M = J ∨ conjSub n M = J' := by
  classical
  have hst := h.std.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have c : Ctx p f Ω W := MuTab.muTabCtx hP h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hK hz h.hzW
  obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hK'Ω hzK' h.hzW
  obtain ⟨ρ₃, hρ₃⟩ := c.exists_rep_of_involution_mem h.hJ.1 h.ht h.htW
  have h12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K := by
    rw [hρ₁, hρ₂]
    exact T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K := by
    rw [hρ₁, hρ₃]
    exact h.hJ.2 K (mem_twinSet_self hK hz)
  have h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K := by
    rw [hρ₂, hρ₃]
    exact h.hJ.2 K' h.std.hK'
  obtain ⟨ρ₄, hK41, hK42, hK43, hn41, hn42, hn43, hprod⟩ :=
    c.exists_fourth hnc ρ₁ ρ₂ ρ₃ h12 h13 h23 (hρ₁ ▸ hz) (hρ₂ ▸ hzK') (hρ₃ ▸ h.ht)
  obtain ⟨z₄, hz₄⟩ := hΩ.exists_uniqueInvolution hst.odd hst.five ρ₄.hK
  have hz₄t : z₄ = t := by
    have h4 := hprod z₄ hz₄
    have hzz : z * z = 1 := hz.sq
    have h1 : t * z₄ = 1 := by
      have : z * z * t * z₄ = 1 := h4
      rwa [hzz, one_mul] at this
    have h2 : z₄ = t⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_left h.ht.sq
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hmemC : ∀ σ : Rep Ω W, σ.K ∈ omegaNbr Ω ρ₁.K →
      T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := fun σ hσ =>
    ⟨T7D.imgQ_mem σ, (Subtype.ext (c.comm_of_omega ρ₁ σ hσ)).symm⟩
  have hcl4 : (Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁)).ncard ≤ 4 := by
    rcases thompsonClique G Ω hP W h.hW hnc (T7D.imgQ ρ₁) (T7D.imgQ_mem ρ₁) with h | h | ⟨h, -⟩
    · omega
    · omega
    · omega
  have hx₁C : T7D.imgQ ρ₁ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) :=
    Star3T.self_mem_cent (T7D.imgQ_mem ρ₁)
  have h12' : ρ₁.K ≠ ρ₂.K := fun e => h12.2.1 e.symm
  have h13' : ρ₁.K ≠ ρ₃.K := fun e => h13.2.1 e.symm
  have h14' : ρ₁.K ≠ ρ₄.K := fun e => hK41 e.symm
  have h23' : ρ₂.K ≠ ρ₃.K := fun e => h23.2.1 e.symm
  have h24' : ρ₂.K ≠ ρ₄.K := fun e => hK42 e.symm
  have h34' : ρ₃.K ≠ ρ₄.K := fun e => hK43 e.symm
  refine ⟨ρ₄.K, ρ₄.hK, hz₄t ▸ hz₄, ?_, ?_, ?_, ?_⟩
  · rw [← hρ₃]; exact hK43
  · rw [← hρ₁]; exact hK41
  · rw [← hρ₂]; exact hK42
  intro M hM
  have hMstar : M ∈ omegaStarNbr Ω K := T3.omegaNbr_subset_omegaStarNbr hP.1 hΩ K hM
  obtain ⟨g, ρ_K, ρ_M, hρK, hρM⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK hMstar
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hnc ρ₁ ρ_K
  rw [hρ₁, hρK] at hmK
  have hmN : m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inv_mem _ (MGrp_le_normalizer Ω W hm)
  have hnK : conjSub (m⁻¹ * g) K = K := by
    rw [conjSub_mul, ← hmK, conjSub_inv_conjSub]
  have hnN : m⁻¹ * g ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnK
  have hLK : (T7D.conjRep hΩ hmN ρ_M).K = conjSub (m⁻¹ * g) M := by
    show conjSub m⁻¹ ρ_M.K = _
    rw [hρM, conjSub_mul]
  have hMn : conjSub (m⁻¹ * g) M ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant hM (m⁻¹ * g)
    rwa [hnK] at this
  have hLnbr : (T7D.conjRep hΩ hmN ρ_M).K ∈ omegaNbr Ω ρ₁.K := by
    rw [hLK, hρ₁]
    exact hMn
  have hLC := hmemC _ hLnbr
  have hcases := eq_of_mem_cent_of_ncard_le hcl4 (Star3T.self_mem_cent (T7D.imgQ_mem ρ₁))
    (hmemC ρ₂ h12) (hmemC ρ₃ h13) (hmemC ρ₄ hn41) hLC (hne_of _ _ h12') (hne_of _ _ h13')
    (hne_of _ _ h14') (hne_of _ _ h23') (hne_of _ _ h24') (hne_of _ _ h34')
  have hKL : ∀ σ : Rep Ω W, T7D.imgQ (T7D.conjRep hΩ hmN ρ_M) = T7D.imgQ σ →
      conjSub (m⁻¹ * g) M = σ.K := fun σ e => by
    rw [← hLK]
    exact c.K_eq_of_img_eq _ σ (congrArg Subtype.val e)
  refine ⟨m⁻¹ * g, hnN, ?_⟩
  rcases hcases with e | e | e | e
  · exfalso
    have := hKL ρ₁ e
    rw [hρ₁] at this
    exact hMn.2.1 this
  · left
    rw [hKL ρ₂ e, hρ₂]
  · right; left
    rw [hKL ρ₃ e, hρ₃]
  · right; right
    exact hKL ρ₄ e

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
