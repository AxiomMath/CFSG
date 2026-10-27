module

public import CFSG.LargeExtraspecial.DWNormalFour
public import CFSG.LargeExtraspecial.OrthoF2Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem even_finrank_of_isCompl_perp (S : Setting G) {U : Submodule (ZMod 2) S.Qt}
    (hU : IsCompl U (perp S U)) : Even (finrank (ZMod 2) U) := by
  have halt : (LinearMap.BilinForm.restrict S.q.polarBilin U).IsAlt := fun x =>
    S.polarBilin_isAlt (x : S.Qt)
  have hnd : (LinearMap.BilinForm.restrict S.q.polarBilin U).Nondegenerate :=
    (restrict_nondegenerate_iff_isCompl (S := S)).mpr hU
  exact LinearMap.BilinForm.IsAlt.even_finrank halt hnd

section Simple

variable [IsSimpleGroup G]

theorem q_eq_one_of_finrank_eq_two (S : Setting G) (h2 : 2 ≤ S.width)
    {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    (hrank : finrank (ZMod 2) W = 2) (hdisj : W ⊓ perp S W = ⊥) :
    ∀ w ∈ W, w ≠ 0 → S.q w = 1 := by
  obtain ⟨v, w, hli, hspan⟩ :=
    CFSG.LargeExtraspecial.OrthoF2.exists_pair_of_finrank_eq_two (V := S.Qt) hrank
  obtain ⟨hv0, hw0, hne⟩ :=
    CFSG.LargeExtraspecial.OrthoF2.linearIndependent_pair_iff.mp hli
  have huv : v + w ≠ 0 := by
    intro h
    apply hne
    have h' : v + w + w = w := by rw [h, zero_add]
    rw [add_assoc, CFSG.LargeExtraspecial.OrthoF2.vec_add_self w, add_zero] at h'
    exact h'
  have hpolar : polar S.q v w = 1 := by
    rcases zmod2_cases (polar S.q v w) with hzero | hone
    · exfalso
      have hvperp : v ∈ perp S W := by
        rw [← hspan]
        show v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
          (Submodule.span (ZMod 2) {v, w})
        rw [CFSG.LargeExtraspecial.OrthoF2.mem_orthogonal_span_pair_iff]
        exact ⟨CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero S.q v,
          by rw [polar_comm]; exact hzero⟩
      have hmem : v ∈ W ⊓ perp S W :=
        ⟨hspan ▸ Submodule.subset_span (by simp), hvperp⟩
      rw [hdisj] at hmem
      exact hv0 (by simpa using hmem)
    · exact hone
  have hsum : S.q (v + w) = S.q v + S.q w + 1 := by
    rw [QuadraticMap.map_add S.q v w, hpolar]
  by_cases hgood : S.q v = 1 ∧ S.q w = 1
  · intro x hx hx0
    have hx' : x ∈ Submodule.span (ZMod 2) {v, w} := by rwa [hspan]
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx'
    rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
    · simp only [zero_smul, add_zero] at hx0
      exact absurd rfl hx0
    · simpa using hgood.2
    · simpa using hgood.1
    · simp only [one_smul]
      rw [hsum, hgood.1, hgood.2]
      decide
  ·
    have hcases : (S.q v = 0 ∧ S.q w = 0) ∨ (S.q v = 0 ∧ S.q w = 1) ∨
        (S.q v = 1 ∧ S.q w = 0) := by
      rcases zmod2_cases (S.q v) with hv | hv <;> rcases zmod2_cases (S.q w) with hw | hw
      · exact Or.inl ⟨hv, hw⟩
      · exact Or.inr (Or.inl ⟨hv, hw⟩)
      · exact Or.inr (Or.inr ⟨hv, hw⟩)
      · exact absurd ⟨hv, hw⟩ hgood
    rcases hcases with ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩
    ·
      have huq : S.q (v + w) = 1 := by rw [hsum, hv, hw]; decide
      have huW : v + w ∈ W := hspan ▸ Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      have huniq : ∀ x ∈ W, x ≠ 0 → S.q x = 1 → x = v + w := by
        intro x hx hx0 hqx
        have hx' : x ∈ Submodule.span (ZMod 2) {v, w} := by rwa [hspan]
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx'
        rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
        · simp only [zero_smul, add_zero] at hx0
          exact absurd rfl hx0
        · simp only [zero_smul, one_smul, zero_add] at hqx
          rw [hw] at hqx
          exact absurd hqx (by decide)
        · simp only [one_smul, zero_smul, add_zero] at hqx
          rw [hv] at hqx
          exact absurd hqx (by decide)
        · simp
      have hfix : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) (v + w) = v + w := by
        intro m
        refine huniq _ (hW m _ huW) (fun h => huv ((LinearEquiv.map_eq_zero_iff (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt)).mp h)) ?_
        rw [q_ρ_apply, huq]
      have hinv : IsMbarInvariant S (ZMod 2 ∙ (v + w)) := by
        intro m y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul, hfix m]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact (not_normal_order_four_of_simple (S := S) h2
        ((S.clPre_le_QG (ZMod 2 ∙ (v + w))).trans S.QG_le_M)
        (fun m hm x hx => conj_mem_clPre hinv hm hx)
        (card_clPre_span_singleton (S := S) huq) (S.z_mem_clPre _)).elim
    ·
      have huW : w ∈ W := hspan ▸ Submodule.subset_span (by simp)
      have huniq : ∀ x ∈ W, x ≠ 0 → S.q x = 1 → x = w := by
        intro x hx hx0 hqx
        have hx' : x ∈ Submodule.span (ZMod 2) {v, w} := by rwa [hspan]
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx'
        rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
        · simp only [zero_smul, add_zero] at hx0
          exact absurd rfl hx0
        · simp
        · simp only [one_smul, zero_smul, add_zero] at hqx
          rw [hv] at hqx
          exact absurd hqx (by decide)
        · simp only [one_smul] at hqx
          rw [hsum, hv, hw] at hqx
          exact absurd hqx (by decide)
      have hfix : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
        intro m
        refine huniq _ (hW m _ huW) (fun h => hw0 ((LinearEquiv.map_eq_zero_iff (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt)).mp h)) ?_
        rw [q_ρ_apply, hw]
      have hinv : IsMbarInvariant S (ZMod 2 ∙ w) := by
        intro m y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul, hfix m]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact (not_normal_order_four_of_simple (S := S) h2
        ((S.clPre_le_QG (ZMod 2 ∙ w)).trans S.QG_le_M)
        (fun m hm x hx => conj_mem_clPre hinv hm hx)
        (card_clPre_span_singleton (S := S) hw) (S.z_mem_clPre _)).elim
    ·
      have huW : v ∈ W := hspan ▸ Submodule.subset_span (by simp)
      have huniq : ∀ x ∈ W, x ≠ 0 → S.q x = 1 → x = v := by
        intro x hx hx0 hqx
        have hx' : x ∈ Submodule.span (ZMod 2) {v, w} := by rwa [hspan]
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx'
        rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
        · simp only [zero_smul, add_zero] at hx0
          exact absurd rfl hx0
        · simp only [zero_smul, one_smul, zero_add] at hqx
          rw [hw] at hqx
          exact absurd hqx (by decide)
        · simp
        · simp only [one_smul] at hqx
          rw [hsum, hv, hw] at hqx
          exact absurd hqx (by decide)
      have hfix : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
        intro m
        refine huniq _ (hW m _ huW) (fun h => hv0 ((LinearEquiv.map_eq_zero_iff (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt)).mp h)) ?_
        rw [q_ρ_apply, hv]
      have hinv : IsMbarInvariant S (ZMod 2 ∙ v) := by
        intro m y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul, hfix m]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact (not_normal_order_four_of_simple (S := S) h2
        ((S.clPre_le_QG (ZMod 2 ∙ v)).trans S.QG_le_M)
        (fun m hm x hx => conj_mem_clPre hinv hm hx)
        (card_clPre_span_singleton (S := S) hv) (S.z_mem_clPre _)).elim

theorem exists_quat_of_isCompl (S : Setting G) (hw : S.width = 3)
    {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W) (h0 : W ≠ ⊥) (htop : W ≠ ⊤)
    (hcompl : IsCompl W (perp S W)) :
    ∃ P : Subgroup G, P ≤ S.QG ∧ (∀ m ∈ S.M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) ∧
      Nat.card P = 8 ∧ ∀ p ∈ P, p ≠ 1 → p ≠ S.z → p * p = S.z := by
  have hdimQ : finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hdim : finrank (ZMod 2) W + finrank (ZMod 2) (perp S W) = 6 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, hdimQ]
  have hperp_perp : perp S (perp S W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W
  have hcomplP : IsCompl (perp S W) (perp S (perp S W)) := by
    rw [hperp_perp]
    exact hcompl.symm
  have hevenW : Even (finrank (ZMod 2) W) := even_finrank_of_isCompl_perp S hcompl
  have hevenP : Even (finrank (ZMod 2) (perp S W)) :=
    even_finrank_of_isCompl_perp S hcomplP
  have hposW : 0 < finrank (ZMod 2) W := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact h0
  have hposP : 0 < finrank (ZMod 2) (perp S W) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    exact htop (by
      have h : W ⊔ perp S W = ⊤ := codisjoint_iff.mp hcompl.codisjoint
      rwa [hbot, sup_bot_eq] at h)
  obtain ⟨k, hk⟩ := hevenW
  obtain ⟨l, hl⟩ := hevenP
  have hcases : finrank (ZMod 2) W = 2 ∨ finrank (ZMod 2) (perp S W) = 2 := by
    omega
  rcases hcases with h2W | h2P
  · refine ⟨S.clPre W, S.clPre_le_QG W, fun m hm p hp => conj_mem_clPre hW hm hp, ?_, ?_⟩
    · rw [S.card_clPre, S.card_submodule, h2W]
      norm_num
    · intro p hp hp1 hpz
      have hpQ : p ∈ S.QG := S.clPre_le_QG W hp
      have hclmem : S.cl p ∈ W := hp.2
      have hclne : S.cl p ≠ 0 := by
        intro h
        rcases (S.cl_eq_zero_iff hpQ).mp h with h1 | hz
        · exact hp1 h1
        · exact hpz hz
      have hq : S.q (S.cl p) = 1 :=
        q_eq_one_of_finrank_eq_two S (by rw [hw]; norm_num) hW h2W hcompl.inf_eq_bot _ hclmem hclne
      simpa [pow_two] using
        (S.sq_eq_one_or_z hpQ).resolve_left ((S.q_cl_eq_one_iff hpQ).mp hq)
  · have hInvP : IsMbarInvariant S (perp S W) := hW.perp
    refine ⟨S.clPre (perp S W), S.clPre_le_QG (perp S W),
      fun m hm p hp => conj_mem_clPre hInvP hm hp, ?_, ?_⟩
    · rw [S.card_clPre, S.card_submodule, h2P]
      norm_num
    · intro p hp hp1 hpz
      have hpQ : p ∈ S.QG := S.clPre_le_QG (perp S W) hp
      have hclmem : S.cl p ∈ perp S W := hp.2
      have hclne : S.cl p ≠ 0 := by
        intro h
        rcases (S.cl_eq_zero_iff hpQ).mp h with h1 | hz
        · exact hp1 h1
        · exact hpz hz
      have hdisjP : perp S W ⊓ perp S (perp S W) = ⊥ := by
        rw [hperp_perp]
        exact hcompl.symm.inf_eq_bot
      have hq : S.q (S.cl p) = 1 :=
        q_eq_one_of_finrank_eq_two S (by rw [hw]; norm_num) hInvP h2P hdisjP _ hclmem hclne
      simpa [pow_two] using
        (S.sq_eq_one_or_z hpQ).resolve_left ((S.q_cl_eq_one_iff hpQ).mp hq)

end Simple

end CFSG.LargeExtraspecial.DW
