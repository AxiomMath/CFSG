module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Rk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem eq_bot_of_centralizes {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hperf : commutator K = ⊤) (R' W : Subgroup K) [R'.Normal]
    (hW : W = ⁅R', (⊤ : Subgroup K)⁆) (hcore : CFSG.pPrimeCore q ↥W = ⊥) (hnc : NoCompIn W)
    (hcent : ∀ k : K, ∀ v ∈ (CFSG.pCore q ↥W).map W.subtype, k * v = v * k) : W = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have hlayer : CFSG.layer W = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun L hL => ?_)
    exfalso
    obtain ⟨-, hsub, hqs⟩ := (CFSG.isComponent_iff_open L).mp hL
    have hJsub : CFSG.Open.IsSubnormal (L.map W.subtype) ⊤ := by
      have hWn : W.Normal := by rw [hW]; infer_instance
      have h1 := i227rk_isSubnormal_map W.subtype hsub
      rw [Subgroup.map_top, Subgroup.range_subtype] at h1
      exact i227rk_isSubnormal_trans h1
        (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤))
    exact hnc _ (Subgroup.map_subtype_le L) hJsub
      (i227rk_isQuasisimple_map W.subtype W.subtype_injective hqs)
  have hchar : CFSG.IsCharacteristicP q W :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot W q hcore hlayer
  set O : Subgroup W := CFSG.pCore q W with hOdef
  set V : Subgroup K := O.map W.subtype with hVdef
  have hWV : W ≤ V := by
    intro w hw
    have hmem : (⟨w, hw⟩ : W) ∈ Subgroup.centralizer (O : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      exact Subtype.ext (hcent w _ (Subgroup.mem_map_of_mem _ ho)).symm
    exact ⟨_, hchar hmem, rfl⟩
  have hWK : ⁅W, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact hcent g w (hWV hw)
  have hrot : ⁅⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆, R'⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm (⊤ : Subgroup K) R', ← hW]; exact hWK
    · rw [← hW]; exact hWK
  have htop : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact hperf
  rw [htop] at hrot
  rw [hW, Subgroup.commutator_comm]
  exact hrot

theorem coreIn_eq_top_of_rank_three {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (W : Subgroup K) [W.Normal] (Q : Subgroup K)
    (hQc : Nat.card Q = q ^ (Nat.card K).factorization q)
    (hr : 3 ≤ CFSG.Open.pRank q ((CFSG.pCore q ↥W).map W.subtype)) :
    coreIn q 3 Q ⊤ = ⊤ ∧ 3 ≤ CFSG.Open.pRank q (Q ⊓ W) := by
  have : Fact q.Prime := ⟨hq⟩
  set V : Subgroup K := (CFSG.pCore q ↥W).map W.subtype with hV
  have hVn : V.Normal := i227rk_normal_map W (CFSG.pCore q ↥W)
  have hVp : IsPGroup q V :=
    (CFSG.pCore_isPGroup (p := q) (G := W)).of_equiv
      ((CFSG.pCore q ↥W).equivMapOfInjective W.subtype W.subtype_injective)
  have hVQ : V ≤ Q := by
    have := hVp.le_sylow_of_normal (Sylow.ofCard Q hQc)
    simpa using this
  have hVW : V ≤ W := Subgroup.map_subtype_le _
  refine ⟨?_, hr.trans (CFSG.SectionRank.pRank_mono hq.one_lt (le_inf hVQ hVW))⟩
  rw [eq_top_iff]
  intro x _
  unfold coreIn
  refine Subgroup.mem_iSup_of_mem V (Subgroup.mem_iSup_of_mem ⟨hVQ, hr⟩ ⟨Subgroup.mem_top _, ?_⟩)
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top x

theorem card_le_sq_of_not_three_le {K : Type*} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    {V : Subgroup K} (hr : ¬ 3 ≤ CFSG.Open.pRank q V) :
    ∀ E : Subgroup K, E ≤ V → CFSG.Open.IsElemAbelian q E → Nat.card E ≤ q ^ 2 := by
  intro E hEV hEa
  have : Fact q.Prime := ⟨hq⟩
  have hEp : IsPGroup q E := fun x => ⟨1, Subtype.ext (by simpa using hEa.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hnle : n ≤ CFSG.Open.pRank q V := CFSG.SectionRank.le_pRank hq.one_lt hEV hEa hn
  rw [hn]
  exact Nat.pow_le_pow_right hq.pos (by omega)

end CFSG.LocalAnalysis.GLTheoremA.H248L227
