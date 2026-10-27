module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3FiveR2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine GenLocL3NineR3
open scoped MatrixGroups Classical

namespace GenLocL3Five

variable {K : Type} [Field K]

@[expose] def ShapeE5 (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) : Prop :=
  ∃ (r : D) (v : Fin 3 → Kˣ), (r : MulAut (LinearFlag.projectiveSL 3 K)) =
    LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K ∧
    ∀ m : Fin 3, IsSquare ((v (crd m 0) : K) * v (crd m 1))

theorem rank3_cases [Finite K] (hK : Nat.card K = 5)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) :
    (∃ m m' : Fin 3, m ≠ m' ∧ GoodBlk D hfs m ∧ GoodBlk D hfs m') ∨ ShapeE5 D := by
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have : Fintype ↥D := Fintype.ofFinite _
  have hD := hA.1
  have hσ : ∀ σ : K ≃+* K, σ = 1 := sigma_eq_one hK
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  have hcardD : (Finset.univ : Finset ↥D).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h8]
  have nd : ∀ y : D, (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ noDual K →
      (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ diagSub K := by
    intro y hy
    obtain ⟨x, σ, hx, hax⟩ := hy
    obtain ⟨u, rfl⟩ := exists_diag3 hx
    refine ⟨diag3 u, isDiag_diag3 u, ?_⟩
    rw [hax, hσ σ, map_one, mul_one]
  have hT4 : 4 ≤ (T1D D).card := by
    have hadm := adm_comap_noDual hD D.subtype hα
    set E0 : Subgroup ↥D := (noDual K).comap D.subtype with hE0
    have hidx : E0.index ≤ 2 := (GenLocBasic.adm_iff_index hD E0).1 hadm
    have h1 := Subgroup.card_mul_index E0
    rw [h8] at h1
    have h4 : 4 ≤ Nat.card E0 := by
      by_contra hlt
      push Not at hlt
      have : Nat.card E0 * E0.index ≤ 3 * 2 := Nat.mul_le_mul (by omega) hidx
      omega
    have hsub : (Finset.univ : Finset ↥D).filter (fun y => y ∈ E0) ⊆ T1D D := by
      intro y hy
      rw [Finset.mem_filter] at hy
      exact (mem_T1D D).2 (nd y hy.2)
    have hc : ((Finset.univ : Finset ↥D).filter (fun y => y ∈ E0)).card = Nat.card E0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc 4 ≤ Nat.card E0 := h4
      _ = ((Finset.univ : Finset ↥D).filter (fun y => y ∈ E0)).card := hc.symm
      _ ≤ (T1D D).card := Finset.card_le_card hsub
  have hT4' : (T1D D).card = 4 := le_antisymm (card_T1D_le D hD) hT4
  have hK3 : ∀ m : Fin 3, ∃ (z : D) (w : Fin 3 → Kˣ), z ≠ 1 ∧
      (z : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 w) ∧
        w (crd m 0) = w (crd m 1) := by
    intro m
    obtain ⟨z, hz, hzm⟩ := exists_T1_block D hD hT4' m
    obtain ⟨u, hu, hm, -⟩ := blockFun_spec D hD (Finset.mem_erase.1 hz).2
    rw [hzm] at hm
    exact ⟨z, u, (Finset.mem_erase.1 hz).1, hu, hm⟩
  obtain ⟨r, hr⟩ : ∃ r : D, (r : MulAut (LinearFlag.projectiveSL 3 K)) ∉ noDual K := by
    by_contra h
    push Not at h
    have : T1D D = Finset.univ :=
      Finset.eq_univ_of_forall fun z => (mem_T1D D).2 (nd z (h z))
    rw [this, hcardD] at hT4'
    omega
  obtain ⟨v, σ, ε, hε, hrv⟩ := exists_data (hfs r.2)
  have hσ1 : σ = 1 := hσ σ
  have hε1 : ε = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · exact absurd ⟨diag3 v, σ, isDiag_diag3 v, by rw [hrv, pow_zero, mul_one]⟩ hr
    · rfl
  subst hσ1 hε1
  by_cases h2 : ∃ m m' : Fin 3, m ≠ m' ∧ ¬ IsSquare ((v (crd m 0) : K) * v (crd m 1)) ∧
      ¬ IsSquare ((v (crd m' 0) : K) * v (crd m' 1))
  · left
    obtain ⟨m, m', hmm', hs, hs'⟩ := h2
    have hni : ∀ m : Fin 3, ¬ IsSquare ((v (crd m 0) : K) * v (crd m 1)) →
        ¬ (blkAct D hfs m).range ≤ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range :=
      fun m hs h => hs (isSquare_of_rho_inner m (hfs r.2) le_rfl hrv (h ⟨r, rfl⟩))
    obtain ⟨z, wz, hz1, hzw, hzm⟩ := hK3 m
    obtain ⟨z', wz', hz1', hzw', hzm'⟩ := hK3 m'
    exact ⟨m, m', hmm',
      goodBlk_of_ker_not_inner hK D hfs hA h8 m z hz1 (rho_eq_one_of_eq m (hfs z.2) hzw hzm) (hni m hs),
      goodBlk_of_ker_not_inner hK D hfs hA h8 m' z' hz1' (rho_eq_one_of_eq m' (hfs z'.2) hzw' hzm')
        (hni m' hs')⟩
  · right
    refine ⟨r, v, by rw [hrv, map_one, mul_one, pow_one], fun m => ?_⟩
    by_contra hm
    have key : ∀ m' : Fin 3, m' ≠ m → IsSquare ((v (crd m' 0) : K) * v (crd m' 1)) := by
      intro m' hne'
      by_contra hm'
      exact h2 ⟨m, m', hne'.symm, hm, hm'⟩
    fin_cases m
    · have h1 := key 1 (by decide)
      have h2' := key 2 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 1) (v 0) (v 2) (by simpa [mul_comm] using h2') h1)
    · have h1 := key 0 (by decide)
      have h2' := key 2 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 0) (v 1) (v 2) h2' h1)
    · have h1 := key 0 (by decide)
      have h2' := key 1 (by decide)
      simp [crd] at hm h1 h2'
      exact hm (isSquare_of_mid (v 0) (v 2) (v 1) h2' (by simpa [mul_comm] using h1))

theorem rank3_gen [Finite K] (hK : Nat.card K = 5)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) (hs : ¬ ShapeE5 D) : gammaAct D.subtype = ⊤ := by
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  rcases rank3_cases hK D hfs hA h8 with ⟨m, m', hmm', h, h'⟩ | h5
  · exact gammaAct_eq_top_of_two_good D.subtype hα hmm' h h'
  · exact absurd h5 hs

end GenLocL3Five

end CFSG.GH74.Generic.BProg.B2
