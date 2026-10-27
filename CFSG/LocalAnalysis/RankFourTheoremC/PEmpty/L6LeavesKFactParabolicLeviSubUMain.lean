module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUBlocks
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUR
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open Matrix CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {f t s ε : ℕ}

theorem uni_hcen (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (y : ↥(flagStabilizer h (t + s) ε ↑I))
    (hy : hypProj h (t + s) ε (y : hypSU h (t + s) ε) = 1) (j : Option ↥I) :
    uniLeviHom h hε hI y j ∈ Subgroup.center (uniBlockGroup K s ε I j) := by
  have hy' : (y : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε := by
    rw [← ker_hypProj]
    exact hy
  obtain ⟨c, -, -, hc⟩ := hy'
  have hcm : (((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      Matrix.scalar (HypIndex (t + s) ε) (c : K) := by
    have := congrArg (fun g : GL (HypIndex (t + s) ε) K =>
      (g : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) hc
    simpa only [GeneralLinearGroup.coe_scalar] using this
  rcases j with _ | b
  · have hsc : resBlockHom h hε (Finset.mem_coe.mpr hI.mem) y =
        GeneralLinearGroup.scalar (HypIndex s ε) c := by
      apply Units.ext
      rw [coe_resBlockHom, hcm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.submatrix_diagonal _ _ (resIdx_injective t)]
      ext a b
      simp [Matrix.diagonal_apply, Matrix.scalar_apply]
    change resBlockHom h hε (Finset.mem_coe.mpr hI.mem) y ∈ Subgroup.center (GL (HypIndex s ε) K)
    rw [hsc, Subgroup.mem_center_iff]
    intro g
    exact (commute_scalar c g).eq
  · have hbr := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
    have hsc : eBlockHom h hε b.2 (hI.le b.1 b.2).1 hbr y =
        GeneralLinearGroup.scalar (Fin (b.1 - predCut I b.1)) c := by
      apply Units.ext
      rw [coe_eBlockHom, hcm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.submatrix_diagonal _ _ (eIdx_injective hbr)]
      ext a b
      simp [Matrix.diagonal_apply, Matrix.scalar_apply]
    change eBlockHom h hε b.2 (hI.le b.1 b.2).1 hbr y ∈
      Subgroup.center (GL (Fin (b.1 - predCut I b.1)) K)
    rw [hsc, Subgroup.mem_center_iff]
    intro g
    exact (commute_scalar c g).eq

theorem leviAt_hypPSU (h : UnitaryFieldData 2 f K) {r : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card K - 1 →
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (hypPSU h r ε)))
    (K₀ : Subgroup (hypPSU h r ε)) (p : ℕ)
    (hBJ : hypBorel h r ε ≤ K₀.comap (hypProj h r ε)) : LeviAt K₀ p := by
  intro hB hp h5 hrank1 hpar hne hsyl
  classical
  haveI : Finite K := h.finite
  have hnd : ¬ p ∣ Nat.card K - 1 := fun hd =>
    absurd hrank1 (by have := hrank p hp (by omega) hd; omega)
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hJ := eq_flagStabilizer_overgroupCuts h hr hε hc hc0 _ hBJ
  have hI₀ := overgroupCuts_subset (r := r) (ε := ε) h hc (K₀.comap (hypProj h r ε))
  generalize overgroupCuts ε h c hc (K₀.comap (hypProj h r ε)) = I₀ at hJ hI₀
  have hfin : I₀.Finite := (Set.finite_Icc 1 r).subset hI₀
  obtain ⟨I, rfl⟩ : ∃ I : Finset ℕ, (↑I : Set ℕ) = I₀ := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hIne : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [Finset.coe_empty, flagStabilizer_empty] at hJ
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hypProj_surjective h r ε x
    have : y ∈ K₀.comap (hypProj h r ε) := by rw [hJ]; exact mem_top y
    exact this
  obtain ⟨t, htI, htmax⟩ : ∃ t ∈ I, ∀ i ∈ I, i ≤ t :=
    ⟨I.max' hIne, I.max'_mem hIne, fun i hi => I.le_max' i hi⟩
  have htr : t ≤ r := (hI₀ (Finset.mem_coe.mpr htI)).2
  obtain ⟨s, rfl⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  have hIt : IsTopCut I t :=
    ⟨htI, fun i hi => ⟨(hI₀ (Finset.mem_coe.mpr hi)).1, htmax i hi⟩⟩
  have hρK : ((hypProj h (t + s) ε).comp (flagStabilizer h (t + s) ε (↑I : Set ℕ)).subtype).range
      ≤ K₀ := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : hypSU h (t + s) ε) ∈ K₀.comap (hypProj h (t + s) ε) := by
      rw [hJ]
      exact y.2
    exact hy
  have hK₀ : K₀ = (flagStabilizer h (t + s) ε (↑I : Set ℕ)).map (hypProj h (t + s) ε) := by
    rw [← hJ]
    exact (Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h _ _) K₀).symm
  have hpQ : p ∣ Nat.card ↥(flagStabilizer h (t + s) ε (↑I : Set ℕ)) := by
    have h1 := dvd_card_of_sylow_hyp hp hsyl
    rw [hK₀] at h1
    exact h1.trans (Subgroup.card_map_dvd _ _)
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card, pow_mul]
    have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
    rwa [show 2 ^ 2 - 1 = 3 by norm_num] at this
  exact leviAt_of_blocks (K₀ := K₀)
    ((hypProj h (t + s) ε).comp (flagStabilizer h (t + s) ε (↑I : Set ℕ)).subtype) hρK hp h5 hpQ
    (uniLeviHom h hε hIt) (isPGroup_ker_uniLeviHom h hε hIt) (uniBlockSub (s := s) (ε := ε) h I)
    (pi_uniBlockSub_le_range h hε hIt)
    (fun g hgp hg1 => uni_hblk h hε hIt hp h5 hnd g hgp hg1)
    (fun y hy j => uni_hcen h hε hIt y hy j) (hrank 3 Nat.prime_three (by norm_num) h3)

theorem leviSubAt_hypPSU (h : UnitaryFieldData 2 f K) {r : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card K - 1 →
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (hypPSU h r ε))) : LeviSubAt (hypPSU h r ε) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := h.finite
  obtain ⟨T₀, hT₀⟩ := (unitary_order_and_Sylow h hr hε).2.2.2.2.1
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => leviAt_hypPSU h hr hε hrank K₀ p ?_
  intro b hb
  have hb' : b ∈ Subgroup.normalizer (hypUnitriangular h r ε : Set (hypSU h r ε)) := by
    rw [normalizer_hypUnitriangular h hr hε]
    exact hb
  have h1 : hypProj h r ε b ∈ Subgroup.normalizer
      (((hypUnitriangular h r ε).map (hypProj h r ε) : Subgroup (hypPSU h r ε)) :
        Set (hypPSU h r ε)) :=
    Subgroup.le_normalizer_map (hypProj h r ε) ⟨b, hb', rfl⟩
  have hT : (T₀ : Subgroup (hypPSU h r ε)) = (hypUnitriangular h r ε).map (hypProj h r ε) := hT₀
  rw [← hT] at h1
  exact hN h1

theorem leviSubAt_of_psuFour {S : Type} [Group S] [Finite S] {n f : ℕ} (h4 : 4 ≤ n)
    (hm : StatedClassicalModel S .PSU n 2 f) : LeviSubAt S := by
  have hm' := hm
  obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hm'
  have hf : 1 ≤ f := hadm.2.1
  have hu : UnitaryFieldData 2 f K := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport hu (r := r) (ε := ε)
  let e' : hypPSU hu r ε ≃* StatedProj (StatedSU (2 * r + ε) (2 ^ f) K) :=
    hypPSUEquivStatedProj hu hR (by omega)
  have hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card K - 1 →
      2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (hypPSU hu r ε)) := by
    intro q hq hq2 hqd
    rw [hcard] at hqd
    have := two_le_pRank_psu_of_dvd h4 hm hq hq2 hqd
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt (e.trans e'.symm)] at this
  exact LeviSubAt.of_mulEquiv (e.trans e'.symm) (leviSubAt_hypPSU hu hr hε hrank)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
