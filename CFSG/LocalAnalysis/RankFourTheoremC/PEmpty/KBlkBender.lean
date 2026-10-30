module

public import CFSG.GH74.Uniqueness.Bender.Dickson

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

open CFSG.GH74.Uniqueness.Bender Subgroup
open scoped Pointwise

variable {K : Type} [Group K] [Finite K] {n : ℕ}

theorem card_sylow_two (h : BenderType K n 1 1) :
    Nat.card (Sylow 2 K) = 2 ^ n + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  rw [Sylow.card_eq_index_normalizer Q]
  have h1 : (borel (Q : Subgroup K)).index = 2 ^ n + 1 := by
    have := hc.index_eq
    rwa [pow_one] at this
  exact h1

theorem sylow_card_comm (h : BenderType K n 1 1) (P : Sylow 2 K) :
    Nat.card (P : Subgroup K) = 2 ^ n ∧ ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K),
      x * y = y * x := by
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have hcard : Nat.card (P : Subgroup K) = 2 ^ n := by simpa using hc.card_eq
  refine ⟨hcard, fun x hx y hy => ?_⟩
  have hPZ : rootCenter (P : Subgroup K) = (P : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc.card_center, hcard]))
  have hy' : y ∈ rootCenter (P : Subgroup K) := by rw [hPZ]; exact hy
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2 x hx

theorem sylow_inf_eq_bot (h : BenderType K n 1 1) {P Q : Sylow 2 K}
    (hPQ : P ≠ Q) : (P : Subgroup K) ⊓ (Q : Subgroup K) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨tP, hcP⟩ := h.exists_benderCore P
  have hV2 : IsPGroup 2 ((P : Subgroup K) ⊓ (Q : Subgroup K) : Subgroup K) :=
    P.isPGroup'.to_le inf_le_left
  have hVP : ((P : Subgroup K) ⊓ (Q : Subgroup K) : Subgroup K) ≤ borel (P : Subgroup K) :=
    inf_le_left.trans (le_borel _)
  have hN : normalizer (((P : Subgroup K) ⊓ (Q : Subgroup K) : Subgroup K) : Set K) ≤
      borel (P : Subgroup K) := IsStronglyEmbedded.normalizer_le hcP.strong hVP hV2 hne
  have hQN : (Q : Subgroup K) ≤ normalizer (P : Set K) := by
    intro x hxQ
    have hxC : x ∈ centralizer ((((P : Subgroup K) ⊓ (Q : Subgroup K) : Subgroup K)) : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (sylow_card_comm h Q).2 v (Subgroup.mem_inf.mp hv).2 x hxQ
    exact hN (Subgroup.centralizer_le_normalizer _ hxC)
  have hle : (Q : Subgroup K) ≤ (P : Subgroup K) := by
    have := Q.isPGroup'.inf_normalizer_sylow P
    rw [inf_eq_left.mpr hQN] at this
    exact this.le.trans inf_le_right
  exact hPQ (Sylow.ext (Q.is_maximal' P.isPGroup' hle))

theorem eq_top_of_sylow_le (h : BenderType K n 1 1) (P : Sylow 2 K)
    (J : Subgroup K) (hPJ : (P : Subgroup K) ≤ J) (hJ : ¬ J ≤ normalizer (P : Set K)) :
    J = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup K := h.isSimple
  have hcardP := (sylow_card_comm h P).1
  obtain ⟨j, hjJ, hjP⟩ : ∃ j ∈ J, j ∉ normalizer (P : Set K) := by
    by_contra hcon
    push Not at hcon
    exact hJ hcon
  set P' : Sylow 2 K := j • P with hP'
  have hP'ne : P' ≠ P := fun h' => hjP (Sylow.smul_eq_iff_mem_normalizer.mp h')
  have hne : ∀ u : (P : Subgroup K), (u : K) • P' ≠ P := by
    intro u hu
    apply hP'ne
    have h1 : (u : K)⁻¹ • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr
        (Subgroup.inv_mem _ (Subgroup.le_normalizer u.2))
    calc P' = (u : K)⁻¹ • ((u : K) • P') := (inv_smul_smul _ _).symm
      _ = P := by rw [hu, h1]
  let f : ↥(P : Subgroup K) → {Q : Sylow 2 K // Q ≠ P} := fun u => ⟨(u : K) • P', hne u⟩
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (u : K) • P' = (v : K) • P' := congrArg Subtype.val huv
    have h2 : ((v : K)⁻¹ * u) • P' = P' := by
      rw [mul_smul, h1, inv_smul_smul]
    have h3 : (v : K)⁻¹ * u ∈ normalizer (P' : Set K) := Sylow.smul_eq_iff_mem_normalizer.mp h2
    have h4 : (v : K)⁻¹ * u ∈ (P : Subgroup K) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ v.2) u.2
    have h5 : (v : K)⁻¹ * u ∈ (P : Subgroup K) ⊓ (P' : Subgroup K) := by
      rw [← P.isPGroup'.inf_normalizer_sylow P']
      exact ⟨h4, h3⟩
    rw [sylow_inf_eq_bot h hP'ne.symm, Subgroup.mem_bot] at h5
    exact Subtype.ext (inv_mul_eq_one.mp h5).symm
  have hcard : Nat.card {Q : Sylow 2 K // Q ≠ P} ≤ Nat.card ↥(P : Subgroup K) := by
    have h1 : Nat.card {Q : Sylow 2 K // Q ≠ P} = Nat.card (Sylow 2 K) - 1 := by
      have : Fintype (Sylow 2 K) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
    rw [h1, card_sylow_two h, hcardP]
    omega
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard
  have hall : ∀ g : K, ((g • P : Sylow 2 K) : Subgroup K) ≤ J := by
    intro g
    by_cases hg : g • P = P
    · rw [hg]
      exact hPJ
    · obtain ⟨u, hu⟩ := hbij.2 ⟨g • P, hg⟩
      have hQ : (u : K) • P' = g • P := congrArg Subtype.val hu
      rw [← hQ, hP', ← mul_smul]
      exact Sylow.smul_le hPJ ⟨(u : K) * j, J.mul_mem (hPJ u.2) hjJ⟩
  have hnc : Subgroup.normalClosure (P : Set K) ≤ J := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le J).mpr ?_
    intro y hy
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hmem : (MulAut.conj c) • a ∈ (MulAut.conj c) • (P : Subgroup K) :=
      Subgroup.smul_mem_pointwise_smul a (MulAut.conj c) (P : Subgroup K) ha
    have := hall c hmem
    rw [← hc]
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hPne : (P : Subgroup K) ≠ ⊥ := by
    intro hbot
    have : Nat.card (P : Subgroup K) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcardP] at this
    have h2 : 2 ≤ n := h.two_le.2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hncne : Subgroup.normalClosure (P : Set K) ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [eq_bot_iff]
    exact (Subgroup.subset_normalClosure (s := (P : Set K))).trans (by rw [hbot])
  have htop : Subgroup.normalClosure (P : Set K) = ⊤ :=
    (Subgroup.normalClosure_normal.eq_bot_or_eq_top).resolve_left hncne
  exact eq_top_iff.mpr (htop ▸ hnc)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk
