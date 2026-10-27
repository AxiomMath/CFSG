module

public import CFSG.LocalAnalysis.SteinbergBKSolvableQuaternionWitness

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H

open Subgroup CFSG.LocalAnalysis.SteinbergBK
open scoped MatrixGroups

theorem two_core_of_cp {R : Type*} [Group R] [Finite R]
    (hO : CFSG.pPrimeCore 2 R = ⊥)
    (hCP : centralizer (CFSG.pCore 2 R : Set R) ≤ CFSG.pCore 2 R) (S : Sylow 2 R) {r : ℕ} (hr : 3 ≤ r)
    (eS : (S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) :
    CFSG.fittingSubgroup R = CFSG.pCore 2 R ∧
    centralizer (CFSG.pCore 2 R : Set R) ≤ CFSG.pCore 2 R ∧
    ∃ t : R, t ∈ CFSG.pCore 2 R ∧ orderOf t = 2 ∧ (∀ u : R, orderOf u = 2 → u = t) ∧
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (CFSG.pCore 2 R ≃* QuaternionGroup (2 ^ k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 R with hPdef
  have hF : CFSG.fittingSubgroup R = P := CFSG.Fitting_eq_pcore R 2 hO
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hm : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hSnc : ¬ ∀ u v : (S : Subgroup R), u * v = v * u := by
    intro h
    apply quaternionGroup_not_commute hm
    have := h (eS.symm (QuaternionGroup.a 1)) (eS.symm (QuaternionGroup.xa 0))
    simpa [← map_mul] using congrArg eS this
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hSnc
    intro u v
    have htop : (⊤ : Subgroup R) ≤ ⊥ := by
      calc (⊤ : Subgroup R) = centralizer (P : Set R) := by
            rw [hP, Subgroup.coe_bot]
            exact (Subgroup.centralizer_eq_top_iff_subset.mpr
              (Set.singleton_subset_iff.mpr (one_mem _))).symm
        _ ≤ P := hCP
        _ = ⊥ := hP
    have h1 : (u : R) = 1 := (Subgroup.mem_bot).mp (htop (mem_top _))
    have h2 : (v : R) = 1 := (Subgroup.mem_bot).mp (htop (mem_top _))
    have hu1 : u = 1 := Subtype.ext (by rw [h1]; rfl)
    have hv1 : v = 1 := Subtype.ext (by rw [h2]; rfl)
    rw [hu1, hv1]
  have hTuniq : ∀ T : Sylow 2 R, ∀ u v : R, u ∈ (T : Subgroup R) → v ∈ (T : Subgroup R) →
      orderOf u = 2 → orderOf v = 2 → u = v := by
    intro T u v hu hv hou hov
    let f : (T : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)) := (Sylow.equiv T S).trans eS
    have h1 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (r - 2))
      (by positivity) (f ⟨u, hu⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hou)
    have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (r - 2))
      (by positivity) (f ⟨v, hv⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hov)
    exact congrArg Subtype.val (f.injective (h1.trans h2.symm))
  have hinT : ∀ u : R, orderOf u = 2 → ∃ T : Sylow 2 R, u ∈ (T : Subgroup R) ∧
      P ≤ (T : Subgroup R) := by
    intro u hu
    have hzp : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨T, hT⟩ := hzp.exists_le_sylow
    refine ⟨T, hT (mem_zpowers u), ?_⟩
    have hsup : IsPGroup 2 (P ⊔ (T : Subgroup R) : Subgroup R) :=
      hPp.to_sup_of_normal_left T.isPGroup'
    have := T.is_maximal' hsup le_sup_right
    rw [← this]
    exact le_sup_left
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hPne (Subgroup.eq_bot_of_card_eq P (by rw [hn, pow_zero]))
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have ht : orderOf (t₀ : R) = 2 := by rw [Subgroup.orderOf_coe]; exact ht₀
  have huniq : ∀ u : R, orderOf u = 2 → u = t₀ := by
    intro u hu
    obtain ⟨T, huT, hPT⟩ := hinT u hu
    exact hTuniq T u t₀ huT (hPT t₀.2) hu ht
  have hrank : CFSG.pRank 2 P ≤ 1 :=
    CFSG.ComponentClassification.UnbalancedAltSeven.pRank_le_one_of_unique (z := t₀) ht₀
      (fun y hy => Subtype.ext (huniq y (by rw [Subgroup.orderOf_coe]; exact hy)))
  refine ⟨hF, hCP, t₀, t₀.2, ht, huniq, ?_⟩
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    hPp).mp hrank with hcyc | ⟨-, n', hn', ⟨eP⟩⟩
  · exfalso
    have hA := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup P hPp
    have hR := isPGroup_of_centralizer_le_of_isPGroup_mulAut hPp hCP hA
    have hPtop : (⊤ : Subgroup R) ≤ P := le_sSup ⟨inferInstance, hR.to_subgroup ⊤⟩
    have hSc : IsCyclic (S : Subgroup R) :=
      isCyclic_of_injective (Subgroup.inclusion (le_top.trans hPtop))
        (Subgroup.inclusion_injective _)
    apply hSnc
    intro u v
    exact (IsMulCommutative.is_comm (M := (S : Subgroup R))).comm u v
  · exact ⟨n' - 2, by omega, ⟨eP⟩⟩



theorem quaternion_witness_of_cp {R : Type} [Group R] [Finite R] (hO : CFSG.pPrimeCore 2 R = ⊥)
    (hCP : centralizer (CFSG.pCore 2 R : Set R) ≤ CFSG.pCore 2 R)
    (S : Sylow 2 R) {r : ℕ} (hr : 3 ≤ r)
    (eS : (S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) (hnot : ¬ IsPGroup 2 R) :
    ∃ (t : R) (_ : CFSG.pCore 2 R ≃* QuaternionGroup 2),
      orderOf t = 2 ∧ (∀ u : R, orderOf u = 2 → u = t) ∧
      centralizer (CFSG.pCore 2 R : Set R) = zpowers t ∧
      (axisAction (CFSG.pCore 2 R)).ker = CFSG.pCore 2 R ∧
      (Nat.card R = 24 ∨ Nat.card R = 48) ∧
      (Nat.card R = 24 → Nonempty (R ≃* SL(2, ZMod 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, hCP', t, htP, ht, huniq, k, hk, ⟨eP⟩⟩ := two_core_of_cp hO hCP S hr eS
  obtain ⟨hC, hZ, hZR, hnab⟩ := solvable_quaternion_centers htP ht huniq hCP' hk eP
  have hk1 : k = 1 := by
    by_contra hk1
    have hA : IsPGroup 2 (MulAut (CFSG.pCore 2 R)) :=
      (isPGroup_mulAut_quaternionGroup (by omega : 2 ≤ k)).of_equiv (MulAut.congr eP).symm
    exact hnot (isPGroup_of_centralizer_le_of_isPGroup_mulAut CFSG.pCore_isPGroup hCP' hA)
  subst hk1
  have e8 : CFSG.pCore 2 R ≃* QuaternionGroup 2 := eP
  have hP8 : Nat.card (CFSG.pCore 2 R) = 8 := by
    rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  obtain ⟨hcardR, h36, hrange⟩ := axisAction_range rfl e8 huniq hC ht hnot
  have hker := axisAction_ker rfl e8 huniq hC ht
  have hQ : Nat.card (R ⧸ CFSG.pCore 2 R) = 3 ∨ Nat.card (R ⧸ CFSG.pCore 2 R) = 6 := by
    have h1 : Nat.card (R ⧸ CFSG.pCore 2 R) = Nat.card (axisAction (CFSG.pCore 2 R)).range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (axisAction (CFSG.pCore 2 R))).toEquiv,
        hker]
    rwa [h1]
  obtain ⟨hJ24, hJidx, hPJ, hSyl⟩ := threeCoreInverseImage_facts hP8 hQ
  have hcard : Nat.card R = 24 ∨ Nat.card R = 48 := by
    rcases h36 with h | h
    · left; rw [hcardR, h]
    · right; rw [hcardR, h]
  refine ⟨t, e8, ht, huniq, hC, hker, hcard, fun h24 => ?_⟩
  obtain ⟨a, x, y, haJ, hxP, hyP, ha3, hx2, hy2, hyx, hax, hay⟩ :=
    exists_quaternion_triple (J := threeCoreInverseImage (CFSG.pCore 2 R)) e8 ht huniq hC
      (by rw [hJ24]; norm_num)
  obtain ⟨ψ, -, -, -⟩ := exists_mulEquiv_slTwoThree hPJ hP8 hJ24 haJ hxP hyP ha3 hx2 hy2 hyx hax hay
    ht1 ht2
  have hJtop : threeCoreInverseImage (CFSG.pCore 2 R) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hJ24, h24])
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hJtop.symm)).trans ψ⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H
