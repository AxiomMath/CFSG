module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2M22Crit
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Quasithin.Background.SmithB45MatM12Cls
public import CFSG.Sporadic.Bridge.M12

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator

private theorem card_centralizerIn_m12_involution
    {v : Equiv.Perm (Fin 12)}
    (hv : v ∈ NativeSporadic.M12) (h2 : orderOf v = 2) :
    Nat.card (centralizerIn NativeSporadic.M12 v) = 192 ∨
      Nat.card (centralizerIn NativeSporadic.M12 v) = 240 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := CFSG.ComponentClassification.M12Cover.m12_involution_cover.1 v
    (by rw [inv_one, one_mul]; exact hv) h2
  rw [← Nat.card_congr
    (CFSG.ComponentClassification.M12Cover.centralizerInConjEquiv NativeSporadic.M12 hc r).toEquiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl CFSG.ComponentClassification.M12Cover.card_centralizerIn_m12Rep1
  · exact Or.inr CFSG.ComponentClassification.M12Cover.card_centralizerIn_m12Rep2

private theorem not_nine_dvd_card_centralizerIn_inner :
    ∀ u ∈ m12D.originalSubgroup, orderOf u = 2 →
      ¬ 9 ∣ Nat.card (centralizerIn m12D.originalSubgroup u) := by
  intro u hu ho
  obtain ⟨g, rfl⟩ : ∃ g : NativeSporadic.M12, (m12EquivD g : Equiv.Perm (Fin 24)) = u :=
    ⟨m12EquivD.symm ⟨u, hu⟩, by rw [MulEquiv.apply_symm_apply]⟩
  have hg2 : orderOf (g : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq m12EquivD g, ← Subgroup.orderOf_coe]
    exact ho
  rw [CFSG.ComponentClassification.M12Cover.card_centralizerIn_blockGroup g]
  rcases card_centralizerIn_m12_involution g.2 hg2 with h | h <;> rw [h] <;> norm_num

private theorem not_nine_dvd_card_centralizerIn_outer :
    ∀ u, m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
      ¬ 9 ∣ Nat.card (centralizerIn m12D.originalSubgroup u) := by
  intro u hu ho
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, hord⟩ := m12_sigma_cover
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hord' : orderOf m12Sigma = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB)
    m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, hord'⟩) 1000 hok
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  rw [List.mem_singleton] at hr
  subst hr
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective,
    CFSG.ComponentClassification.M12Cover.centralizerIn_blockGroup_sigma,
    ← m12SigmaCentQ.orderCertificate_eq_card m12_sigma_cent.1, m12_sigma_cent.2.1]
  norm_num

private theorem orderOf_eq_three_of_odd
    (x : m12D.originalSubgroup) (hx : Odd (orderOf x))
    (h3 : 3 ∣ orderOf x) : orderOf x = 3 := by
  have h := CFSG.Quasithin.B45Mat.M12.orderOf_mem_of_isPRegular (m12EquivD.symm x)
    (show IsPRegular 2 (m12EquivD.symm x) by
      rw [IsPRegular, MulEquiv.orderOf_eq]
      exact Nat.coprime_two_right.2 hx)
  rw [MulEquiv.orderOf_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

private theorem isLocallyBalancedAbs_m12D :
    IsLocallyBalancedAbs 3 2 m12D.originalSubgroup :=
  isLocallyBalancedAbs_three_two_of_oneOuter m12D.originalSubgroup m12Sigma
    m12D_sigma_normalizes m12D_sigma_sq m12D_center m12D_sigma_outer m12D_mulAut_card
    not_nine_dvd_card_centralizerIn_inner not_nine_dvd_card_centralizerIn_outer
    orderOf_eq_three_of_odd

theorem sporadicTwoBalanceThree_M12 :
    SporadicTwoBalanceThree .M12 := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact IsLocallyBalancedAbs.of_mulEquiv ((e.trans b.symm).trans m12EquivD)
    isLocallyBalancedAbs_m12D

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
