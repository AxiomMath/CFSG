module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRadical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearFiveTwo

public section

namespace CFSG.ComponentClassification.RankTwoHypIILinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoHypIIClassical

variable {K : Type} [Field K] {n : ℕ}

theorem false_of_config [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hn : 4 ≤ n)
    (h4 : ¬ (n = 4 ∧ m = 1)) {E M : Subgroup (MulAut (projectiveSL n K))}
    (hc : HypIIConfig (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range E M) :
    False := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  set X := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hXdef
  have hXn : X.Normal := (autModel_mulAut (center_projectiveSL_eq_bot K (by omega))).normal
  have h5 : n = 5 → m = 1 → RigidInvolution X (dualAut n K) := by
    rintro rfl rfl
    exact rigidInvolution_dualAut_five_two (by rw [hK, pow_one])
  obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp hc.not_le
  have ht1 : t ≠ 1 := fun h => htX (h ▸ X.one_mem)
  rcases rigid_or_dualAut hm hK hn h4 h5 htX (hc.elemAbelian.2 t htE) with
    hrig | ⟨hev, -, w, hw⟩
  · exact hc.not_rigidInvolution htE ht1 hrig
  have hc' := hc.conj hXn w⁻¹
  set E' := E.map (MulAut.conj w⁻¹).toMonoidHom with hE'
  have hδ : dualAut n K ∈ E' :=
    ⟨t, htE, by rw [hw]; simp [mul_assoc]⟩
  have hδX : dualAut n K ∉ X := dualAut_not_mem_range (by omega)
  have hE0 : ∃ e ∈ E', e ∈ X ∧ e ≠ 1 := by
    obtain ⟨s, hsE, hs1, hsδ⟩ : ∃ s ∈ E', s ≠ 1 ∧ s ≠ dualAut n K := by
      by_contra hcon
      push Not at hcon
      have hle : E' ≤ zpowers (dualAut n K) := fun s hs => by
        by_cases h1 : s = 1
        · rw [h1]
          exact one_mem _
        · rw [hcon s hs h1]
          exact mem_zpowers _
      have hcard := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at hcard
      have := orderOf_le_of_pow_eq_one two_pos (hc'.elemAbelian.2 _ hδ)
      have := hc'.four_le_card
      omega
    by_cases hsX : s ∈ X
    · exact ⟨s, hsE, hsX, hs1⟩
    · rcases rigid_or_dualAut hm hK hn h4 h5 hsX (hc'.elemAbelian.2 s hsE) with
        hrig | ⟨-, ⟨B, hB⟩, -⟩
      · exact absurd hrig (hc'.not_rigidInvolution hsE hs1)
      · obtain ⟨-, -, -, hδδ, -⟩ := standard_automorphism_transport (n := n) (K := K)
        have hsδ' : s * dualAut n K = conjAut n K B := by
          rw [hB, mul_assoc, hδδ, mul_one]
        refine ⟨s * dualAut n K, mul_mem hsE hδ, ?_, ?_⟩
        · rw [hsδ']
          have h2 : conjAut n K B ^ 2 = 1 := by
            rw [← hsδ']
            exact hc'.elemAbelian.2 _ (mul_mem hsE hδ)
          by_cases h1 : conjAut n K B = 1
          · rw [h1]
            exact one_mem _
          · obtain ⟨p, -, hp⟩ := OutcomeLocal.exists_involution_eq_conjAut (by omega) B h2 h1
            exact ⟨p, hp.symm⟩
        · intro h1
          apply hsδ
          rw [mul_eq_one_iff_eq_inv] at h1
          rw [h1, inv_eq_of_mul_eq_one_right hδδ]
  exact false_of_config_dualAut hm hK hev hn h4 hc' hδ hE0

theorem hypII_of_projectiveSL [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hn : 4 ≤ n) (h4 : ¬ (n = 4 ∧ m = 1)) {A : Type*} [Group A] (hA : commutator A = ⊤)
    (hodd : Odd (Nat.card (center A))) (e : A ⧸ center A ≃* projectiveSL n K) :
    AS76b.HypII A := by
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  exact hypII_of_forall_not_config (autModel_mulAut (center_projectiveSL_eq_bot K (by omega)))
    (fun _ _ hc => false_of_config hm hK hn h4 hc) hA hodd e

theorem hypII_of_psl {A : Type} [Group A] (hA : commutator A = ⊤)
    (hodd : Odd (Nat.card (center A))) {n m : ℕ} (hn : 4 ≤ n) (h4 : (n, m) ≠ (4, 1))
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSL n 2 m) :
    AS76b.HypII A := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  exact hypII_of_projectiveSL hm hK hn (fun h => h4 (by rw [h.1, h.2])) hA hodd
    (e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)))

end CFSG.ComponentClassification.RankTwoHypIILinear
