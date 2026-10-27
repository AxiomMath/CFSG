module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {X : Type} [Group X] [Finite X]

theorem caseA_of_gen {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hc : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)))
    (T : Set X) (hTK : Subgroup.closure T = K)
    (hT : ∀ k ∈ T, ∃ b ∈ B, b ∉ Subgroup.centralizer (K : Set X) ∧ b * k = k * b) :
    I271CaseA p K B := by
  have hp := hH.prime
  have hBel : IsElemAbelian p B := hH.scp.2.1
  refine ⟨hH.rank_four, i271h_isInGOne_of_le hBN ?_⟩
  obtain ⟨Cb, hCb⟩ : ∃ Cb : Subgroup X, Cb = B ⊓ Subgroup.centralizer (K : Set X) := ⟨_, rfl⟩
  rw [← hCb] at hc
  have hCbB : Cb ≤ B := hCb ▸ inf_le_left
  have hCbC : ∀ q ∈ Cb, q ∈ Subgroup.centralizer (K : Set X) := fun q hq => (hCb ▸ hq).2
  have hCbel : IsElemAbelian p Cb := i271_isElemAbelian_of_le hBel hCbB
  obtain ⟨c, hcard⟩ := i271_exists_card_eq hp hCbel
  have hc2 : 2 ≤ c := by rw [← i271_pRank_eq hp hCbel hcard]; exact hc
  have hTK' : ∀ k ∈ T, k ∈ K := fun k hk => hTK ▸ Subgroup.subset_closure hk
  have hTcore : ∀ k ∈ T, k ∈ coreIn p 3 B K := by
    intro k hk
    obtain ⟨x, hxB, hxCb', hxk⟩ := hT k hk
    have hxCb : x ∉ Cb := fun h => hxCb' (hCbC x h)
    obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup X, Q = Cb ⊔ Subgroup.zpowers x := ⟨_, rfl⟩
    have hQB : Q ≤ B := hQ ▸ sup_le hCbB ((Subgroup.zpowers_le).2 hxB)
    have hQel : IsElemAbelian p Q := i271_isElemAbelian_of_le hBel hQB
    obtain ⟨j, hj⟩ := i271_exists_card_eq hp hQel
    have hCQ : Cb ≤ Q := hQ ▸ le_sup_left
    have hxQ : x ∈ Q := hQ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hcj : c ≤ j := by
      have := Subgroup.card_dvd_of_le hCQ
      rw [hcard, hj] at this
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 this
    have hcj' : c ≠ j := by
      intro hcj''
      apply hxCb
      have hle : Nat.card Q ≤ Nat.card Cb := by rw [hcard, hj, hcj'']
      rw [Subgroup.eq_of_le_of_card_ge hCQ hle]
      exact hxQ
    have hj3 : 3 ≤ j := by omega
    have hQrank : 3 ≤ CFSG.Open.pRank p Q := by rw [i271_pRank_eq hp hQel hj]; exact hj3
    have hkQ : k ∈ Subgroup.centralizer (Q : Set X) := by
      have hQle : Q ≤ Subgroup.centralizer ({k} : Set X) := by
        rw [hQ]
        refine sup_le (fun q hq => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 (hCbC q hq) k (hTK' k hk)).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hxk
      rw [Subgroup.mem_centralizer_iff]
      intro q hq'
      exact Subgroup.mem_centralizer_singleton_iff.1 (hQle hq')
    have hS : Subgroup.zpowers k ≤ K ⊓ Subgroup.centralizer (Q : Set X) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hTK' k hk, hkQ⟩
    exact i271h_le_coreIn_of_le_centralizer hQB hQrank hS (Subgroup.mem_zpowers k)
  exact hTK.symm.le.trans ((Subgroup.closure_le _).2 hTcore)

end CFSG.HardMathSupport.Dickson.I271
