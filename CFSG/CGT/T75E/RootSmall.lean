module

public import CFSG.CGT.T75E.RootOrders
public import CFSG.CGT.Timmesfeld75.ListWCL2

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open

variable {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f : ℕ}

theorem rootGroup_a6 (e : K ≃* alternatingGroup (Fin 6)) (hf : 2 ≤ f)
    (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ) : False := by
  have h := card_psu3_dvd_card ρ hρ
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_alternatingGroup_six
  have h1 := Nat.le_of_dvd (by rw [hK]; norm_num) h
  have h2 := card_psu3Model_gt hf
  omega

theorem rootGroup_sz {a : ℕ} (e : K ≃* Sz a) (hf : 2 ≤ f)
    (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ) : False :=
  not_three_dvd_card_of_mulEquiv_sz e
    ((three_dvd_card_psu3Model (by omega)).trans (card_psu3_dvd_card ρ hρ))

theorem rootGroup_l2 {m : ℕ} (hG : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 2 m)
    (hT : IsWC Tb) (hT1 : Tb ≠ ⊥) (hf : 2 ≤ f) (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f)
    (hρ : Function.Surjective ρ) : False := by
  obtain ⟨hm, he⟩ := exists_psl2_galois_of_statedClassicalModel hG
  obtain ⟨⟨-, ⟨S, hS⟩, -⟩, -⟩ := psl2_wc hG hT hT1
  have hpair : IsL2Pair K (S : Subgroup K) (2 ^ m) := IsL2Pair.of_psl_sylow (by omega) he S
  subst hS
  by_cases h1 : conjSubgroup c₁ (S : Subgroup K) = (S : Subgroup K)
  · refine Y3_ne_sup ρ hρ hT hf 0 2 ?_
    simp only [Y3, T3, h1, sup_idem]
    rfl
  · have htop := hpair.sup_conj_eq_top (a := 1) (b := c₁)
      (by rw [conjSubgroup_one]; exact fun h => h1 h.symm)
    rw [conjSubgroup_one] at htop
    have h0 : T3 (S : Subgroup K) c₁ c₂ 0 ⊔ T3 (S : Subgroup K) c₁ c₂ 1 = ⊤ := htop
    have hY : Y3 (S : Subgroup K) c₁ c₂ = ⊤ :=
      eq_top_iff.2 (h0 ▸ sup_le (T3_le_Y3 _ _ _ 0) (T3_le_Y3 _ _ _ 1))
    exact Y3_ne_sup ρ hρ hT hf 0 1 (hY.trans h0.symm)

end CFSG.CGT.T75E
