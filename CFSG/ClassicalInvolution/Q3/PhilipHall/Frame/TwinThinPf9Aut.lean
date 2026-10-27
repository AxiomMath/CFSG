module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts28

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE

theorem natCard_map_subgroupOf {n : ℕ} (hn : 5 ≤ n) (σ : ↥(Hn n) →* ↥(Hn n))
    (hσ : Function.Injective σ) (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool) :
    Nat.card ↥(((memBar β hβ c).subgroupOf (Hn n)).map σ) = 8 := by
  rw [Subgroup.card_map_of_injective hσ, ← natCard_memBar hn β hβ c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_Hn β hβ c)).toEquiv


theorem natCard_subgroupOf_memBar {n : ℕ} (hn : 5 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4)
    (c : Bool) : Nat.card ↥((memBar β hβ c).subgroupOf (Hn n)) = 8 := by
  rw [← natCard_memBar hn β hβ c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_Hn β hβ c)).toEquiv

theorem aeAut_of_model117 (h117 : TL4.Model117) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7) :
    AEAut n := by
  intro H hH σ hσ hperm
  subst hH
  let β : MulAut ↥(Hn n) := MulEquiv.ofBijective σ hσ
  obtain ⟨x, hx⟩ := h117 n hn5 hn7 β (fun α h b => by
    obtain ⟨β', hβ', c', hm⟩ := hperm α h b
    refine ⟨β', hβ', c', ?_⟩
    have hle : ((memBar α h b).subgroupOf (Hn n)).map β.toMonoidHom ≤
        (memBar β' hβ' c').subgroupOf (Hn n) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hm y (Subgroup.mem_subgroupOf.mp hy))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have e1 := natCard_subgroupOf_memBar hn5 β' hβ' c'
    have e2 := natCard_map_subgroupOf hn5 σ hσ.1 α h b
    exact (e1.trans e2.symm).le)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) x
  exact ⟨w, hx⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
