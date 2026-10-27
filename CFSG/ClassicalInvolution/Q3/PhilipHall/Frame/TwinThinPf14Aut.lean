module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.Mdl117
open CFSG.ComponentClassification.PresentationLocal

theorem model117_at {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≠ 8) (hA : AdjInv n)
    (β : MulAut ↥(GBar n)) (hβ : MemberPerm β) :
    ∃ x : AEQ n, ∀ g : ↥(GBar n), ((β g : ↥(GBar n)) : AEQ n) = x * g * x⁻¹ := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_memberPerm hn5 hn8 hA hβ
  have hfix := exists_beta1 hσ
  set β₁ := (MulAut.conjNormal (mkQ n (ofPerm σ)))⁻¹ * β with hβ₁def
  have hgen : ∀ k : CarmichaelIndex n, ∃ w : Fin n → ZMod 2, NormAt k w ∧
      ((β₁ (altHom n (carmichaelCycle k)) : ↥(GBar n)) : AEQ n) =
        mkQ n (ofPerm (carmichaelPerm k) * ofVec w) := by
    intro k
    obtain ⟨v, -, e⟩ := exists_vec_of_fix_zBar hn5 hn8 hfix (altHom n (carmichaelCycle k))
    rw [coe_altHom, ← map_mul] at e
    change _ = mkQ n (ofPerm (carmichaelPerm k) * ofVec v) at e
    have h3 : mkQ n ((ofPerm (carmichaelPerm k) * ofVec v) ^ 3) = 1 := by
      rw [map_pow, ← e, ← Subgroup.coe_pow, ← map_pow, ← map_pow, carmichaelCycle_pow_three,
        map_one, map_one, Subgroup.coe_one]
    obtain ⟨w', hw', he⟩ := exists_norm_of_cube k h3
    exact ⟨w', hw', e.trans he.symm⟩
  choose w hw he using hgen
  have hpair : ∀ k l : CarmichaelIndex n, k ≠ l → w k (carmZero k) = w l (carmZero l) := by
    intro k l hkl
    refine eq_at_zero_of_sq hn5 hkl (hw k) (hw l) ?_
    rw [map_pow, map_mul, ← he k, ← he l, ← Subgroup.coe_mul, ← map_mul, ← Subgroup.coe_pow,
      ← map_pow, ← map_mul, ← map_pow, carmichaelCycle_mul_sq k l hkl, map_one, map_one,
      Subgroup.coe_one]
  obtain ⟨k₀⟩ : Nonempty (CarmichaelIndex n) := ⟨⟨⟨2, by omega⟩, le_rfl⟩⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = w k₀ (carmZero k₀) := ⟨_, rfl⟩
  have hc : ∀ k, w k (carmZero k) = c := by
    intro k
    rw [hcdef]
    by_cases hk : k = k₀
    · rw [hk]
    · exact hpair k k₀ hk
  have hu : ∀ k : CarmichaelIndex n, β₁ (altHom n (carmichaelCycle k)) =
      MulAut.conjNormal (mkQ n (ofVec (uVec c w))) (altHom n (carmichaelCycle k)) := by
    intro k
    apply Subtype.ext
    rw [he k, MulAut.conjNormal_apply, coe_altHom, ← map_inv, ← map_mul, ← map_mul]
    show _ = mkQ n (ofVec (uVec c w) * ofPerm (carmichaelPerm k) * (ofVec (uVec c w))⁻¹)
    rw [conj_uVec hw hc k]
  have heq : β₁ = MulAut.conjNormal (mkQ n (ofVec (uVec c w))) := by
    refine eq_of_agree_carmichael (by omega) hu fun v hv g hg => ?_
    apply Subtype.ext
    rw [fix_vec_of_fix_zBar_gen hn5 hfix hv g hg, MulAut.conjNormal_apply, hg,
      ← map_inv (mkQ n), ← map_mul (mkQ n), ← map_mul (mkQ n), conj_ofVec_ofVec]
  have hβe : β = MulAut.conjNormal (mkQ n (ofPerm σ)) *
      MulAut.conjNormal (mkQ n (ofVec (uVec c w))) := by
    rw [← heq, hβ₁def, mul_inv_cancel_left]
  refine ⟨mkQ n (ofPerm σ) * mkQ n (ofVec (uVec c w)), fun g => ?_⟩
  rw [hβe, MulAut.mul_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  group

theorem natCard_map_subgroupOf' {n : ℕ} (hn : 5 ≤ n) (σ : ↥(Hn n) →* ↥(Hn n))
    (hσ : Function.Injective σ) (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool) :
    Nat.card ↥(((memBar β hβ c).subgroupOf (Hn n)).map σ) = 8 := by
  rw [Subgroup.card_map_of_injective hσ, ← natCard_memBar hn β hβ c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_Hn β hβ c)).toEquiv

theorem natCard_subgroupOf_memBar' {n : ℕ} (hn : 5 ≤ n) (β : Finset (Fin n)) (hβ : β.card = 4)
    (c : Bool) : Nat.card ↥((memBar β hβ c).subgroupOf (Hn n)) = 8 := by
  rw [← natCard_memBar hn β hβ c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_Hn β hβ c)).toEquiv

theorem aeAut_of_adjInv {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≠ 8) (hA : AdjInv n) : AEAut n := by
  intro H hH σ hσ hperm
  subst hH
  let β : MulAut ↥(Hn n) := MulEquiv.ofBijective σ hσ
  obtain ⟨x, hx⟩ := model117_at hn5 hn8 hA β (fun α h b => by
    obtain ⟨β', hβ', c', hm⟩ := hperm α h b
    refine ⟨β', hβ', c', ?_⟩
    have hle : ((memBar α h b).subgroupOf (Hn n)).map β.toMonoidHom ≤
        (memBar β' hβ' c').subgroupOf (Hn n) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hm y (Subgroup.mem_subgroupOf.mp hy))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have e1 := natCard_subgroupOf_memBar' hn5 β' hβ' c'
    have e2 := natCard_map_subgroupOf' hn5 σ hσ.1 α h b
    exact (e1.trans e2.symm).le)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) x
  exact ⟨w, hx⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
