module

public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.ClassicalInvolution.AschTight.Hall196Main

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem sup_eq_of_le (hd : Sec19DataT p f K z S W L t V)
    (hPC : (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z) :
    W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W := by
  have hd0 := hd.toSec19Data
  have ef := S1911.etaYForm p f G K z S W L t V hd
  have hSY : (S : Subgroup G) ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    hd0.hSz.trans (Hall196.centralizer_le_normalizer_sec19Y hd0.tight)
  have hP := Hall196.isSylow2In_inf_of_le_normalizer S hSY
  have hPeq : (S : Subgroup G) ⊓ sec19Y K z = W ⊓ sec19Y K z :=
    le_antisymm hPC (inf_le_inf_right _ hd0.hWS)
  exact Hall196.sup_eq_oddCoreOf_sup_of_isCyclic hP (hPeq ▸ ef.cyclic) (hPC.trans inf_le_left)

theorem exists_swap (hstar : C19_11aTmp p f) (hd : Sec19DataT p f K z S W L t V)
    (hPC : ¬ (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z) :
    ∃ q ∈ (S : Subgroup G) ⊓ sec19Y K z, q ∉ W ⊓ sec19Y K z ∧ q * t * q⁻¹ = z * t ∧
      (∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) ∧ (q * q = 1 ∨ q * q = z) ∧
      (∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z → q⁻¹ * x ∈ W ⊓ sec19Y K z) ∧
      Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) ∧
      (q * q = z → IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd0 := hd.toSec19Data
  have ef := S1911.etaYForm p f G K z S W L t V hd
  obtain ⟨-, -, -, hVcyc, -⟩ := hd.memV
  have hcomm : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, ∀ w ∈ W,
      x * w * x⁻¹ * w⁻¹ ∈ W ⊓ sec19Y K z := by
    intro x hx w hw
    refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (ef.normalizes hx) w).mp hw)
      (W.inv_mem hw), ?_⟩
    have hw' : w * x⁻¹ * w⁻¹ ∈ sec19Y K z := by
      rw [← Hall196.conjSub_sec19Y hd0.tight (hd0.hSz (hd0.hWS hw))]
      exact conj_mem_conjSub (Subgroup.inv_mem _ hx.2)
    have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx.2 hw'
  have hstar' := fun x hx hxt => Hall196.mem_inf_of_commute hstar hd ef (x := x) hx hxt
  have hCP : W ⊓ sec19Y K z ≤ (S : Subgroup G) ⊓ sec19Y K z := inf_le_inf_right _ hd0.hWS
  have hC4 : 4 ≤ Nat.card ↥(W ⊓ sec19Y K z) := ef.card ▸ ef.four
  have hC2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd0.hWS)
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hd.leW.trans hd0.hWS)
  obtain ⟨q, hqP, hqC, zc, hzcC, hzc1, hzc2, -, hqt, hqinv, -, hq2, hcoset, hcardP, -⟩ :=
    Hall196.exists_swap_of_not_le ef.comm hd.leW inf_le_left ef.cyclic hVcyc ef.card.symm hC4 hC2
      hV2 hd.memT hd.invL.ne_one hd.invL.sq hCP ef.normalizes hcomm hstar' hPC
  have hqk := Hall196.isQuaternionSub_of_swap ef.cyclic hC4 hC2 hCP hqP hzcC hzc1 hzc2 hqinv
    hcoset hcardP
  have hzc : zc = z :=
    ((S1916.isUniqueInvolution_W_inf hd).unique zc hzcC hzc2).resolve_left hzc1
  rw [hzc] at hqt hq2 hqk
  exact ⟨q, hqP, hqC, hqt, hqinv, hq2, hcoset, hcardP, hqk.1⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
