module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

theorem commute_of_odd_order_of_commutator_central {Q U : Subgroup G} {c : G}
    (hodd : Odd (orderOf c)) (hw : ∀ x ∈ Q, ⁅c, x⁆ ∈ U)
    (hUz : ∀ w ∈ U, (∀ k ∈ Q, k * w = w * k) ∧ w ^ 2 = 1) (hUc : ∀ w ∈ U, c * w = w * c) :
    ∀ x ∈ Q, c * x = x * c := by
  intro x hx
  set w : G := ⁅c, x⁆ with hwdef
  have hwU : w ∈ U := hw x hx
  have hcx : c * x * c⁻¹ = w * x := by
    rw [hwdef]
    simp only [commutatorElement_def]
    group
  have hcomm : Commute c w := hUc w hwU
  have key : ∀ k : ℕ, c ^ k * x * (c ^ k)⁻¹ = w ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcwk : c * w ^ k = w ^ k * c := (hcomm.pow_right k).eq
      calc c ^ (k + 1) * x * (c ^ (k + 1))⁻¹ = c * (c ^ k * x * (c ^ k)⁻¹) * c⁻¹ := by
            rw [pow_succ']
            group
        _ = c * (w ^ k * x) * c⁻¹ := by rw [ih]
        _ = (c * w ^ k) * x * c⁻¹ := by group
        _ = (w ^ k * c) * x * c⁻¹ := by rw [hcwk]
        _ = w ^ k * (c * x * c⁻¹) := by group
        _ = w ^ k * (w * x) := by rw [hcx]
        _ = w ^ (k + 1) * x := by rw [pow_succ, mul_assoc]
  have h1 := key (orderOf c)
  rw [pow_orderOf_eq_one] at h1
  simp only [inv_one, mul_one, one_mul] at h1
  have h2 : w ^ orderOf c = 1 := by
    have : w ^ orderOf c * x = 1 * x := by rw [← h1, one_mul]
    exact mul_right_cancel this
  obtain ⟨j, hj⟩ := hodd
  have h3 : w = 1 := by
    have e : w ^ orderOf c = (w ^ 2) ^ j * w := by
      rw [hj, pow_succ, pow_mul]
    rw [e, (hUz w hwU).2, one_pow, one_mul] at h2
    exact h2
  have h4 : c * x * c⁻¹ = x := by rw [hcx, h3, one_mul]
  calc c * x = c * x * c⁻¹ * c := by group
    _ = x * c := by rw [h4]

theorem isPGroup_two_of_odd_eq_one [Finite G] {C : Subgroup G}
    (h : ∀ c ∈ C, Odd (orderOf c) → c = 1) : IsPGroup 2 ↥C := by
  intro c
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : G)).ne'
  refine ⟨k, ?_⟩
  have hodd : Odd (orderOf ((c : G) ^ (2 ^ k))) := by
    have : orderOf ((c : G) ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    rwa [this]
  exact Subtype.ext (h _ (C.pow_mem c.2 _) hodd)

theorem centralizer_normal_of_normal {V : Subgroup G} (hV : V.Normal) :
    (Subgroup.centralizer (V : Set G)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := hV.conj_mem v hv g⁻¹
    simpa using this
  have := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * v := by group

end Tools

section Main

theorem natKernelProp : NatKernelProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc hgen hsum
  classical
  have hS := ctx.setting
  have hbase := hloc.base
  have hQn := natQ_normal hS
  have hLSn := normal_L_sup_baum hS
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hS.reduced.2.1)
  have hCn := centralizer_normal_of_normal hVn
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set Q : Subgroup G := pCoreOf 2 (L ⊔ baum R) with hQ
  have hQ2 : IsPGroup 2 ↥Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (L ⊔ baum R)
  have hQLS : Q ≤ L ⊔ baum R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (L ⊔ baum R)
  have hQO : Q ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q ⊤ le_top inferInstance hQ2
  have hO2C : pCoreOf 2 (⊤ : Subgroup G) ≤ Subgroup.centralizer (V : Set G) := by
    have hO2 : IsPGroup 2 ↥(pCoreOf 2 (⊤ : Subgroup G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 ⊤
    refine hS.reduced.2.2.2 _ le_top
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤) fun d hd => ?_
    obtain ⟨k, hk⟩ := hO2 ⟨d, hd⟩
    exact ⟨k, by
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact Subgroup.one_mem _⟩
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := hQO.trans hO2C
  have hUQ : ⁅Q, L⁆ ≤ BlueprintB2.centerTorsion 2 Q := by
    have := hgen.central
    rwa [BlueprintB2.omegaOneCenterOf_eq_centerTorsion] at this
  have hQLV : ⁅Q, L⁆ = ⁅V, L⁆ := hsum.commutator.1
  have hVL_le : ⁅V, L⁆ ≤ V := Subgroup.commutator_le_left V L
  have hodd1 : ∀ c ∈ (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G), Odd (orderOf c) → c = 1 := by
    intro c hc hodd
    have hcL : c ∈ L := Subgroup.subset_closure ⟨Subgroup.mem_top c, hodd⟩
    have hcQ : ∀ x ∈ Q, c * x = x * c := by
      refine commute_of_odd_order_of_commutator_central (U := ⁅Q, L⁆) hodd (fun x hx => ?_)
        (fun w hw => ?_) (fun w hw => ?_)
      · have h := Subgroup.commutator_mem_commutator hcL hx
        rwa [Subgroup.commutator_comm] at h
      · obtain ⟨-, hc', h2⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hUQ hw)
        exact ⟨hc', h2⟩
      · have hwV : w ∈ V := hVL_le (hQLV ▸ hw)
        exact (Subgroup.mem_centralizer_iff.mp hc.2 w hwV).symm
    have hcQ' : c ∈ (L ⊔ baum R) ⊓ Subgroup.centralizer (Q : Set G) :=
      ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcQ x hx).symm⟩
    have hcQmem : c ∈ Q := hbase.charTwo hcQ'
    obtain ⟨k, hk⟩ := hQ2 ⟨c, hcQmem⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hCLS : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) ≤ Q := by
    have hC2 : IsPGroup 2 ↥((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) :=
      isPGroup_two_of_odd_eq_one hodd1
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ (L ⊔ baum R)
      inf_le_left ?_ hC2
    have := hLSn
    have := hCn
    exact Subgroup.normal_subgroupOf
  have hK2 : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) = Q :=
    le_antisymm hCLS (le_inf hQLS hQC)
  refine ⟨?_, hK2⟩
  refine le_antisymm ?_ (le_inf le_top hO2C)
  have hC2 : IsPGroup 2 ↥((⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) := by
    refine isPGroup_two_of_odd_eq_one fun c hc hodd => ?_
    have hcL : c ∈ L := Subgroup.subset_closure ⟨Subgroup.mem_top c, hodd⟩
    exact hodd1 c ⟨(le_sup_left : L ≤ L ⊔ baum R) hcL, hc.2⟩ hodd
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ ⊤ le_top ?_ hC2
  have := hCn
  exact Subgroup.normal_subgroupOf

end Main

end CFSG.QuasithinUnique.Setup.Lift
