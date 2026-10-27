module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

section Cores

variable {G : Type*} [Group G]

theorem pCore_eq_of_forall_le {N : Subgroup G} (hN : N.Normal) (hN2 : IsPGroup 2 N)
    (hO : ∀ M : Subgroup G, M.Normal → IsPGroup 2 M → M ≤ N) : CFSG.pCore 2 G = N :=
  le_antisymm (sSup_le fun M hM => hO M hM.1 hM.2) (le_sSup ⟨hN, hN2⟩)

theorem oddCore_eq_bot_of_forall (h : ∀ M : Subgroup G, M.Normal → Odd (Nat.card M) → M = ⊥) :
    CFSG.oddCore G = ⊥ :=
  sSup_eq_bot.2 fun M hM => h M hM.1 hM.2

theorem conj_mem_inf_centralizer {Γ : Subgroup G} {h y x : G} (hh : h ∈ Γ)
    (hy : y ∈ Γ ⊓ Subgroup.centralizer {x}) :
    h * y * h⁻¹ ∈ Γ ⊓ Subgroup.centralizer {h * x * h⁻¹} := by
  obtain ⟨hyΓ, hyc⟩ := Subgroup.mem_inf.1 hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyc
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hh hyΓ) (inv_mem hh),
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc h * y * h⁻¹ * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
    _ = h * (x * y) * h⁻¹ := by rw [hyc]
    _ = h * x * h⁻¹ * (h * y * h⁻¹) := by group

theorem card_inf_centralizer_conj {Γ : Subgroup G} {g x : G} (hg : g ∈ Γ) :
    Nat.card (Γ ⊓ Subgroup.centralizer {g * x * g⁻¹} : Subgroup G) =
      Nat.card (Γ ⊓ Subgroup.centralizer {x} : Subgroup G) := by
  have hback : ∀ y ∈ Γ ⊓ Subgroup.centralizer {g * x * g⁻¹},
      g⁻¹ * y * g ∈ Γ ⊓ Subgroup.centralizer {x} := fun y hy => by
    have h := conj_mem_inf_centralizer (inv_mem hg) hy
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  exact Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y * g, hback y y.2⟩
      invFun := fun y => ⟨g * y * g⁻¹, conj_mem_inf_centralizer hg y.2⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }

end Cores

theorem large_Ree_two_centralizer_orders_ne (m : ℕ) :
    (2 ^ (2 * m + 1)) ^ 10 * ((2 ^ (2 * m + 1)) ^ 2 - 1) ≠
      (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
  set q : ℕ := 2 ^ (2 * m + 1) with hq
  have h2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : q ^ 10 * (q ^ 2 - 1) < q ^ 12 := by
    have hq2 : 0 < q ^ 2 := by positivity
    calc q ^ 10 * (q ^ 2 - 1) < q ^ 10 * q ^ 2 :=
          Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hq2 one_pos) (by positivity)
      _ = q ^ 12 := by ring
  have hle : q ^ 12 ≤ q ^ 12 * (q - 1) * (q ^ 2 + 1) := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by positivity))
  omega

theorem large_Ree_two_involution_centralizers
    (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K]
    [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} =
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ⊔ rankOneGroupTwo K m ∧
    F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ⊓ rankOneGroupTwo K m = ⊥ ∧
    ((F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩).subgroupOf
      (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1})).Normal ∧
    Nat.card (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) = (2 ^ (2 * m + 1)) ^ 10 ∧
    Nonempty (rankOneGroupTwo K m ≃* CFSG.Blueprint.suzukiGroup m K) ∧
    F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} = tKernel K m ⊔ rankOneGroupOne K m ∧
    tKernel K m ⊓ rankOneGroupOne K m = ⊥ ∧
    ((tKernel K m).subgroupOf (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1})).Normal ∧
    (tKernel K m : Set (ModGL F4.tag K)) = sylowVec m K '' {x | x 0 = 0 ∧ x 1 = 0 ∧ x 3 = 0} ∧
    Nat.card (tKernel K m) = (2 ^ (2 * m + 1)) ^ 9 ∧
    Nonempty (rankOneGroupOne K m ≃* SL2 K) ∧
    CFSG.pCore 2
        ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} : Subgroup (ModGL F4.tag K)) =
      (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩).subgroupOf
        (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1}) ∧
    Subgroup.centralizer ((F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩).subgroupOf
        (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1}) :
          Set ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :
            Subgroup (ModGL F4.tag K))) ≤
      (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩).subgroupOf
        (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1}) ∧
    CFSG.pCore 2
        ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} : Subgroup (ModGL F4.tag K)) =
      (tKernel K m).subgroupOf (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1}) ∧
    Subgroup.centralizer ((tKernel K m).subgroupOf
        (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1}) :
          Set ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} :
            Subgroup (ModGL F4.tag K))) ≤
      (tKernel K m).subgroupOf (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1}) ∧
    CFSG.oddCore
        ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} : Subgroup (ModGL F4.tag K)) =
      ⊥ ∧
    CFSG.oddCore
        ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} : Subgroup (ModGL F4.tag K)) =
      ⊥ ∧
    (∀ c : K, centralZ K m c ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} ∧
      F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} ≤
        Subgroup.centralizer {centralZ K m c}) ∧
    (∀ c : K, sylowL m K c ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} ∧
      F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} ≤
        Subgroup.centralizer {sylowL m K c}) ∧
    Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :
      Subgroup (ModGL F4.tag K)) =
        (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) ∧
    Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ 10 * ((2 ^ (2 * m + 1)) ^ 2 - 1) ∧
    ∀ g ∈ F4.reeGamma K m, g * centralZ K m 1 * g⁻¹ ≠ sylowL m K 1 := by
  obtain ⟨hz, hzR, ⟨eSz⟩, hzN, hzN2, hzC, hzO, hzOdd, -, -, -, -⟩ :=
    large_Ree_centralZ_centralizer hm hK
  obtain ⟨ht, htR, hQ, hQcard, ⟨eSL⟩, htN, htN2, htC, htO, htOdd, -, -, -, htcard, hU⟩ :=
    large_Ree_tOne_centralizer hm hK
  obtain ⟨hV2, hzcard⟩ := card_complement_two_and_centralizerZ hm hK hU
  have hz' : F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} = centralizerZ K m := hz
  have ht' : F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} = centralizerT K m := ht
  have hzcard' : Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :
      Subgroup (ModGL F4.tag K)) =
        (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
    rw [hz']
    exact hzcard
  have htcard' : Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ 10 * ((2 ^ (2 * m + 1)) ^ 2 - 1) := by
    rw [ht']
    exact htcard
  refine ⟨hz, hzR, by rw [hz']; exact hzN, hV2, ⟨eSz⟩, ht, htR, by rw [ht']; exact htN, hQ,
    hQcard, ⟨eSL.symm⟩, by rw [hz']; exact pCore_eq_of_forall_le hzN hzN2 hzO,
    by rw [hz']; exact hzC, by rw [ht']; exact pCore_eq_of_forall_le htN htN2 htO,
    by rw [ht']; exact htC, by rw [hz']; exact oddCore_eq_bot_of_forall hzOdd,
    by rw [ht']; exact oddCore_eq_bot_of_forall htOdd, fun c => ⟨?_, ?_⟩, fun c => ⟨?_, ?_⟩,
    hzcard', htcard', fun g hg hgt => ?_⟩
  · rw [hz']
    exact Subgroup.mem_sup_left (centralZ_mem_complement hm hK c)
  · rw [hz']
    exact centralizerZ_le_centralizer hm hK c
  · rw [ht']
    exact Subgroup.mem_sup_left (sylowL_mem_tKernel hK c)
  · rw [ht']
    exact sup_le (tKernel_le_centralizer hK c) (rankOneGroupOne_le_centralizer_sylowL c)
  · have h := card_inf_centralizer_conj (x := centralZ K m 1) hg
    rw [hgt, htcard', hzcard'] at h
    exact large_Ree_two_centralizer_orders_ne m h

end CFSG.LieType.Ree.LargeReeInvolution
