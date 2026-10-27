module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_tG_not_mem_normal (hc : Ctx10 t L S x₁ x₂ lam rho tau) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (hRcard : (Nat.card A - 1) * 2 ^ 7 < Nat.card R)
    (hAR : NormalIn A R) (g : G) : g * t * g⁻¹ ∉ A := by
  intro hmem
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hc.hyp.ord_t
    rw [h, orderOf_one] at h2
    norm_num at h2
  have ha1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hb := card_le_mul_card_centralizer (R := R) (A := A) hAR.2 hmem ha1 hAR.1
  have hQp : IsPGroup 2 (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) :=
    hR.to_le inf_le_left
  have hQbound := S4A.card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t)
    hc.le_invCent hc.isPGroup hc.relIndex_odd (Ctx4.card_S_seven hc.toCtx4) g hQp inf_le_right
  have hRle : Nat.card R ≤ (Nat.card A - 1) * 2 ^ 7 :=
    calc Nat.card R
        ≤ (Nat.card A - 1) *
            Nat.card (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) := hb
      _ ≤ (Nat.card A - 1) * 2 ^ 7 := Nat.mul_le_mul_left _ hQbound
  exact absurd hRcard (not_lt.mpr hRle)

theorem q13b_cent_t (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    𝒮 ⊓ centralizer ({t} : Set G) = S :=
  c17_cent_eq h.c11.toCtx10 h𝒮 (h.c11.S_le_U.trans hU)

theorem q13b_mem_closure_pair {a b x : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hx : x ∈ closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hx using closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]

theorem q13b_mem_zpowers_sq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    simpa [pow_two] using hz
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem q13b_normal_meets_center {𝒮 F : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hF : NormalIn F 𝒮)
    (hne : F ≠ ⊥) : ∃ c ∈ F, c ≠ 1 ∧ c ∈ 𝒮 ⊓ centralizer ((𝒮 : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥𝒮 := IsPGroup.isNilpotent h𝒮
  let F' : Subgroup ↥𝒮 := F.subgroupOf 𝒮
  have hF'normal : F'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hF.2 (g : G) g.2 (n : G) hn
  have hF'ne : F' ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro f hf
    have hmem : (⟨f, hF.1 hf⟩ : ↥𝒮) ∈ F' := by
      rw [Subgroup.mem_subgroupOf]
      exact hf
    rw [hbot] at hmem
    simpa using hmem
  have hneBot : F' ⊓ Subgroup.center ↥𝒮 ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hF'ne
  obtain ⟨c', hc'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hneBot
  have hc'F : (c'.1 : G) ∈ F := by
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp c'.2).1
  have hc'1 : (c'.1 : G) ≠ 1 := by
    intro h1
    exact hc' (Subtype.ext (Subtype.ext h1))
  have hc'cent : (c'.1 : G) ∈ centralizer ((𝒮 : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr (fun s hs => ?_)
    have hcomm : (⟨s, hs⟩ : ↥𝒮) * c'.1 = c'.1 * (⟨s, hs⟩ : ↥𝒮) :=
      (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp c'.2).2) ⟨s, hs⟩
    exact congrArg Subtype.val hcomm
  exact ⟨(c'.1 : G), hc'F, hc'1, Subgroup.mem_inf.mpr ⟨c'.1.2, hc'cent⟩⟩

private theorem q13b_om_not_comm_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * t ≠ t * om := by
  intro hc
  have homt : om * t = t * tau * om := by
    calc om * t = (om * t * om⁻¹) * om := by group
      _ = (t * tau) * om := by rw [h.t_om]
  have h2 : tau * om = 1 * om := by
    apply mul_left_cancel (a := t)
    calc t * (tau * om) = t * tau * om := by group
      _ = om * t := homt.symm
      _ = t * om := hc
      _ = t * (1 * om) := by group
  exact q13b_tau_ne_one h (mul_right_cancel h2)

theorem q13b_Z_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    𝒮 ⊓ centralizer ((𝒮 : Subgroup G) : Set G) = zpowers ((x₁ * x₂) ^ 2) := by
  obtain ⟨hz1, hz2⟩ := q13b_z_facts h
  have ht𝒮 : t ∈ 𝒮 := hU (q13b_O_le_U h (q13b_t_mem_O h))
  have hom𝒮 : om ∈ 𝒮 := hU (q13b_O_le_U h (q13b_om_mem_O h))
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzX : (x₁ * x₂) ^ 2 ∈ ctxX t tau x₁ x₂ :=
    ((p0_V_le_N_le_X t tau x₁ x₂).1.trans (p0_V_le_N_le_X t tau x₁ x₂).2) hzV
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htZ : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t := q13a_X_comm h t htX _ hzX
  have hZle : 𝒮 ⊓ centralizer ((𝒮 : Subgroup G) : Set G) ≤ zpowers ((x₁ * x₂) ^ 2) := by
    intro c hc
    obtain ⟨hc𝒮, hcC⟩ := Subgroup.mem_inf.mp hc
    have hct : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hcC) t ht𝒮
    have hcS : c ∈ S := by
      have : c ∈ 𝒮 ⊓ centralizer ({t} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hc𝒮, Subgroup.mem_centralizer_singleton_iff.mpr hct.symm⟩
      rwa [q13b_cent_t h h𝒮 hU] at this
    have hcCS : c ∈ S ⊓ centralizer ((S : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcS, Subgroup.mem_centralizer_iff.mpr
        (fun s hs => (Subgroup.mem_centralizer_iff.mp hcC) s (hU (h.c11.S_le_U hs)))⟩
    rw [Ctx4.center_S h.c11.toCtx10.toCtx4] at hcCS
    rcases q13b_mem_closure_pair (q13a_t_mul_self h) hz2 htZ hcCS with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd (show om * t = t * om by
          rw [← h1]; exact (Subgroup.mem_centralizer_iff.mp hcC) om hom𝒮)
        (q13b_om_not_comm_t h)
    · rw [h1]; exact Subgroup.mem_zpowers _
    · apply absurd ?_ (q13b_om_not_comm_t h)
      have hczom : om * ((x₁ * x₂) ^ 2) = ((x₁ * x₂) ^ 2) * om :=
        (q13a_om_comm h).2.2 _ hzV
      have hcomm_om : om * c = c * om := (Subgroup.mem_centralizer_iff.mp hcC) om hom𝒮
      rw [h1] at hcomm_om
      have : om * t * (x₁ * x₂) ^ 2 = t * om * (x₁ * x₂) ^ 2 := by
        calc om * t * (x₁ * x₂) ^ 2 = om * (t * (x₁ * x₂) ^ 2) := by group
          _ = (t * (x₁ * x₂) ^ 2) * om := hcomm_om
          _ = t * ((x₁ * x₂) ^ 2 * om) := by group
          _ = t * (om * (x₁ * x₂) ^ 2) := by rw [hczom]
          _ = t * om * (x₁ * x₂) ^ 2 := by group
      exact mul_right_cancel this
  refine le_antisymm hZle ?_
  rw [Subgroup.zpowers_le]
  have hne : 𝒮 ≠ ⊥ := by
    intro hbot
    have htbot : t ∈ (⊥ : Subgroup G) := hbot ▸ ht𝒮
    exact S4A.t_ne_one h.c11.hyp (Subgroup.mem_bot.mp htbot)
  have hnorm : NormalIn 𝒮 𝒮 :=
    ⟨le_rfl, fun g hg k hk => 𝒮.mul_mem (𝒮.mul_mem hg hk) (𝒮.inv_mem hg)⟩
  obtain ⟨c, _, hc1, hcZ⟩ := q13b_normal_meets_center h𝒮 hnorm hne
  rcases q13b_mem_zpowers_sq hz2 (hZle hcZ) with h1 | h1
  · exact absurd h1 hc1
  · rw [← h1]; exact hcZ

theorem q13b_tG_N (h : Q13Om t L S x₁ x₂ lam rho tau om) (g : G) :
    g * t * g⁻¹ ∉ ctxN tau x₁ x₂ := by
  refine q13b_tG_not_mem_normal h.c11.toCtx10 (R := ctxU t tau x₁ x₂ lam)
    (A := ctxN tau x₁ x₂) (q13b_isPGroup_U h) ?_ (q13b_N_normal_U h) g
  rw [q13b_card_N h, q13b_card_U h]
  norm_num

theorem q13b_z_mem_of_normal (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮) (hne : F ≠ ⊥) :
    (x₁ * x₂) ^ 2 ∈ F := by
  obtain ⟨c, hcF, hc1, hcZ⟩ := q13b_normal_meets_center h𝒮 hF hne
  rw [q13b_Z_eq h h𝒮 hU] at hcZ
  rcases q13b_mem_zpowers_sq (q13b_z_facts h).2 hcZ with h1 | h1
  · exact absurd h1 hc1
  · rw [← h1]; exact hcF

theorem q13b_z_central (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    ∀ u ∈ 𝒮, u * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * u := by
  intro u hu
  have hz : (x₁ * x₂) ^ 2 ∈ 𝒮 ⊓ centralizer ((𝒮 : Subgroup G) : Set G) := by
    rw [q13b_Z_eq h h𝒮 hU]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_centralizer_iff.mp hz.2 u hu

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
