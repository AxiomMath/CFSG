module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512A
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem false_of_e8_le_C {c₁ c₂ : G} (hc₁ : c₁ ∈ coreActionKernel L)
    (hc₂ : c₂ ∈ coreActionKernel L) (hc₁2 : c₁ * c₁ = 1) (hc₂2 : c₂ * c₂ = 1) (hc₁1 : c₁ ≠ 1)
    (hc₂1 : c₂ ≠ 1) (hc₁₂ : c₁ ≠ c₂) (hcc : c₁ * c₂ = c₂ * c₁) (hzc₁ : c₁ * z = z * c₁)
    (hzc₂ : c₂ * z = z * c₂)
    (hz : ∀ w ∈ kleinFourOfCommutingInvolutions c₁ c₂ hc₁2 hc₂2 hcc, w ≠ z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  set U := kleinFourOfCommutingInvolutions c₁ c₂ hc₁2 hc₂2 hcc with hU
  have hU4 : Nat.card U = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions c₁ c₂ hc₁2 hc₂2 hc₁1 hc₂1 hc₁₂ hcc).card_four
  have hUmem : ∀ w ∈ U, w = c₁ * c₂ ∨ w = c₁ ∨ w = c₂ ∨ w = 1 := fun w hw =>
    (mem_kleinFour_iff hc₁2 hc₂2 hcc).mp hw
  have hUsq : ∀ w ∈ U, w * w = 1 := fun w hw => by
    rcases hUmem w hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ by group, ← hcc,
        show c₁ * (c₁ * c₂) * c₂ = (c₁ * c₁) * (c₂ * c₂) by group, hc₁2, hc₂2, one_mul]
    · exact hc₁2
    · exact hc₂2
    · exact one_mul 1
  have hUz : ∀ w ∈ U, ∀ y ∈ zpowers z, w * y = y * w := by
    intro w hw y hy
    rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hy with h1 | h1 <;> rw [h1]
    · rw [mul_one, one_mul]
    · rcases hUmem w hw with h2 | h2 | h2 | h2 <;> rw [h2]
      · rw [mul_assoc, hzc₂, ← mul_assoc, hzc₁, mul_assoc]
      · exact hzc₁
      · exact hzc₂
      · rw [one_mul, mul_one]
  have hdisj : U ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rcases eq_one_or_eq_of_mem_zpowers_sq hz2 (mem_inf.mp hw).2 with h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd h1 (hz w (mem_inf.mp hw).1)
  have h8 : Nat.card ↥(U ⊔ zpowers z) = 8 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U (zpowers z)
      (le_normalizer_of_commute hUz) (disjoint_iff.mpr hdisj), hU4, Nat.card_zpowers, h.z2]
  have hUC : U ≤ coreActionKernel L := fun w hw => by
    rcases hUmem w hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact mul_mem hc₁ hc₂
    · exact hc₁
    · exact hc₂
    · exact one_mem _
  have hEC : U ⊔ zpowers z ≤ coreActionKernel L :=
    sup_le hUC (zpowers_le.mpr (h.Q_le h.zQ))
  have hEsq : ∀ w ∈ U ⊔ zpowers z, w ^ 2 = 1 := fun w hw => by
    rw [sq]
    exact sq_eq_one_of_mem_sup hUsq (fun y hy => by
      rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hy with h1 | h1 <;> rw [h1]
      · exact one_mul 1
      · exact hz2) hUz hw
  have h3 := Foote47.three_le_pRank_of_card_eight hEC hEsq h8
  rw [h.rankCL] at h3
  omega

include ε in
theorem false_of_fourgroup_cent_z (hD : Foote5AutData 𝕊 Lin) {V : Subgroup G}
    (hVz : V ≤ centralizer ({z} : Set G)) (hVsq : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4)
    (hVL : V ⊓ L = ⊥) {y : G} (hyz : y * z = z * y) (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hyfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.z2
    rw [h1, orderOf_one] at this
    omega
  have hVN : ∀ v ∈ V, v ∈ normalizer (L : Set G) := fun v hv => h.centralizer_le_normalizer (hVz hv)
  have hyN : y ∈ normalizer (L : Set G) :=
    h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr hyz)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hVsq ha hb
  have hVzc : ∀ v ∈ V, v * z = z * v := fun v hv => mem_centralizer_singleton_iff.mp (hVz hv)
  have hzVL : ∀ v ∈ V, ∀ ℓ ∈ L, z ≠ v * ℓ := by
    intro v hv ℓ hℓ hzv
    have h1 : y * z * y⁻¹ = z := by rw [hyz, mul_inv_cancel_right]
    rw [hzv] at h1
    have hyℓ : y * ℓ * y⁻¹ ∈ L := (mem_normalizer_iff.mp hyN ℓ).mp hℓ
    have h2 : v⁻¹ * (y * v * y⁻¹) = ℓ * (y * ℓ * y⁻¹)⁻¹ := by
      calc v⁻¹ * (y * v * y⁻¹) = v⁻¹ * (y * (v * ℓ) * y⁻¹) * (y * ℓ * y⁻¹)⁻¹ := by group
        _ = v⁻¹ * (v * ℓ) * (y * ℓ * y⁻¹)⁻¹ := by rw [h1]
        _ = ℓ * (y * ℓ * y⁻¹)⁻¹ := by group
    have h3 : v⁻¹ * (y * v * y⁻¹) ∈ V ⊓ L := mem_inf.mpr ⟨mul_mem (inv_mem hv) (hyV v hv),
      h2 ▸ mul_mem hℓ (inv_mem hyℓ)⟩
    rw [hVL, mem_bot, inv_mul_eq_one] at h3
    have hv1 := hyfix v hv h3.symm
    rw [hv1, one_mul] at hzv
    have h4 : z ∈ Q ⊓ L := mem_inf.mpr ⟨h.zQ, hzv ▸ hℓ⟩
    rw [h.Q_inf_L, mem_bot] at h4
    exact hz1 h4
  let f : ↥V → ↥V := fun w => ⟨(w : G)⁻¹ * (y * w * y⁻¹), mul_mem (inv_mem w.2) (hyV w w.2)⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (a : G)⁻¹ * (y * a * y⁻¹) = (b : G)⁻¹ * (y * b * y⁻¹) := congrArg Subtype.val hab
    have h2 : y * ((b : G) * (a : G)⁻¹) * y⁻¹ = (b : G) * (a : G)⁻¹ := by
      have hya := hyV a a.2
      have hyb := hyV b b.2
      calc y * ((b : G) * (a : G)⁻¹) * y⁻¹ = (y * b * y⁻¹) * (y * a * y⁻¹)⁻¹ := by group
        _ = b * ((b : G)⁻¹ * (y * b * y⁻¹)) * (y * a * y⁻¹)⁻¹ := by group
        _ = b * ((a : G)⁻¹ * (y * a * y⁻¹)) * (y * a * y⁻¹)⁻¹ := by rw [h1]
        _ = (b : G) * (a : G)⁻¹ := by group
    have h3 := hyfix _ (mul_mem b.2 (inv_mem a.2)) h2
    exact Subtype.ext ((mul_inv_eq_one.mp h3).symm)
  have hfsurj := Finite.surjective_of_injective hfinj
  have hinn : ∀ v ∈ V, actG L ε v ∈ innAut5 𝕊 := by
    intro v hv
    obtain ⟨w, hw⟩ := hfsurj ⟨v, hv⟩
    have hwv : (w : G)⁻¹ * (y * w * y⁻¹) = v := congrArg Subtype.val hw
    have hwN := hVN w w.2
    rw [← hwv, actG_mul ε (inv_mem hwN) (mul_mem (mul_mem hyN hwN) (inv_mem hyN)),
      actG_mul ε (mul_mem hyN hwN) (inv_mem hyN), actG_mul ε hyN hwN, actG_inv ε hwN,
      actG_inv ε hyN]
    have h1 := hD.commutator_mem (actG L ε w)⁻¹ (actG L ε y)
    rw [inv_inv] at h1
    convert h1 using 1
    group
  by_cases hA : ∃ v ∈ V, v ≠ 1 ∧ v ∈ coreActionKernel L
  ·
    obtain ⟨v, hv, hv1, hvC⟩ := hA
    set v' := y * v * y⁻¹ with hv'
    have hv'V := hyV v hv
    have hv'C : v' ∈ coreActionKernel L :=
      (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L hyN) v).mp hvC
    have hv'1 : v' ≠ 1 := fun h1 => hv1 (by
      calc v = y⁻¹ * v' * y := by rw [hv']; group
        _ = 1 := by rw [h1]; group)
    have hvv' : v ≠ v' := fun h1 => hv1 (hyfix v hv h1.symm)
    have hvv'c := hVc v hv v' hv'V
    refine h.false_of_e8_le_C hvC hv'C (hVsq v hv) (hVsq v' hv'V) hv1 hv'1 hvv' hvv'c
      (hVzc v hv) (hVzc v' hv'V) fun w hw hwz => ?_
    have hwV : w ∈ V := by
      rcases (mem_kleinFour_iff (hVsq v hv) (hVsq v' hv'V) hvv'c).mp hw with h1 | h1 | h1 | h1
        <;> rw [h1]
      · exact mul_mem hv hv'V
      · exact hv
      · exact hv'V
      · exact one_mem _
    rw [hwz] at hwV
    exact hzVL z hwV 1 (one_mem L) (by rw [mul_one])
  · push Not at hA
    obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hv₂1, hv₁₂⟩ := exists_two_ne_one_of_card_four V hV4
    obtain ⟨x₁, hx₁⟩ := hinn v₁ hv₁
    obtain ⟨x₂, hx₂⟩ := hinn v₂ hv₂
    have hv₁N := hVN v₁ hv₁
    have hv₂N := hVN v₂ hv₂
    have hcinj := h.conj_injective ε
    have hx₁2 : x₁ * x₁ = 1 := hcinj (by
      rw [map_mul, hx₁, ← actG_mul ε hv₁N hv₁N, hVsq v₁ hv₁, actG_one, map_one])
    have hx₂2 : x₂ * x₂ = 1 := hcinj (by
      rw [map_mul, hx₂, ← actG_mul ε hv₂N hv₂N, hVsq v₂ hv₂, actG_one, map_one])
    have hact1 : ∀ v ∈ V, v ≠ 1 → actG L ε v ≠ 1 := fun v hv hv1 h1 =>
      hA v hv hv1 ((actG_eq_one_iff ε (hVN v hv)).mp h1)
    have hx₁1 : x₁ ≠ 1 := fun h1 => hact1 v₁ hv₁ hv₁1 (by rw [← hx₁, h1, map_one])
    have hx₂1 : x₂ ≠ 1 := fun h1 => hact1 v₂ hv₂ hv₂1 (by rw [← hx₂, h1, map_one])
    have hx₁₂c : x₁ * x₂ = x₂ * x₁ := hcinj (by
      rw [map_mul, map_mul, hx₁, hx₂, ← actG_mul ε hv₁N hv₂N, ← actG_mul ε hv₂N hv₁N,
        hVc v₁ hv₁ v₂ hv₂])
    have hx₁₂ : x₁ ≠ x₂ := fun h1 => by
      have h2 : actG L ε (v₁⁻¹ * v₂) = 1 := by
        rw [actG_mul ε (inv_mem hv₁N) hv₂N, actG_inv ε hv₁N, ← hx₁, ← hx₂, h1, inv_mul_cancel]
      exact hact1 _ (mul_mem (inv_mem hv₁) hv₂) (fun h3 => hv₁₂ (by
        rw [inv_mul_eq_one] at h3
        exact h3)) h2
    set B := V ⊔ zpowers z with hBdef
    have hVzcomm : ∀ v ∈ V, ∀ w ∈ zpowers z, v * w = w * v := by
      intro v hv w hw
      rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hw with h1 | h1 <;> rw [h1]
      · rw [mul_one, one_mul]
      · exact hVzc v hv
    have hBN : B ≤ normalizer (L : Set G) :=
      sup_le (fun v hv => hVN v hv) (zpowers_le.mpr (h.S_le h.zS_mem))
    have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => sq_eq_one_of_mem_sup hVsq (fun w hw => by
      rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hw with h1 | h1 <;> rw [h1]
      · exact one_mul 1
      · exact hz2) hVzcomm hb
    have hB2 : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by
      rw [pow_one, sq]
      exact hBsq b b.2)⟩
    have hfixB : ∀ x : 𝕊, (∀ v ∈ V, MulAut.conj x * actG L ε v = actG L ε v * MulAut.conj x) →
        ∀ b ∈ B, actG L ε b x = x := by
      intro x hx b hb
      obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup_commute hVzcomm hb
      have hwN : w ∈ normalizer (L : Set G) := hBN (mem_sup_right hw)
      have hw1 : actG L ε w = 1 := by
        rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hw with h1 | h1 <;> rw [h1]
        · exact actG_one ε
        · exact (h.actG_eq_one_iff_mem_Q ε h.zS_mem).mpr h.zQ
      rw [actG_mul ε (hVN v hv) hwN, hw1, mul_one]
      obtain ⟨xv, hxv⟩ := hinn v hv
      have h1 := hx v hv
      rw [← hxv, ← map_mul, ← map_mul] at h1
      have h2 := hcinj h1
      rw [← hxv, MulAut.conj_apply, ← h2]
      group
    have hfix₁ := hfixB x₁ fun v hv => by
      rw [hx₁, ← actG_mul ε hv₁N (hVN v hv), ← actG_mul ε (hVN v hv) hv₁N, hVc v₁ hv₁ v hv]
    have hfix₂ := hfixB x₂ fun v hv => by
      rw [hx₂, ← actG_mul ε hv₂N (hVN v hv), ← actG_mul ε (hVN v hv) hv₂N, hVc v₂ hv₂ v hv]
    set N := L ⊓ centralizer (B : Set G) with hNdef
    have hlift : ∀ x : 𝕊, (∀ b ∈ B, actG L ε b x = x) → x ∈ (N.subgroupOf L).map (psi L ε) := by
      intro x hx
      obtain ⟨k, hkL, hkC, hk⟩ := exists_lift_of_fixed_pgroup ε hB2 hBN hx
      exact (mem_map_psi_iff ε).mpr ⟨k, hkL, mem_inf.mpr ⟨hkL, hkC⟩, hk⟩
    obtain ⟨u₁, hu₁N, u₂, hu₂N, hu₁L, hu₂L, hψ₁, hψ₂, hu₁2, hu₂2, hu₁₂⟩ :=
      exists_commuting_involution_lifts ε (hlift x₁ hfix₁) (hlift x₂ hfix₂) hx₁2 hx₂2 hx₁1 hx₂1
        hx₁₂c
    have huB : ∀ u ∈ N, ∀ b ∈ B, u * b = b * u := fun u hu b hb =>
      (mem_centralizer_iff.mp (mem_inf.mp hu).2 b hb).symm
    have hu₁N' := le_normalizer hu₁L
    have hu₂N' := le_normalizer hu₂L
    have hc₁C : u₁ * v₁ ∈ coreActionKernel L := by
      rw [← actG_eq_one_iff ε (mul_mem hu₁N' hv₁N), actG_mul ε hu₁N' hv₁N,
        actG_of_mem_self ε hu₁L, hψ₁, ← hx₁, ← map_mul, hx₁2, map_one]
    have hc₂C : u₂ * v₂ ∈ coreActionKernel L := by
      rw [← actG_eq_one_iff ε (mul_mem hu₂N' hv₂N), actG_mul ε hu₂N' hv₂N,
        actG_of_mem_self ε hu₂L, hψ₂, ← hx₂, ← map_mul, hx₂2, map_one]
    have hv₁B : v₁ ∈ B := mem_sup_left hv₁
    have hv₂B : v₂ ∈ B := mem_sup_left hv₂
    have hzB : z ∈ B := mem_sup_right (mem_zpowers z)
    have hu₁v₁ := huB u₁ hu₁N v₁ hv₁B
    have hu₁v₂ := huB u₁ hu₁N v₂ hv₂B
    have hu₂v₁ := huB u₂ hu₂N v₁ hv₁B
    have hu₂v₂ := huB u₂ hu₂N v₂ hv₂B
    have hVLmem : ∀ v ∈ V, v ∈ L → v = 1 := fun v hv hvL => by
      have h1 : v ∈ V ⊓ L := mem_inf.mpr ⟨hv, hvL⟩
      rwa [hVL, mem_bot] at h1
    have hc₁2 : u₁ * v₁ * (u₁ * v₁) = 1 := by
      rw [show u₁ * v₁ * (u₁ * v₁) = u₁ * (v₁ * u₁) * v₁ by group, ← hu₁v₁,
        show u₁ * (u₁ * v₁) * v₁ = (u₁ * u₁) * (v₁ * v₁) by group, hu₁2, hVsq v₁ hv₁, one_mul]
    have hc₂2 : u₂ * v₂ * (u₂ * v₂) = 1 := by
      rw [show u₂ * v₂ * (u₂ * v₂) = u₂ * (v₂ * u₂) * v₂ by group, ← hu₂v₂,
        show u₂ * (u₂ * v₂) * v₂ = (u₂ * u₂) * (v₂ * v₂) by group, hu₂2, hVsq v₂ hv₂, one_mul]
    have hc₁1 : u₁ * v₁ ≠ 1 := fun h1 => hv₁1 (hVLmem v₁ hv₁ (by
      rw [show v₁ = u₁⁻¹ * (u₁ * v₁) by group, h1, mul_one]
      exact inv_mem hu₁L))
    have hc₂1 : u₂ * v₂ ≠ 1 := fun h1 => hv₂1 (hVLmem v₂ hv₂ (by
      rw [show v₂ = u₂⁻¹ * (u₂ * v₂) by group, h1, mul_one]
      exact inv_mem hu₂L))
    have hc₁₂ : u₁ * v₁ ≠ u₂ * v₂ := fun h1 => hv₁₂ (by
      have h2 : v₁ * v₂⁻¹ ∈ L := by
        rw [show v₁ * v₂⁻¹ = u₁⁻¹ * (u₁ * v₁) * v₂⁻¹ by group, h1,
          show u₁⁻¹ * (u₂ * v₂) * v₂⁻¹ = u₁⁻¹ * u₂ by group]
        exact mul_mem (inv_mem hu₁L) hu₂L
      have h3 := hVLmem _ (mul_mem hv₁ (inv_mem hv₂)) h2
      rw [mul_inv_eq_one] at h3
      exact h3)
    have hcc : u₁ * v₁ * (u₂ * v₂) = u₂ * v₂ * (u₁ * v₁) := by
      calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by group
        _ = u₁ * (u₂ * v₁) * v₂ := by rw [hu₂v₁]
        _ = (u₁ * u₂) * (v₁ * v₂) := by group
        _ = (u₂ * u₁) * (v₂ * v₁) := by rw [hu₁₂, hVc v₁ hv₁ v₂ hv₂]
        _ = u₂ * (u₁ * v₂) * v₁ := by group
        _ = u₂ * (v₂ * u₁) * v₁ := by rw [hu₁v₂]
        _ = u₂ * v₂ * (u₁ * v₁) := by group
    have hzc₁ : u₁ * v₁ * z = z * (u₁ * v₁) := by
      rw [mul_assoc, hVzc v₁ hv₁, ← mul_assoc, huB u₁ hu₁N z hzB, mul_assoc]
    have hzc₂ : u₂ * v₂ * z = z * (u₂ * v₂) := by
      rw [mul_assoc, hVzc v₂ hv₂, ← mul_assoc, huB u₂ hu₂N z hzB, mul_assoc]
    refine h.false_of_e8_le_C hc₁C hc₂C hc₁2 hc₂2 hc₁1 hc₂1 hc₁₂ hcc hzc₁ hzc₂ fun w hw hwz => ?_
    rcases (mem_kleinFour_iff hc₁2 hc₂2 hcc).mp hw with h1 | h1 | h1 | h1
    · apply hzVL (v₁ * v₂) (mul_mem hv₁ hv₂) (u₁ * u₂) (mul_mem hu₁L hu₂L)
      have huv := huB (u₁ * u₂) (mul_mem hu₁N hu₂N) (v₁ * v₂) (mul_mem hv₁B hv₂B)
      rw [← hwz, h1]
      calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by group
        _ = u₁ * (u₂ * v₁) * v₂ := by rw [← hu₂v₁]
        _ = (u₁ * u₂) * (v₁ * v₂) := by group
        _ = v₁ * v₂ * (u₁ * u₂) := huv
    · exact hzVL v₁ hv₁ u₁ hu₁L (by rw [← hwz, h1, hu₁v₁])
    · exact hzVL v₂ hv₂ u₂ hu₂L (by rw [← hwz, h1, hu₂v₂])
    · exact hz1 (by rw [← hwz, h1])

end Sec5

end CFSG.ComponentClassification.Foote5
