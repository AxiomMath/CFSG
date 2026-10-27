module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Cond
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conf
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Outer
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Rank

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] {x : G}

theorem card_sup_zpowers {V : Subgroup G} (hx : x * x = 1) (hxV : x ∉ V)
    (hcomm : ∀ v ∈ V, v * x = x * v) : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) =
      2 * Nat.card V := by
  have hpow : ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro k
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left; rw [zpow_mul, zpow_two, hx, one_zpow]
    · right; rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]
  have hcommV : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((commute_of_mul_eq (hcomm a ha)).zpow_right k).eq
  have hrel : V.relIndex (V ⊔ Subgroup.zpowers x) = 2 := by
    have hdvd : V.relIndex (V ⊔ Subgroup.zpowers x) ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨x, mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
      intro b hb
      obtain ⟨v, hv, c, hc, rfl⟩ := (mem_sup_iff_of_comm hcommV).1 hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      rcases hpow k with h1 | h1
      · right; rw [h1, mul_one]; exact hv
      · left
        have : v * x * x = v := by rw [mul_assoc, hx, mul_one]
        rw [h1, this]; exact hv
    have hne : V.relIndex (V ⊔ Subgroup.zpowers x) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hxV (h1 (mem_sup_right (Subgroup.mem_zpowers x)))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := Subgroup.relIndex_mul_card V (V ⊔ Subgroup.zpowers x)
  rw [inf_of_le_left le_sup_left, hrel] at this
  omega

variable [Finite G] {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]

theorem three_le_pRank_C (hgen : IVK.IVK_1_2_general) (h12c : IVK.IVK_1_2c) (hx : x * x = 1)
    (hx1 : x ≠ 1) (hm : IsL2Model ↥Kb) : 3 ≤ pRank 2 ↥(Cx x) := by
  obtain ⟨F, _, _, hF, ⟨e0⟩⟩ := hm
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨T, hT, -⟩ := exists_sylow2_ge hbot (bot_le : (⊥ : Subgroup G) ≤ Cx x)
  obtain ⟨e, N, hsit⟩ := sitFacts_of_general x Kb hgen hF e0 hT
  obtain ⟨V, hVP, hV⟩ := ip_P_four hsit h12c
  have hxQ : x ∈ Qg x Kb T := hsit.x_mem_Q hx hx1
  have hxV : x ∉ V := by
    intro hxV
    have hmem : x ∈ Pg x Kb T ⊓ Qg x Kb T := ⟨hVP hxV, hxQ⟩
    rw [Pg_inf_Qg x Kb (IVK.conj_injective_of_L2 e) hsit.sylow, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hVC : V ≤ Cx x := fun g hg => ((mem_Kg x Kb).1 (hVP hg).2).1
  have hcomm : ∀ v ∈ V, v * x = x * v := fun v hv => (mem_Cx x).1 (hVC hv)
  have hxC : x ∈ Cx x := x_mem_Cx x
  have hcommV : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((commute_of_mul_eq (hcomm a ha)).zpow_right k).eq
  have hEC : V ⊔ Subgroup.zpowers x ≤ Cx x := sup_le hVC (Subgroup.zpowers_le.2 hxC)
  have hE : IsElemAb2 (V ⊔ Subgroup.zpowers x) := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcommV).1 hg
    have hbb := zpowers_sq_one hx b hb
    have haa := (hV.1 a ha).1
    have hab := hcommV a ha b hb
    refine ⟨?_, ?_⟩
    · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by simp only [mul_assoc]
        _ = 1 := by rw [haa, hbb, mul_one]
    · intro g' hg'
      obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_comm hcommV).1 hg'
      have h1 : a * a' = a' * a := (hV.1 a ha).2 a' ha'
      have h2 : b * b' = b' * b := zpowers_comm x b hb b' hb'
      have h3 : a * b' = b' * a := hcommV a ha b' hb'
      have h4 : a' * b = b * a' := hcommV a' ha' b hb
      calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
        _ = a * (a' * b) * b' := by rw [h4]
        _ = (a * a') * (b * b') := by simp only [mul_assoc]
        _ = (a' * a) * (b' * b) := by rw [h1, h2]
        _ = a' * (a * b') * b := by simp only [mul_assoc]
        _ = a' * (b' * a) * b := by rw [h3]
        _ = a' * b' * (a * b) := by simp only [mul_assoc]
  have hcard : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 2 ^ 3 := by
    rw [card_sup_zpowers hx hxV hcomm, hV.2]; norm_num
  have hEA : ∀ a ∈ (V ⊔ Subgroup.zpowers x).subgroupOf (Cx x),
      a * a = 1 ∧ ∀ b ∈ (V ⊔ Subgroup.zpowers x).subgroupOf (Cx x), a * b = b * a :=
    fun a ha => ⟨Subtype.ext ((hE _ ha).1), fun b hb => Subtype.ext ((hE _ ha).2 _ hb)⟩
  have hcard' : Nat.card ((V ⊔ Subgroup.zpowers x).subgroupOf (Cx x)) = 2 ^ 3 := by
    rw [card_subgroupOf hEC]; exact hcard
  exact le_pRank_of_card (isElementaryAbelian_of_isEA hEA) hcard'

theorem isEA_of_isElementaryAbelian {X : Type*} [Group X] {A : Subgroup X}
    (hA : IsElementaryAbelian 2 ↥A) : Dihedral.IsEA A := by
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [pow_two] at this
  · have := (IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this

omit [Finite G] in
theorem pRank_Cx_le [Finite G] (x : G) : pRank 2 ↥(Cx x) ≤ pRank 2 G := by
  apply csSup_le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro s ⟨B, -, hB⟩
    calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  · exact ⟨0, ⊥, isElementaryAbelian_of_isEA (fun a ha => by
      have : a = 1 := by simpa using ha
      subst this; simp), by simp⟩
  · rintro r ⟨A, hA, hr⟩
    refine ⟨A.map (Cx x).subtype, isElementaryAbelian_of_isEA ?_, ?_⟩
    · exact isEA_map_hom _ (isEA_of_isElementaryAbelian hA)
    · rw [Subgroup.card_map_of_injective (Cx x).subtype_injective]; exact hr

end CFSG.GH74.GLS.Stage1.Thm6.Glue
