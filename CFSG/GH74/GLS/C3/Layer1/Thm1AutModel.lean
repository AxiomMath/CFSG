module

public import CFSG.GH74.GLS.C3.Layer1.P34Stmt
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutGood

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

@[expose] def AutLevelF (Kb : Type) [Group Kb] : Prop :=
  ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
    ∀ E : Subgroup (MulAut Kb), E ≤ B → IsElementaryAbelian 2 ↥E → 8 ≤ Nat.card ↥E →
      ∃ σ y p z : MulAut Kb, y ∈ E ∧ p ∈ B ⊓ innAut Kb ∧ σ = p⁻¹ * y ∧ σ ∈ B ∧ orderOf σ = 2 ∧
        (∀ q ∈ B ⊓ innAut Kb, σ * q = q * σ) ∧ P34.IsFAutL2A7 Kb σ ∧ σ ∉ innAut Kb ∧
        (∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(B ⊓ innAut Kb) n) ∧
        z ∈ B ⊓ innAut Kb ∧ orderOf z = 2 ∧ (∀ q ∈ B ⊓ innAut Kb, z * q = q * z) ∧
        (∀ w ∈ B ⊓ innAut Kb, (∀ q ∈ B ⊓ innAut Kb, w * q = q * w) → w = 1 ∨ w = z) ∧
        (∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
          ∀ u ∈ (B ⊓ innAut Kb) ⊔ zpowers σ', orderOf u = 2 →
            ∃ g ∈ innAut Kb, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = σ' ∨ g * u * g⁻¹ = σ' * z) ∧
        (∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
          P34.IsFAutL2A7 Kb σ') ∧
        (∀ k₀ : Kb, (MulAut.conj k₀ : MulAut Kb) = z →
          Group.IsSolvable ↥(centralizer ({k₀} : Set Kb))) ∧
        ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
          GoodC Kb σ' ∨ (Nonempty (Kb ≃* alternatingGroup (Fin 7)) ∧ GoodC Kb (σ' * z))

theorem exists_l2_model_of_hasL2Model {H : Type} [Group H] (h : HasL2Model H Odd) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (H ≃* L2 F) := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨F, hF, hFin, ⟨?_, ?_⟩, ⟨e⟩⟩
    · rw [hcard]; exact hP
    · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
      have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
      have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
      have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hP
      rw [hcard]
      omega
  all_goals exact absurd h0 (by norm_num)

theorem hasL2Model_nine {H : Type} [Group H] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9) (e : H ≃* L2 F) : HasL2Model H (fun q => q = 9) := by
  refine ⟨3, 2, Nat.prime_three, by norm_num, by norm_num, ?_⟩
  refine Or.inl ⟨by simp [Blueprint.classicalTags], ?_, F, inferInstance, inferInstance,
    by rw [hF]; norm_num, ⟨e⟩⟩
  exact ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩

theorem autLevelF_of_L2
    {Kb : Type} [Group Kb] [Finite Kb] (h2hb : IVK_1_2h_b)
    (h9 : ¬ HasL2Model Kb (fun q => q = 9)) (h : HasL2Model Kb Odd) : AutLevelF Kb := by
  obtain ⟨F, hFf, hFin, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
  have hF9 : Nat.card F ≠ 9 := fun h' => h9 (hasL2Model_nine h' e)
  intro B hB hSyl E hEB hE hE8
  obtain ⟨e', N, σ, y, p, hBN, hPeq, hyE, hpB, hσR, hσ2, hσ, hσinn⟩ :=
    exists_notation_field_inv hF e B hB hSyl E hEB hE hE8
  have hqP : ∀ q ∈ B ⊓ innAut Kb, q ∈ N.P := fun q hq => by rw [hPeq]; exact hq
  have hcent : ∀ q ∈ B ⊓ innAut Kb, σ * q = q * σ := fun q hq =>
    (N.R_cent σ hσR hσ2 q (hqP q hq)).symm
  have hσB : σ ∈ B := by
    rw [hσ]
    exact B.mul_mem (B.inv_mem hpB.1) (hEB hyE)
  have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσ2; omega
  obtain ⟨n, hn⟩ := ivk_1_2c F hF Kb e' N
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hn.2
  have hcard : Nat.card ↥N.P = 2 ^ n := by
    have h1 : Nat.card ↥N.P = Nat.card (DihedralGroup k) := Nat.card_congr φ.toEquiv
    have hk0 : NeZero k := ⟨by omega⟩
    rw [h1, Nat.card_eq_fintype_card, DihedralGroup.card]
    omega
  have hn3 : 3 ≤ n := three_le_of_involution_mem_R hF N hσR hσ2 n hcard
  obtain ⟨z, hzP, hz1, hzz, hzc⟩ := P_exists_central_involution hF N n hcard hn3
  have hzB : z ∈ B ⊓ innAut Kb := by rw [← hPeq]; exact hzP
  have hzu : ∀ w ∈ N.P, (∀ q ∈ N.P, w * q = q * w) → w = 1 ∨ w = z := by
    intro w hw hwc
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (P_central_unique hF N n hcard hn3 hw hzP hw1 hz1 hwc (fun q hq => hzc q hq))
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  refine ⟨σ, y, p, z, hyE, hpB, hσ, hσB, hσ2, hcent,
    ⟨hσ1, Or.inl ⟨F, hFf, hFin, e', hF.1, hσR.2⟩⟩, hσinn, ⟨n, hn3, ?_⟩, hzB, hz2,
    fun q hq => hzc q (hqP q hq),
    fun w hw hwc => hzu w (hqP w hw) (fun q hq => hwc q (by rw [← hPeq]; exact hq)),
    (fus_L2 h2hb hF N B hPeq hσR hσ2 hzP hz2 (fun q hq => hzc q hq) hzu).2, ?_, ?_, ?_⟩
  · rw [← hPeq]
    exact hn
  · intro σ' hσ'B hσ'2 hσ'inn hσ'c
    have hσ'1 : σ' ≠ 1 := fun h => by
      rw [h, orderOf_one] at hσ'2
      omega
    obtain ⟨e'', he''⟩ := fa_L2 hF N B hPeq hσR hσ2 hzP
      (fus_L2 h2hb hF N B hPeq hσR hσ2 hzP hz2 (fun q hq => hzc q hq) hzu).1 σ' hσ'B hσ'2 hσ'inn
      hσ'c
    exact ⟨hσ'1, Or.inl ⟨F, hFf, hFin, e'', hF.1, he''⟩⟩
  · intro k₀ hk₀
    have hkk : k₀ * k₀ = 1 := by
      apply IVK.conj_injective_of_L2 e
      rw [map_mul, hk₀, map_one]
      have := pow_orderOf_eq_one z
      rwa [hz2, sq] at this
    have hk1 : k₀ ≠ 1 := fun h => by
      rw [h, map_one] at hk₀
      rw [← hk₀, orderOf_one] at hz2
      omega
    exact solv_L2 hF e k₀ (orderOf_eq_prime (by rw [sq]; exact hkk) hk1)
  · intro σ' hσ'B hσ'2 hσ'inn hσ'c
    obtain ⟨e'', he''⟩ := fa_L2 hF N B hPeq hσR hσ2 hzP
      (fus_L2 h2hb hF N B hPeq hσR hσ2 hzP hz2 (fun q hq => hzc q hq) hzu).1 σ' hσ'B hσ'2 hσ'inn
      hσ'c
    exact Or.inl (goodC_of_fieldAut hF hF9 e'' he'' hσ'2)

theorem not_mem_innAut_of_isFAutL2A7 {Kb : Type} [Group Kb] [Finite Kb] {α : MulAut Kb}
    (h : P34.IsFAutL2A7 Kb α) : α ∉ innAut Kb := by
  obtain ⟨hne, ⟨F, _, _, e, -, hα⟩ | ⟨-, hα⟩⟩ := h
  · intro hinn
    exact hne (eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e hα (innAut_le_innDiagSub e hinn))
  · exact hα

end CFSG.GH74.GLS.C3.Layer1.Thm1
