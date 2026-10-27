module

public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

@[expose] def AutLevelRF (Kb : Type) [Group Kb] : Prop :=
  ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
    ∀ E : Subgroup (MulAut Kb), E ≤ B → IsElementaryAbelian 2 ↥E → 8 ≤ Nat.card ↥E →
      ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
        25 ≤ Nat.card ↥(fixedSubgroup Kb σ') →
        ∀ q ∈ B ⊓ innAut Kb, orderOf q = 2 →
          (¬ ∃ c ∈ oResidual 2 ↥(fixedSubgroup Kb σ'), (MulAut.conj (c : Kb) : MulAut Kb) = q) →
          ∃ g ∈ innAut Kb, g * (σ' * q) * g⁻¹ = σ'

theorem map_oResidual_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (oResidual 2 X).map e.toMonoidHom = oResidual 2 Y := by
  unfold oResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show Nat.Coprime (orderOf (e x)) 2
    rw [MulEquiv.orderOf_eq]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    show Nat.Coprime (orderOf (e.symm y)) 2
    rw [MulEquiv.orderOf_eq]
    exact hy

@[expose] noncomputable def fixedEquivConj {K : Type} [Group K] {y f a : MulAut K}
    (h : a * y * a⁻¹ = f) : ↥(fixedSubgroup K y) ≃* ↥(fixedSubgroup K f) :=
  ((a : K ≃* K).subgroupMap (fixedSubgroup K y)).trans
    (MulEquiv.subgroupCongr (IVK.Proofs2.map_fixedSubgroup_eq h))

theorem fixedEquivConj_apply {K : Type} [Group K] {y f a : MulAut K} (h : a * y * a⁻¹ = f)
    (k : ↥(fixedSubgroup K y)) : ((fixedEquivConj h k : ↥(fixedSubgroup K f)) : K) = a (k : K) :=
  rfl

variable {F : Type} [Field F] [Finite F] {Kb : Type} [Group Kb] [Finite Kb]

theorem autLevelRF_of_L2
    (h2hb : IVK_1_2h_b) (hF : L2Field F) (e : Kb ≃* L2 F) : AutLevelRF Kb := by
  classical
  intro B hB hSyl E hEB hE hE8 σ' hσ'B hσ'2 hσ'inn hσ'c _ q₀ hq₀B hq₀2 hq₀O
  obtain ⟨e', N, σ, y, p, hBN, hPeq, hyE, hpB, hσR, hσ2, hσ, hσinn⟩ :=
    exists_notation_field_inv hF e B hB hSyl E hEB hE hE8
  have hqP : ∀ q ∈ B ⊓ innAut Kb, q ∈ N.P := fun q hq => by rw [hPeq]; exact hq
  have hcent : ∀ q ∈ N.P, σ * q = q * σ := fun q hq => (N.R_cent σ hσR hσ2 q hq).symm
  obtain ⟨n, hn⟩ := ivk_1_2c F hF Kb e' N
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hn.2
  have hcard : Nat.card ↥N.P = 2 ^ n := by
    have h1 : Nat.card ↥N.P = Nat.card (DihedralGroup k) := Nat.card_congr φ.toEquiv
    have hk0 : NeZero k := ⟨by omega⟩
    rw [h1, Nat.card_eq_fintype_card, DihedralGroup.card]
    omega
  have hn3 : 3 ≤ n := three_le_of_involution_mem_R hF N hσR hσ2 n hcard
  obtain ⟨z, hzP, hz1, hzz, hzc⟩ := P_exists_central_involution hF N n hcard hn3
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hzu : ∀ w ∈ N.P, (∀ q ∈ N.P, w * q = q * w) → w = 1 ∨ w = z := by
    intro w hw hwc
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (P_central_unique hF N n hcard hn3 hw hzP hw1 hz1 hwc (fun q hq => hzc q hq))
  have hPinn : N.P ≤ innAut Kb := inf_le_right
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  obtain ⟨-, h2⟩ := h2hb F hF Kb e' N σ hσR hσ2 z hzP hz2 (fun x hx => (hzc x hx).symm)
  have hmain : ∀ q ∈ N.P, orderOf q = 2 →
      (¬ ∃ c ∈ oResidual 2 ↥(fixedSubgroup Kb σ), (MulAut.conj (c : Kb) : MulAut Kb) = q) →
      ∃ g ∈ innAut Kb, g * (σ * q) * g⁻¹ = σ := by
    intro q hq hq2 hqO
    have hqO' : q ∉ ((oResidual 2 ↥(fixedSubgroup Kb σ)).map (fixedSubgroup Kb σ).subtype).map
        (MulAut.conj : Kb →* MulAut Kb) := by
      rintro ⟨a, ⟨c, hc, rfl⟩, hac⟩
      exact hqO ⟨c, hc, hac⟩
    have hqσ : q * σ = σ * q := (hcent q hq).symm
    have hne : q * σ ≠ 1 := by
      intro h
      apply hσinn
      have : σ = q⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (innAut Kb).inv_mem (hPinn hq)
    have hord : orderOf (q * σ) = 2 := orderOf_mul_eq_two_of_commute hq2 hσ2 hqσ hne
    obtain ⟨g, hg, hgq⟩ := h2 q hq hqO' hord
    exact ⟨g, hg, by rw [← hqσ]; exact hgq⟩
  have hcls := (fus_L2 h2hb hF N B hPeq hσR hσ2 hzP hz2 (fun q hq => hzc q hq) hzu).1 σ' hσ'B hσ'2
    hσ'inn hσ'c
  rcases hcls with h | h
  · subst h
    exact hmain q₀ (hqP q₀ hq₀B) hq₀2 hq₀O
  ·
    subst h
    have ht := ivk_1_2i_a F hF Kb e' N σ hσR hσ2 z hzP hz2 (fun x hx => (hzc x hx).symm)
    have hzσ : z * σ = σ * z := hcent z hzP |>.symm
    have htσ : N.t * σ * N.t⁻¹ = σ * z := by
      have h1 : N.t * σ * N.t⁻¹ * σ⁻¹ = z := ht
      calc N.t * σ * N.t⁻¹ = (N.t * σ * N.t⁻¹ * σ⁻¹) * σ := by group
        _ = z * σ := by rw [h1]
        _ = σ * z := hzσ
    have htT : N.t ∈ (N.T : Subgroup (MulAut Kb)) := N.t_mem
    have hq₀P : q₀ ∈ N.P := hqP q₀ hq₀B
    set q' : MulAut Kb := N.t⁻¹ * q₀ * N.t with hq'
    have hq'P : q' ∈ N.P := by
      refine ⟨(N.T : Subgroup (MulAut Kb)).mul_mem
        ((N.T : Subgroup (MulAut Kb)).mul_mem ((N.T : Subgroup (MulAut Kb)).inv_mem htT) hq₀P.1) htT, ?_⟩
      have := (inferInstance : (innAut Kb).Normal).conj_mem _ (hPinn hq₀P) N.t⁻¹
      simpa using this
    have hq'2 : orderOf q' = 2 := by
      rw [hq', ← hq₀2]
      have := (MulAut.conj N.t⁻¹).orderOf_eq q₀
      simpa [MulAut.conj_apply] using this
    have hq'O : ¬ ∃ c ∈ oResidual 2 ↥(fixedSubgroup Kb σ), (MulAut.conj (c : Kb) : MulAut Kb) = q' := by
      rintro ⟨c, hc, hcq⟩
      apply hq₀O
      let ε := fixedEquivConj htσ
      refine ⟨ε c, ?_, ?_⟩
      · have : ε c ∈ (oResidual 2 ↥(fixedSubgroup Kb σ)).map ε.toMonoidHom := ⟨c, hc, rfl⟩
        rwa [map_oResidual_equiv ε] at this
      · have hεc : ((ε c : ↥(fixedSubgroup Kb (σ * z))) : Kb) = N.t (c : Kb) := fixedEquivConj_apply htσ c
        rw [hεc]
        have h1 : N.t * MulAut.conj (c : Kb) * N.t⁻¹ = MulAut.conj (N.t (c : Kb)) := by
          ext w
          simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
        rw [← h1, hcq, hq']
        group
    obtain ⟨g, hg, hgq⟩ := hmain q' hq'P hq'2 hq'O
    refine ⟨N.t * g * N.t⁻¹, ?_, ?_⟩
    · have := (inferInstance : (innAut Kb).Normal).conj_mem _ hg N.t
      simpa [mul_assoc] using this
    · have h1 : (N.t * g * N.t⁻¹) * ((σ * z) * q₀) * (N.t * g * N.t⁻¹)⁻¹ =
          N.t * (g * (σ * q') * g⁻¹) * N.t⁻¹ := by
        rw [← htσ, hq']
        group
      rw [h1, hgq, htσ]

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
