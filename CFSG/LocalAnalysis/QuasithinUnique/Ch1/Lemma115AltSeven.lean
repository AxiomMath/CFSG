module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate4032

public section

namespace CFSG.QuasithinUnique.Ch1

open Equiv Equiv.Perm CFSG.Open CFSG.QuasithinUnique

namespace AltSeven

@[expose] def cent (σ : Perm (Fin 7)) : Subgroup (Perm (Fin 7)) where
  carrier := {g | Perm.sign g = 1 ∧ σ * g = g * σ}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, one_mul], by
    rw [← mul_assoc, ha.2, mul_assoc, hb.2, mul_assoc]⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1, inv_one], (Commute.inv_right ha.2 :)⟩

theorem mem_cent {σ g : Perm (Fin 7)} : g ∈ cent σ ↔ Perm.sign g = 1 ∧ σ * g = g * σ := Iff.rfl

theorem fix_invol : ∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 →
    fixCount σ = 1 ∨ fixCount σ = 3 ∨ fixCount σ = 5 :=
  Certificates.certificate4032.1

theorem type22 :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = 3 → P22 σ :=
  Certificates.certificate4032.2.1

theorem type2 :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = 5 → Q2 σ :=
  Certificates.certificate4032.2.2.1

theorem nontriv2 : ∀ σ : Perm (Fin 7), σ * σ = 1 → fixCount σ = 5 →
    ∃ c : Perm (Fin 7), Perm.sign c = 1 ∧ c ≠ 1 ∧ σ * c = c * σ :=
  Certificates.certificate4032.2.2.2.1

theorem central7 :
    ∀ τ : Perm (Fin 7), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
    τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ →
    τ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * τ →
    τ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * τ →
    τ * (swap 4 5 * swap 5 6) = (swap 4 5 * swap 5 6) * τ → τ = 1 :=
  Certificates.certificate4032.2.2.2.2

theorem cycleType_of_fix_one {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hf : fixCount σ = 1) : σ.cycleType = {2, 2, 2} := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_two : (orderOf σ).Prime)
  rw [hord] at hn
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsupp : σ.support.card = 6 := by
    have : σ.support = Finset.univ.filter (fun i : Fin 7 => ¬ σ i = i) := by
      ext i; simp [Equiv.Perm.mem_support]
    rw [this]
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun i : Fin 7 => σ i = i)
    simp only [fixCount] at hf
    simp at h3
    omega
  have : n = 2 := by omega
  rw [hn, this]
  rfl

theorem not_charTwo_cent_of_fix_three {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (hf : fixCount σ = 3) :
    ¬ CharTwo (cent σ) := by
  obtain ⟨c, hs, hc3, hc1, hcσ, hnorm⟩ := type22 σ h2 hf
  have hcC : c ∈ cent σ := ⟨hs, hcσ⟩
  have hNC : Subgroup.zpowers c ≤ cent σ := Subgroup.zpowers_le.mpr hcC
  have hord : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by simpa [pow_succ, mul_assoc] using hc3) hc1
  refine not_charTwo_of_normal_odd hNC ?_ ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNC, Subgroup.le_normalizer_iff]
    intro g hg n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    rcases hnorm g hg.1 hg.2 with h | h
    · rw [h]; exact Subgroup.zpow_mem_zpowers c k
    · rw [h]
      exact ⟨-k, by simp [zpow_neg]⟩
  · rw [Nat.card_zpowers, hord]
    exact ⟨1, rfl⟩
  · intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    exact hc1 hbot

theorem not_charTwo_cent_of_fix_five {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (hf : fixCount σ = 5) :
    ¬ CharTwo (cent σ) := by
  obtain ⟨c, hs, hc1, hcσ⟩ := nontriv2 σ h2 hf
  have hQ := type2 σ h2 hf
  refine not_charTwo_of_pCoreOf_eq_bot ?_ ?_
  · intro hbot
    have : c ∈ cent σ := ⟨hs, hcσ⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hc1 this
  · apply pCoreOf_eq_bot_of_involution_products
    intro x hx hx2 hx1
    obtain ⟨g, hgs, hgσ, hy3, hy1⟩ := hQ x hx.1 hx.2 hx2 hx1
    exact ⟨g, ⟨hgs, hgσ⟩, hy3, hy1⟩

theorem invCaseD_of_altSeven {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) {β : K ≃* K} (h : InvDatum K β)
    (hz : Subgroup.center K = ⊥) : InvCaseD K β := by
  let β' : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := (e.symm.trans β).trans e
  obtain ⟨σ₀, hσ₀⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr le_rfl : (7 : ℕ) = 5 ∨ 7 ≤ 7) β'
  have hβx : ∀ x : K, ((e (β x) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ₀ * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ₀⁻¹ := fun x => by
    have := hσ₀ (e x)
    simpa [β'] using this
  have hsq : σ₀ * σ₀ = 1 := by
    have hcomm : ∀ g : Perm (Fin 7), Perm.sign g = 1 → σ₀ * σ₀ * g = g * (σ₀ * σ₀) := by
      intro g hg
      let a : alternatingGroup (Fin 7) := ⟨g, by simpa [Perm.mem_alternatingGroup] using hg⟩
      let x : K := e.symm a
      have hex : ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = g := by simp [x, a]
      have h1 : ((e (β (β x)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = g := by
        rw [h.involutory x, hex]
      rw [hβx (β x), hβx x, hex] at h1
      calc σ₀ * σ₀ * g = (σ₀ * (σ₀ * g * σ₀⁻¹) * σ₀⁻¹) * (σ₀ * σ₀) := by group
        _ = g * (σ₀ * σ₀) := by rw [h1]
    exact central7 _ (hcomm _ (by simp)) (hcomm _ (by simp)) (hcomm _ (by simp))
      (hcomm _ (by simp)) (hcomm _ (by simp))
  have hne : σ₀ ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := h.nontrivial
    apply hx
    have hbx : β x = x := by
      apply e.injective
      apply Subtype.ext
      rw [hβx x]
      simp
    rw [hbx, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hcharCent : CharTwo (cent σ₀) := by
    have h1 : CharTwo ((fixedSubgroup β).map e.toMonoidHom) := charTwo_map_mulEquiv e h.charTwo
    have h2 : CharTwo (((fixedSubgroup β).map e.toMonoidHom).map
        (alternatingGroup (Fin 7)).subtype) := charTwo_map_subtype (charTwo_iff_internal.mp h1)
    have h3 : ((fixedSubgroup β).map e.toMonoidHom).map (alternatingGroup (Fin 7)).subtype =
        cent σ₀ := by
      ext g
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have hx' : β x = x := hx
        refine ⟨?_, ?_⟩
        · exact (Perm.mem_alternatingGroup.mp (e x).2)
        · have := hβx x
          rw [hx'] at this
          calc σ₀ * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7))
              = (σ₀ * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ₀⁻¹) * σ₀ := by group
            _ = ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ₀ := by rw [← this]
      · rintro ⟨hs, hc⟩
        let a : alternatingGroup (Fin 7) := ⟨g, Perm.mem_alternatingGroup.mpr hs⟩
        refine ⟨a, ⟨e.symm a, ?_, by simp⟩, rfl⟩
        show β (e.symm a) = e.symm a
        apply e.injective
        apply Subtype.ext
        rw [hβx]
        simp only [MulEquiv.apply_symm_apply, a]
        rw [hc]
        group
    rwa [h3] at h2
  have hfix : fixCount σ₀ = 1 ∨ fixCount σ₀ = 3 ∨ fixCount σ₀ = 5 := fix_invol σ₀ hsq hne
  have hf1 : fixCount σ₀ = 1 := by
    rcases hfix with hf | hf | hf
    · exact hf
    · exact absurd hcharCent (not_charTwo_cent_of_fix_three hsq hf)
    · exact absurd hcharCent (not_charTwo_cent_of_fix_five hsq hf)
  have hcyc : σ₀.cycleType = {2, 2, 2} := cycleType_of_fix_one hsq hne hf1
  let ψ : K ≃* K ⧸ Subgroup.center K := mulEquivQuotientOfCenterEqBot hz
  refine ⟨ψ.symm.trans e, σ₀⁻¹, Or.inl (by rw [hz]; exact Subgroup.card_bot),
    by rw [Equiv.Perm.cycleType_inv]; exact hcyc, fun x => ?_⟩
  have hψ : ∀ y : K, ψ.symm (QuotientGroup.mk y) = y := fun y => ψ.symm_apply_apply y
  show (((ψ.symm.trans e) (QuotientGroup.mk (β x)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
    σ₀⁻¹⁻¹ * ((((ψ.symm.trans e) (QuotientGroup.mk x)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
      σ₀⁻¹
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ, hψ, hβx x, inv_inv]

end AltSeven

theorem simpleInspection_altSeven :
    SimpleInspection (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) := by
  intro K _ _ β h hz ⟨e⟩
  exact Or.inr (Or.inr (Or.inr (Or.inl (AltSeven.invCaseD_of_altSeven e h hz))))

end CFSG.QuasithinUnique.Ch1
