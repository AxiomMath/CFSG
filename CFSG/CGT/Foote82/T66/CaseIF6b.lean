module

public import CFSG.CGT.Foote82.T66.CaseIF6
public import CFSG.CGT.Foote82.T66.CaseIHeartH
public import CFSG.CGT.Foote82.T66.CaseIF8

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIClimbAux
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.false_of_le7 (h : Hyp G L z v H₁ m ψ) (hm : m ≤ 1)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) (h511 : CaseILemma511) : False := by
  have hext := h.std.extremal
  obtain ⟨J, hJ, hEJ⟩ := h.exists_component_eq hK2 h25
  have hqE : Open.IsQuasisimple ↥(layerIn G) := by rw [hEJ]; exact hJ.2.2
  obtain ⟨T₀, hzT, hyT⟩ := exists_sylow_T₀ (m := m)
  have hEG : layerIn G ≤ G := layerIn_le G
  have hEn : ((layerIn G).subgroupOf G).Normal := by
    rw [layerIn_subgroupOf]
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hirr : IsIrr (layerIn G) ⊤ := hext.setup.isIrr_of_layerIn_le le_rfl
  have hLcomp : IsComponentOf L (G ⊓ Subgroup.centralizer {z}) := by
    have := h.setup6.component
    rwa [centralizer_zpowers_eq] at this
  have hPE : PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ≤ layerIn G :=
    (h.PP_le_H _).trans h.H_le_layerIn
  have hsyl : ∃ (m' : ℕ) (P : Subgroup ↥(layerIn G)) (Q : Subgroup (alternatingGroup (Fin m'))),
      (m' = 8 ∨ m' = 9) ∧ IsPGroup 2 P ∧ ¬ 2 ∣ P.index ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index ∧
        Nonempty (↥P ≃* ↥Q) := by
    refine ⟨m + 6 + 2, (PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2))))).subgroupOf (layerIn G),
      ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ⊓ alternatingGroup (Fin (m + 6 + 2))).subgroupOf
        (alternatingGroup (Fin (m + 6 + 2))), by omega,
      ((T₀.isPGroup'.to_inf_left).map _).comap_subtype, h.P_not_dvd hK2 h25 T₀ hzT hyT,
      T₀.isPGroup'.to_inf_left.comap_subtype, ?_, ?_⟩
    · show ¬ 2 ∣ ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ⊓
        alternatingGroup (Fin (m + 6 + 2))).relIndex (alternatingGroup (Fin (m + 6 + 2)))
      rw [relIndex_inf_alt_eq _ hzT]
      exact T₀.not_dvd_index
    · exact ⟨((Subgroup.subgroupOfEquivOfLe hPE).trans
        (((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ⊓ alternatingGroup (Fin (m + 6 + 2))).equivMapOfInjective
          (pe ψ) pe_injective).symm).trans (Subgroup.subgroupOfEquivOfLe inf_le_right).symm⟩
  have hk : m + 6 = 6 ∨ m + 6 = 7 := by omega
  obtain ⟨-, hb⟩ := h511 V (layerIn G) G L z (m + 6) (eL h) hEG hEn
    (h.relIndex_layerIn hK2 h25).le (isQuasisimple_native' hqE) h.odd_card_center_layerIn
    (h.centralizer_layerIn_le hK2 h25) hirr h.z_mem_G h.std.orderOf_s hLcomp hk
    h.isAltNaturalModule_L (fun c hc => h.finrank_eq_two c hc)
  have hcardH : Nat.card (HH G L v) = (m + 6 + 2).factorial / 2 := by
    rw [h.H_eq, Subgroup.card_map_of_injective pe_injective, card_altGroup (by omega)]
  have hHE : HH G L v ≤ layerIn G := h.H_le_layerIn
  have hdvd : Nat.card (HH G L v) ∣ Nat.card (layerIn G) := Subgroup.card_dvd_of_le hHE
  have hfin : layerIn G = HH G L v → False := by
    intro hEH
    apply hext.not_concl
    obtain ⟨eL'⟩ := h.L_equiv
    refine Or.inr (Or.inl ⟨m + 6, 1, by omega, le_rfl, ⟨eL'⟩, ?_⟩)
    rw [show m + 6 + 2 * 1 = m + 6 + 2 by ring, hEH]
    rw [hEH] at hirr
    exact h.isAltHeartFor_H hirr
  have h8 : (8 : ℕ).factorial / 2 = 20160 := by decide
  have h9 : (9 : ℕ).factorial / 2 = 181440 := by decide
  rcases hb hsyl with he8 | he9 | h259
  · obtain ⟨e8⟩ := he8
    have hcardE : Nat.card (layerIn G) = 20160 :=
      (Nat.card_congr e8.toEquiv).trans ((card_altGroup (by norm_num)).trans h8)
    interval_cases m
    · exact hfin (Subgroup.eq_of_le_of_card_ge hHE (by rw [hcardE, hcardH, h8])).symm
    · rw [hcardE, hcardH, h9] at hdvd
      exact absurd hdvd (by decide)
  · obtain ⟨e9⟩ := he9
    have hcardE : Nat.card (layerIn G) = 181440 :=
      (Nat.card_congr e9.toEquiv).trans ((card_altGroup (by norm_num)).trans h9)
    interval_cases m
    ·
      have hnorm : G ≤ Subgroup.normalizer (layerIn G : Set (GLV V)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hEG).1 hEn
      obtain ⟨τ, hττ, h5, hτL⟩ := exists_altOn_fix (by norm_num) e9 hEG hnorm h.zz h.z_mem_G
        h.setup6.component hext.setup.toSetup6.le_layerIn
      have hcardL : Nat.card ↥L = 360 := by
        obtain ⟨eL'⟩ := h.L_equiv
        exact (Nat.card_congr eL'.toEquiv).trans ((card_altGroup (by norm_num)).trans (by decide))
      have hcardA : Nat.card ↥(altOn ({i | τ i = i} : Set (Fin 9))) = 360 := by
        rw [← hτL, Subgroup.card_map_of_injective (Subtype.val_injective.comp e9.injective),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hext.setup.toSetup6.le_layerIn).toEquiv,
          hcardL]
      have h2 := two_mul_card_altOn ({i | τ i = i} : Set (Fin 9)) (by omega)
      rw [hcardA] at h2
      have h6 : Nat.card ↥({i | τ i = i} : Set (Fin 9)) = 6 := by
        have h720 : (Nat.card ↥({i | τ i = i} : Set (Fin 9))).factorial = (6 : ℕ).factorial := by
          rw [← h2]; decide
        exact (Nat.factorial_inj (by omega)).1 h720
      have hsum := Set.ncard_add_ncard_compl ({i | τ i = i} : Set (Fin 9))
      rw [← Nat.card_coe_set_eq, h6, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
      have hsupp : ({i | τ i = i} : Set (Fin 9))ᶜ = (τ.support : Set (Fin 9)) := by
        ext i
        simp [Equiv.Perm.mem_support]
      rw [hsupp, Set.ncard_coe_finset] at hsum
      obtain ⟨hs, -⟩ := card_support_of_mul_self hττ
      omega
    · exact hfin (Subgroup.eq_of_le_of_card_ge hHE (by rw [hcardE, hcardH, h9])).symm
  · rw [h259, hcardH] at hdvd
    interval_cases m
    · rw [h8] at hdvd; exact absurd hdvd (by decide)
    · rw [h9] at hdvd; exact absurd hdvd (by decide)

end CaseIAux

end CFSG.CGT.Foote82
