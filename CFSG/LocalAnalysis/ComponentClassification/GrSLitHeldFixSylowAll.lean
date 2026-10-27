module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFour
public import CFSG.Sporadic.SmallOddCore.LocalTransport

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem two_pow_factorization_card_heP : 2 ^ (Nat.card heP).factorization 2 = 1024 := by
  rw [card_heP, show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem two_pow_factorization_card_heAutGroup :
    2 ^ (Nat.card heAutGroup).factorization 2 = 2048 := by
  rw [card_heAutGroup, show (8060774400 : ℕ) = 2 ^ 11 * 3935925 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem exists_conj_hfT {T : Subgroup (Equiv.Perm (Fin 8330))} (hT : T ≤ heP)
    (hcard : Nat.card T = 1024) : ∃ g ∈ heP, T = hfT.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_conj_eq_map_of_card hfT_le_heP hT
    (by rw [card_hfT, two_pow_factorization_card_heP]) (by rw [hcard, card_hfT])

theorem exists_conj_hfT0 {T₀ : Subgroup (Equiv.Perm (Fin 8330))} (hT : T₀ ≤ heAutGroup)
    (hcard : Nat.card T₀ = 2048) :
    ∃ g ∈ heAutGroup, T₀ = hfT0.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_conj_eq_map_of_card hfT0_le_heAutGroup hT
    (by rw [card_hfT0, two_pow_factorization_card_heAutGroup]) (by rw [hcard, card_hfT0])

theorem mem_map_conj_iff {g x : Equiv.Perm (Fin 8330)} {S : Subgroup (Equiv.Perm (Fin 8330))} :
    x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_heP_iff {g x : Equiv.Perm (Fin 8330)} (hg : g ∈ heAutGroup) :
    g * x * g⁻¹ ∈ heP ↔ x ∈ heP := by
  have h := (mem_normalizer_iff.1 (heAutGroup_le_normalizer hg) x)
  exact h.symm

theorem sylow_center_two {T : Subgroup (Equiv.Perm (Fin 8330))} (hT : T ≤ heP)
    (hcard : Nat.card T = 1024) : Nat.card (center T) = 2 := by
  obtain ⟨g, -, rfl⟩ := exists_conj_hfT hT hcard
  let e : hfT ≃* hfT.map (MulAut.conj g).toMonoidHom :=
    hfT.equivMapOfInjective _ (MulAut.conj g).injective
  have h1 : (center hfT).map e.toMonoidHom = center (hfT.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_center_eq e
  have h0 : Nat.card ((center hfT).map e.toMonoidHom) = Nat.card (center hfT) :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) (by exact e.injective)
  rw [← h1, h0, card_center_hfT]

theorem sylow_elementary_sixtyFour {T : Subgroup (Equiv.Perm (Fin 8330))} (hT : T ≤ heP)
    (hcard : Nat.card T = 1024) :
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ T ∧ T ≤ normalizer (E : Set _) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 64 := by
  obtain ⟨g, -, rfl⟩ := exists_conj_hfT hT hcard
  obtain ⟨hle, hnorm, hcomm, hsq, hcardE⟩ := hfEgrp_facts
  set c := (MulAut.conj g).toMonoidHom
  refine ⟨hfEgrp.map c, map_mono hle, ?_, ?_, ?_, ?_⟩
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hnorm
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardE]

theorem sylow_four_group_generation {T : Subgroup (Equiv.Perm (Fin 8330))} (hT : T ≤ heP)
    (hcard : Nat.card T = 1024) :
    (⨆ (B : Subgroup (Equiv.Perm (Fin 8330))) (_ : B ≤ T) (_ : Nat.card B = 4)
      (_ : ∀ x ∈ B, x * x = 1), heP ⊓ normalizer (B : Set _)) = heP := by
  obtain ⟨g, hg, rfl⟩ := exists_conj_hfT hT hcard
  set c := (MulAut.conj g).toMonoidHom
  refine le_antisymm (iSup_le fun B => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    inf_le_left) ?_
  conv_lhs => rw [← CFSG.Sporadic.SmallOddCore.map_conj_self hg, ← hfFour_gen]
  rw [Subgroup.map_iSup]
  refine iSup_le fun B => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hB => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hB4 => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hB2 => ?_
  have hB' : B.map c ≤ hfT.map c := map_mono hB
  have hB4' : Nat.card (B.map c) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB4]
  have hB2' : ∀ x ∈ B.map c, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hB2 x hx, map_one]
  refine le_trans ?_ (le_iSup_of_le (B.map c) (le_iSup_of_le hB' (le_iSup_of_le hB4'
    (le_iSup_of_le hB2' le_rfl))))
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    CFSG.Sporadic.SmallOddCore.map_conj_self hg, map_equiv_normalizer_eq]

theorem sylow_outer_involution_rank {T₀ : Subgroup (Equiv.Perm (Fin 8330))}
    (hT : T₀ ≤ heAutGroup) (hcard : Nat.card T₀ = 2048) {a : Equiv.Perm (Fin 8330)}
    (ha : a ∈ T₀) (haP : a ∉ heP) (ha2 : orderOf a = 2) {a₁ : Equiv.Perm (Fin 8330)}
    (ha₁ : a₁ ∈ T₀ ⊓ heP) (ha₁2 : a₁ * a₁ = 1) (hc : a₁ * a = a * a₁) :
    ∃ F : Subgroup (Equiv.Perm (Fin 8330)),
      F ≤ T₀ ⊓ heP ⊓ centralizer {a} ⊓ centralizer {a₁} ∧
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 := by
  obtain ⟨g, hg, rfl⟩ := exists_conj_hfT0 hT hcard
  set c := (MulAut.conj g).toMonoidHom
  have hga : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  have hga₁ : g * (g⁻¹ * a₁ * g) * g⁻¹ = a₁ := by group
  have ha' : g⁻¹ * a * g ∈ hfT0 := mem_map_conj_iff.1 ha
  have haP' : g⁻¹ * a * g ∉ heP := by
    rw [← conj_mem_heP_iff hg, hga]
    exact haP
  have ha2' : orderOf (g⁻¹ * a * g) = 2 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
    rw [← ha2, ← h]
    simp
  have ha₁' : g⁻¹ * a₁ * g ∈ hfT0 ⊓ heP := by
    refine mem_inf.2 ⟨mem_map_conj_iff.1 (mem_inf.1 ha₁).1, ?_⟩
    rw [← conj_mem_heP_iff hg, hga₁]
    exact (mem_inf.1 ha₁).2
  have ha₁2' : g⁻¹ * a₁ * g * (g⁻¹ * a₁ * g) = 1 := by
    rw [show g⁻¹ * a₁ * g * (g⁻¹ * a₁ * g) = g⁻¹ * (a₁ * a₁) * g by group, ha₁2]
    group
  have hc' : g⁻¹ * a₁ * g * (g⁻¹ * a * g) = g⁻¹ * a * g * (g⁻¹ * a₁ * g) := by
    rw [show g⁻¹ * a₁ * g * (g⁻¹ * a * g) = g⁻¹ * (a₁ * a) * g by group, hc]
    group
  obtain ⟨F, hF, hcomm, hsq, hcardF⟩ := hfOuter_e8 ha' haP' ha2' ha₁' ha₁2' hc'
  refine ⟨F.map c, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨⟨hxT, hxP⟩, hxa⟩, hxa₁⟩ := mem_inf.1 (hF hx) |>.imp_left mem_inf.1 |>.imp_left
      (fun h => h.imp_left mem_inf.1)
    refine mem_inf.2 ⟨mem_inf.2 ⟨mem_inf.2 ⟨⟨x, hxT, rfl⟩, ?_⟩, ?_⟩, ?_⟩
    · show g * x * g⁻¹ ∈ heP
      rw [conj_mem_heP_iff hg]
      exact hxP
    · rw [mem_centralizer_singleton_iff] at hxa ⊢
      show g * x * g⁻¹ * a = a * (g * x * g⁻¹)
      rw [← hga]
      rw [show g * x * g⁻¹ * (g * (g⁻¹ * a * g) * g⁻¹) = g * (x * (g⁻¹ * a * g)) * g⁻¹ by group,
        hxa]
      group
    · rw [mem_centralizer_singleton_iff] at hxa₁ ⊢
      show g * x * g⁻¹ * a₁ = a₁ * (g * x * g⁻¹)
      rw [← hga₁]
      rw [show g * x * g⁻¹ * (g * (g⁻¹ * a₁ * g) * g⁻¹) = g * (x * (g⁻¹ * a₁ * g)) * g⁻¹ by
        group, hxa₁]
      group
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardF]

end CFSG.ComponentClassification.GrSLit.HeldFix
