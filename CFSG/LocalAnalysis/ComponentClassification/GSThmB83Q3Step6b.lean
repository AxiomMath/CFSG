module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem eq_Wsub_of_le {P : Subgroup (Equiv.Perm (Fin 6))} (hP : IsPGroup 2 P)
    (hle : S6M.Wsub ≤ P) : P = S6M.Wsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 720 := by
    rw [← hk, ← card_perm_six]
    exact card_subgroup_dvd_card P
  have hk4 : k ≤ 4 := by
    have hle' : 2 ^ k ≤ 720 := Nat.le_of_dvd (by norm_num) hdvd
    have hk9 : k < 10 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    interval_cases k <;> omega
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hk, S6M.card_Wsub]
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    _ = 16 := by norm_num

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem exists_U (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    ∃ (W : Sylow 2 ↥d.NE) (U : Sylow 2 X), d.R.subgroupOf d.NE ≤ W ∧
      (W : Subgroup ↥d.NE).map d.NE.subtype ≤ U ∧
      (U : Subgroup X) ⊓ d.NE = (W : Subgroup ↥d.NE).map d.NE.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hRW⟩ := ((d.isPGroup_R hCF1 hCF2).comap_subtype :
    IsPGroup 2 (d.R.subgroupOf d.NE)).exists_le_sylow
  obtain ⟨U, hWU⟩ := ((W.isPGroup'.map d.NE.subtype) :
    IsPGroup 2 ((W : Subgroup ↥d.NE).map d.NE.subtype)).exists_le_sylow
  refine ⟨W, U, hRW, hWU, ?_⟩
  have hS : ∃ T : Sylow 2 ↥d.NE, (T : Subgroup ↥d.NE) =
      ((W : Subgroup ↥d.NE).map d.NE.subtype).subgroupOf d.NE :=
    ⟨W, (comap_map_eq_self_of_injective d.NE.subtype_injective _).symm⟩
  exact eq_of_sylow_of_le hS (le_inf hWU (map_subtype_le _)) inf_le_right
    (U.isPGroup'.to_le inf_le_left)

theorem exists_good (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ (L : d.LClass) (U : Sylow 2 X), d.R ≤ U ∧
      (∀ n : ↥d.NE, (n : X) ∈ (U : Subgroup X) → L.πN n ∈ Eight.S6M.Wsub) ∧
      ∀ t ∈ Eight.S6M.Wsub, ∃ n : ↥d.NE, (n : X) ∈ (U : Subgroup X) ∧ L.πN n = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  obtain ⟨L₀⟩ := d.nonempty_LClass hq hF
  obtain ⟨W, U, hRW, hWU, hUN⟩ := d.exists_U hCF1 hCF2
  have hsurj := L₀.πN_surjective hq hF
  set P : Sylow 2 (Equiv.Perm (Fin 6)) := W.mapSurjective hsurj with hP
  have hWp : IsPGroup 2 Eight.S6M.Wsub :=
    IsPGroup.of_card (n := 4) (by rw [Eight.S6M.card_Wsub]; norm_num)
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  have hQ : (Q : Subgroup (Equiv.Perm (Fin 6))) = Eight.S6M.Wsub :=
    Eight.eq_Wsub_of_le Q.isPGroup' hWQ
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) P Q
  have hmem : ∀ t, t ∈ Eight.S6M.Wsub ↔ τ⁻¹ * t * τ ∈ (W : Subgroup ↥d.NE).map L₀.πN := by
    intro t
    rw [← hQ, ← hτ, Sylow.coe_subgroup_smul, hP, Sylow.coe_mapSurjective,
      Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [MulAut.smul_def, MulAut.conj_apply,
        show τ⁻¹ * (τ * s * τ⁻¹) * τ = s by group]
      exact hs
    · intro hs
      exact ⟨τ⁻¹ * t * τ, hs, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩
  have hR : d.R ≤ U := fun x hx => hWU ⟨⟨x, d.R_le_normalizer_E hx⟩,
    hRW (show (⟨x, d.R_le_normalizer_E hx⟩ : ↥d.NE) ∈ d.R.subgroupOf d.NE from hx), rfl⟩
  refine ⟨L₀.relabel τ⁻¹, U, hR, ?_, ?_⟩
  · intro n hn
    rw [L₀.relabel_πN, inv_inv, hmem, show τ⁻¹ * (τ * L₀.πN n * τ⁻¹) * τ = L₀.πN n by group]
    have hnW : (n : X) ∈ (W : Subgroup ↥d.NE).map d.NE.subtype := by
      rw [← hUN]
      exact Subgroup.mem_inf.mpr ⟨hn, n.2⟩
    obtain ⟨m, hm, hmn⟩ := mem_map.mp hnW
    have : m = n := Subtype.ext hmn
    rw [← this]
    exact mem_map_of_mem _ hm
  · intro t ht
    obtain ⟨m, hm, hmt⟩ := mem_map.mp ((hmem t).mp ht)
    refine ⟨m, hWU (mem_map_of_mem _ hm), ?_⟩
    rw [L₀.relabel_πN, inv_inv, hmt]
    group

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
