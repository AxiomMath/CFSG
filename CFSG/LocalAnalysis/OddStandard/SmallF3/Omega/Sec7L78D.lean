module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l78_E16_data [Finite G] (hP : Asc82Tab6P) {L N D : Subgroup G} (hL : IsOm6P L)
    (hD : IsElemAb2 D 4) (hDN : D ≤ N) (hNL : N ≤ L) (hDnorm : (D.subgroupOf N).Normal)
    (hcard : Nat.card N = 1920) :
    ∃ P : Subgroup G, IsSylow2Of P L ∧ IsNormalE16In P D ∧
      N = L ⊓ normalizer (D : Set G) := by
  classical
  obtain ⟨P₁syl⟩ := Sylow.nonempty (p := 2) (G := ↥L)
  let P₁ : Subgroup G := (P₁syl : Subgroup ↥L).map L.subtype
  have hP₁ : IsSylow2Of P₁ L := isSylow2Of_map_sylow P₁syl
  obtain ⟨B₁, B₂, _, hB₁, _, _⟩ := hP.sylow_E16 G L hL P₁ hP₁
  obtain ⟨φ, hAct⟩ := sec7l78_act_of_aut_B hP hL hP₁ hB₁
  have hP₁le : P₁ ≤ L ⊓ normalizer (B₁ : Set G) :=
    le_inf hP₁.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hB₁.1).mp hB₁.2.2)
  have hP₁N₁ : IsSylow2Of P₁ (L ⊓ normalizer (B₁ : Set G)) := by
    refine ⟨hP₁le, hP₁.2.1, ?_⟩
    intro h2
    have h := Subgroup.relIndex_mul_relIndex P₁ (L ⊓ normalizer (B₁ : Set G)) L hP₁le inf_le_left
    exact hP₁.2.2 (h ▸ dvd_mul_of_dvd_left h2 _)
  have hP₁card : Nat.card P₁ = 2 ^ 7 := hAct.card_sylow hP₁N₁
  have hmulL : P₁.relIndex L * 2 ^ 7 = Nat.card L := by
    have h := Subgroup.relIndex_mul_card (H := P₁) (K := L)
    rwa [inf_eq_left.mpr hP₁.1, hP₁card] at h
  obtain ⟨PNsyl⟩ := Sylow.nonempty (p := 2) (G := ↥N)
  let P : Subgroup G := (PNsyl : Subgroup ↥N).map N.subtype
  have hPN : IsSylow2Of P N := isSylow2Of_map_sylow PNsyl
  have hNrel : ¬ 2 ∣ N.relIndex L := by
    have hmulN : N.relIndex L * 1920 = Nat.card L := by
      have h := Subgroup.relIndex_mul_card (H := N) (K := L)
      rwa [inf_eq_left.mpr hNL, hcard] at h
    have hEq : N.relIndex L * 15 = P₁.relIndex L := by
      have h : N.relIndex L * 1920 = P₁.relIndex L * 2 ^ 7 := hmulN.trans hmulL.symm
      have h' : (N.relIndex L * 15) * 2 ^ 7 = P₁.relIndex L * 2 ^ 7 := by
        rw [mul_assoc, show 15 * 2 ^ 7 = 1920 by norm_num]
        exact h
      exact mul_right_cancel₀ (by norm_num : (2 : ℕ) ^ 7 ≠ 0) h'
    exact fun h2 => hP₁.2.2 (hEq ▸ dvd_mul_of_dvd_left h2 15)
  have hPL : IsSylow2Of P L := by
    refine ⟨hPN.1.trans hNL, hPN.2.1, ?_⟩
    intro h2
    rw [← Subgroup.relIndex_mul_relIndex P N L hPN.1 hNL] at h2
    rcases Nat.prime_two.dvd_mul.mp h2 with h | h
    · exact hPN.2.2 h
    · exact hNrel h
  have hNnorm : N ≤ normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDN).mp hDnorm
  have hDsub : IsPGroup 2 (D.subgroupOf N) :=
    IsPGroup.of_card (n := 4) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv, hD.2])
  haveI : (D.subgroupOf N).Normal := hDnorm
  have hDlePsub : D.subgroupOf N ≤ (PNsyl : Subgroup ↥N) :=
    IsPGroup.le_sylow_of_normal hDsub PNsyl
  have hDleP : D ≤ P := by
    intro d hd
    exact Subgroup.mem_map.mpr ⟨⟨d, hDN hd⟩, hDlePsub (Subgroup.mem_comap.mpr hd), rfl⟩
  have hDnormP : IsNormalE16In P D :=
    ⟨hDleP, hD, (Subgroup.normal_subgroupOf_iff_le_normalizer hDleP).mpr (hPN.1.trans hNnorm)⟩
  obtain ⟨φD, hActD⟩ := sec7l78_act_of_aut_B hP hL hPL hDnormP
  have hNDcard : Nat.card (L ⊓ normalizer (D : Set G) : Subgroup G) = 1920 := hActD.card_N
  exact ⟨P, hPL, hDnormP,
    Subgroup.eq_of_le_of_card_ge (le_inf hNL hNnorm) (by rw [hcard]; exact le_of_eq hNDcard)⟩

theorem sec7l78_sideL' [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72)
    (h76 : Asc82Lemma76) (hP : Asc82Tab6P) (h77a : Asc82Lemma77a) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∃ P : Subgroup G, Sec7L78Side (CFSG.conjugate L g) P (ASub S B ⊓ CFSG.conjugate L g)
        (ASub S B) (g⁻¹ * t * g) ∧
      CFSG.conjugate L g ⊓ MSub S B =
        CFSG.conjugate L g ⊓ normalizer ((ASub S B ⊓ CFSG.conjugate L g : Subgroup G) : Set G) := by
  classical
  have hctx' : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hc.ctx.conjugate g
  have hL' : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hc.ctx.isOm6P g
  have hD : IsElemAb2 (ASub S B ⊓ CFSG.conjugate L g) 4 := (h77a G t L S z g B hc).1
  obtain ⟨ρ, hρs, hρk⟩ := (h77a G t L S z g B hc).2
  have hcomm := sec7l78_A_comm_sq h36 h76 hP hc
  have hsA : g⁻¹ * t * g ∈ ASub S B := sec7l78_s_mem_A hP h36 hc
  have hA_le_cent : ASub S B ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hcomm.1 a ha (g⁻¹ * t * g) hsA).symm
  have hA_N : ASub S B ≤ normalizer (CFSG.conjugate L g : Set G) :=
    fun a ha => hctx'.cent_le_normalizer h36 a (hA_le_cent ha)
  have hcyc : ∀ P : Subgroup G,
      IsSylow2Of P (centralizer (CFSG.conjugate L g : Set G)) → IsCyclic P :=
    h72 G (g⁻¹ * t * g) (CFSG.conjugate L g) hctx'.toSec3SettingLB hctx'.omega6
  have hA_cent : ∀ a ∈ ASub S B,
      a ∈ centralizer (CFSG.conjugate L g : Set G) → a = 1 ∨ a = g⁻¹ * t * g := by
    intro a ha haC
    exact eq_one_or_eq_of_commute hcyc haC hctx'.t_mem_centralizer (hcomm.2 a ha) hctx'.involution
      (hcomm.1 a ha (g⁻¹ * t * g) hsA)
  have hcardN₂ : Nat.card (CFSG.conjugate L g ⊓ MSub S B : Subgroup G) = 1920 := by
    have h1 : Nat.card (CFSG.conjugate L g ⊓ MSub S B : Subgroup G) =
        Nat.card ((CFSG.conjugate L g ⊓ MSub S B : Subgroup G) ⧸ ρ.ker) * Nat.card ρ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card ((CFSG.conjugate L g ⊓ MSub S B : Subgroup G) ⧸ ρ.ker) =
        Nat.card (Equiv.Perm (Fin 5)) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv
    have hle : CFSG.conjugate L g ⊓ ASub S B ≤ CFSG.conjugate L g ⊓ MSub S B :=
      le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
    have h3 : Nat.card ρ.ker = 16 := by
      rw [hρk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        inf_comm (CFSG.conjugate L g) (ASub S B), hD.2]
      norm_num
    have h4 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [h1, h2, h3, h4]
  have hDN : ASub S B ⊓ CFSG.conjugate L g ≤ CFSG.conjugate L g ⊓ MSub S B :=
    le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hNL : CFSG.conjugate L g ⊓ MSub S B ≤ CFSG.conjugate L g := inf_le_left
  have hDnorm : ((ASub S B ⊓ CFSG.conjugate L g).subgroupOf
      (CFSG.conjugate L g ⊓ MSub S B)).Normal := by
    rw [inf_comm (ASub S B) (CFSG.conjugate L g), ← hρk]
    exact MonoidHom.normal_ker ρ
  obtain ⟨P, hPsyl, hPnorm, hNeq⟩ :=
    sec7l78_E16_data hP hL' hD hDN hNL hDnorm hcardN₂
  exact ⟨P, ⟨hL', hPsyl, hPnorm, hA_N, rfl, hsA, hctx'.t_mem_centralizer, hctx'.involution,
    hA_cent, hcomm.1, hcomm.2⟩, hNeq⟩

end CFSG.OddStandard.SmallF3.Omega
