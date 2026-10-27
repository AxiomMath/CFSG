module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ARank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem card_eq_mul_card_map {X J B D : Subgroup Ω} (hN : NLAct 3 X J B D) :
    Nat.card B = Nat.card D *
      Nat.card ((B.subgroupOf (Subgroup.normalizer (J : Set Ω))).map (chevAut 3 J)) := by
  set N : Subgroup Ω := Subgroup.normalizer (J : Set Ω)
  have hker : (chevAut 3 J).ker ⊓ B.subgroupOf N = D.subgroupOf N := by
    ext ⟨e, he⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => (hN.ker e h.2 he).1 h.1,
      fun hd => ⟨(hN.ker e (hN.le hd) he).2 hd, hN.le hd⟩⟩
  have h1 := Subgroup.relIndex_mul_card (H := (chevAut 3 J).ker) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_ker, hker, D4T.card_subgroupOf_of_le (hN.le.trans hN.norm),
    D4T.card_subgroupOf_of_le hN.norm] at h1
  rw [← h1, mul_comm]

private theorem image_facts {J B : Subgroup Ω} (hB : IsElemAbelian 3 B)
    (hF : D4T.D4TwoFacts (PSimple 3 J))
    (hout : ∃ e ∈ B, ∃ he : e ∈ Subgroup.normalizer (J : Set Ω),
      chevAut 3 J ⟨e, he⟩ ∉ D4T.innerAut (PSimple 3 J)) :
    IsElemAbelian 3 ((B.subgroupOf (Subgroup.normalizer (J : Set Ω))).map (chevAut 3 J)) ∧
      ¬ (B.subgroupOf (Subgroup.normalizer (J : Set Ω))).map (chevAut 3 J) ≤
        D4T.innerAut (PSimple 3 J) ∧
      Nat.card ((B.subgroupOf (Subgroup.normalizer (J : Set Ω))).map (chevAut 3 J)) ≤ 27 := by
  set N : Subgroup Ω := Subgroup.normalizer (J : Set Ω)
  set ρ : ↥N →* MulAut (PSimple 3 J) := chevAut 3 J
  have hAel : IsElemAbelian 3 ((B.subgroupOf N).map ρ) :=
    S9.l94t_isElemAbelian_map ρ (hB.comap N.subtype_injective)
  have hAni : ¬ (B.subgroupOf N).map ρ ≤ D4T.innerAut (PSimple 3 J) := by
    obtain ⟨e, heB, he, hne⟩ := hout
    exact fun hle => hne (hle (Subgroup.mem_map_of_mem ρ
      (show (⟨e, he⟩ : ↥N) ∈ B.subgroupOf N from heB)))
  exact ⟨hAel, hAni, hF.aut_le _ hAel hAni⟩

private theorem exists_lift_eightyOne {J D : Subgroup Ω} (hZ : Subgroup.center (PQuot 3 J) = ⊥)
    (hD : IsElemAbelian 3 D) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hF : D4T.D4TwoFacts (PSimple 3 J)) :
    ∃ E : Subgroup Ω, E ≤ J ∧ IsElemAbelian 3 (E ⊔ D) ∧
      Nat.card ↥(E ⊔ D) = 81 * Nat.card D := by
  obtain ⟨Eb, hEb, hEbc⟩ := hF.rank4
  obtain ⟨E, hEJ, hEel, hEc⟩ := exists_lift_sup hZ hD hDJ hEb
  exact ⟨E, hEJ, hEel, by rw [hEc, hEbc]; norm_num⟩

theorem tri_noTwo_comp {X J B D W : Subgroup Ω}
    (hN : NLAct 3 X J B D) (hB : IsElemAbelian 3 B)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hF : D4T.D4TwoFacts (PSimple 3 J))
    (hout : ∃ e ∈ B, ∃ he : e ∈ Subgroup.normalizer (J : Set Ω),
      chevAut 3 J ⟨e, he⟩ ∉ D4T.innerAut (PSimple 3 J))
    (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (hW : IsPGroup 2 W) (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hWJ : W ≤ Subgroup.centralizer (J : Set Ω)) : W = ⊥ := by
  by_contra hne
  have hD : IsElemAbelian 3 D := isElemAbelian_mono hB hN.le
  have hDpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨E, hEJ, hEel, hEc⟩ := exists_lift_eightyOne hZ hD hDJ hF
  have hJW : J ≤ Subgroup.centralizer (W : Set Ω) := Subgroup.le_centralizer_iff.1 hWJ
  have hEW : E ⊔ D ≤ Subgroup.normalizer (W : Set Ω) :=
    sup_le ((hEJ.trans hJW).trans (Subgroup.centralizer_le_normalizer _)) (hN.le.trans hBW)
  have h := (card_le_pow_glaTwoLocalRank Nat.prime_three hEel hne hW hEW).trans hrank
  have h3 : Nat.card D * 81 ≤ Nat.card D * 27 :=
    calc Nat.card D * 81 = Nat.card ↥(E ⊔ D) := by rw [hEc, mul_comm]
      _ ≤ Nat.card B := h
      _ = Nat.card D * _ := card_eq_mul_card_map hN
      _ ≤ Nat.card D * 27 := Nat.mul_le_mul_left _ (image_facts hB hF hout).2.2
  have := Nat.le_of_mul_le_mul_left h3 hDpos
  omega

theorem tri_noTwo_cent {X J B D W : Subgroup Ω}
    (hN : NLAct 3 X J B D) (hB : IsElemAbelian 3 B)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hCD : Subgroup.centralizer (D : Set Ω) ≤ Subgroup.normalizer (J : Set Ω))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hF : D4T.D4TwoFacts (PSimple 3 J))
    (hout : ∃ e ∈ B, ∃ he : e ∈ Subgroup.normalizer (J : Set Ω),
      chevAut 3 J ⟨e, he⟩ ∉ D4T.innerAut (PSimple 3 J))
    (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (hW : IsPGroup 2 W) (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hWD : W ≤ Subgroup.centralizer (D : Set Ω)) : W = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hD : IsElemAbelian 3 D := isElemAbelian_mono hB hN.le
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hcardB := card_eq_mul_card_map hN
  obtain ⟨hAel, hAni, hAle⟩ := image_facts hB hF hout
  set N : Subgroup Ω := Subgroup.normalizer (J : Set Ω)
  set ρ : ↥N →* MulAut (PSimple 3 J) := chevAut 3 J
  set A : Subgroup (MulAut (PSimple 3 J)) := (B.subgroupOf N).map ρ
  obtain ⟨E3, W3, hE3el, hE3c, hW32, hW3ne, hE3W⟩ := hF.rank3
  have hlow : 27 * Nat.card D ≤ Nat.card B := by
    have h := (card_mul_card_le_rank hZ hD hDJ hE3el hW32 hW3ne hE3W).trans hrank
    rwa [hE3c] at h
  have hA27 : Nat.card A = 27 := by
    refine le_antisymm hAle (le_of_not_gt fun hlt => ?_)
    have h := Nat.mul_lt_mul_of_pos_left hlt hDpos
    linarith
  have hBcard : Nat.card B = 27 * Nat.card D := by rw [hcardB, hA27, mul_comm]
  obtain ⟨E, hEJ, hEel, hEc⟩ := exists_lift_eightyOne hZ hD hDJ hF
  have hWN : W ≤ N := hWD.trans hCD
  by_cases hact : ∀ t (ht : t ∈ W), ρ ⟨t, hWN ht⟩ = 1
  ·
    have hcomm : ∀ t ∈ W, ∀ l ∈ J, ⁅l, t⁆ ∈ GLAPPrimeCoreOf 3 J := fun t ht l hl =>
      (centMod_iff.1 ((chevAut_eq_one_iff Nat.prime_three hN.comp (hWN ht)).1
        (hact t ht))).2 l hl
    set O : Subgroup Ω := GLAPPrimeCoreOf 3 J
    have hOJ : O ≤ J := Subgroup.map_subtype_le _
    have hWO : W ≤ Subgroup.normalizer (O : Set Ω) :=
      hWN.trans (normalizer_le_normalizer_glaPPrimeCoreOf 3 J)
    have hY3 : ¬ 3 ∣ Nat.card ↥(O ⊔ W) := by
      intro h3
      have h3' : 3 ∣ Nat.card O * Nat.card W :=
        card_sup_mul_card_inf_of_le_normalizer hWO ▸ dvd_mul_of_dvd_left h3 _
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3' with h | h
      · exact CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three J h
      · obtain ⟨k, hk⟩ := hW.exists_card_eq
        rw [hk] at h
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        omega
    have hYeven : Even (Nat.card ↥(O ⊔ W)) := by
      obtain ⟨k, hk⟩ := hW.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne (Subgroup.card_eq_one.1 (by simpa using hk))
      exact even_iff_two_dvd.2
        ((hk ▸ dvd_pow_self 2 hk0).trans (Subgroup.card_dvd_of_le le_sup_right))
    have hEY : E ⊔ D ≤ Subgroup.normalizer ((O ⊔ W : Subgroup Ω) : Set Ω) := by
      rw [Subgroup.sup_eq_closure O W]
      refine sup_le (Subgroup.le_normalizer_closure_iff.2 ?_)
        (Subgroup.le_normalizer_closure_iff.2 ?_)
      · rintro e he g (hg | hg)
        · exact Subgroup.subset_closure
            (Set.mem_union_left _ (chev_conj_mem_glaPPrimeCoreOf (hEJ he) hg))
        · have e1 : e * g * e⁻¹ = ⁅e, g⁆ * g := by
            rw [commutatorElement_def]
            group
          rw [e1]
          exact mul_mem (Subgroup.subset_closure (Set.mem_union_left _ (hcomm g hg e (hEJ he))))
            (Subgroup.subset_closure (Set.mem_union_right _ hg))
      · intro d hd g hg
        have hdg : d * g = g * d := by
          rcases hg with hg | hg
          · exact (Subgroup.mem_centralizer_iff.1 (hDJ hd) g (hOJ hg)).symm
          · exact Subgroup.mem_centralizer_iff.1 (hWD hg) d hd
        rw [hdg, mul_inv_cancel_right]
        exact Subgroup.subset_closure hg
    obtain ⟨W', hW'ne, -, hW'2, hEW'⟩ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.exists_twoGroup_normalized_of_coprime_even
        Nat.prime_three (by norm_num) (isPGroup_of_isElemAbelian hEel) hEY hY3 hYeven
    have h := (card_le_pow_glaTwoLocalRank Nat.prime_three hEel hW'ne hW'2 hEW').trans hrank
    omega
  ·
    push Not at hact
    obtain ⟨t, ht, hρt⟩ := hact
    set Wh : Subgroup (MulAut (PSimple 3 J)) := (W.subgroupOf N).map ρ
    have hWhne : Wh ≠ ⊥ := fun h => hρt (by
      have hmem : ρ ⟨t, hWN ht⟩ ∈ Wh := Subgroup.mem_map_of_mem ρ
        (show (⟨t, hWN ht⟩ : ↥N) ∈ W.subgroupOf N from ht)
      rwa [h, Subgroup.mem_bot] at hmem)
    have hnorm : A ≤ Subgroup.normalizer (Wh : Set (MulAut (PSimple 3 J))) := by
      rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem _ ?_)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 (hBW (Subgroup.mem_subgroupOf.1 hb)) (y : Ω)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
      exact h1
    exact hF.aut_norm A Wh hAel hAni (by rw [hA27]; norm_num) (hW.comap_subtype.map ρ)
      hWhne hnorm

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
