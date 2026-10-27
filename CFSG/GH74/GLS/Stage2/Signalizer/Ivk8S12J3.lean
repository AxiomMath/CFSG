module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12TwoSpec
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Count
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate5248

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.Sporadic.Schreier hiding j3S
open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.GroupTheory.TwoWeights
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem not_threeCfg_j3R :
    ¬ ThreeCfg (⊤ : Subgroup ↥j3R) := by
  classical
  have hn : (6156 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hrep, -⟩ := ctuc_j3_involution_centralizer_data
  obtain ⟨hSR, hScard, -, hrows, -, -, -, hoddcore⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨-, -, -, -, -, -, -, hnormal, hRcard, -⟩ :=
    ctuc_j3_normalizing_involution_permutation_model
  have hcheck := Certificates.certificate5248
  simp only [Certificates.Ivk8Two.J3.j3TwoOK, Bool.and_eq_true] at hcheck
  obtain ⟨⟨h2, hc⟩, ht9⟩ := hcheck
  set gG : List (Equiv.Perm (Fin 6156)) :=
    [tp 6156 (j3CentTbl 1), tp 6156 (j3CentTbl 2), tp 6156 (j3CentTbl 3), tp 6156 (j3CentTbl 4),
      tp 6156 (j3CentTbl 5), tp 6156 (j3CentTbl 6), tp 6156 (j3CentTbl 7),
      tp 6156 (j3CentTbl 8)] with hgG
  have hgT : List.Forall₂ (Rep 6156) Certificates.Ivk8Two.J3.gensT gG :=
    .cons (hrep 1 (by norm_num)) (.cons (hrep 2 (by norm_num)) (.cons (hrep 3 (by norm_num))
      (.cons (hrep 4 (by norm_num)) (.cons (hrep 5 (by norm_num)) (.cons (hrep 6 (by norm_num))
        (.cons (hrep 7 (by norm_num)) (.cons (hrep 8 (by norm_num)) .nil)))))))
  have hmemS : ∀ t ∈ j3SylowGenTbls, tp 6156 t ∈ gG := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
    have hi8 : i < 8 := List.mem_range.1 hi
    interval_cases i <;> simp [hgG]
  have hgN : ∀ g ∈ gG, g ∈ j3S := by
    intro g hg
    simp only [hgG, List.mem_cons, List.not_mem_nil, or_false] at hg
    have hsub : ∀ k, 1 ≤ k → k ≤ 8 → tp 6156 (j3CentTbl k) ∈ j3S := by
      intro k hk1 hk8
      apply Subgroup.subset_closure
      refine ⟨j3CentTbl k, ?_, rfl⟩
      show j3CentTbl k ∈ j3SylowGenTbls.toArray
      rw [List.mem_toArray]
      exact List.mem_map.2 ⟨k - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel hk1]⟩
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hsub 1 (by norm_num) (by norm_num), hsub 2 (by norm_num) (by norm_num),
      hsub 3 (by norm_num) (by norm_num), hsub 4 (by norm_num) (by norm_num),
      hsub 5 (by norm_num) (by norm_num), hsub 6 (by norm_num) (by norm_num),
      hsub 7 (by norm_num) (by norm_num), hsub 8 (by norm_num) (by norm_num)]
  obtain ⟨a, u₁, u₂, u₃, x, y, ha, h₁, h₂, h₃, hx, hy, hane, haw, D, hcard⟩ :=
    two_spec hn hgT hgN h2
  have hcenG := central_spec hn hgT hc
  have hat : a = tp 6156 (j3CentTbl 9) := by
    have h19 := (tblEq_eq_iff (hrep 1 (by norm_num)) (hrep 9 (by norm_num))).1 ht9
    have hev : evalCodes gG [1] = tp 6156 (j3CentTbl 1) := by
      rw [evalCodes, evalCodes, ite_eq_left_of_eq_true _ _ (eq_true (by norm_num : (0 : ℤ) < 1)),
        mul_one]
      exact List.getD_cons_zero
    exact haw.trans (hev.trans h19)
  have hcentS : ∀ s ∈ j3S, s * a = a * s := by
    intro s hs
    have hle : j3S ≤ centralizer ({a} : Set (Equiv.Perm (Fin 6156))) := by
      rw [j3S, Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      have := hcenG _ (hmemS t (by simpa using ht))
      rw [← haw] at this
      exact (Subgroup.mem_centralizer_singleton_iff.2 this.symm)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hs)
  have haR : a ∈ j3R := hSR ha
  have D' := data_of_mem j3R D haR (hSR h₁) (hSR h₂) (hSR h₃) (hSR hx) (hSR hy)
  set T₀ : Subgroup ↥j3R := j3S.subgroupOf j3R with hT₀
  have hT₀card : Nat.card ↥T₀ = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR).toEquiv, hScard]
    norm_num
  have hT₀2 : IsPGroup 2 ↥T₀ := IsPGroup.of_card hT₀card
  have hX2 : ¬ 2 ^ (8 + 1) ∣ Nat.card ↥j3R := by rw [hRcard]; norm_num
  have hX3 : ¬ 3 ^ 8 ∣ Nat.card ↥j3R := by rw [hRcard]; norm_num
  have hcen : ∀ t ∈ T₀, t * (⟨a, haR⟩ : ↥j3R) = ⟨a, haR⟩ * t := fun t ht =>
    Subtype.ext (hcentS _ ht)
  refine not_threeCfg_of_data D' hT₀2 hcen ha h₁ h₂ h₃ hx hy (le_of_eq hT₀card.symm) hX2 hX3 ?_
  intro E hE3 hEne hEC hN
  have hPR : j3P ≤ j3R := le_sup_left
  have hEP : E ≤ j3P.subgroupOf j3R := by
    have := hnormal
    refine odd_card_map_le_of_index_le_two (j3P.subgroupOf j3R) ?_ ?_
    · rw [hRcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv, card_j3P]
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
      rw [hk]
      exact Odd.pow (by decide)
  set Ē : Subgroup (Equiv.Perm (Fin 6156)) := E.map j3R.subtype with hĒ
  have hĒ3 : IsPGroup 3 ↥Ē :=
    hE3.of_equiv (E.equivMapOfInjective j3R.subtype j3R.subtype_injective)
  have hĒne : Ē ≠ ⊥ := fun h =>
    hEne ((Subgroup.map_eq_bot_iff_of_injective E j3R.subtype_injective).1 h)
  have hĒC : Ē ≤ j3P ⊓ centralizer ({a} : Set (Equiv.Perm (Fin 6156))) := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨hEP he, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hEC he)))
  have hS : IsSylowOf 2 j3S j3R := by
    refine isSylowOf_of_card hSR ?_
    rw [hScard, hRcard, factorization_100465920]
    norm_num
  have hRN : j3R ≤ normalizer (j3P : Set (Equiv.Perm (Fin 6156))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPR).1 hnormal
  have hTsyl : IsSylowOf 2 (j3S ⊓ j3P) j3P := hS.inf_of_le_normalizer hPR hRN
  have hTcard : Nat.card ↥(j3S ⊓ j3P) = 128 := by
    rw [hTsyl.card_eq, card_j3P, factorization_two_eq (k := 7) (by norm_num) (by norm_num)]
    norm_num
  have hTC : j3S ⊓ j3P ≤ j3P ⊓ centralizer ({a} : Set (Equiv.Perm (Fin 6156))) := fun t ht =>
    ⟨ht.2, Subgroup.mem_centralizer_singleton_iff.2 (hcentS t ht.1)⟩
  have hTN : j3S ⊓ j3P ≤ normalizer (Ē : Set (Equiv.Perm (Fin 6156))) := by
    intro t ht
    have htR : t ∈ j3R := hSR ht.1
    have htT : (⟨t, htR⟩ : ↥j3R) ∈ T₀ := ht.1
    have hn' := Subgroup.mem_normalizer_iff.mp (hN htT)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨t, htR⟩ * e * ⟨t, htR⟩⁻¹, (hn' e).1 he, rfl⟩
    · rintro ⟨e', he', hee'⟩
      have hx' : (⟨t, htR⟩⁻¹ * e' * ⟨t, htR⟩ : ↥j3R) ∈ E := (hn' _).2 (by
        have : (⟨t, htR⟩ : ↥j3R) * (⟨t, htR⟩⁻¹ * e' * ⟨t, htR⟩) * ⟨t, htR⟩⁻¹ = e' := by group
        rw [this]
        exact he')
      refine ⟨_, hx', ?_⟩
      show t⁻¹ * (e' : Equiv.Perm (Fin 6156)) * t = z
      rw [show (e' : Equiv.Perm (Fin 6156)) = t * z * t⁻¹ from hee']
      group
  have hr0 : j3Rows[0]'(by simp [j3Rows]) ∈ j3Rows := List.getElem_mem _
  obtain ⟨hr1, hr2, -, -, hr5, -⟩ := hrows _ hr0
  have hrep0 : (j3Rows[0]'(by simp [j3Rows])).rep = j3CentTbl 9 := by simp [j3Rows]
  have hcent0 : (j3Rows[0]'(by simp [j3Rows])).centOrder = 1920 := by simp [j3Rows]
  rw [hrep0, ← hat] at hr1 hr2 hr5
  rw [hcent0] at hr5
  have hCodd : ∀ N : Subgroup ↥(j3P ⊓ centralizer ({a} : Set (Equiv.Perm (Fin 6156)))),
      N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hNn hNodd
    have hle := CFSG.ComponentClassification.SmallLocal.le_oddCore_of_normal_odd hNn hNodd
    rw [hoddcore a hr1 hr2, le_bot_iff] at hle
    exact hle
  exact not_three_of_odd_trivial hr5 hCodd hTC hTcard hĒC hĒ3 hĒne hTN

theorem card_of_isSporadic_J3
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .J3) : Nat.card Y = 50232960 := by
  obtain ⟨e⟩ := hY
  have e₀ : Y ≃* NativeSporadic.J3 := e
  rw [Nat.card_congr (e₀.trans j3PermEquiv).toEquiv]
  exact card_j3P

theorem not_sylCfg8_J3
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J3)
    {T W : Subgroup (MulAut Y)} (hcfg : SylCfg Y T W) (hT : Nat.card ↥T = 2 ^ 8) : False := by
  obtain ⟨e⟩ := hY
  have e₀ : Y ≃* NativeSporadic.J3 := e
  have e' : Y ≃* j3P := e₀.trans j3PermEquiv
  have : Finite Y := Finite.of_equiv ↥j3P e'.symm.toEquiv
  obtain ⟨Θ₀, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have Θ : ↥j3R ≃* MulAut Y := Θ₀.trans (MulAut.congr e'.symm)
  have h2 : ¬ 2 ^ (8 + 1) ∣ Nat.card ↥j3R := by rw [hRcard]; norm_num
  exact not_threeCfg_j3R (threeCfg_top_of_syl8 Θ hcfg hT h2)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
