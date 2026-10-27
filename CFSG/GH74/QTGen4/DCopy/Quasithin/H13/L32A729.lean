module

public import CFSG.Quasithin.H13.L32A729
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A706f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem thm14_7_29_of_F4 (h28 : Lemma14_7_28_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Thm14_7_29_F4 := by
  intro G _ _ T L V hyp X hLX hXG hXs
  by_contra hXM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hV1 := Hyp147.isTSub_V1_F4 hyp hMod
  have hTX : T ≤ X := le_sup_right.trans hLX
  have hV1T : fsuV1 T V ≤ T := by
    have hZ : quasithinOmegaOneCenter T ≤ T :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
    exact inf_le_right.trans hZ
  have hV1O : fsuV1 T V ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 (hV1T.trans hTX) hXG ?_
    exact IsPGroup.of_card hV1.2.1
  have hO2 : pCoreOf 2 X ≠ ⊥ := by
    intro h
    have : Nat.card ↥(fsuV1 T V) = 1 := by
      rw [h, le_bot_iff] at hV1O
      rw [hV1O, Subgroup.card_bot]
    rw [hV1.2.1] at this
    norm_num at this
  have S : Setting147 G T L V X := ⟨hyp, ⟨⟨hLX, hO2⟩, hXG, hXM⟩⟩

  set Xs := ↥X ⧸ CFSG.pCore 2 ↥X with hXs'
  have hs : Group.IsSolvable Xs := by
    have := hXs
    infer_instance
  have h2 : CFSG.pCore 2 Xs = ⊥ := pCore_two_quot_eq_bot ↥X
  have hFO := fitting_le_oddCore h2

  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L hyp.hyp.h13 L hyp.hyp.h13.faithful).2.1.1
  have hl1L : l1 T L V ≤ Subgroup.normalizer (L : Set G) :=
    (oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)
  have hOT : pCoreOf 2 X ≤ T := pCoreOf_le_of_le hyp hTX

  suffices himg : modO2Image X (l1 T L V ⊔ T) = ⊤ by
    apply hXM
    intro x hx
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ : Xs) ∈
        modO2Image X (l1 T L V ⊔ T) := by rw [himg]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := by
      rw [← QuotientGroup.eq]
      exact hyx
    have hO : ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ pCoreOf 2 X := by
      refine ⟨y⁻¹ * ⟨x, hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, CFSG.QuasithinUnique.Lin2.openPCore_eq_pCore]
      exact hyx'
    have hx' : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
    rw [hx']
    refine Subgroup.mul_mem _ ?_ (hTL (hOT hO))
    exact sup_le hl1L hTL (Subgroup.mem_subgroupOf.mp hy)

  set I := modO2Image X (l1 T L V ⊔ T) with hI
  have hTI : modO2Image X T ≤ I := Subgroup.map_mono (Subgroup.subgroupOf_mono X le_sup_right)
  have hLI : modO2Image X (l1 T L V) ≤ I :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono X le_sup_left)

  have hT2 : ¬ 2 ∣ I.index := by
    intro h2I
    have hTs : ¬ 2 ∣ (modO2Image X T).index := by
      have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).ker ≤ T.subgroupOf X := by
        rw [QuotientGroup.ker_mk']
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        refine hOT ⟨y, ?_, rfl⟩
        rw [SetLike.mem_coe, CFSG.QuasithinUnique.Lin2.openPCore_eq_pCore]
        exact hy
      rw [modO2Image, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
      intro hd
      apply hyp.fsu.sylow.2
      rw [← Subgroup.relIndex_mul_index hTX]
      exact Dvd.dvd.mul_right hd _
    exact hTs (h2I.trans (Subgroup.index_dvd_of_le hTI))

  have hFne : CFSG.fittingSubgroup Xs = ⊥ → I = ⊤ := by
    intro hF
    have h1 : Nat.card Xs = 1 := (CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable Xs).mp hF
    have : Subsingleton Xs := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  rcases h28 G T L V X S with hO | hO
  · exact hFne (le_bot_iff.mp (hFO.trans hO.le))
  set L1s := modO2Image X (l1 T L V) with hL1s

  by_cases hF1 : CFSG.fittingSubgroup Xs = ⊥
  · exact hFne hF1
  have hL1odd : Odd (Nat.card ↥L1s) := by
    rw [← hO]
    exact CFSG.Quasithin.A312.odd_card_oddCore Xs
  have hL1d : Nat.card ↥L1s ∣ 3 := by
    have hl1X : l1 T L V ≤ X := le_sup_left.trans hLX
    have hdvd : Nat.card ↥L1s ∣ Nat.card ↥(l1 T L V) := by
      have h1 := Subgroup.card_map_dvd ((l1 T L V).subgroupOf X)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1X).toEquiv] at h1
    have hidx := (M76.relIndex_l1_T_F4 S h1222 h1332 h1334).1
    have hcard : Nat.card ↥(l1 T L V) = 3 * Nat.card ↥(pCoreOf 2 (l1 T L V)) := by
      have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
      rw [inf_eq_left.mpr (pCoreOf_le 2 (l1 T L V)), hidx] at h1
      exact h1.symm
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
    rw [hcard, ha] at hdvd
    have hcop : Nat.Coprime (Nat.card ↥L1s) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hL1odd)
    exact hcop.dvd_of_dvd_mul_right hdvd

  have hFL : CFSG.fittingSubgroup Xs ≤ L1s := hO ▸ hFO
  have hF3 : Nat.card ↥(CFSG.fittingSubgroup Xs) = 3 := by
    have hd : Nat.card ↥(CFSG.fittingSubgroup Xs) ∣ 3 :=
      (Subgroup.card_dvd_of_le hFL).trans hL1d
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hF1
    · exact h
  have hFeq : CFSG.fittingSubgroup Xs = L1s :=
    Subgroup.eq_of_le_of_card_ge hFL (by rw [hF3]; exact Nat.le_of_dvd (by norm_num) hL1d)

  set F := CFSG.fittingSubgroup Xs with hFdef
  have hcardX : Nat.card Xs ≤ 6 := by
    set ψ : Xs →* MulAut ↥F := MulAut.conjNormal with hψ
    have hker : ψ.ker ≤ F := by
      refine le_trans ?_ (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg (fun φ : MulAut ↥F => ((φ ⟨f, hf⟩ : ↥F) : Xs)) (MonoidHom.mem_ker.mp hx)
      simp only [hψ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc f * x = x * f * x⁻¹ * x := by rw [h1]
        _ = x * f := by group
    have hFc : IsCyclic ↥F := isCyclic_of_prime_card (p := 3) hF3
    have hAut : Nat.card (MulAut ↥F) = 2 := by
      rw [IsCyclic.card_mulAut, hF3]
      decide
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ↥ψ.ker ≤ 3 := hF3 ▸ Subgroup.card_le_of_le hker
    have h3 : Nat.card ↥ψ.range ≤ 2 :=
      (Subgroup.card_le_card_group ψ.range).trans hAut.le
    rw [← h1]
    calc Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ 3 * 2 := Nat.mul_le_mul h2 h3
      _ = 6 := by norm_num

  have hLidx : L1s.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index F
    rw [hF3] at h1
    rw [← hFeq]
    omega
  have hIdvd : I.index ∣ L1s.index := Subgroup.index_dvd_of_le hLI
  have hLpos : 0 < L1s.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hIle : I.index ≤ 2 := (Nat.le_of_dvd hLpos hIdvd).trans hLidx
  have hIpos : 0 < I.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hI2 : I.index ≠ 2 := fun h => hT2 ⟨1, by omega⟩
  have hI1 : I.index = 1 := by omega
  exact Subgroup.index_eq_one.mp hI1

end CFSG.Quasithin.H13.L32A
