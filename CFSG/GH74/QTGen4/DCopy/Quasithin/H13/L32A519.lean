module

public import CFSG.Quasithin.H13.L32A519
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134W

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem exists_normal_of_cComp_le_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (S : Setting147 G T L V H) (h13322 : Stmt13_3_2_two_F4)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKM : K ≤ Subgroup.normalizer (L : Set G)) :
    ∃ N : Subgroup G, K ≤ N ∧ N ≤ Subgroup.normalizer (L : Set G) ⊓ H ∧
      H ≤ Subgroup.normalizer (N : Set G) ∧ ⁅N, N⁆ = N := by
  have h := S.hyp
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := h.normalizes_F4 h13322
  have hpc : pCoreOf 2 H ≠ ⊥ := S.hz.1.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKp : ⁅K, K⁆ = K := hK.2.1
  by_cases hKT : ∀ t ∈ T, t ∈ Subgroup.normalizer (K : Set G)
  · have hn := lemma_1_2_4_normal h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h38 hpc hTsyl
      (cComp_subset_lFamily hTH hK) le_rfl hK hKT
    exact ⟨K, le_rfl, le_inf hKM hKH,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn, hKp⟩
  push Not at hKT
  obtain ⟨t, ht, htn⟩ := hKT
  rcases lemma_1_2_1_three h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h38 hpc hK with
    hKn | ⟨hcard, -⟩
  · exact ⟨K, le_rfl, le_inf hKM hKH,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn, hKp⟩
  · have hne : conjSub t K ≠ K := fun h' => htn (conjSub_eq_self_iff.mp h')
    have hK₁ : K ∈ conjSubgroupsBy H K := ⟨1, H.one_mem, (conjSub_one K).symm⟩
    have hK₂ : conjSub t K ∈ conjSubgroupsBy H K := ⟨t, hTH ht, rfl⟩
    have hpair : ({K, conjSub t K} : Set (Subgroup G)) = conjSubgroupsBy H K := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro x (rfl | rfl)
        · exact hK₁
        · exact hK₂
      · rw [Set.ncard_pair hne.symm, hcard]
    have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
        conjSub t K ≤ X → K ≤ conjSub t⁻¹ X := by
      intro X g _ hle x hx
      have h1 : t * x * t⁻¹ ∈ X := hle (mul_mem_conjSub hx)
      have h2 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ ∈ conjSub t⁻¹ X := mul_mem_conjSub h1
      simpa [mul_assoc] using h2
    have hKt_le : ∀ {X : Subgroup G}, T ≤ X → K ≤ X → conjSub t K ≤ X := by
      intro X hTX hKX x hx
      have h1 : t⁻¹ * x * t ∈ K := mem_conjSub.mp hx
      have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [e]
      exact X.mul_mem (X.mul_mem (hTX ht) (hKX h1)) (X.inv_mem (hTX ht))
    refine ⟨K ⊔ conjSub t K, le_sup_left, ?_, ?_, ?_⟩
    · exact le_inf (sup_le hKM (hKt_le hTM hKM)) (sup_le hKH (hKt_le hTH hKH))
    · refine le_normalizer_of_forall_conjSub_le' fun g hg => ?_
      rw [conjSub_sup]
      refine sup_le ?_ ?_
      · have : conjSub g K ∈ ({K, conjSub t K} : Set (Subgroup G)) := by
          rw [hpair]
          exact ⟨g, hg, rfl⟩
        rcases this with h' | h'
        · rw [h']; exact le_sup_left
        · rw [h']; exact le_sup_right
      · have : conjSub g (conjSub t K) ∈ ({K, conjSub t K} : Set (Subgroup G)) := by
          rw [hpair, ← conjSub_mul]
          exact ⟨g * t, H.mul_mem hg (hTH ht), rfl⟩
        rcases this with h' | h'
        · rw [h']; exact le_sup_left
        · rw [h']; exact le_sup_right
    · have hKtp : ⁅conjSub t K, conjSub t K⁆ = conjSub t K := by
        rw [conjSub, ← Subgroup.map_commutator, hKp]
      refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      · calc K = ⁅K, K⁆ := hKp.symm
          _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc conjSub t K = ⁅conjSub t K, conjSub t K⁆ := hKtp.symm
          _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem lemma14_5_19_of_F4
    (h1332 : Stmt13_3_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Lemma14_5_19_F4 := by
  intro G _ _ T L V H S K hK
  have h := S.hyp
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have h1338 : A6.Stmt13_3_8_F4 := U3.stmt13_3_8_holds_F4 h1332
  have h1334 : A6.Stmt13_3_4_F4 := U3.stmt13_3_4_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hnot : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
    intro hKM
    obtain ⟨N, hKN, hNMH, hHN, hNp⟩ := exists_normal_of_cComp_le_F4 h37 h38 S h13322 hK hKM
    have hNo : oTwoRes N = N := by
      rw [oTwoRes_eq_oTwoUpper]
      exact oTwoUpper_eq_of_perfect_F9 hNp
    have h23 := (h1338 G T L L H N h.hyp.h13 h.fsu.faithful ⟨hTH, S.hz.1.2⟩ S.hz.2.2 hNo
      (hNMH.trans inf_le_right) hHN (hNMH.trans inf_le_left)).2
    have hsN : Group.IsSolvable ↥N := A5.isSolvable_of_isTwoThreeGroup h23
    exact not_isSolvable_of_mem_cComp hK
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKN)
        (Subgroup.inclusion_injective hKN))
  refine ⟨hnot, h, ⟨⟨le_sup_right, ?_⟩, ?_, ?_⟩⟩
  ·
    have hT := h.isTSub_V1_F4 hMod
    obtain ⟨-, hV1c, hTN⟩ := hT
    have hV1 : Nat.card (fsuV1 T V) = 2 := by rw [hV1c, pow_one]
    have hp : IsPGroup 2 (fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hV1)
    have hV1T : fsuV1 T V ≤ T := by
      intro z hz
      exact (Subgroup.closure_le _).mpr (fun x hx => hx.1.1) hz.2
    have hX : conjClosure K T ⊔ (L32A.l1 T L V ⊔ T) ≤ H :=
      sup_le (conjClosure_le fun t ht k hk => H.mul_mem (H.mul_mem (hTH ht) (hKH hk))
        (H.inv_mem (hTH ht))) S.hz.1.1
    have hle : fsuV1 T V ≤ pCoreOf 2 (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T)) :=
      le_pCoreOf_of_le_normalizer 2 (hV1T.trans (le_sup_right.trans le_sup_right))
        (hX.trans S.hz.2.1) hp
    intro hbot
    have h1 : fsuV1 T V = ⊥ := le_bot_iff.mp (hbot ▸ hle)
    rw [h1, Subgroup.card_bot] at hV1
    exact absurd hV1 (by norm_num)
  · exact (sup_le (conjClosure_le fun t ht k hk => H.mul_mem (H.mul_mem (hTH ht) (hKH hk))
      (H.inv_mem (hTH ht))) S.hz.1.1).trans S.hz.2.1
  · intro hle
    exact hnot ((le_conjClosure K T).trans (le_sup_left.trans hle))

end CFSG.Quasithin.H13.L32A
