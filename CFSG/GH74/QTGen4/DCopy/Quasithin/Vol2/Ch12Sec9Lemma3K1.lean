module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3K1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Final1291
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement

open L1293 in

theorem lemma12_9_3K1_of_inputs_F4
    (h1222 : Stmt12_2_2_F4) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (hDyn : DynkinFact1293) : Lemma12_9_3K1_F4 := by
  classical
  intro G _ _ T L V n hcx V₁ hV₁
  have h := hcx.hyp
  have hyp := h.hyp
  have hn45 := hcx.n45
  have hn : n ≠ 3 := by omega
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes_F4 h1222
  obtain ⟨K₁, hLK, hK, hK₁n⟩ := exists_cComp_normalizer_ge_lOne_F4 h1222 h37 h38 h39 h hn hV₁
  refine ⟨K₁, hLK, hK, hK₁n, ?_⟩
  obtain ⟨hS, hH, hBH, hB⟩ := lOne_lemma_1_2_4_data_F4 h1222 h hn hV₁
  have hKc : K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)) := hK
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp hKc
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := hV₁.2.2
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hBK : modO2Image (Subgroup.normalizer (V₁ : Set G)) (lOne L V₁) ≤
      modO2Image (Subgroup.normalizer (V₁ : Set G)) K₁ :=
    Subgroup.map_mono (fun x hx => hLK hx)

  obtain ⟨eL⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
  obtain ⟨eB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
  have hD := data1293_of (B := modO2Image (Subgroup.normalizer (V₁ : Set G)) (lOne L V₁))
    (k := n - 1) (by omega) (eB.symm.trans eL)
  obtain ⟨eK⟩ := modO2_mulEquiv hKc
  rcases lemma_1_2_4_list hyp.qtke hyp.simple hyp.nonabelian h312 hH hS hBH hB hKc hLK with
    heq | hcase | hnq
  ·
    left
    refine eq_of_modO2Image_eq hLK hK₁G₁ (perfect_of_mem_cComp hKc) ?_ heq
    have hP : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ T :=
      pCoreOf_two_le_of_isSylowTwoOf hS
    exact L1295.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer (hP.trans hTL₁)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
  ·
    right
    have hnoDyn : ¬ DynkinPair1293 (modO2Image (Subgroup.normalizer (V₁ : Set G)) (lOne L V₁))
        (modO2Image (Subgroup.normalizer (V₁ : Set G)) K₁) := by
      intro hpair

      have hTbar : QuasithinUnique.IsSylowTwoOf
          (modO2Image (Subgroup.normalizer (V₁ : Set G)) T) ⊤ :=
        isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS) _
          (QuotientGroup.mk'_surjective _)
      have hKn : (modO2Image (Subgroup.normalizer (V₁ : Set G)) K₁).Normal :=
        Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁G₁).2 hK₁n) _
          (QuotientGroup.mk'_surjective _)
      have hSK := F7.isSylowTwoOf_inf_normal hTbar le_top (le_top.trans
        (Subgroup.normalizer_eq_top (H := modO2Image (Subgroup.normalizer (V₁ : Set G)) K₁)).ge)
      obtain ⟨s, hs, hout⟩ := hDyn _ _ _ _ hBK hpair hSK
        (inf_le_left.trans (modO2Image_le_normalizer hTL₁))
      obtain ⟨t, ht, rfl⟩ := hs.1
      have htT : (t : G) ∈ T := ht

      obtain ⟨b, hb, hbx⟩ :=
        lOne_inner_F4 h1222 h hn hV₁ (hyp.normalizes htT) (hTV htT) (hTG₁ htT)
      obtain ⟨xbar, hxbar, hnot⟩ := hout _ ⟨⟨b, hBH hb⟩, hb, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hxbar
      have hxL : (x : G) ∈ lOne L V₁ := hx
      apply hnot
      have hc : ⁅(t : G) * b⁻¹, (x : G)⁆ ∈ pCoreOf 2 (lOne L V₁) := by
        have hy : b⁻¹ * (x : G) * b ∈ lOne L V₁ :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hxL) hb
        have h1 := hbx _ hy
        have h2 := (Subgroup.mem_normalizer_iff.mp
          (LieType.BorelTits.le_normalizer_pCoreOf 2 (lOne L V₁) hb) _).mp h1
        rw [commutatorElement_def]
        convert h2 using 1
        group

      have hPbar : modO2Image (Subgroup.normalizer (V₁ : Set G)) (pCoreOf 2 (lOne L V₁)) ≤
          pCoreOf 2 (modO2Image (Subgroup.normalizer (V₁ : Set G)) (lOne L V₁)) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          (Subgroup.map_mono (fun y hy => LieType.BorelTits.pCoreOf_le 2 (lOne L V₁) hy))
          (modO2Image_le_normalizer (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
          ((A4.isPGroup_subgroupOf_of_le ((LieType.BorelTits.pCoreOf_le 2 _).trans hBH)
            (LieType.BorelTits.pCoreOf_isPGroup 2 _)).map _)
      refine hPbar ⟨⁅t * (⟨b, hBH hb⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))⁻¹, x⁆, ?_, ?_⟩
      · show ((⁅t * (⟨b, hBH hb⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))⁻¹, x⁆ :
          ↥(Subgroup.normalizer (V₁ : Set G))) : G) ∈ pCoreOf 2 (lOne L V₁)
        simpa [commutatorElement_def] using hc
      · rw [map_commutatorElement, map_mul, map_inv]
    rcases hD.list_of_case hnoDyn hcase with h2 | ⟨hk3, h3⟩
    · exact Or.inl (h2.of_mulEquiv eK.symm)
    · exact Or.inr ⟨by omega, h3.of_mulEquiv eK.symm⟩
  ·
    right
    right
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH
    obtain ⟨hk3, hSL⟩ := hD.list_of_nonquasi hBK (h36 _ hQ _ (modO2Image_mem_cComp hKc)) hnq
    refine ⟨by omega, ?_⟩
    have h3 : IsList1293Three ↥(modO2Image (Subgroup.normalizer (V₁ : Set G)) K₁) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSL))))))
    exact h3.of_mulEquiv eK.symm

end CFSG.Quasithin.H13
