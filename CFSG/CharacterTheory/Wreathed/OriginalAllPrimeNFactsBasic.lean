module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSetting

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion
open CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open scoped commutatorElement Pointwise

section General

variable {H : Type*} [Group H]

theorem eq_bot_or_le_of_simple_selfCentralizing {L : Subgroup H} [L.Normal] [IsSimpleGroup L]
    (hC : Subgroup.centralizer (L : Set H) = ⊥) (B : Subgroup H) [B.Normal] :
    B = ⊥ ∨ L ≤ B := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((B ⊓ L).subgroupOf L) with h | h
  · left
    have hBL : B ⊓ L = ⊥ := by
      have hdisj := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_assoc, inf_idem] at hdisj
    have hcomm : ⁅B, L⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_le_inf B L).trans hBL.le)
    rw [← le_bot_iff, ← hC]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  · right
    exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left

theorem eq_bot_of_isSolvable_of_simple_selfCentralizing {L : Subgroup H} [L.Normal]
    [IsSimpleGroup L] (hnonab : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set H) = ⊥) (B : Subgroup H) [B.Normal]
    (hB : Group.IsSolvable B) : B = ⊥ := by
  rcases eq_bot_or_le_of_simple_selfCentralizing hC B with h | hLB
  · exact h
  · exfalso
    have : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLB)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

theorem commutator_le_inf_of_le_normalizer (Y M : Subgroup H) [M.Normal]
    (hMY : M ≤ Subgroup.normalizer (Y : Set H)) : ⁅Y, M⁆ ≤ Y ⊓ M := by
  rw [Subgroup.commutator_le]
  intro y hy m hm
  refine ⟨?_, ?_⟩
  · have hconj : m * y⁻¹ * m⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hMY hm) y⁻¹).mp (Y.inv_mem hy)
    have h : ⁅y, m⁆ = y * (m * y⁻¹ * m⁻¹) := by rw [commutatorElement_def]; group
    rw [h]
    exact Y.mul_mem hy hconj
  · rw [commutatorElement_def]
    exact M.mul_mem (Subgroup.Normal.conj_mem inferInstance m hm y) (M.inv_mem hm)

theorem eq_bot_of_odd_of_le_two_group {W P : Subgroup H} (hWP : W ≤ P) (hP : IsPGroup 2 P)
    (hW : Odd (Nat.card W)) : W = ⊥ := by
  have hWp : IsPGroup 2 W := hP.to_le hWP
  rcases hWp.card_eq_or_dvd with h | h
  · exact Subgroup.eq_bot_of_card_eq W h
  · exact absurd (even_iff_two_dvd.mpr h) (Nat.not_even_iff_odd.mpr hW)

theorem le_of_isPerfect_of_le_sup_center (M A Z : Subgroup H) [Group.IsPerfect M]
    (hZ : Z ≤ Subgroup.center H) (hM : M ≤ A ⊔ Z) : M ≤ A := by
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [← Subgroup.commutator_eq_self (H := M)]
  refine (Subgroup.commutator_mono hM hM).trans ?_
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₁
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₂
  have hc₁ := Subgroup.mem_center_iff.mp (hZ hz₁)
  have hc₂ := Subgroup.mem_center_iff.mp (hZ hz₂)
  have h : ⁅a₁ * z₁, a₂ * z₂⁆ = ⁅a₁, a₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
        = a₁ * (z₁ * a₂) * z₂ * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * (a₂ * z₁) * z₂ * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [← hc₁ a₂]
      _ = a₁ * a₂ * (z₁ * z₂) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * a₂ * (z₂ * z₁) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [← hc₁ z₂]
      _ = a₁ * a₂ * (z₂ * a₁⁻¹) * z₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * a₂ * (a₁⁻¹ * z₂) * z₂⁻¹ * a₂⁻¹ := by rw [← hc₂ a₁⁻¹]
      _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group
  rw [h]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem wreathedSetting_T_eq (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) : (wreathedSetting n S e p f).T = modelT n S e :=
  (CompatibleFamilies.modelT_eq_closure S e hn).symm

omit [Finite G] in
theorem wreathedSetting_D_eq (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) : (wreathedSetting n S e p f).D = (S : Subgroup G) := by
  change (S : Subgroup G) ⊓ Subgroup.normalizer ((wreathedSetting n S e p f).T : Set G) = S
  rw [wreathedSetting_T_eq n hn S e p f]
  exact inf_eq_left.mpr ((sylow_le_modelBase_normalizer S e).trans
    (modelBase_normalizer_le_modelT_normalizer n hn S e))

omit [Finite G] in
theorem centralizerOddCoreMap_ker (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
  QuotientGroup.ker_mk' _

theorem centralizerFullQuotientMap_ker (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullQuotientMap n hn S e).ker = centralizerFullCenterImage n hn S e :=
  QuotientGroup.ker_mk' _

theorem wreathed_layer_facts
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal ∧
      CFSG.IsQuasisimple (CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
      Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
        Set (centralizerOddCoreQuotient n S e)) = centralizerFullCenterImage n hn S e ∧
      (CFSG.layer (centralizerOddCoreQuotient n S e)).map (centralizerFullQuotientMap n hn S e) =
        centralizerSimpleLayer n hn S e := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [hdata.layer]
  refine ⟨hdata.normal, hdata.quasisimple, ?_, ?_⟩
  · rw [hdata.centralizer]
    exact centralizerFullQuotientMap_ker n hn S e
  · apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_right
    · intro l hl
      obtain ⟨m, hm⟩ := hdata.restriction_surjective ⟨l, hl⟩
      exact ⟨m, m.property, congrArg Subtype.val hm⟩

theorem wreathed_simpleLayer_facts
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    IsSimpleGroup (centralizerSimpleLayer n hn S e) ∧
      (∃ a b : centralizerSimpleLayer n hn S e, a * b ≠ b * a) ∧
      Subgroup.centralizer (centralizerSimpleLayer n hn S e :
        Set (centralizerFullQuotient n hn S e)) = ⊥ := by
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem wreathed_oddCore_sup_fullCenter_isSolvable (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Group.IsSolvable (centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e :
      Subgroup (involutionCentralizer n S e)) := by
  let : IsCyclic (Subgroup.center
      (involutionCentralizer n S e ⧸ centralizerOddCore n S e)) := by
    change IsCyclic (Subgroup.center (centralizerOddCoreQuotient n S e))
    exact original_quotient_center_isCyclic n hn S e
  have h := solvable_center_preimage (centralizerOddCore n S e) (centralizerOddCore_card_odd n S e)
  change Group.IsSolvable ((Subgroup.center (centralizerOddCoreQuotient n S e)).comap
    (centralizerOddCoreMap n S e)) at h
  rwa [original_center_preimage n hn S e] at h

theorem wreathed_solvableRadical_eq
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.solvableRadical (involutionCentralizer n S e) =
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e := by
  apply le_antisymm
  · set A := CFSG.solvableRadical (involutionCentralizer n S e)
    have hAn : A.Normal := CFSG.ABGLocalTools.solvableRadical_normal
    have : Group.IsSolvable A := CFSG.ABGLocalTools.solvableRadical_isSolvable
    have hA1n : (A.map (centralizerOddCoreMap n S e)).Normal :=
      hAn.map _ (centralizerOddCoreMap_surjective n S e)
    have : Group.IsSolvable (A.map (centralizerOddCoreMap n S e)) :=
      Group.isSolvable_of_surjective ((centralizerOddCoreMap n S e).subgroupMap_surjective A)
    have hBn : ((A.map (centralizerOddCoreMap n S e)).map
        (centralizerFullQuotientMap n hn S e)).Normal :=
      hA1n.map _ (centralizerFullQuotientMap_surjective n hn S e)
    have hBs : Group.IsSolvable ((A.map (centralizerOddCoreMap n S e)).map
        (centralizerFullQuotientMap n hn S e)) :=
      Group.isSolvable_of_surjective
        ((centralizerFullQuotientMap n hn S e).subgroupMap_surjective _)
    obtain ⟨hsimple, hnonabL, hC⟩ := wreathed_simpleLayer_facts hnonab n hn S e hfour
    have hB := eq_bot_of_isSolvable_of_simple_selfCentralizing hnonabL hC _ hBs
    rw [Subgroup.map_eq_bot_iff, centralizerFullQuotientMap_ker,
      ← centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e,
      Subgroup.map_le_iff_le_comap, original_center_preimage n hn S e] at hB
    exact hB
  · apply le_sSup
    refine ⟨?_, wreathed_oddCore_sup_fullCenter_isSolvable n hn S e⟩
    rw [← original_center_preimage n hn S e]
    exact Subgroup.Normal.comap inferInstance _

omit [Finite G] in
theorem wreathed_centerOf_sylow (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centerOf (S : Subgroup G) =
      (centralizerFullCenter n hn S e).map (involutionCentralizer n S e).subtype := by
  rw [centralizerFullCenter_map, centerOf, BrauerWong.sylow_inf_centralizer n hn S e]

theorem wreathedSetting_solvRadIn_N_eq
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) (p f : ℕ) :
    solvRadIn (wreathedSetting n S e p f).N =
      (centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e).map
        (involutionCentralizer n S e).subtype := by
  change (CFSG.solvableRadical (involutionCentralizer n S e)).map
    (involutionCentralizer n S e).subtype = _
  rw [wreathed_solvableRadical_eq hnonab n hn S e hfour]

theorem wreathedSetting_N_solvRad
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    solvRadIn (wreathedSetting n S e p f).N =
      (wreathedSetting n S e p f).ON ⊔ centerOf ((wreathedSetting n S e p f).S : Subgroup G) := by
  rw [wreathedSetting_solvRadIn_N_eq hnonab n hn S e hfour p f, Subgroup.map_sup]
  change _ = (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊔
    centerOf (S : Subgroup G)
  rw [wreathed_centerOf_sylow n hn S e]

theorem wreathedSetting_N_coverTransfer
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (wreathedSetting n S e p f).N →
      (wreathedSetting n S e p f).L₀ ≤ K ⊔ solvRadIn (wreathedSetting n S e p f).N →
        ((wreathedSetting n S e p f).L₀ : Set G) ⊆
          (K : Set G) * (wreathedSetting n S e p f).ON := by
  intro K hKN hL₀
  obtain ⟨-, hMq, -, -⟩ := wreathed_layer_facts hnonab n hn S e hfour
  have hsolv := wreathedSetting_solvRadIn_N_eq hnonab n hn S e hfour p f
  set N := involutionCentralizer n S e
  set π := centralizerOddCoreMap n S e
  set M := CFSG.layer (centralizerOddCoreQuotient n S e)
  have hK : (K.subgroupOf N).map N.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (show K ≤ N from hKN)]
  have h1 : M.comap π ≤ K.subgroupOf N ⊔
      (centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) := by
    rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, Subgroup.map_sup, hK,
      ← hsolv]
    exact hL₀
  have hRbot : (centralizerOddCore n S e).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, centralizerOddCoreMap_ker]
  have h2 : M ≤ (K.subgroupOf N).map π ⊔ centralizerFullCenterImage n hn S e := by
    have h := Subgroup.map_mono (f := π) h1
    rwa [Subgroup.map_comap_eq_self_of_surjective (centralizerOddCoreMap_surjective n S e),
      Subgroup.map_sup, Subgroup.map_sup, hRbot, bot_sup_eq] at h
  have : Group.IsPerfect M := hMq.1
  have h3 : M ≤ (K.subgroupOf N).map π :=
    le_of_isPerfect_of_le_sup_center M _ _
      (centralizerFullCenterImage_le_center_and_factorization n hn S e).1 h2
  intro g hg
  obtain ⟨l, hl, rfl⟩ := hg
  obtain ⟨k, hk, hkl⟩ := h3 hl
  have hr : k⁻¹ * l ∈ centralizerOddCore n S e := by
    rw [← centralizerOddCoreMap_ker, MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
  exact ⟨(k : G), hk, ((k⁻¹ * l : N) : G), Subgroup.mem_map_of_mem N.subtype hr, by simp⟩

theorem wreathed_layer_le_map_of_normal
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (B : Subgroup (involutionCentralizer n S e)) [B.Normal]
    (hB : ¬ B ≤ centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤ B.map (centralizerOddCoreMap n S e) := by
  obtain ⟨hsimple, -, hC⟩ := wreathed_simpleLayer_facts hnonab n hn S e hfour
  obtain ⟨-, hMq, -, hMmap⟩ := wreathed_layer_facts hnonab n hn S e hfour
  have hBn : ((B.map (centralizerOddCoreMap n S e)).map
      (centralizerFullQuotientMap n hn S e)).Normal :=
    ((inferInstance : B.Normal).map _ (centralizerOddCoreMap_surjective n S e)).map _
      (centralizerFullQuotientMap_surjective n hn S e)
  rcases eq_bot_or_le_of_simple_selfCentralizing hC ((B.map (centralizerOddCoreMap n S e)).map
      (centralizerFullQuotientMap n hn S e)) with hbot | hLB
  · exfalso
    apply hB
    rw [Subgroup.map_eq_bot_iff, centralizerFullQuotientMap_ker,
      ← centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e,
      Subgroup.map_le_iff_le_comap, original_center_preimage n hn S e] at hbot
    exact hbot
  · rw [← hMmap, Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq,
      centralizerFullQuotientMap_ker] at hLB
    have : Group.IsPerfect (CFSG.layer (centralizerOddCoreQuotient n S e)) := hMq.1
    exact le_of_isPerfect_of_le_sup_center _ _ _
      (centralizerFullCenterImage_le_center_and_factorization n hn S e).1 hLB

theorem wreathedSetting_N_minimalNormal
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (wreathedSetting n S e p f).N →
      (wreathedSetting n S e p f).N ≤ Subgroup.normalizer (K : Set G) →
        ¬ K ≤ solvRadIn (wreathedSetting n S e p f).N →
          (wreathedSetting n S e p f).L₀ ≤ K ⊔ solvRadIn (wreathedSetting n S e p f).N := by
  intro K hKN hKnorm hKS
  have hsolv := wreathedSetting_solvRadIn_N_eq hnonab n hn S e hfour p f
  have hKN' : K ≤ involutionCentralizer n S e := hKN
  have hK : (K.subgroupOf (involutionCentralizer n S e)).map
      (involutionCentralizer n S e).subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKN']
  have : (K.subgroupOf (involutionCentralizer n S e)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN').mpr hKnorm
  have hnot : ¬ K.subgroupOf (involutionCentralizer n S e) ≤
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e := by
    intro h
    apply hKS
    rw [hsolv, ← hK]
    exact Subgroup.map_mono h
  have hM := Subgroup.comap_mono (f := centralizerOddCoreMap n S e)
    (wreathed_layer_le_map_of_normal hnonab n hn S e hfour _ hnot)
  rw [Subgroup.comap_map_eq, centralizerOddCoreMap_ker] at hM
  rw [hsolv, ← hK, ← Subgroup.map_sup]
  exact Subgroup.map_mono (hM.trans (sup_le_sup_left le_sup_left _))

theorem wreathed_odd_normalized_by_layer_eq_bot
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (Y : Subgroup (centralizerOddCoreQuotient n S e)) (hY : Odd (Nat.card Y))
    (hMY : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      Subgroup.normalizer (Y : Set (centralizerOddCoreQuotient n S e))) :
    Y = ⊥ := by
  obtain ⟨hMn, -, hMC, hMmap⟩ := wreathed_layer_facts hnonab n hn S e hfour
  obtain ⟨hsimple, -, -⟩ := wreathed_simpleLayer_facts hnonab n hn S e hfour
  have heven := centralizerSimpleLayer_even hnonab n hn S e hfour
  have htwo := centralizerFullCenterImage_isTwoGroup n hn S e
  set M := CFSG.layer (centralizerOddCoreQuotient n S e)
  set φ := centralizerFullQuotientMap n hn S e
  set L := centralizerSimpleLayer n hn S e
  have hWodd : Odd (Nat.card (Y ⊓ M : Subgroup _)) :=
    Odd.of_dvd_nat hY (Subgroup.card_dvd_of_le inf_le_left)
  have hMW : M ≤ Subgroup.normalizer ((Y ⊓ M : Subgroup _) : Set _) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hMY hm, Subgroup.le_normalizer hm⟩
  have hle : (Y ⊓ M).map φ ≤ L := hMmap ▸ Subgroup.map_mono inf_le_right
  have hLW : L ≤ Subgroup.normalizer (((Y ⊓ M).map φ : Subgroup _) : Set _) :=
    hMmap ▸ (Subgroup.map_mono hMW).trans (Subgroup.le_normalizer_map φ)
  have hnormal : (((Y ⊓ M).map φ).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hLW
  have hW : Y ⊓ M ≤ centralizerFullCenterImage n hn S e := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Y ⊓ M).map φ).subgroupOf L) with
      hb | ht
    · have hbot : (Y ⊓ M).map φ = ⊥ := by
        have hdisj := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
        rwa [inf_eq_left.mpr hle] at hdisj
      rw [Subgroup.map_eq_bot_iff, centralizerFullQuotientMap_ker] at hbot
      exact hbot
    · exfalso
      have hLle : L ≤ (Y ⊓ M).map φ := Subgroup.subgroupOf_eq_top.mp ht
      have hdvd : Nat.card L ∣ Nat.card (Y ⊓ M : Subgroup _) :=
        (Subgroup.card_dvd_of_le hLle).trans (Subgroup.card_map_dvd _ _)
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hWodd hdvd)) heven
  have hWbot : Y ⊓ M = ⊥ := eq_bot_of_odd_of_le_two_group hW htwo hWodd
  have hcomm : ⁅Y, M⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_le_inf_of_le_normalizer Y M hMY).trans hWbot.le)
  have hYC : Y ≤ Subgroup.centralizer (M : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rw [hMC] at hYC
  exact eq_bot_of_odd_of_le_two_group hYC htwo hY

theorem wreathedSetting_N_oddCore_of_cover
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (wreathedSetting n S e p f).N →
      ((wreathedSetting n S e p f).L₀ : Set G) ⊆ (K : Set G) * (wreathedSetting n S e p f).ON →
        oddCoreIn K ≤ (wreathedSetting n S e p f).ON := by
  intro K hKN hcov
  set N := involutionCentralizer n S e
  set π := centralizerOddCoreMap n S e
  set M := CFSG.layer (centralizerOddCoreQuotient n S e)
  have hXN : oddCoreIn K ≤ N := (oddCoreIn_le K).trans hKN
  have hX : ((oddCoreIn K).subgroupOf N).map N.subtype = oddCoreIn K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXN]
  have hXodd : Odd (Nat.card ((oddCoreIn K).subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv]
    exact odd_card_oddCoreIn K
  have hMK : M ≤ (K.subgroupOf N).map π := by
    intro m hm
    obtain ⟨l, rfl⟩ := centralizerOddCoreMap_surjective n S e m
    have hl : (l : G) ∈ (wreathedSetting n S e p f).L₀ := ⟨l, hm, rfl⟩
    obtain ⟨k, hk, o, ho, hko⟩ := hcov hl
    have ho2 : o ∈ (centralizerOddCore n S e).map N.subtype := ho
    obtain ⟨o', ho', rfl⟩ := ho2
    have hko' : k = (l : G) * (o' : G)⁻¹ := by
      rw [← hko]
      simp
    have hkN : k ∈ N := hko' ▸ N.mul_mem l.property (N.inv_mem o'.property)
    refine ⟨⟨k, hkN⟩, hk, ?_⟩
    have hkl : (⟨k, hkN⟩ : N) = l * o'⁻¹ := Subtype.ext hko'
    have ho'1 : π o' = 1 :=
      MonoidHom.mem_ker.mp (by rw [centralizerOddCoreMap_ker]; exact ho')
    rw [hkl, map_mul, map_inv, ho'1, inv_one, mul_one]
  have hnorm : M ≤ Subgroup.normalizer
      ((((oddCoreIn K).subgroupOf N).map π : Subgroup _) : Set _) := by
    refine hMK.trans ((Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π))
    rw [← Subgroup.subgroupOf_normalizer_eq hXN]
    exact fun x hx => le_normalizer_oddCoreIn K hx
  have hY := wreathed_odd_normalized_by_layer_eq_bot hnonab n hn S e hfour _
    (Odd.of_dvd_nat hXodd (Subgroup.card_map_dvd _ _)) hnorm
  rw [Subgroup.map_eq_bot_iff, centralizerOddCoreMap_ker] at hY
  rw [← hX]
  exact Subgroup.map_mono hY

theorem wreath_mem_base_sup_Y (m : ℕ) (g : Wreath m) : g ∈ baseSubgroup m ⊔ Original.Y m := by
  obtain ⟨⟨a, b, c⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b c ∈ _
  rcases swap_exponent_cases c with rfl | rfl
  · exact Subgroup.mem_sup_left ((element_mem_base m a b 0).mpr rfl)
  · have hd : Original.d m ∈ Original.Y m := Subgroup.subset_closure (by simp)
    have h : element m a b 1 = element m (a - ((m / 2 : ℕ) : ZMod m)) b 0 * Original.d m := by
      rw [Original.d_eq, element_base_mul, sub_add_cancel, add_zero]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((element_mem_base m _ _ 0).mpr rfl))
      (Subgroup.mem_sup_right hd)

omit [Finite G] in
theorem sylow_eq_modelBase_sup_modelY {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (S : Subgroup G) = modelBase S e ⊔ modelY S e := by
  apply le_antisymm
  · rw [← wreathModelHom_range S e, MonoidHom.range_eq_map]
    refine (Subgroup.map_mono (fun g _ => wreath_mem_base_sup_Y m g)).trans ?_
    rw [Subgroup.map_sup]
    exact le_rfl
  · exact sup_le (modelBase_le_sylow S e) (modelY_le_sylow S e)

theorem modelY_le_wreathedSetting_L₀
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) (p f : ℕ) :
    modelY S e ≤ (wreathedSetting n S e p f).L₀ := by
  rw [← centralizerQuaternion_map n hn S e]
  exact Subgroup.map_mono (Subgroup.map_le_iff_le_comap.mp
    (original_quaternion_image_le_layer hnonab n hn S e hfour))

theorem wreathedSetting_L_eq
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).L = (wreathedSetting n S e p f).L₀ ⊔
      ((wreathedSetting n S e p f).D ⊓
        Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G)) := by
  rw [wreathedSetting_D_eq n (by omega) S e p f, wreathedSetting_T_eq n (by omega) S e p f]
  change (wreathedSetting n S e p f).L₀ ⊔ (S : Subgroup G) = _
  apply le_antisymm
  · refine sup_le le_sup_left ((le_of_eq (sylow_eq_modelBase_sup_modelY S e)).trans ?_)
    refine sup_le ?_ ?_
    · exact le_sup_of_le_right (le_inf (modelBase_le_sylow S e)
        (modelBase_le_modelTCentralizer n (by omega) S e))
    · exact le_sup_of_le_left (modelY_le_wreathedSetting_L₀ hnonab n hn S e hfour p f)
  · exact sup_le_sup_left inf_le_left _

omit [Finite G] in
theorem wreathedSetting_sylow_eq_of_D_le (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (S₁ : Sylow 2 G)
    (hS₁ : (wreathedSetting n S e p f).D ≤ (S₁ : Subgroup G)) :
    (S₁ : Subgroup G) = S := by
  rw [wreathedSetting_D_eq n hn S e p f] at hS₁
  exact S.is_maximal' S₁.isPGroup' hS₁

omit [Finite G] in
theorem wreathed_x_center_involution (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ centerOf (S : Subgroup G) ∧
      ∀ z ∈ centerOf (S : Subgroup G), orderOf z = 2 →
        z = wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [centerOf, BrauerWong.sylow_inf_centralizer n hn S e]
  refine ⟨Subgroup.mem_map.mpr ⟨Original.x _,
    (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩, ?_⟩
  intro z hz hz2
  rw [BrauerWong.modelCenter_eq_zpowers] at hz
  have hA : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).generator_orders.2.2.1
  rw [AdaptedBaseFusion.eq_pow_half_of_mem_zpowers (by omega) hA hz hz2, ← map_pow,
    ← BrauerWong.WreathGenerators.half_eq (by omega)]
  rfl

theorem wreathedSetting_center_S_eq_center_D [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (_hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    centerOf ((wreathedSetting n S e p f).S : Subgroup G) =
      centerOf (wreathedSetting n S e p f).D := by
  rw [wreathedSetting_D_eq n (by omega) S e p f]
  rfl

theorem wreathedSetting_center_involution_of_sylow [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (_hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ S₁ : Sylow 2 G, (wreathedSetting n S e p f).D ≤ (S₁ : Subgroup G) →
      (wreathedSetting n S e p f).x ∈ centerOf (S₁ : Subgroup G) ∧
        ∀ z ∈ centerOf (S₁ : Subgroup G), orderOf z = 2 → z = (wreathedSetting n S e p f).x := by
  intro S₁ hS₁
  rw [wreathedSetting_sylow_eq_of_D_le n (by omega) S e p f S₁ hS₁]
  exact wreathed_x_center_involution n hn S e

theorem wreathedSetting_normal_le_center_of_inf_D [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (_hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ S₁ : Sylow 2 G, (wreathedSetting n S e p f).D ≤ (S₁ : Subgroup G) → ∀ X : Subgroup G,
      X ≤ S₁ → (S₁ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        X ⊓ (wreathedSetting n S e p f).D ≤ centerOf (wreathedSetting n S e p f).D →
          X ≤ centerOf (S₁ : Subgroup G) := by
  intro S₁ hS₁ X hX _ hXD
  rw [wreathedSetting_sylow_eq_of_D_le n (by omega) S e p f S₁ hS₁] at hX ⊢
  rw [wreathedSetting_D_eq n (by omega) S e p f, inf_eq_left.mpr hX] at hXD
  exact hXD

theorem wreathedSetting_automizer_T [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (_hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    automizerIndex (wreathedSetting n S e p f).T = 6 := by
  rw [wreathedSetting_T_eq n (by omega) S e p f]
  obtain ⟨e3⟩ := modelBaseNormalizerQuotient_sym3_of_simple hnonab n hn S e
  change Nat.card (Subgroup.normalizer (modelT n S e : Set G) ⧸
    (Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
      (Subgroup.normalizer (modelT n S e : Set G))) = 6
  rw [Nat.card_congr ((originalFourToBaseNormalizerQuotientEquiv n hn S e).trans e3).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

end CFSG.Wreathed.OriginalAllPrime
