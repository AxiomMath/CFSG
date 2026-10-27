module

public import CFSG.Quasithin.H13.A5S1515a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1514

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem UH_le_L1_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) : conjClosure S.V3 H ≤ S.L1 := by
  have h1 := S.commutator_UH_L1 hH hn
  refine (S.lemma_13_5_14_one_F4 h1323 hH ?_).2
  rw [h1]
  exact sup_eq_left.mpr (S.V1_le_V3.trans (le_conjClosure _ _))

theorem G248_data_F4 (h1323 : Input1323Two_F4) (hG248 : StmtG248) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (S.V1 : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l = L ∧ IsShort2 L ∧ IsAltType L 5 ∧
      pCoreOf 2 L = V ∧ conjClosure S.V3 H = pCoreOf 2 S.L1 ∧
      IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hU : ⁅conjClosure S.V3 H, lOne L S.V1⁆ ⊔ S.V1 = conjClosure S.V3 H := by
    rw [lOne_eq_L₁Of]
    show ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 = conjClosure S.V3 H
    rw [S.commutator_UH_L1 hH hn]
    exact sup_eq_left.mpr (S.V1_le_V3.trans (le_conjClosure _ _))
  have hO : pCoreOf 2 (lOne L S.V1) ≤ pCoreOf 2 H := by
    rw [lOne_eq_L₁Of]
    exact S.pCoreOf_L1_le hH hn
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    hG248 G S.V3 S.V1 L T H (S.almostSpecialA5Hyp_F4 h1323 hH hna) hU hO l hl hlN
  refine ⟨c1, c2, c3, c4.trans S.conjClosure_V1_L, ?_, c6⟩
  rw [c5, lOne_eq_L₁Of]
  rfl

theorem not_V_le_QH_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : ¬ V ≤ pCoreOf 2 H := fun h =>
  hna (((S.tfae_13_5_10_F4 h1323 hH).out 1 2).1 h)

theorem F956_data_F4 (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    ∃ h ∈ H, IsQ8Sq ↥(S.V3 ⊔ conjSub h⁻¹ S.V3) ∧
      (∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
        Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
          Equiv.Perm (Fin 3))) ∧
      (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = S.V3 ⊔ conjSub h⁻¹ S.V3 := by
  have hF := S.hypF91_F4 h1323 hH
  have hV := S.not_V_le_QH_F4 h1323 hH hna
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 hV
  obtain ⟨g, hgH, y, hy, hyQ⟩ :=
    exists_not_isPGroup_mod_of_not_mem (hF.V_le_H hvV) (S.elemAbelian_V.2 v hvV) hvQ

  have hcl : Subgroup.closure ({v, g * v * g⁻¹} : Set G) ≤ V ⊔ conjSub (g⁻¹)⁻¹ V := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left hvV
    · refine Subgroup.mem_sup_right ?_
      rw [inv_inv, mem_conjSub]
      simpa [mul_assoc] using hvV
  have hI : ¬ (∀ x ∈ V ⊔ conjSub (g⁻¹)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) := by
    intro hall
    obtain ⟨n, hn⟩ := hall y (hcl hy)
    exact hyQ n hn
  have hcard : Nat.card V = 2 ^ 4 := S.card_V.trans (by norm_num)
  obtain ⟨hQ8, hS3⟩ := hF956 G T V L S.V1 S.V3 H hF S.relIndex_V3 hV
    (fun g hg hlt => S.isPGroup_sup_of_lt_F4 h1323 h1326 h1336 hH hg hlt) (S.hyp_F956_F4 h1323 H)
    hcard g⁻¹ (H.inv_mem hgH) hI
  exact ⟨g⁻¹, H.inv_mem hgH, hQ8, hS3, hF.F95_UI_eq S.relIndex_V3 hV (H.inv_mem hgH)⟩

theorem I_data_F4 (h1323 : Input1323Two_F4) (hG248 : StmtG248) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {h : G} (hh : h ∈ H)
    (hQ8 : IsQ8Sq ↥(S.V3 ⊔ conjSub h⁻¹ S.V3))
    (hS3 : ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
      Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
        Equiv.Perm (Fin 3)))
    (hUI : (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = S.V3 ⊔ conjSub h⁻¹ S.V3) :
    S.V3 ⊔ conjSub h⁻¹ S.V3 = conjClosure S.V3 H ∧
      pCoreOf 2 (V ⊔ conjSub h⁻¹ V) = conjClosure S.V3 H ∧
      Nat.card (pCoreOf 2 (V ⊔ conjSub h⁻¹ V)) = 32 ∧
      Nonempty (oTwoQuot ↥(V ⊔ conjSub h⁻¹ V) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := V ⊔ conjSub h⁻¹ V with hIdef
  obtain ⟨l, hl, hlN⟩ := S.exists_L_not_normalizer_V1
  obtain ⟨-, -, -, -, -, hUQ8⟩ := S.G248_data_F4 h1323 hG248 hH hn hna hl hlN

  have hUIeq : S.V3 ⊔ conjSub h⁻¹ S.V3 = conjClosure S.V3 H :=
    Subgroup.eq_of_le_of_card_ge (S.UI_le_UH hh) (by rw [hQ8.1, hUQ8.1])
  have hF := S.hypF91_F4 h1323 hH
  have hIH : I ≤ H := sup_le hF.V_le_H (hF.conjSub_inv_le_H hh)

  have hO2 : pCoreOf 2 I = I ⊓ pCoreOf 2 H := by
    apply le_antisymm
    ·
      obtain ⟨hNorm, ⟨e⟩⟩ := hS3
      have hP :
          (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) = ⊥ := by
        have hnorm : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).Normal :=
          Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _
            (QuotientGroup.mk'_surjective _)
        have hpg : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))) :=
          (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
        have h1 : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom = ⊥ := by
          have : ((((CFSG.Open.pCore 2 ↥I).map
              (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom)).Normal :=
            Subgroup.Normal.map hnorm _ e.surjective
          exact perm3_normal_pgroup_eq_bot _ (hpg.map _)
        rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
        exact h1
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hx1 : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x = 1 := by
        have : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x ∈
            (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) :=
          ⟨x, hx, rfl⟩
        rw [hP, Subgroup.mem_bot] at this
        exact this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx1
      exact hx1
    · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxI, hxQ⟩
        exact ⟨I.mul_mem (I.mul_mem hy hxI) (I.inv_mem hy),
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mp hxQ⟩
      · rintro ⟨hxI, hxQ⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mpr
          hxQ⟩
        have := I.mul_mem (I.mul_mem (I.inv_mem hy) hxI) hy
        simpa [mul_assoc] using this
  have hO2' : pCoreOf 2 I = conjClosure S.V3 H := by rw [hO2, hUI, hUIeq]
  refine ⟨hUIeq, hO2', by rw [hO2', hUQ8.1], ?_⟩

  obtain ⟨hNorm, ⟨e⟩⟩ := hS3
  have hsub : CFSG.Open.pCore 2 ↥I = (pCoreOf 2 H).subgroupOf I := by
    have h1 : (pCoreOf 2 I).subgroupOf I = CFSG.Open.pCore 2 ↥I := by
      show ((CFSG.Open.pCore 2 ↥I).map I.subtype).subgroupOf I = _
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
    rw [← h1, hO2]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hsub).trans e⟩

end Setting

end CFSG.Quasithin.H13.A5
