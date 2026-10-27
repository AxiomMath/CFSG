module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

theorem centralizes_fstar_aux_isSubnormal_map {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z)
    {A B : Subgroup Y} (h : CFSG.Open.IsSubnormal A B) :
    CFSG.Open.IsSubnormal (A.map π) (B.map π) := by
  induction h with
  | refl H => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hHM hnorm hMK ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_mono hHM) ?_ ih
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n₀, hn₀, hnn₀⟩ := hn
    obtain ⟨g₀, hg₀, hgg₀⟩ := g.2
    have h1 := hnorm.conj_mem ⟨n₀, hHM hn₀⟩ hn₀ ⟨g₀, hg₀⟩
    refine ⟨g₀ * n₀ * g₀⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hnn₀, hgg₀]
    rfl

theorem centralizes_fstar_aux_component_map {Y : Type} [Group Y] (Chat : Subgroup Y)
    {K : Subgroup ↥Chat} (hK : CFSG.IsComponent K) :
    CFSG.Open.IsComponentOf (K.map Chat.subtype) Chat := by
  obtain ⟨-, hsub, hq⟩ := (CFSG.isComponent_iff_open K).1 hK
  refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
  · have := centralizes_fstar_aux_isSubnormal_map Chat.subtype hsub
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (K.equivMapOfInjective Chat.subtype Chat.subtype_injective).symm hq

theorem centralizes_fstar_aux_layer_le {Y : Type} [Group Y] (Chat : Subgroup Y) :
    (CFSG.layer ↥Chat).map Chat.subtype ≤ layerIn Chat := by
  rw [CFSG.layer.eq_sSup, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (centralizes_fstar_aux_component_map Chat hK)

theorem centralizes_fstar_aux_pCoreOf_two {Y : Type} [Group Y] [Finite Y]
    (hO2 : CFSG.pCore 2 Y = ⊥) (Chat : Subgroup Y) [Chat.Normal] :
    CFSG.Open.pCoreOf 2 Chat = ⊥ := by
  have h1 : CFSG.Open.pCoreOf 2 Chat ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨pCoreOf_normal 2 Chat, pCoreOf_isPGroup 2 Nat.prime_two Chat⟩
  rw [hO2] at h1
  exact le_bot_iff.1 h1

theorem centralizes_fstar {Y : Type} [Group Y] [Finite Y] (hO2 : CFSG.pCore 2 Y = ⊥)
    (Chat : Subgroup Y) [Chat.Normal] (V : Subgroup Y)
    (hlayer : V ≤ Subgroup.centralizer (layerIn Chat : Set Y))
    (hloc : ∀ r : ℕ, r.Prime → r ≠ 2 →
      V ≤ Subgroup.centralizer (CFSG.Open.pCoreOf r Chat : Set Y)) :
    V ≤ Subgroup.centralizer (fstarIn Chat : Set Y) := by
  rw [Subgroup.le_centralizer_iff]
  unfold fstarIn
  rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    by_cases h2 : p.1.1 = 2
    · have h3 : (CFSG.pCore p.1.1 ↥Chat).map Chat.subtype = ⊥ := by
        rw [h2]
        exact centralizes_fstar_aux_pCoreOf_two hO2 Chat
      rw [h3]
      exact bot_le
    · exact Subgroup.le_centralizer_iff.1
        (hloc p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) h2)
  · exact (centralizes_fstar_aux_layer_le Chat).trans (Subgroup.le_centralizer_iff.1 hlayer)

theorem isComponent_of_centralizes_fstar_aux_normal {Y : Type} [Group Y] (Chat : Subgroup Y)
    [Chat.Normal] : (fstarIn Chat).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h1 := Subgroup.characteristic_iff_map_eq.1
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥Chat)).1
    (MulAut.conjNormal (H := Chat) g)
  have h2 : (MulAut.conjNormal (H := Chat) g) a ∈ CFSG.generalizedFitting ↥Chat := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ ha
  exact ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩

theorem isComponent_of_centralizes_fstar_aux_selfCentralizing {Y : Type} [Group Y] [Finite Y]
    (Chat : Subgroup Y) {x : Y} (hx : x ∈ Chat)
    (hc : x ∈ Subgroup.centralizer (fstarIn Chat : Set Y)) : x ∈ fstarIn Chat := by
  have h1 : (⟨x, hx⟩ : ↥Chat) ∈
      Subgroup.centralizer (CFSG.generalizedFitting ↥Chat : Set ↥Chat) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hc) (a : Y) ⟨a, ha, rfl⟩
  exact ⟨_, CFSG.centralizer_generalizedFitting_le ↥Chat h1, rfl⟩

theorem isComponent_of_centralizes_fstar_aux_threeSubgroups {Y : Type} [Group Y]
    (V N : Subgroup Y) (hV : ⁅V, V⁆ = V)
    (hVN : ⁅V, N⁆ ≤ Subgroup.centralizer (V : Set Y)) :
    N ≤ Subgroup.centralizer (V : Set Y) := by
  have h1 : ⁅⁅V, N⁆, V⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hVN
  have h2 : ⁅⁅N, V⁆, V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm N V]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hV] at h3
  exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)

theorem isComponent_of_centralizes_fstar_aux_commutator_le {Y Z : Type} [Group Y] [Group Z]
    (π : Y →* Z) (Ls : Subgroup Z) (V : Subgroup Y) (hVs : V.map π = Ls) :
    ⁅V, zPre π Ls V⁆ ≤ V ⊓ π.ker := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨hbV, c, hc, hcb⟩ := hb
  have haL : π a ∈ Ls := by
    rw [← hVs]
    exact Subgroup.mem_map_of_mem π ha
  refine ⟨V.mul_mem (V.mul_mem (V.mul_mem ha hbV) (V.inv_mem ha)) (V.inv_mem hbV), ?_⟩
  change π ⁅a, b⁆ = 1
  rw [map_commutatorElement]
  have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨π a, haL⟩)
  change π a * (c : Z) = (c : Z) * π a at h1
  have h2 : (c : Z) = π b := hcb
  rw [h2] at h1
  exact commutatorElement_eq_one_iff_mul_comm.2 h1

theorem isComponent_of_centralizes_fstar_aux_inf_le {Y : Type} [Group Y] [Finite Y]
    (Chat V : Subgroup Y) (hcent : V ≤ Subgroup.centralizer (fstarIn Chat : Set Y)) :
    V ⊓ Chat ≤ Subgroup.centralizer (V : Set Y) := by
  intro x hx
  have hxF : x ∈ fstarIn Chat :=
    isComponent_of_centralizes_fstar_aux_selfCentralizing Chat hx.2 (hcent hx.1)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.1 (hcent hv)) x hxF).symm

theorem isComponent_of_centralizes_fstar_aux_center {Y Z : Type} [Group Y] [Group Z]
    (π : Y →* Z) (Ls : Subgroup Z) (V : Subgroup Y) (hVs : V.map π = Ls)
    (hZ : zPre π Ls V ≤ Subgroup.centralizer (V : Set Y)) :
    Subgroup.center ↥V = (zPre π Ls V).subgroupOf V := by
  ext z
  constructor
  · intro hz
    have hzL : π z.1 ∈ Ls := by
      rw [← hVs]
      exact Subgroup.mem_map_of_mem π z.2
    refine ⟨z.2, ⟨π z.1, hzL⟩, ?_, rfl⟩
    show (⟨π z.1, hzL⟩ : ↥Ls) ∈ Subgroup.center ↥Ls
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨v, hv, hvl⟩ : (l : Z) ∈ V.map π := by
      rw [hVs]
      exact l.2
    apply Subtype.ext
    have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨v, hv⟩)
    change v * z.1 = z.1 * v at h1
    change (l : Z) * π z.1 = π z.1 * (l : Z)
    rw [← hvl, ← map_mul, ← map_mul, h1]
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hZ (show z.1 ∈ zPre π Ls V from hz))) g.1 g.2

theorem isComponent_of_centralizes_fstar_aux_quasisimple {Y Z : Type} [Group Y] [Group Z]
    (π : Y →* Z) (Ls : Subgroup Z) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (V : Subgroup Y)
    (hVs : V.map π = Ls) (hV : ⁅V, V⁆ = V)
    (hZ : zPre π Ls V ≤ Subgroup.centralizer (V : Set Y)) :
    CFSG.Open.IsQuasisimple ↥V := by
  refine ⟨?_, ?_⟩
  · have h1 : ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
      apply Subgroup.map_injective V.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hV]
    rw [commutator_def]
    exact h1
  · haveI : ((zPre π Ls V).subgroupOf V).Normal := zPre_normal π Ls V hVs.le
    obtain ⟨e⟩ := zPre_equiv π Ls V hVs
    haveI : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq
      (isComponent_of_centralizes_fstar_aux_center π Ls V hVs hZ)).trans e).isSimpleGroup

theorem isComponent_of_centralizes_fstar_aux_subnormal {Y : Type} [Group Y] [Finite Y]
    (Chat V : Subgroup Y) [Chat.Normal] (hsub : CFSG.Open.IsSubnormal (V ⊔ Chat) ⊤)
    (hcent : V ≤ Subgroup.centralizer (fstarIn Chat : Set Y)) :
    CFSG.Open.IsSubnormal V ⊤ := by
  haveI : (fstarIn Chat).Normal := isComponent_of_centralizes_fstar_aux_normal Chat
  set W : Subgroup Y := (V ⊔ Chat) ⊓ Subgroup.centralizer (fstarIn Chat : Set Y) with hW
  have hVW : V ≤ W := le_inf le_sup_left hcent
  have hWH : W ≤ V ⊔ Chat := inf_le_left
  have hVWn : (V.subgroupOf W).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup_of_normal_right.1 g.2.1
    have hcF : c ∈ fstarIn Chat := by
      apply isComponent_of_centralizes_fstar_aux_selfCentralizing Chat hc
      have hc' : c = a⁻¹ * g.1 := by
        rw [← hac]
        group
      rw [hc']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hcent ha)) g.2.2
    have hn' : (n : Y) ∈ V := hn
    have hcomm : c * n.1 = n.1 * c := (Subgroup.mem_centralizer_iff.1 (hcent hn')) c hcF
    change g.1 * n.1 * g.1⁻¹ ∈ V
    rw [← hac]
    have h2 : a * c * n.1 * (a * c)⁻¹ = a * n.1 * a⁻¹ := by
      calc a * c * n.1 * (a * c)⁻¹ = a * (c * n.1) * c⁻¹ * a⁻¹ := by group
        _ = a * (n.1 * c) * c⁻¹ * a⁻¹ := by rw [hcomm]
        _ = a * n.1 * a⁻¹ := by group
    rw [h2]
    exact V.mul_mem (V.mul_mem ha hn') (V.inv_mem ha)
  have hWHn : (W.subgroupOf (V ⊔ Chat)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact ⟨(V ⊔ Chat).mul_mem ((V ⊔ Chat).mul_mem g.2 n.2) ((V ⊔ Chat).inv_mem g.2),
      centralizer_conj_mem (fstarIn Chat) hn.2⟩
  exact CFSG.Open.IsSubnormal.step hVW hVWn (CFSG.Open.IsSubnormal.step hWH hWHn hsub)

theorem isComponent_of_centralizes_fstar {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (Ls : Subgroup Z) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (V : Subgroup Y) (hVs : V.map π = Ls)
    (hV : ⁅V, V⁆ = V) (hsub : CFSG.Open.IsSubnormal (V ⊔ π.ker) ⊤)
    (hcent : V ≤ Subgroup.centralizer (fstarIn π.ker : Set Y)) :
    CFSG.Open.IsComponentOf V ⊤ := by
  haveI : (π.ker).Normal := MonoidHom.normal_ker π
  have hZ : zPre π Ls V ≤ Subgroup.centralizer (V : Set Y) := by
    refine isComponent_of_centralizes_fstar_aux_threeSubgroups V _ hV ?_
    exact (isComponent_of_centralizes_fstar_aux_commutator_le π Ls V hVs).trans
      (isComponent_of_centralizes_fstar_aux_inf_le π.ker V hcent)
  exact ⟨le_top, isComponent_of_centralizes_fstar_aux_subnormal π.ker V hsub hcent,
    isComponent_of_centralizes_fstar_aux_quasisimple π Ls hLs V hVs hV hZ⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
