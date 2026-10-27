module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC0
public import CFSG.CGT.PushingUpLit.SolKNA.FinalCaseB

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.Assembly (pCoreOf)

open CFSG.ComponentClassification.AS76b (oUpperTwoPrime)

open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate rightConjugate_card
  mem_rightConjugate_iff)

open CFSG.Open (IsElemAbelian)

open CFSG.RankThree.GF2n (mem_normalizer_inf)

open CFSG.ComponentClassification.LiteratureLocal.TightCommuting (rightConjugate_mono)

variable {G : Type} [Group G]

theorem isSylowOf_self {P : Subgroup G} (h2 : IsPGroup 2 P) : IsSylowOf 2 P P :=
  exists_sylow_sylowImg_eq h2

theorem oUpperTwoPrime_eq_of_isPGroup {P : Subgroup G} (h2 : IsPGroup 2 P) :
    oUpperTwoPrime P = P := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  · intro x hx
    exact Subgroup.subset_closure ⟨hx, exists_pow_two_pow_eq_one h2 hx⟩

theorem le_of_isSylowOf_of_normal {P T X : Subgroup G} (hT : IsSylowOf 2 T P) (hXP : X ≤ P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hX2 : IsPGroup 2 X) : X ≤ T := by
  obtain ⟨Q, hQ⟩ := hT
  have hn : (X.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr hPX
  have hp : IsPGroup 2 (X.subgroupOf P) := hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
  have hle : X.subgroupOf P ≤ (Q : Subgroup ↥P) := hp.le_sylow_of_normal Q
  rw [← hQ, ← Subgroup.map_subgroupOf_eq_of_le hXP]
  exact Subgroup.map_mono hle

theorem mem_normalizer_rightConjugate' {K : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer ((rightConjugate K g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
  have h : rightConjugate K g = conjSubgroup g⁻¹ K := rfl
  rw [h, ← conjSubgroup_normalizer, mem_conjSubgroup]
  simp

theorem isElemAbelian_mono {T X : Subgroup G} (h : IsElemAbelian 2 T) (hXT : X ≤ T) :
    IsElemAbelian 2 X := CFSG.Open.IsElemAbelian.mono h hXT

theorem card_le_two_mul_inf [Finite G] {A B T : Subgroup G} (hB : A.relIndex B = 2) (hTB : T ≤ B) :
    Nat.card ↥T ≤ 2 * Nat.card ↥(A ⊓ T) := by
  have h1 : A.relIndex T ≤ A.relIndex B :=
    Subgroup.relIndex_le_of_le_right hTB (by rw [hB]; norm_num)
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := T)
  rw [hB] at h1
  calc Nat.card ↥T = A.relIndex T * Nat.card ↥(A ⊓ T) := h2.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ T) := Nat.mul_le_mul_right _ h1

section Rev

structure RevPair (H : Subgroup G) (g : G) : Prop where
  normal : ∀ x ∈ H ⊔ rightConjugate H g, x ∈ Subgroup.normalizer
    (((H ⊓ Subgroup.normalizer (rightConjugate H g : Set G)) ⊔
      (rightConjugate H g ⊓ Subgroup.normalizer (H : Set G)) : Subgroup G) : Set G)
  frattini_le : (frattini ↥(rightConjugate H g)).map (rightConjugate H g).subtype ≤
    rightConjugate H g ⊓ Subgroup.normalizer (H : Set G)
  le_center : rightConjugate H g ⊓ Subgroup.normalizer (H : Set G) ≤
    rightConjugate H g ⊓ Subgroup.centralizer ((rightConjugate H g : Subgroup G) : Set G)

end Rev

namespace II5

variable [Finite G] {K R T H : Subgroup G} {g : G}

theorem isPGroup (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) : IsPGroup 2 H :=
  cfg.sylowR.isPGroup.to_le h5.H_le

theorem le_K (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) : H ≤ K :=
  h5.H_le.trans cfg.R_le_K

theorem K_le_normalizer (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) :
    K ≤ Subgroup.normalizer (H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_K cfg h5)).mp h5.normal

omit [Finite G] in
theorem card_N (h5 : CaseII5 K R T H) :
    Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T := by
  obtain ⟨e⟩ := h5.iso
  exact Nat.card_congr e.toEquiv

omit [Finite G] in
theorem ne_bot (h5 : CaseII5 K R T H) : H ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥H = 1 := by rw [hbot]; exact Subgroup.card_bot
  have h4 := h5.four_le
  have h2 := h5.card_H
  rw [h1] at h2
  nlinarith

theorem normalizer_eq (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    Subgroup.normalizer (H : Set G) = Subgroup.normalizer (K : Set G) :=
  normalizer_eq_of_normal cfg.stSetting (isPGroup cfg h5) (ne_bot h5) hHM

theorem le_pCoreOf (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) :
    H ≤ pCoreOf 2 K :=
  le_pCoreOf_of_normal (le_K cfg h5) (isPGroup cfg h5) (K_le_normalizer cfg h5)

theorem stSetting (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    STSetting G H :=
  STSetting.of_normal cfg.stSetting (isPGroup cfg h5) (ne_bot h5) (le_pCoreOf cfg h5) hHM

theorem isTI (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) : IsTI H :=
  isTI_of_normal_le_pCoreOf cfg.stSetting.tight (le_pCoreOf cfg h5) hHM

omit [Finite G] in
theorem not_elemAbelian (h5 : CaseII5 K R T H) : ¬ IsElemAbelian 2 H := by
  intro hel
  have hHN : H ≤ R ⊓ Subgroup.normalizer (T : Set G) := fun x hx => h5.omega_le x hx (hel.2 x hx)
  have heq : H = R ⊓ Subgroup.normalizer (T : Set G) := le_antisymm hHN h5.N_le
  have h1 : Nat.card ↥H = Nat.card ↥T := by rw [heq]; exact card_N h5
  have h4 := h5.four_le
  have h2 := h5.card_H
  rw [h1] at h2
  nlinarith

end II5

namespace II5

variable [Finite G] {K R T H : Subgroup G} {g : G}

abbrev TH (H : Subgroup G) (g : G) : Subgroup G :=
  rightConjugate H g ⊓ Subgroup.normalizer (H : Set G)

theorem isPGroup_TH (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) : IsPGroup 2 (TH H g) :=
  ((isPGroup cfg h5).map (MulAut.conj g⁻¹).toMonoidHom).to_le inf_le_left

theorem TH_le_T (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) : TH H g ≤ T := by
  have hHN := normalizer_eq cfg h5 hHM
  have hHK := le_K cfg h5
  have hKH := K_le_normalizer cfg h5
  have hJn : rightConjugate K g ≤ Subgroup.normalizer (rightConjugate H g : Set G) :=
    fun x hx => mem_normalizer_rightConjugate'.mpr (hKH ((mem_rightConjugate_iff K g x).mp hx))
  have hPn : rightConjugate K g ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((TH H g : Subgroup G) : Set G) := fun x hx => by
    obtain ⟨hxJ, hxM⟩ := Subgroup.mem_inf.mp hx
    refine mem_normalizer_inf (hJn hxJ) ?_
    rw [hHN]
    exact Subgroup.le_normalizer hxM
  have hTHP : TH H g ≤ rightConjugate K g ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (inf_le_left.trans (rightConjugate_mono g hHK)) (by rw [← hHN]; exact inf_le_right)
  exact le_of_isSylowOf_of_normal cfg.sylowT hTHP hPn (isPGroup_TH cfg h5)

theorem card_T_le_two_mul_TH (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥T ≤ 2 * Nat.card ↥(TH H g) := by
  have hHN := normalizer_eq cfg h5 hHM
  have hrel : (rightConjugate H g).relIndex (rightConjugate R g) = 2 := by
    rw [← h5.relIndex_two]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective
  have h1 := card_le_two_mul_inf hrel cfg.T_le
  have h2 : rightConjugate H g ⊓ T ≤ TH H g :=
    inf_le_inf_left _ (cfg.T_le_normalizer.trans hHN.ge)
  exact h1.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le h2))

theorem TH_ne_bot (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) : TH H g ≠ ⊥ := by
  intro hbot
  have h1 := card_T_le_two_mul_TH cfg h5 hHM
  have h4 := h5.four_le
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem card_TH_lt (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(TH H g) < Nat.card ↥H := by
  have h1 := Subgroup.card_le_of_le (TH_le_T cfg h5 hHM)
  have h4 := h5.four_le
  rw [h5.card_H]
  nlinarith

omit [Finite G] in
theorem two_le_pRank [Finite G] (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) :
    2 ≤ CFSG.Open.pRank 2 H := by
  have hN2 : IsPGroup 2 ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
    (isPGroup cfg h5).to_le h5.N_le
  obtain ⟨V, hVN, hV, hV4⟩ := exists_fourGroup_of_card hN2
    (fun x hx y hy => h5.N_central x hx y (h5.N_le hy)) h5.elem_N (by
      rw [card_N h5]; exact h5.four_le)
  have := CFSG.ComponentClassification.Asc76X.one_lt_pRank_of_fourGroup (hVN.trans h5.N_le) hV hV4
  omega

theorem cfgH (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hnc : ¬ IsCommSubgroup H) : NAConfig G H H (TH H g) g where
  stSetting := stSetting cfg h5 hHM
  perfect := oUpperTwoPrime_eq_of_isPGroup (isPGroup cfg h5)
  sylowR := isSylowOf_self (isPGroup cfg h5)
  noncomm := hnc
  rank := two_le_pRank cfg h5
  g_not := by rw [normalizer_eq cfg h5 hHM]; exact cfg.g_not
  sylowT := isSylowOf_self (isPGroup_TH cfg h5)
  T_ne := TH_ne_bot cfg h5 hHM
  T_lt := card_TH_lt cfg h5 hHM
  T_norm := inf_le_right
  T_le := inf_le_left

end II5

section Certs

namespace II5

variable [Finite G] {K R T H : Subgroup G} {g : G}

theorem not_isCyclic (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H) : ¬ IsCyclic ↥H := by
  intro hcyc
  obtain ⟨e⟩ := h5.iso
  have hNH : IsCyclic ↥((R ⊓ Subgroup.normalizer (T : Set G)).subgroupOf H) := inferInstance
  have hN : IsCyclic ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h5.N_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h5.N_le).surjective
  exact cfg.not_isCyclic (isCyclic_of_surjective e.toMonoidHom e.surjective)

end II5

end Certs

end CFSG.CGT.PushingUpLit.SolKNA
