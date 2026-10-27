module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section TheoremZ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_normal_of_unique (h : D1PhaseThree p P M H R) {D J : Subgroup G}
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hQD : pCoreOf 2 M ≤ D)
    (hND : GLBPrimeCore p H ≤ D) (hDH : D ⊓ H ≤ R ⊔ GLBPrimeCore p H)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False := by
  obtain ⟨T, hTN, hT2, hTidx, hRT, hST⟩ := h.exists_sylowTwo_primeCore
  have hT1 : T ≠ ⊥ := fun hbot => twoLocal_pCoreOf_ne_bot H h.maxTwoLocal_H.1
    (le_bot_iff.mp (hbot ▸ hST))
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc := hNJ (Subgroup.commutator_mem_commutator ((GLBPrimeCore p H).inv_mem (hTN ht)) hj)
    rw [commutatorElement_def, inv_inv] at hc
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht (hST hc)
  exact h.false_of_normal_inf_le_sup h.isPGroup_R h.le_H hTN hT2 hTidx hT1
    (fun C hCT hC hchar => normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT hRT huniq hCT hC hchar)
    hDM hMD hQD hND hDH hCGT hD2

@[expose] def pCoreCentralizerPreimage (p : ℕ) (M : Subgroup G) : Subgroup G :=
  ((Subgroup.centralizer (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :
    Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

omit [Finite G] in
theorem pCoreCentralizerPreimage_facts (p : ℕ) (M : Subgroup G) :
    pCoreCentralizerPreimage p M ≤ M ∧
      M ≤ Subgroup.normalizer (pCoreCentralizerPreimage p M : Set G) ∧
      pCoreOf 2 M ≤ pCoreCentralizerPreimage p M ∧
      ∀ m ∈ M, (∀ y ∈ pCorePreimage p M, m * y * m⁻¹ * y⁻¹ ∈ pCoreOf 2 M) →
        m ∈ pCoreCentralizerPreimage p M := by
  set D := pCoreCentralizerPreimage p M with hDdef
  set Q := pCoreOf 2 M with hQdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf M = (Subgroup.centralizer (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap mk :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mp
      (hDsub ▸ Subgroup.Normal.comap inferInstance mk)
  have hmemD : ∀ m ∈ M, (∀ y ∈ pCorePreimage p M, m * y * m⁻¹ * y⁻¹ ∈ Q) → m ∈ D := by
    intro m hmM hm
    refine ⟨⟨m, hmM⟩, ?_, rfl⟩
    change mk ⟨m, hmM⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) o
    have hyY : (y : G) ∈ pCorePreimage p M := ⟨y, ho, rfl⟩
    have hq := hm y hyY
    have h1 : mk (⟨m, hmM⟩ * y * (⟨m, hmM⟩ : M)⁻¹ * y⁻¹) = 1 :=
      (mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc mk y * mk ⟨m, hmM⟩
        = mk ⟨m, hmM⟩ * mk y * (mk ⟨m, hmM⟩)⁻¹ * (mk y)⁻¹ * (mk y * mk ⟨m, hmM⟩) := by
          rw [h1, one_mul]
      _ = mk ⟨m, hmM⟩ * mk y := by group
  refine ⟨hDM, hMD, fun q hq => ?_, hmemD⟩
  have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
  refine hmemD q hqM fun y hy => ?_
  have hyM : y ∈ M := pCorePreimage_le p M hy
  have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
  rw [e]
  exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp
    (localGroup_le_normalizer_pCoreOf 2 M hyM) q⁻¹).mp (Q.inv_mem hq))

theorem D1PhaseThree.glbPrimeCore_le_pCoreCentralizerPreimage (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    GLBPrimeCore p H ≤ pCoreCentralizerPreimage p M := by
  intro n hn
  refine (pCoreCentralizerPreimage_facts p M).2.2.2 n (h.primeCore_le hn) fun y hy => ?_
  have := h.commutator_pCorePreimage_le h84 hD2 (Subgroup.commutator_mem_commutator hn hy)
  rwa [commutatorElement_def] at this

end TheoremZ

section ZGen

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_normal_inf_le_sup_of (h : D1PhaseThree p P M H R)
    {X T D N₁ : Subgroup G} (hX : IsPGroup p X) (hXH : X ≤ H) (hN₁H : N₁ ≤ H)
    (hXN₁ : X ≤ Subgroup.normalizer (N₁ : Set G)) (hTN : T ≤ N₁) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf N₁).index) (hT1 : T ≠ ⊥)
    (hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H)
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hQD : pCoreOf 2 M ≤ D)
    (hND : N₁ ≤ D) (hDH : D ⊓ H ≤ X ⊔ N₁)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : Subgroup.normalizer (T : Set G) ≤ H :=
    hloc T le_rfl hT1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hTD : ¬ 2 ∣ (T.subgroupOf D).index :=
    not_dvd_index_of_inf_normalizer_le hTN hND hT2 hTidx fun U hU hUD =>
      le_of_le_sup_of_isPGroup_of_ne h.ne_two hX hXN₁ hU
        fun u hu => hDH ⟨(hUD hu).1, hTH (hUD hu).2⟩
  have hcgs : cgsIn D T = D := by
    by_contra hne
    have hDtop : D ≠ ⊤ := fun htop => h.not_le ((top_le_iff.mp (htop ▸ hDM) : M = ⊤) ▸ le_top)
    have hK : Open.IsKGroup ↥D :=
      isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper h.glob.kProper D hDtop)
    have hQcore : pCoreOf 2 M ≤ pCoreOf 2 D :=
      normal_pGroup_le_pCoreOf 2 _ _ hQD
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr
          (hDM.trans (localGroup_le_normalizer_pCoreOf 2 M)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    have hchar : CharTwo D := fun x hx =>
      hQcore (h.charTwo.1 ⟨hDM hx.1, Subgroup.centralizer_le hQcore hx.2⟩)
    obtain ⟨Y, hYD, hYsub, hYX, -⟩ := hCGT G D T hK hchar ⟨hTN.trans hND, hT2, hTD⟩ hne
    exact hD2 G h.glob M Y h.maxTwoLocal_M (hYD.trans hDM)
      (isSubnormal_of_isSubnormal_of_normal hYsub hDM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mpr hMD)) hYX
  have hDH' : D ≤ H :=
    calc D = cgsIn D T := hcgs.symm
      _ ≤ D ⊓ H := iSup_le fun C => iSup_le fun hCT => iSup_le fun hC => iSup_le fun hchar =>
          inf_le_inf_left D (hloc C hCT hC hchar)
      _ ≤ X ⊔ N₁ := hDH
      _ ≤ H := sup_le hXH hN₁H
  have hMH : M ≤ H := by
    intro m hm
    obtain ⟨d, hd, hdm⟩ :=
      exists_mem_inv_mul_mem_normalizer_of_not_dvd_index (hTN.trans hND) hT2 hTD (hMD hm)
    have e : m = d * (d⁻¹ * m) := by group
    rw [e]
    exact H.mul_mem (hDH' hd) (hTH hdm)
  exact h.not_le (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem D1PhaseThree.false_of_normal_of_unique_of (h : D1PhaseThree p P M H R)
    {N₁ T D J : Subgroup G} (hN₁H : N₁ ≤ H) (hHN₁ : H ≤ Subgroup.normalizer (N₁ : Set G))
    (hTN : T ≤ N₁) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf N₁).index)
    (hRT : R ≤ Subgroup.normalizer (T : Set G)) (hST : pCoreOf 2 H ≤ T)
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hQD : pCoreOf 2 M ≤ D)
    (hND : N₁ ≤ D) (hDH : D ⊓ H ≤ R ⊔ N₁) (hNJ : ⁅N₁, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False := by
  have hT1 : T ≠ ⊥ := fun hbot => twoLocal_pCoreOf_ne_bot H h.maxTwoLocal_H.1
    (le_bot_iff.mp (hbot ▸ hST))
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc := hNJ (Subgroup.commutator_mem_commutator (N₁.inv_mem (hTN ht)) hj)
    rw [commutatorElement_def, inv_inv] at hc
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht (hST hc)
  exact h.false_of_normal_inf_le_sup_of h.isPGroup_R h.le_H hN₁H (h.le_H.trans hHN₁) hTN hT2
    hTidx hT1
    (fun C hCT hC hchar => normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT hRT huniq hCT hC hchar)
    hDM hMD hQD hND hDH hCGT hD2

end ZGen

section MaxChoice

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem exists_unique_of_competitorsOn {C : Subgroup G → Prop} {R X : Subgroup G}
    (hC : ∀ H, C H → D1PhaseThree p P M H R ∧ X ≤ R ∧ X ≠ ⊥) (hcomp : D1JCompetitorsOn C R X)
    {H : Subgroup G} (h : C H) :
    ∃ H₀ : Subgroup G, C H₀ ∧
      ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → nclIn H₀ X ≤ H' → R ≤ H' → H' = H₀ := by
  obtain ⟨H₀, h₀, hmax⟩ := Set.exists_max_image {H' : Subgroup G | C H'}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H, h⟩
  obtain ⟨h3, hXR, hX1⟩ := hC H₀ h₀
  refine ⟨H₀, h₀, fun H' hH' hJH' hRH' => ?_⟩
  obtain ⟨h', hJJ'⟩ := hcomp H₀ h₀ H' hH' hJH' hRH'
  have heq : nclIn H₀ X = nclIn H' X := Subgroup.eq_of_le_of_card_ge hJJ' (hmax H' h')
  have hJn' : ((nclIn H₀ X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) ≤ nclIn H₀ X :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) : Set G) = H₀ :=
    maxTwoLocal_normalizer_eq_of_normal h3.maxTwoLocal_H
      (h3.pCoreOf_two_primeCore_ne_bot hXR hX1)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
      (hAJ.trans (nclIn_le_self H₀ X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₀ X) (nclIn_normal H₀ X))
  have hH'H : H' ≤ H₀ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer (hAJ.trans hJH')).mp
    (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
  exact (hH'.2 H₀ h3.maxTwoLocal_H.1 hH'H).symm

end MaxChoice

end CFSG.AGLEmbedding
