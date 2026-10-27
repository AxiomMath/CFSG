module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaInputs

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.OmegaPilot (diagOmega)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.Quasithin (perfectCore)

variable (k : Type) [Field k]

@[expose] noncomputable def omegaPlusFieldAut (ρ : k ≃+* k) :
    MulAut (StatedOmega (StatedQuadPlus 4 k)) :=
  ((glCongr ρ).subgroupMap (StatedOmega (StatedQuadPlus 4 k))).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega ρ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp ρ)))

theorem coe_omegaPlusFieldAut (ρ : k ≃+* k) (A : StatedOmega (StatedQuadPlus 4 k)) :
    (((omegaPlusFieldAut k ρ A : StatedOmega (StatedQuadPlus 4 k)) : GL (Fin 4 ⊕ Fin 4) k) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) =
      ((A : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).map ρ := rfl

theorem comp_omegaPlusVec (ρ : k ≃+* k) : (ρ : k → k) ∘ omegaPlusVec k = omegaPlusVec k := by
  funext i
  rcases i with i | i
  · simp only [Function.comp_apply, omegaPlusVec_inl]
    split_ifs <;> simp
  · simp only [Function.comp_apply, omegaPlusVec_inr]
    split_ifs <;> simp

variable [CharP k 2] [Finite k]

theorem omegaPlusFieldAut_iota {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k))
    (ρ : k ≃+* k) (g : StatedSp 3 k) :
    omegaPlusFieldAut k ρ (omegaPlusIota hK hf hdiag g) =
      omegaPlusIota hK hf hdiag (statedSpMap (ρ : k →+* k) 3 g) := by
  set x := omegaPlusIota hK hf hdiag g with hxdef
  have hx : x ∈ fixedSubgroup (omegaPlusBetaC k) :=
    (range_omegaPlusIota hK hf hdiag) ▸ ⟨g, rfl⟩
  have hρx : omegaPlusFieldAut k ρ x ∈ fixedSubgroup (omegaPlusBetaC k) := by
    rw [mem_fixedSubgroup_omegaPlusBetaC_iff] at hx ⊢
    rw [coe_omegaPlusFieldAut]
    funext i
    have h1 := RingHom.map_mulVec (ρ : k →+* k)
      ((x : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) (omegaPlusVec k) i
    rw [hx, RingEquiv.coe_toRingHom, comp_omegaPlusVec] at h1
    rw [← h1]
    exact congrFun (comp_omegaPlusVec k ρ) i
  symm
  apply omegaPlusIota_eq_of_res hK hf hdiag (y := ⟨_, hρx⟩)
  have hres := omegaPlusRes_omegaPlusIota hK hf hdiag g
  have hg : ((g : GL (Fin 3 ⊕ Fin 3) k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) =
      ((x : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix
        plusEmb plusEmb := by
    rw [← hres, coe_omegaPlusRes]
  apply mat_injective
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_omegaPlusRes, coe_omegaPlusFieldAut,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_statedSpMap, coe_map_GL, hg]
  rfl

omit [Field k] [CharP k 2] [Finite k] in
theorem card_perfectCore_centralizer_eq_of_coe {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {S : Subgroup H} {X : Set G} (hX : ((S.map H.subtype : Subgroup G) : Set G) = X) :
    Nat.card (perfectCore (centralizer (S : Set H))) =
      Nat.card (perfectCore (H ⊓ centralizer X)) := by
  have h1 := map_centralizer_eq_inf_centralizer (MulEquiv.refl H) S
  have e : H.subtype.comp (MulEquiv.refl H).toMonoidHom = H.subtype := rfl
  rw [e, hX] at h1
  rw [← h1, ← CFSG.Quasithin.map_perfectCore,
    Subgroup.card_map_of_injective H.subtype_injective]

variable {k}

theorem coe_map_omegaPlusIota_torus {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k))
    {A : Type*} [Group A] (p : A →* (Fin 3 → kˣ)) :
    (((((⊤ : Subgroup A).map ((sp6Diag k).comp p)).map (omegaPlusIota hK hf hdiag)).map
        (StatedOmega (StatedQuadPlus 4 k)).subtype : Subgroup (GL (Fin 4 ⊕ Fin 4) k)) :
          Set (GL (Fin 4 ⊕ Fin 4) k)) =
      diagOmega k 4 '' Set.range (fun a => snocOne k (p a)) := by
  ext X
  constructor
  · rintro ⟨_, ⟨_, ⟨a, -, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, (coe_omegaPlusIota_sp6Diag hK hf hdiag (p a)).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨a, Subgroup.mem_top a, rfl⟩, rfl⟩, coe_omegaPlusIota_sp6Diag hK hf hdiag (p a)⟩

omit [CharP k 2] [Finite k] in
theorem range_snocOne_paramA :
    Set.range (fun a => snocOne k (sp6ParamA k a)) = {t | t 1 = 1 ∧ t 2 = 1 ∧ t 3 = 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_, snocOne_three k _⟩
    · exact (snocOne_castSucc k _ 1).trans (by simp [sp6ParamA])
    · exact (snocOne_castSucc k _ 2).trans (by simp [sp6ParamA])
  · rintro ⟨h1, h2, h3⟩
    refine ⟨t 0, funext fun i => ?_⟩
    fin_cases i
    · exact (snocOne_castSucc k _ 0).trans (by simp [sp6ParamA])
    · exact (snocOne_castSucc k _ 1).trans (by simp [sp6ParamA, h1])
    · exact (snocOne_castSucc k _ 2).trans (by simp [sp6ParamA, h2])
    · exact (snocOne_three k _).trans h3.symm

omit [CharP k 2] [Finite k] in
theorem range_snocOne_paramM2 :
    Set.range (fun a => snocOne k (sp6ParamM2 k a)) = {t | t 2 = 1 ∧ t 3 = 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, snocOne_three k _⟩
    exact (snocOne_castSucc k _ 2).trans (by simp [sp6ParamM2])
  · rintro ⟨h2, h3⟩
    refine ⟨(t 0, t 1), funext fun i => ?_⟩
    fin_cases i
    · exact (snocOne_castSucc k _ 0).trans (by simp [sp6ParamM2])
    · exact (snocOne_castSucc k _ 1).trans (by simp [sp6ParamM2])
    · exact (snocOne_castSucc k _ 2).trans (by simp [sp6ParamM2, h2])
    · exact (snocOne_three k _).trans h3.symm

omit [CharP k 2] [Finite k] in
theorem range_snocOne_paramM3 :
    Set.range (fun a => snocOne k (sp6ParamM3 k a)) = {t | t 2 = t 1 ∧ t 3 = 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, snocOne_three k _⟩
    show snocOne k _ (Fin.castSucc 2) = snocOne k _ (Fin.castSucc 1)
    rw [snocOne_castSucc, snocOne_castSucc]
    simp [sp6ParamM3]
  · rintro ⟨h2, h3⟩
    refine ⟨(t 0, t 1), funext fun i => ?_⟩
    fin_cases i
    · exact (snocOne_castSucc k _ 0).trans (by simp [sp6ParamM3])
    · exact (snocOne_castSucc k _ 1).trans (by simp [sp6ParamM3])
    · exact (snocOne_castSucc k _ 2).trans (by simp [sp6ParamM3, h2])
    · exact (snocOne_three k _).trans h3.symm

theorem pieceCards_omegaPlus8 {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k))
    (G : Type) [Group G] [Finite G] (Φ : StatedOmega (StatedQuadPlus 4 k) →* G)
    (hΦ : Φ.ker ≤ center (StatedOmega (StatedQuadPlus 4 k))) :
    pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup kˣ)).map (omegaPlusIota hK hf hdiag)).map Φ)
      (((sp6TorusM2 (⊤ : Subgroup kˣ)).map (omegaPlusIota hK hf hdiag)).map Φ)
      (((sp6TorusM3 (⊤ : Subgroup kˣ)).map (omegaPlusIota hK hf hdiag)).map Φ) =
        pieceOrders .omegaPlus8 (2 ^ f) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hΦ.trans (center_omegaPlus8 k).le
  set Φ' : StatedOmega (StatedQuadPlus 4 k) ≃* Φ.range := MonoidHom.ofInjective hinj
  have hΦ' : Φ.range.subtype.comp Φ'.toMonoidHom = Φ := by
    ext x
    rfl
  rw [pieceCards_eq_of_mulEquiv Φ' (by rw [hΦ']) (by rw [hΦ']) (by rw [hΦ']), pieceCards_top]
  have hA := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaPlusIota_torus hK hf hdiag (sp6ParamA k))
  have h2 := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaPlusIota_torus hK hf hdiag (sp6ParamM2 k))
  have h3 := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaPlusIota_torus hK hf hdiag (sp6ParamM3 k))
  rw [range_snocOne_paramA, card_perfectCore_omegaPlus8_A k hk4] at hA
  rw [range_snocOne_paramM2, card_perfectCore_omegaPlus8_M2 k hk4] at h2
  rw [range_snocOne_paramM3, card_perfectCore_omegaPlus8_M3 k hk4] at h3
  rw [sp6TorusA, sp6TorusM2, sp6TorusM3, Subgroup.top_prod_top, hA, h2, h3, hK]
  rfl

omit [CharP k 2] [Finite k] in
theorem graphKindModelInput_omegaPlus8 :
    GraphKindModelInput .omegaPlus8 := by
  intro f hf k _ _ hK
  have : CharP k 2 := charP_two_of_natCard_eq_two_pow hK
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdiag := diagOmega_mem_omegaPlus8 k
  refine ⟨StatedOmega (StatedQuadPlus 4 k), inferInstance, inferInstance, isPerfect_omegaPlus8 k,
    omegaPlusIota hK hf hdiag, omegaPlusBetaC k, ?_, ?_, omegaPlusIota_injective hK hf hdiag,
    (range_omegaPlusIota hK hf hdiag).symm, ?_, ?_, ?_⟩
  · intro E' _ _ π' hπ' hc
    exact omegaPlus8_exists_section k hk4 E' π' hπ' hc
  · intro S _ hS
    exact omegaPlus8_covers k hK S hS
  · intro ρ
    exact ⟨omegaPlusFieldAut k ρ, omegaPlusFieldAut_iota k hK hf hdiag ρ⟩
  · intro β hβ2 hβo f' hfix
    exact exists_conj_omegaPlusBetaC k (by omega) hK β hβ2 hβo hfix
  · intro G _ _ Φ hΦ
    exact pieceCards_omegaPlus8 hK hf hdiag G Φ hΦ

end CFSG.SeitzReduction.F4Pilot
