module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4LA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section SL3

variable {F : Type} [Field F] [Finite F]

theorem sl3_center_eq_bot (hF : Nat.card F = 3) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr3 : r ^ 3 = r := by
      have : Fintype F := Fintype.ofFinite F
      have h := FiniteField.pow_card r
      rwa [← Nat.card_eq_fintype_card, hF] at h
    have h1 : r = 1 := by
      rw [Fintype.card_fin] at hr
      rw [← hr3, hr]
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

noncomputable def sl3EquivPSL3 (hF : Nat.card F = 3) :
    SL(3, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
  ((QuotientGroup.quotientMulEquivOfEq (sl3_center_eq_bot hF)).trans QuotientGroup.quotientBot).symm

theorem lieModel_L33_of_equiv_sl3 (hF : Nat.card F = 3) {M : Type} [Group M] (e : M ≃* SL(3, F)) :
    LieModel M .PSL 3 3 1 := by
  refine Or.inl ⟨by simp [classicalTags], ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num,
    by norm_num⟩, F, inferInstance, inferInstance, by simpa using hF, ⟨?_⟩⟩
  exact e.trans ((sl3EquivPSL3 hF).trans
    (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F))

theorem isSimpleGroup_sl3 (hF : Nat.card F = 3) : IsSimpleGroup SL(3, F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact (sl3EquivPSL3 hF).isSimpleGroup

end SL3

section Central

variable {G : Type*} [Group G]

theorem commutatorElement_central_mul_left {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  calc ⁅z * a, b⁆ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by rw [commutatorElement_def]; group
    _ = a * b * a⁻¹ * z * z⁻¹ * b⁻¹ := by rw [← hz' (a * b * a⁻¹)]
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_central_mul_right {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  calc ⁅a, z * b⁆ = a * z * (b * a⁻¹ * b⁻¹) * z⁻¹ := by rw [commutatorElement_def]; group
    _ = z * (a * (b * a⁻¹ * b⁻¹)) * z⁻¹ := by rw [hz' a]; group
    _ = a * (b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [← hz' (a * (b * a⁻¹ * b⁻¹))]
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group

end Central

section Lift

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {σ : MulAut W} {Q : Type} [Group Q]

theorem conjSub_fixSylGen_le (hΦ : ConjInvariant Φ) {c : W} (hc : σ c = c) :
    conjSub c (fixSylGen Φ σ) ≤ fixSylGen Φ σ := by
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun P => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hP => ?_
  obtain ⟨⟨M, hM, hPM⟩, hPfix⟩ := hP
  refine le_iSup₂_of_le (f := fun P (_ : P ∈ {P : Subgroup W | (∃ M ∈ Φ, IsSylow2In P M) ∧
    ∀ x ∈ P, σ x = x}) => P) (conjSub c P) ⟨⟨conjSub c M, hΦ c M hM, hPM.conj c⟩, ?_⟩ le_rfl
  rintro _ ⟨y, hy, rfl⟩
  show σ (c * y * c⁻¹) = c * y * c⁻¹
  rw [map_mul, map_mul, map_inv, hc, hPfix y hy]

theorem map_fixSylGen_eq (hT : TwinSProp3 Φ K K' k k' σ) (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥)
    (hC : IsSimpleGroup ↥(fixSub (E3S3O.descend f hf σ
      (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ)))) :
    (fixSylGen Φ σ).map f =
      fixSub (E3S3O.descend f hf σ (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ)) := by
  have h := hT.toTwinBase3
  set hσ := E3S3O.map_ker_aut h f hf hf2 hs σ
  set x := E3S3O.descend f hf σ hσ with hxdef
  have hx : ∀ w, x (f w) = f (σ w) := E3S3O.descend_apply f hf σ hσ
  have hker := E3S3O.ker_eq_center_of_simple h f hf hf2 hs
  have hSP := sPHyp_of_reduction hT f hf hf2 hs hOS
  set C := fixSub x with hCdef
  set Y := fixSylGen Φ σ with hYdef
  have hYC : Y.map f ≤ C := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun P hP y hy => ?_
    show x (f y) = f y
    rw [hx, hP.2 y hy]
  have hAC : K.map f ≤ C := fun y hy => hSP.fixA y hy
  have hCperf : ⁅C, C⁆ = C := by
    have hcomm : (commutator ↥C).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥C) with h1 | h1
    · exfalso
      obtain ⟨s, a, b, ha, hb, hs1, -, has, hbs, hab, -⟩ := E1521.quat_rel hSP.quat.q8
      have hab' : (⟨a, hAC ha⟩ : ↥C) * ⟨b, hAC hb⟩ = ⟨b, hAC hb⟩ * ⟨a, hAC ha⟩ := by
        have hmem : ⁅(⟨a, hAC ha⟩ : ↥C), ⟨b, hAC hb⟩⁆ ∈ commutator ↥C :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      have hab2 : a * b = b * a := congrArg Subtype.val hab'
      have hbb : b⁻¹ = b := by rw [← hab, hab2, mul_inv_cancel_right]
      apply hs1
      rw [← hbs, ← mul_inv_cancel b, hbb]
    · rw [← Subgroup.map_subtype_commutator, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCW : C ≤ (fixSub σ).map f := by
    set H := C.comap f with hH
    have hHH : ⁅H, H⁆ ≤ fixSub σ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hz : ∀ w ∈ H, σ w * w⁻¹ ∈ Subgroup.center W := fun w hw => by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hx]
        have : x (f w) = f w := hw
        rw [this, mul_inv_cancel]
      show σ ⁅a, b⁆ = ⁅a, b⁆
      rw [map_commutatorElement]
      have ea : σ a = (σ a * a⁻¹) * a := by group
      have eb : σ b = (σ b * b⁻¹) * b := by group
      rw [ea, eb, commutatorElement_central_mul_left (hz a ha),
        commutatorElement_central_mul_right (hz b hb)]
    calc C = ⁅C, C⁆ := hCperf.symm
      _ = ⁅H.map f, H.map f⁆ := by rw [Subgroup.map_comap_eq_self_of_surjective hf]
      _ = ⁅H, H⁆.map f := (Subgroup.map_commutator H H f).symm
      _ ≤ (fixSub σ).map f := Subgroup.map_mono hHH
  have hnorm : ((Y.map f).subgroupOf C).Normal := by
    constructor
    intro n hn g
    obtain ⟨c, hc, hcg⟩ := hCW g.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hyn⟩ := hn
    have hcy : c * y * c⁻¹ ∈ Y := conjSub_fixSylGen_le h.fam.hyp.conjInvariant hc ⟨y, hy, rfl⟩
    refine ⟨c * y * c⁻¹, hcy, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hcg, hyn]
  have hKY : K ≤ Y := by
    have hK2 := isPGroup_K h f hf hf2 hs hOS
    refine le_iSup₂_of_le (f := fun P (_ : P ∈ {P : Subgroup W | (∃ M ∈ Φ, IsSylow2In P M) ∧
      ∀ x ∈ P, σ x = x}) => P) K ⟨⟨K, h.memK, le_rfl, hK2, fun _ hV _ hle => le_antisymm hV hle⟩,
      fix_K hT f hf hf2 hs hOS⟩ le_rfl
  have hk1 : f k ≠ 1 := fun h1 => E3S3O.not_mem_ker h f hf2 1 (by simpa using h1)
  refine le_antisymm hYC ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y.map f).subgroupOf C) with h1 | h1
  · exfalso
    have hmem : (⟨f k, hYC ⟨k, hKY h.invK.mem, rfl⟩⟩ : ↥C) ∈ (Y.map f).subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr ⟨k, hKY h.invK.mem, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact hk1 (congrArg Subtype.val hmem)
  · intro c hc
    have hmem : (⟨c, hc⟩ : ↥C) ∈ (Y.map f).subgroupOf C := h1 ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

theorem exists_quotient_of_simple_fix (hT : TwinSProp3 Φ K K' k k' σ) (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥)
    (hC : IsSimpleGroup ↥(fixSub (E3S3O.descend f hf σ
      (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ)))) :
    ∃ (B : Subgroup ↥(fixSylGen Φ σ)) (_ : B.Normal), Nonempty (↥(fixSylGen Φ σ) ⧸ B ≃*
      ↥(fixSub (E3S3O.descend f hf σ (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ)))) := by
  have heq := map_fixSylGen_eq hT f hf hf2 hs hOS hC
  set C := fixSub (E3S3O.descend f hf σ (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ))
  set η : ↥(fixSylGen Φ σ) →* ↥C := (f.comp (fixSylGen Φ σ).subtype).codRestrict C
    (fun y => heq ▸ ⟨(y : W), y.2, rfl⟩)
  have hη : Function.Surjective η := by
    rintro ⟨c, hc⟩
    rw [← heq] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    exact ⟨⟨y, hy⟩, rfl⟩
  exact ⟨η.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective η hη⟩⟩

end Lift

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
