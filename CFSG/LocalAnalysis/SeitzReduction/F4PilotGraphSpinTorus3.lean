module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinA3

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus toStdD spinMatrix
  plusFrame)
open CFSG.LieType.RootSystem (roots)
open CFSG.SeitzReduction.OmegaPilot (diagOmega diagOmega_coe)
open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr)

local instance f4PilotGraphSpinTorus3NeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphSpinTorus3NeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Torus

variable (F : Type) [Field F]

@[expose] noncomputable def sp6ParamT3 : Fˣ × Fˣ →* (Fin 3 → Fˣ) :=
  ((MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0) *
      (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 1)).comp (MonoidHom.fst Fˣ Fˣ) *
    (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 2).comp (MonoidHom.snd Fˣ Fˣ)

variable {F}

theorem sp6ParamT3_apply (a b : Fˣ) : sp6ParamT3 F (a, b) = ![a, a, b] := by
  funext i
  fin_cases i <;> simp [sp6ParamT3]

@[expose] noncomputable def sp6Torus3 (A : Subgroup Fˣ) : Subgroup (StatedSp 3 F) :=
  (A.prod A).map ((sp6Diag F).comp (sp6ParamT3 F))

end Torus

section Levi


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_c3LeviEquiv_sp6Torus3 :
    ((sp6Torus3 (⊤ : Subgroup Kˣ)).map (c3LeviEquiv K).toMonoidHom).map (C3Levi K).subtype =
      (leviTorus K {3}).subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨⟨a, a'⟩, -, rfl⟩, rfl⟩, rfl⟩
    refine c3Torus_mem_inf_of_param (sp6ParamT3 K (a, a')) fun j hj => ?_
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [c3TorusParam_apply_three, sp6ParamT3_apply]
    simp
  · intro x hx
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 (mem_subgroupOf.1 hxT)
    obtain ⟨s, hs⟩ := exists_sq_eq_of_ringChar_eq_two (ringChar.eq K 2) (b 1)
    have e := c3Torus_eq_c3LeviEquiv_of_param (x := ⟨x, hxD⟩) hbx.symm
      (sp6ParamT3 K (b 2 * s, s))
      (by rw [c3TorusParam_apply_one, sp6ParamT3_apply, ← hs, sq]; simp)
      (by rw [c3TorusParam_apply_two, sp6ParamT3_apply]; simp)
      (by rw [c3TorusParam_apply_three, sp6ParamT3_apply, hb 3 (by simp)]; simp)
    exact ⟨⟨x, hxD⟩, ⟨_, ⟨(b 2 * s, s), Subgroup.mem_prod.2 ⟨mem_top _, mem_top _⟩, rfl⟩,
      e.symm⟩, rfl⟩

omit [Finite K] [CharP K 2]
  in
theorem map_statedSpCongr_sp6Torus3 {F : Type} [Field F] (ε : F ≃+* K) :
    (sp6Torus3 (⊤ : Subgroup Fˣ)).map (statedSpCongr ε 3).toMonoidHom =
      sp6Torus3 (⊤ : Subgroup Kˣ) := by
  have h := map_statedSpCongr_sp6Torus ε (sp6ParamT3 F) (sp6ParamT3 K) (graphTorusUnitsMap₂ ε)
    (graphTorusUnitsMap₂_surjective ε) fun m i => by
      obtain ⟨a, b⟩ := m
      rw [sp6ParamT3_apply, show graphTorusUnitsMap₂ ε (a, b) =
        (Units.map (ε : F →* K) a, Units.map (ε : F →* K) b) from rfl, sp6ParamT3_apply]
      fin_cases i <;> rfl
  simp only [sp6Torus3, Subgroup.top_prod_top]
  exact h

variable {G : Type} [Group G] {L : Subgroup G}

theorem map_levi6Hom_sp6Torus3 (e : L ≃* adjointGroup .F4 K) {F : Type} [Field F]
    (ε : F ≃+* K) :
    (sp6Torus3 (⊤ : Subgroup Fˣ)).map (levi6Hom e ε) = leviTorusG e {3} ⊓ neighbourLeviG e .X := by
  rw [map_levi6Hom, map_statedSpCongr_sp6Torus3, map_c3LeviEquiv_sp6Torus3, map_inf_C3Levi_eq]
  rfl

end Levi

section Commute

variable {K : Type} [Field K]

omit [Field K] in
theorem snocOne_sp6ParamT3 [Field K] (a b : Kˣ) :
    snocOne K (sp6ParamT3 K (a, b)) = ![a, a, b, 1] := by
  rw [sp6ParamT3_apply]
  funext m
  fin_cases m <;> rfl

theorem commute_diagonal_longMat_zero_one (a b : Kˣ) (s : Bool) :
    Commute (diagonal (diagSpEntry (snocOne K (sp6ParamT3 K (a, b)))))
      (longMat K SpinPlus.plusIdx 0 1 s (!s)) := by
  refine ((mul_diagonal_eq_diagonal_mul_iff _ _).2 fun p q hpq => ?_).symm
  rw [snocOne_sp6ParamT3] at hpq
  simp only [longMat, Matrix.sub_apply, Matrix.single_apply, Bool.not_not]
  cases s <;> rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp_all [SpinPlus.plusIdx]

variable [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem commute_spinX_spinIota_sp6Torus3 {γ : Fin 4 → ℤ}
    (hγ : γ = Pi.single 0 1 ∨ γ = -Pi.single 0 1) (c : K) (a b : Kˣ) :
    Commute (SpinPlus.x 4 K three_le_rank_D4 γ c)
      (spinIota hK hf (sp6Diag K (sp6ParamT3 K (a, b)))) := by
  apply (spinOmegaEquiv (K := K)).injective
  rw [map_mul, map_mul, spinIota_apply, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_spinOmegaEquiv, coe_omegaPlusIota_sp6Diag, diagOmega_coe]
  have hF := SpinPlus.isCoordFrame_plusFrame (K := K) three_le_rank_D4
  change Commute ((spinMatrix (quadPlus 4 K) (rootElt (plusFrame 4 K three_le_rank_D4)
    (toStdD 4 γ) c) : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) _
  rw [coe_spinMatrix_rootElt hF]
  obtain ⟨s, hs⟩ : ∃ s : Bool, toStdD 4 γ =
      Pi.single 0 (CFSG.LieType.Universal.Spin.boolSign s) +
        Pi.single 1 (CFSG.LieType.Universal.Spin.boolSign (!s)) := by
    rcases hγ with rfl | rfl
    · refine ⟨true, ?_⟩
      funext m
      fin_cases m <;> simp [toStdD, CFSG.LieType.Universal.Spin.boolSign]
    · refine ⟨false, ?_⟩
      funext m
      fin_cases m <;> simp [toStdD, CFSG.LieType.Universal.Spin.boolSign]
  rw [rootMat_eq hF (by decide) hs]
  have hL := commute_diagonal_longMat_zero_one (K := K) a b s
  exact (Commute.one_left _).add_left ((hL.symm.smul_left _).smul_left _)

end Commute

section Piece


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem commute_spinEquivD4_symm_one {y : e6Data_valid.minGroup K}
    (hy : y ∈ e6ScLevi K {1}) {s : StatedSp 3 K} (hs : s ∈ sp6Torus3 (⊤ : Subgroup Kˣ)) :
    Commute ((spinEquivD4 K).symm
      ⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_subset_e6D4Nodes hy⟩) (spinIota hK hf s) := by
  have hsingle : (Pi.single 0 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    (SpinPlus.Φ 4 K three_le_rank_D4).single_mem 0
  have hneg : (-Pi.single 0 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ := by
    have := (CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).smul_mem
      ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple 0)
      _ hsingle
    rwa [(CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).simple_single]
      at this
  set C : Subgroup (spinGroup (quadPlus 4 K)) :=
    centralizer (((sp6Torus3 (⊤ : Subgroup Kˣ)).map (spinIota hK hf) :
      Subgroup (spinGroup (quadPlus 4 K))) : Set (spinGroup (quadPlus 4 K))) with hC
  have hmem : ∀ γ, (γ = Pi.single 0 1 ∨ γ = -Pi.single 0 1) → ∀ c : K,
      SpinPlus.x 4 K three_le_rank_D4 γ c ∈ C := by
    intro γ hγ c
    rw [hC, mem_centralizer_iff]
    rintro _ ⟨_, ⟨⟨a, b⟩, -, rfl⟩, rfl⟩
    exact (commute_spinX_spinIota_sp6Torus3 hK hf hγ c a b).symm.eq
  have hle : e6ScLevi K {1} ≤ C.map (spinToE6Sc K) := by
    dsimp only [e6ScLevi]
    rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      refine ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single 0 1) c, hmem _ (Or.inl rfl) c, ?_⟩
      rw [spinToE6Sc_x hsingle, d4Embed_single]
      rfl
    · intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      refine ⟨SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 0 1) c, hmem _ (Or.inr rfl) c, ?_⟩
      rw [spinToE6Sc_x hneg, d4Embed_neg_single]
      rfl
  obtain ⟨w, hw, hwy⟩ := hle hy
  have hw' : (spinEquivD4 K).symm
      ⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_subset_e6D4Nodes hy⟩ = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_spinEquivD4]
    exact hwy.symm
  rw [hw']
  exact ((mem_centralizer_iff.1 hw) _ ⟨s, hs, rfl⟩).symm

theorem scLeviRestrict_one_mem_centralizer
    {e₂ : L ≃* adjointGroup .F4 K} {ε : K ≃+* K}
    {ΦY : spinGroup (quadPlus 4 K) →* G} (hrY : ΦY.range = neighbourCore e₂ .X)
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) (x : e6ScLevi K {1}) :
    scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes x ∈
      centralizer (leviTorusG e₂ {3} : Set G) := by
  set g := scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes x
    with hg
  have hgE : g ∈ neighbourCore e₂ .X := by
    rw [← hrY]
    exact ⟨_, rfl⟩
  have hT : leviTorusG e₂ {3} ⊓ neighbourLeviG e₂ .X ≤ centralizer ({g} : Set G) := by
    rw [← map_levi6Hom_sp6Torus3 e₂ ε]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hn]
    have hc := congrArg ΦY (commute_spinEquivD4_symm_one hK hf x.2 hs).eq
    rw [map_mul, map_mul] at hc
    exact hc.symm
  have hC : centralizer (neighbourCore e₂ .X : Set G) ≤ centralizer ({g} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hz g hgE).symm
  have hle : leviTorusG e₂ {3} ≤ centralizer ({g} : Set G) := by
    refine (le_sup_left (b := centralizer (neighbourCore e₂ .X : Set G))).trans ?_
    rw [leviTorusG_sup_centralizer_eq e₂ three_subset_X]
    exact sup_le hT hC
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hle hz)

theorem range_scLeviRestrict_one_le_pieceCore (hq : 4 ≤ Nat.card K)
    {e₂ : L ≃* adjointGroup .F4 K} {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e₂ .X) (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) :
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes).range ≤
      pieceCore e₂ {3} := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one_of_four_le (K := K) hq
  have hperf : Group.IsPerfect (e6ScLevi K {1}) :=
    Subgroup.isPerfect_iff.2 (commutator_e6ScLevi_singleton 1 ht)
  have hperf' := Subgroup.isPerfect_iff.1 (Group.IsPerfect.range
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes))
  refine le_centralizerPerfectCore hperf' ?_
  rintro _ ⟨x, rfl⟩
  exact scLeviRestrict_one_mem_centralizer hK hf hrY hn x

omit
  [CharP K 2] in
theorem pieceCore_three_trans_graphAutF4_symm [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (e : L ≃* adjointGroup .F4 K) :
    pieceCore (e.trans (graphAutF4 K).symm) {3} = pieceCore e {0} := by
  rw [pieceCore_trans_graphAutF4_symm]
  congr 1

theorem range_scLeviRestrict_one_le_pieceCore_of_frame
    (hq : 4 ≤ Nat.card K)
    {e e₂ : L ≃* adjointGroup .F4 K} {N : AmalgamNeighbour} (he₂ : IsNeighbourFrame e e₂ N)
    {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G} (hrY : ΦY.range = neighbourCore e N)
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) :
    (N = .X → (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
        one_subset_e6D4Nodes).range ≤ pieceCore e {3}) ∧
      (N = .Y → (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
        one_subset_e6D4Nodes).range ≤ pieceCore e {0}) := by
  have h := range_scLeviRestrict_one_le_pieceCore hK hf hq
    (hrY.trans (neighbourFrame_eq he₂).1) hn
  cases N with
  | X =>
    have h' : e₂ = e := he₂
    subst h'
    exact ⟨fun _ => h, fun h'' => absurd h'' (by decide)⟩
  | Y =>
    obtain ⟨hc, rfl⟩ := he₂
    refine ⟨fun h'' => absurd h'' (by decide), fun _ => ?_⟩
    rwa [pieceCore_three_trans_graphAutF4_symm] at h
  | X' => exact he₂.elim

end Piece

end CFSG.SeitzReduction.F4Pilot
