module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockDiagSL
  mem_blockDiagSL)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem pieceCore_eq_map_of_lift (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {k : Fin 3}
    {J : Finset (Fin 3)} (hk : k ∉ spSupport J) {F : Type} [Field F] [Finite F]
    [CharP F 2]
    (σ : K ≃+* F) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G) (hrange : Φ.range = neighbourCore e k)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
      ((e.symm (complSpEquiv k x : complSp K k) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K))
    (hfact : leviTorusSp K J ≤ rootTorusSp K k ⊔ T₄.map (complSpHom k))
    (hT₄ : T₄.map (complSpHom k) ≤ leviTorusSp K J)
    {C : Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F)}
    (hC : perfectCore (centralizer ((((T₄.map β).map (statedSpMap (σ : K →+* F) 2)).map
      (ctEmbed 1) : Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) :
        Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))) = C) :
    pieceCore e J = C.map Φ := by
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hY : modelToG e (T₄.map (complSpHom k)) ≤ neighbourCore e k := by
    refine le_trans ?_ (modelToG_complSp_le_neighbourCore e hK (by norm_num) k)
    refine UnitaryPilot.modelToG_mono e ?_
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv k x).2
  have hTY := map_ctEmbed_eq_of_N1 e k σ β Φ hΦE hN1 T₄
  rw [pieceCore_eq e hk, inf_centralizer_eq_of_le_sup (H := neighbourCore e k)
    (X := modelToG e (rootTorusSp K k))
    (Y := modelToG e (T₄.map (complSpHom k))) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e hT₄)
    (by rw [← UnitaryPilot.modelToG_sup]; exact UnitaryPilot.modelToG_mono e hfact),
    perfectCore_inf_centralizer_eq_map hY, ← hTY, ← hΦ']
  have hcore : perfectCore (centralizer (((((T₄.map β).map (statedSpMap (σ : K →+* F) 2)).map
      (ctEmbed 1)).map Φ' : Subgroup (neighbourCore e k)) : Set (neighbourCore e k))) =
      C.map Φ' := by
    apply le_antisymm
    · rw [← hC]
      exact le_map_perfectCore_centralizer Φ' hΦ's hker' _ (perfectCore_perfect _)
        (perfectCore_le _)
    · rw [← hC]
      exact map_perfectCore_centralizer_le Φ' _
  rw [hcore, Subgroup.map_map]
  rfl

end Lift

section Cores

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem perfectCore_centralizer_oddStdTorus (hF : 4 ≤ Nat.card F) :
    perfectCore (centralizer (oddStdTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))) =
      blockSpecialLinear (K := F) oddFixBlock := by
  refine le_antisymm ?_ (blockSpecialLinear_oddFix_le_perfectCore_centralizer hF)
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hF
  have e3 := coe_units_ne_inv_of_ne_one hκ₀
  have e1 : (κ₀ : F) ≠ 1 := fun h => hκ₀ (Units.ext h)
  have e2 : ((κ₀⁻¹ : Fˣ) : F) ≠ 1 := fun h => hκ₀ (inv_eq_one.1 (Units.ext h))
  have e4 : (κ₀ : F) ≠ (κ₀ : F)⁻¹ := by simpa using e3
  set C := centralizer (oddStdTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
  have hd : ctEmbed 1 (rootTorusHom F 2 0 κ₀) ∈ oddStdTorus F := ⟨_, ⟨κ₀, rfl⟩, rfl⟩
  have hdiag : ∀ (I : Finset (Fin (2 * 2 + 1))), (I = {0} ∨ I = {1}) →
      C ≤ blockDiagSL (K := F) I := by
    intro I hI g hg
    have hc := mem_centralizer_iff.1 hg _ hd
    rw [mem_blockDiagSL]
    intro i j hij
    apply eq_zero_of_commute_diagonal (coe_ctEmbed_rootTorusHom_zero κ₀) hc
    rcases hI with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
      simp at hij ⊢ <;>
      first | exact hκ₀ | exact e1 | exact e1.symm | exact e2 | exact e2.symm | exact e3 |
        exact e3.symm | exact e4 | exact e4.symm
  have hC : perfectCore C ≤ ⁅C, C⁆ := by
    rw [← perfectCore_perfect C]
    exact Subgroup.commutator_mono (perfectCore_le C) (perfectCore_le C)
  have hI : ∀ (I : Finset (Fin (2 * 2 + 1))), (I = {0} ∨ I = {1}) →
      ⁅C, C⁆ ≤ blockSpecialLinear (K := F) Iᶜ := by
    intro I hI
    have h := (Subgroup.commutator_mono (hdiag I hI) (hdiag I hI)).trans
      (LinearPilot.commutator_blockDiagSL_le (K := F) I)
    rcases hI with rfl | rfl <;> rwa [blockSpecialLinear_singleton_eq_bot, bot_sup_eq] at h
  intro g hg
  have h0 := mem_blockSpecialLinear.1 (hI _ (Or.inl rfl) (hC hg))
  have h1 := mem_blockSpecialLinear.1 (hI _ (Or.inr rfl) (hC hg))
  have key : ∀ i j : Fin (2 * 2 + 1), (i ∉ oddFixBlock ∨ j ∉ oddFixBlock) →
      (i ∉ ({0} : Finset (Fin (2 * 2 + 1)))ᶜ ∨ j ∉ ({0} : Finset (Fin (2 * 2 + 1)))ᶜ) ∨
        (i ∉ ({1} : Finset (Fin (2 * 2 + 1)))ᶜ ∨ j ∉ ({1} : Finset (Fin (2 * 2 + 1)))ᶜ) := by
    decide
  rw [mem_blockSpecialLinear]
  intro i j hij
  rcases key i j hij with h | h
  · exact h0 i j h
  · exact h1 i j h

omit [Finite F] in
theorem map_tauSp_rootTorusSp_zero : (rootTorusSp F 0).map tauSp = siegelTorus F 2 := by
  ext x
  constructor
  · rintro ⟨_, ⟨κ, rfl⟩, rfl⟩
    refine ⟨κ, ?_⟩
    change diagSp F 2 (fun _ => κ) = tauSp (rootTorusHom F 2 0 κ)
    rw [tauSp_rootTorusHom_zero]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rintro ⟨s, rfl⟩
    refine ⟨rootTorusHom F 2 0 s, ⟨s, rfl⟩, ?_⟩
    change tauSp (rootTorusHom F 2 0 s) = diagSp F 2 (fun _ => s)
    rw [tauSp_rootTorusHom_zero]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem perfectCore_centralizer_oddSiegTorus (hF : 4 ≤ Nat.card F) :
    perfectCore (centralizer (((siegelTorus F 2).map (ctEmbed 1) :
      Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) :
        Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))) =
      blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB := by
  rw [← map_tauSp_rootTorusSp_zero]
  refine le_antisymm (perfectCore_centralizer_oddTwTorus_le hF) (sup_le ?_ ?_)
  · refine le_perfectCore_of_perfect ?_
      (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)
    intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩
    refine (commute_of_mem_blockSpecialLinear_of_diagonal hx
      (coe_ctEmbed_tauSp_rootTorusHom_zero κ) ?_).symm
    intro i hi j hj
    simp only [oddTwA, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl
  · refine le_perfectCore_of_perfect ?_
      (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)
    intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩
    refine (commute_of_mem_blockSpecialLinear_of_diagonal hx
      (coe_ctEmbed_tauSp_rootTorusHom_zero κ) ?_).symm
    intro i hi j hj
    simp only [oddTwB, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl

end Cores

section Pieces

variable {K : Type} [Field K] {F : Type} [Field F]

theorem map_statedSpMap_rootTorusSp_zero (σ : K ≃+* F) :
    ((rootTorusSp K 0).map (MonoidHom.id (StatedSp 2 K))).map (statedSpMap (σ : K →+* F) 2) =
      rootTorusSp F 0 := by
  rw [Subgroup.map_id]
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    exact ⟨Units.map (σ : K →+* F) κ, by rw [statedSpMap_rootTorusHom]⟩
  · rintro ⟨μ, rfl⟩
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    refine ⟨_, rootTorusHom_mem_rootTorusSp 0 κ, ?_⟩
    change statedSpMap (σ : K →+* F) 2 (rootTorusHom K 2 0 κ) = _
    rw [statedSpMap_rootTorusHom, hμ]

theorem map_statedSpMap_siegelTorus (σ : K ≃+* F) :
    ((siegelTorus K 2).map (MonoidHom.id (StatedSp 2 K))).map (statedSpMap (σ : K →+* F) 2) =
      siegelTorus F 2 := by
  rw [Subgroup.map_id]
  ext d
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨Units.map (σ : K →+* F) s, ?_⟩
    change _ = statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => s))
    rw [statedSpMap_diagSp]
    rfl
  · rintro ⟨μ, rfl⟩
    set s : Kˣ := Units.map (σ.symm : F →+* K) μ with hs
    have hμ : Units.map (σ : K →+* F) s = μ := by
      ext
      simp [hs]
    refine ⟨_, ⟨s, rfl⟩, ?_⟩
    change statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => s)) = diagSp F 2 (fun _ => μ)
    rw [statedSpMap_diagSp]
    congr 1
    funext i
    exact hμ

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [Finite F] [CharP F 2]

theorem pieceCore_two_eq_of_oddStd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G)
    (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) = (blockSpecialLinear (K := F) oddFixBlock).map Φ := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_lift hK e (k := 0) (by decide) σ (MonoidHom.id _) Φ hrange hker hN1
    (rootTorusSp K 0) leviTorusSp_two_le_sup map_rootTorusSp_zero_le_leviTorusSp_two
    (by rw [map_statedSpMap_rootTorusSp_zero]; exact perfectCore_centralizer_oddStdTorus hF4)

theorem pieceCore_one_eq_of_oddStd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G)
    (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({1} : Finset (Fin 3)) =
      (blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB).map Φ := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_lift hK e (k := 0) (by decide) σ (MonoidHom.id _) Φ hrange hker hN1
    (siegelTorus K 2) leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one
    (by rw [map_statedSpMap_siegelTorus]; exact perfectCore_centralizer_oddSiegTorus hF4)

theorem pieceCore_zero_eq_of_oddStd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G)
    (hrange : Φ.range = neighbourCore e 2)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 2 x : complSp K 2) : L) : G)) :
    pieceCore e ({0} : Finset (Fin 3)) =
      (blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB).map Φ := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_lift hK e (k := 2) (by decide) σ (MonoidHom.id _) Φ hrange hker hN1
    (siegelTorus K 2) leviTorusSp_zero_le_sup map_siegelTorus_two_le_leviTorusSp_zero
    (by rw [map_statedSpMap_siegelTorus]; exact perfectCore_centralizer_oddSiegTorus hF4)

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
