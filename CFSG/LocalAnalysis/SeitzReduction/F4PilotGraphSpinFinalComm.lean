module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinAgree

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  blockSpecialLinear_mono commute_blockSpecialLinear_of_disjoint)
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

local instance f4PilotGraphSpinFinalCommNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Weyl

variable (K : Type) [Field K]

@[expose] noncomputable def nRefl01 : adjointGroup .F4 K :=
  CFSG.LieType.Chevalley.weylElement .F4 K 0 * CFSG.LieType.Chevalley.weylElement .F4 K 1 *
    CFSG.LieType.Chevalley.weylElement .F4 K 0

theorem coe_nRefl01 :
    (nRefl01 K : ModGL .F4 K) = weylElt .F4 K 0 1 * weylElt .F4 K 1 1 * weylElt .F4 K 0 1 :=
  rfl

variable {K}

theorem nRefl01_conj_rootDiagUnit (b : Fin (Tag.rank .F4) → Kˣ) :
    (nRefl01 K : ModGL .F4 K) * rootDiagUnit .F4 b * (nRefl01 K : ModGL .F4 K)⁻¹ =
      rootDiagUnit .F4 ![(b 1)⁻¹, (b 0)⁻¹, b 0 * b 1 * b 2, b 3] := by
  rw [coe_nRefl01]
  calc weylElt .F4 K 0 1 * weylElt .F4 K 1 1 * weylElt .F4 K 0 1 * rootDiagUnit .F4 b *
        (weylElt .F4 K 0 1 * weylElt .F4 K 1 1 * weylElt .F4 K 0 1)⁻¹ =
      weylElt .F4 K 0 1 * (weylElt .F4 K 1 1 * (weylElt .F4 K 0 1 * rootDiagUnit .F4 b *
        (weylElt .F4 K 0 1)⁻¹) * (weylElt .F4 K 1 1)⁻¹) * (weylElt .F4 K 0 1)⁻¹ := by group
    _ = _ := by
      rw [weylElt_one_mul_rootDiagUnit_mul_inv, weylElt_one_mul_rootDiagUnit_mul_inv,
        weylElt_one_mul_rootDiagUnit_mul_inv]
      congr 1
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> decide
      have h0 := (b 0).ne_zero
      have h1 := (b 1).ne_zero
      rcases hj with rfl | rfl | rfl | rfl <;> refine Units.ext ?_
      · show ((b 0 * b 0 ^ (-2 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ) *
            ((b 0 * b 0 ^ (-2 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ)) ^ (-2 : ℤ) : Kˣ).val =
          ((b 1)⁻¹ : Kˣ).val
        simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val, _root_.zpow_neg, zpow_two]
        field_simp
      · show ((b 1 * b 0 ^ (1 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (-2 : ℤ) *
            ((b 0 * b 0 ^ (-2 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ)) ^ (1 : ℤ) : Kˣ).val =
          ((b 0)⁻¹ : Kˣ).val
        simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val, _root_.zpow_neg, zpow_two]
        field_simp
      · show ((b 2 * b 0 ^ (0 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ) *
            ((b 0 * b 0 ^ (-2 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ)) ^ (0 : ℤ) : Kˣ).val =
          (b 0 * b 1 * b 2 : Kˣ).val
        simp only [Units.val_mul, zpow_one, zpow_zero, mul_one]
        ring
      · show ((b 3 * b 0 ^ (0 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (0 : ℤ) *
            ((b 0 * b 0 ^ (-2 : ℤ)) * (b 1 * b 0 ^ (1 : ℤ)) ^ (1 : ℤ)) ^ (0 : ℤ) : Kˣ).val =
          (b 3).val
        simp only [zpow_zero, mul_one]

theorem map_conj_nRefl01_leviTorus_one :
    (leviTorus K {1}).map (MulAut.conj (nRefl01 K : ModGL .F4 K)).toMonoidHom ≤
      leviTorus K {0} := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hg
  change (nRefl01 K : ModGL .F4 K) * rootDiagUnit .F4 b * (nRefl01 K : ModGL .F4 K)⁻¹ ∈ _
  rw [nRefl01_conj_rootDiagUnit]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [Finset.mem_singleton] at hj
  subst hj
  simp [hb 1 (Finset.mem_singleton_self 1)]

theorem map_conj_nRefl01_leviTorus_three :
    (leviTorus K {3}).map (MulAut.conj (nRefl01 K : ModGL .F4 K)).toMonoidHom ≤
      leviTorus K {3} := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hg
  change (nRefl01 K : ModGL .F4 K) * rootDiagUnit .F4 b * (nRefl01 K : ModGL .F4 K)⁻¹ ∈ _
  rw [nRefl01_conj_rootDiagUnit]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [Finset.mem_singleton] at hj
  subst hj
  simp [hb 3 (Finset.mem_singleton_self 3)]

end Weyl

theorem commute_of_le_map_conj {G : Type*} [Group G] {M₁ M₂ H₁ H₂ : Subgroup G} {m : G}
    (h₁ : M₁ ≤ H₁.map (MulAut.conj m).toMonoidHom) (h₂ : M₂ ≤ H₂.map (MulAut.conj m).toMonoidHom)
    (h : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) : ∀ x ∈ M₁, ∀ y ∈ M₂, Commute x y := by
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := h₁ hx
  obtain ⟨y', hy', rfl⟩ := h₂ hy
  exact (h x' hx' y' hy').map (MulAut.conj m).toMonoidHom

section Conj


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem pieceCore_zero_le_map_conj (e : L ≃* adjointGroup .F4 K) :
    pieceCore e {0} ≤
      (pieceCore e {1}).map (MulAut.conj ((e.symm (nRefl01 K) : L) : G)).toMonoidHom := by
  rw [pieceCore_def, pieceCore_def, map_centralizerPerfectCore, ← modelToG_map_conj]
  exact centralizerPerfectCore_anti (modelToG_mono e map_conj_nRefl01_leviTorus_one)

theorem pieceCore_three_le_map_conj (e : L ≃* adjointGroup .F4 K) :
    pieceCore e {3} ≤
      (pieceCore e {3}).map (MulAut.conj ((e.symm (nRefl01 K) : L) : G)).toMonoidHom := by
  rw [pieceCore_def, map_centralizerPerfectCore, ← modelToG_map_conj]
  exact centralizerPerfectCore_anti (modelToG_mono e map_conj_nRefl01_leviTorus_three)

end Conj

section Model

variable {F : Type} [Field F]

@[expose] noncomputable def lin6Torus3 (A : Subgroup Fˣ) :
    Subgroup (SpecialLinearGroup (Fin 6) F) :=
  (A.prod A).map ((lin6Torus F).comp (sp6ParamT3 F))

theorem mem_lin6Torus3 {A : Subgroup Fˣ} {a b : Fˣ} (ha : a ∈ A) (hb : b ∈ A) :
    lin6Torus F ![a, a, b] ∈ lin6Torus3 A :=
  ⟨(a, b), ⟨ha, hb⟩, by rw [MonoidHom.comp_apply, sp6ParamT3_apply]⟩

theorem map_sp6ToSL6_sp6Torus3 (A : Subgroup Fˣ) :
    (sp6Torus3 A).map (sp6ToSL6 (F := F)) = lin6Torus3 A := by
  rw [sp6Torus3, lin6Torus3, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun p => ?_
  simp only [MonoidHom.comp_apply, sp6ToSL6_sp6Diag]

theorem map_sp6ToSL6_sp6TorusM2 (A : Subgroup Fˣ) :
    (sp6TorusM2 A).map (sp6ToSL6 (F := F)) = linTorusM2 (lin6Torus F) A := by
  rw [sp6TorusM2, linTorusM2, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun p => ?_
  simp only [MonoidHom.comp_apply, sp6ToSL6_sp6Diag]

theorem map_sp6ToSL6_sp6TorusA (A : Subgroup Fˣ) :
    (sp6TorusA A).map (sp6ToSL6 (F := F)) = linTorusA (lin6Torus F) A := by
  rw [sp6TorusA, linTorusA, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun p => ?_
  simp only [MonoidHom.comp_apply, sp6ToSL6_sp6Diag]

theorem isDiagOf_lin6Torus_D (a₀ : Fˣ) :
    IsDiagOf (lin6Torus F ![1, 1, a₀]) (sepValues a₀) ![2, 2, 0, 2, 2, 1] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin6Torus_apply_self]
    fin_cases i <;> simp [sepValues]

theorem isDiagOf_lin6Torus_E (a₀ : Fˣ) :
    IsDiagOf (lin6Torus F ![a₀, a₀, 1]) (sepValues a₀) ![0, 0, 2, 1, 1, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin6Torus_apply_self]
    fin_cases i <;> simp [sepValues]

omit [Field F] in
theorem rigid_lin6Torus3 [Field F] [DecidableEq F] {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A)
    (hsq : a₀ ^ 2 ≠ 1) (x : SpecialLinearGroup (Fin 6) F)
    (hx : ∀ s ∈ lin6Torus3 A, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin 6) F)) :
    x ∈ centralizer (lin6Torus3 A : Set (SpecialLinearGroup (Fin 6) F)) :=
  rigid_of_isDiagOf (fun _ hd => offDiag_of_mem_map_diagTorusSL hd)
    (mem_lin6Torus3 (one_mem A) ha₀) (injective_sepValues hsq) (isDiagOf_lin6Torus_D a₀) 2
    (by decide) 2 (by decide) x hx

variable [Finite F]

theorem perfectCore_centralizer_lin6Torus3 (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (lin6Torus3 A : Set (SpecialLinearGroup (Fin 6) F))) =
      blockSpecialLinear (K := F) ({0, 1} : Finset (Fin 6)) ⊔ blockSpecialLinear {3, 4} := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 6, i ≠ j →
      ¬ (i ∈ ({0, 1} : Finset (Fin 6)) ∧ j ∈ ({0, 1} : Finset (Fin 6))) →
      ¬ (i ∈ ({3, 4} : Finset (Fin 6)) ∧ j ∈ ({3, 4} : Finset (Fin 6))) →
      (![0, 0, 2, 1, 1, 2] : Fin 6 → Fin 3) i ≠ ![0, 0, 2, 1, 1, 2] j ∨
        (![2, 2, 0, 2, 2, 1] : Fin 6 → Fin 3) i ≠ ![2, 2, 0, 2, 2, 1] j := by decide
  have hconst : ∀ (B : Finset (Fin 6)), (B = {0, 1} ∨ B = {3, 4}) →
      ∀ d ∈ (lin6Torus3 A : Set (SpecialLinearGroup (Fin 6) F)), ∀ i ∈ B, ∀ j ∈ B,
        (d : Matrix (Fin 6) (Fin 6) F) i i = (d : Matrix (Fin 6) (Fin 6) F) j j := by
    rintro B hB _ ⟨p, -, rfl⟩ i hi j hj
    rw [MonoidHom.comp_apply, sp6ParamT3_apply, lin6Torus_apply_self, lin6Torus_apply_self]
    rcases hB with rfl | rfl <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj <;>
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp
  exact perfectCore_centralizer_eq_sup_of_two_blocks (by decide) _
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd) (hconst _ (.inl rfl)) (hconst _ (.inr rfl))
    (fun i j hij h₁ h₂ => exists_mem_ne_of_isDiagOf (mem_lin6Torus3 ha₀ (one_mem A))
      (mem_lin6Torus3 (one_mem A) ha₀) hv (isDiagOf_lin6Torus_E a₀) (isDiagOf_lin6Torus_D a₀)
      (key i j hij h₁ h₂))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)

omit [Finite F] in
theorem commute_lin6BlockM2_of_mem_sup {x y : SpecialLinearGroup (Fin 6) F}
    (hx : x ∈ blockSpecialLinear (K := F) lin6BlockM2)
    (hy : y ∈ blockSpecialLinear (K := F) ({0, 1} : Finset (Fin 6)) ⊔ blockSpecialLinear {3, 4}) :
    Commute x y := by
  have h : blockSpecialLinear (K := F) ({0, 1} : Finset (Fin 6)) ⊔ blockSpecialLinear {3, 4} ≤
      centralizer ({x} : Set (SpecialLinearGroup (Fin 6) F)) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact (commute_blockSpecialLinear_of_disjoint (by decide) hz hx).eq
    · exact (commute_blockSpecialLinear_of_disjoint (by decide) hz hx).eq
  exact (mem_centralizer_singleton_iff.1 (h hy)).symm

end Model

section LinearSix


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem pieceCore_eq_map_of_cover (e : L ≃* adjointGroup .F4 K)
    {Ψ : SpecialLinearGroup (Fin 6) K →* G} (hr : Ψ.range = neighbourCore e .X)
    (hk : Ψ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ AmalgamNeighbour.X.nodes) {S : Subgroup (SpecialLinearGroup (Fin 6) K)}
    (hS : leviTorusG e J ⊓ neighbourLeviG e .X = S.map Ψ)
    (hrig : ∀ x : SpecialLinearGroup (Fin 6) K,
      (∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin 6) K)) →
        x ∈ centralizer (S : Set (SpecialLinearGroup (Fin 6) K))) :
    pieceCore e J =
      (perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin 6) K)))).map Ψ := by
  rw [pieceCore_eq e .X hJ]
  change perfectCore (neighbourCore e .X ⊓ centralizer (leviTorusG e J : Set G)) = _
  rw [inf_centralizer_eq_of_sup_eq (leviTorusG_sup_centralizer_eq e hJ), hS, ← hr,
    range_inf_centralizer_map_eq Ψ hk hrig, CFSG.Quasithin.map_perfectCore]

theorem commute_pieceCore_one_three_of_linear6 {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear6) :
    ∀ g ∈ pieceCore e {1}, ∀ g' ∈ pieceCore e {3}, Commute g g' := by
  classical
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a₀, ha₀⟩ := exists_units_sq_ne_one_of_four_le hq
  obtain ⟨ΦA, hrA, hkA, -, hnA⟩ := exists_graphParamA_normalized_X hw hf e hX
  set Θ := graphParamEquiv K (RingEquiv.refl K) with hΘ
  set Ψ : SpecialLinearGroup (Fin 6) K →* G := ΦA.comp Θ.toMonoidHom with hΨ
  have hr : Ψ.range = neighbourCore e .X := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.surjective,
      ← MonoidHom.range_eq_map, hrA]
  have hk : Ψ.ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
    intro x hx
    have h1 : Θ x ∈ center (e6ScLevi K e6A5Nodes) := hkA hx
    rw [← Subgroup.map_center_eq Θ.symm]
    exact ⟨Θ x, h1, Θ.symm_apply_apply x⟩
  have hn : Ψ.comp sp6ToSL6 = levi6Hom e (RingEquiv.refl K) := MonoidHom.ext fun s => hnA s
  have h1 : leviTorusG e {1} ⊓ neighbourLeviG e .X = (linTorusM2 (lin6Torus K) ⊤).map Ψ := by
    rw [← map_levi6Hom_sp6TorusM2 e (RingEquiv.refl K), ← hn, ← Subgroup.map_map,
      map_sp6ToSL6_sp6TorusM2]
  have h3 : leviTorusG e {3} ⊓ neighbourLeviG e .X = (lin6Torus3 ⊤).map Ψ := by
    rw [← map_levi6Hom_sp6Torus3 e (RingEquiv.refl K), ← hn, ← Subgroup.map_map,
      map_sp6ToSL6_sp6Torus3]
  have hM1 := pieceCore_eq_map_of_cover e hr hk (by decide) h1
    (rigid_lin6 (.inr (.inl rfl)) (mem_top a₀) ha₀)
  have hM3 := pieceCore_eq_map_of_cover e hr hk (by decide) h3
    (rigid_lin6Torus3 (mem_top a₀) ha₀)
  rw [perfectCore_centralizer_lin6TorusM2 hq (mem_top a₀) ha₀] at hM1
  rw [perfectCore_centralizer_lin6Torus3 hq (mem_top a₀) ha₀] at hM3
  intro g hg g' hg'
  rw [hM1] at hg
  rw [hM3] at hg'
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨y, hy, rfl⟩ := hg'
  exact (commute_lin6BlockM2_of_mem_sup hx hy).map Ψ

theorem e6RowPieceCommInput_holds : E6RowPieceCommInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  rcases hk with ⟨hX, -⟩ | ⟨-, hY⟩
  · exact commute_of_le_map_conj (pieceCore_zero_le_map_conj e) (pieceCore_three_le_map_conj e)
      (commute_pieceCore_one_three_of_linear6 hw hf e hX)
  · have hc : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    have hX' : HR8Kind (e.trans (graphAutF4 K).symm) t f .X .linear6 := (hr8Kind_Y_iff_X e).1 hY
    have h := commute_of_le_map_conj (pieceCore_zero_le_map_conj _)
      (pieceCore_three_le_map_conj _) (commute_pieceCore_one_three_of_linear6 hw hf _ hX')
    have h0 : pieceCore (e.trans (graphAutF4 K).symm) {0} = pieceCore e {3} := by
      rw [pieceCore_trans_graphAutF4_symm]
      congr 1
    have h3 : pieceCore (e.trans (graphAutF4 K).symm) {3} = pieceCore e {0} :=
      pieceCore_three_trans_graphAutF4_symm e
    intro g hg g' hg'
    rw [← h3] at hg
    rw [← h0] at hg'
    exact (h g' hg' g hg).symm

end LinearSix

end CFSG.SeitzReduction.F4Pilot
