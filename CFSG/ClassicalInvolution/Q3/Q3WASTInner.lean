module

public import CFSG.ClassicalInvolution.Q3.Q3WASTAsm
public import CFSG.ClassicalInvolution.Q3.Q3WASChart3
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WANodes
import CFSG.ClassicalInvolution.RouteD.SmallTwinChainSLs
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL blockSL2
  blockSL2_transvection_up blockSL2_transvection_down)
open scoped MatrixGroups Matrix

section InnerDiag

variable {F : Type} [Field F]

@[expose] def twoOneEnt3 (μ : Fˣ) (i : Fin (2 + 1)) : Fˣ := if i.val = 2 then μ else 1

theorem innerDiag_three3 [Finite F] (hF3 : Nat.card F = 3)
    (hcl : LinearAutClassification F (2 + 1)) {X : Type} [Group X] (θ : SL(2 + 1, F) →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(2 + 1, F)) (σ : X ≃* X)
    (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 2 0 A)) =
      θ (blockSL2 F 2 0 A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      ∀ x, σ (θ x) = θ (slConjugation (2 + 1) F (diagGL (twoOneEnt3 μ)) x) := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP3 : ∀ l : SL(2, F), l ^ 3 ∈ ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ := fun l =>
    pow_three_mem_commutator_of_equiv hF3 (Subgroup.topEquiv (G := SL(2, F))) l trivial
  have hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x := ker_orderOf_not_dvd_three hF3 (by omega) hker
  obtain ⟨α, g, φ, ε, hαθ, hαmat⟩ := hcl X θ hθ hker σ
  have hαfix : ∀ A : SL(2, F), α (blockSL2 F 2 0 A) = blockSL2 F 2 0 A := by
    intro A
    have := hom_eq_of_central_ker3 θ hker hcop hP3 (α.comp (blockSL2 F 2 0))
      (blockSL2 F 2 0) (fun A => by rw [MonoidHom.comp_apply, hαθ, hfix A])
    exact DFunLike.congr_fun this A
  have hne₁ : (0 : Fin 2).castSucc ≠ (0 : Fin 2).succ := Fin.castSucc_lt_succ.ne
  have hne₂ : (0 : Fin 2).succ ≠ (0 : Fin 2).castSucc := Fin.castSucc_lt_succ.ne'
  have hup : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection hne₁ c) =
      Matrix.SpecialLinearGroup.transvection hne₁ c := by
    intro c
    have := hαfix (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
    rwa [blockSL2_transvection_up] at this
  have hdown : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection hne₂ c) =
      Matrix.SpecialLinearGroup.transvection hne₂ c := by
    intro c
    have := hαfix (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)
    rwa [blockSL2_transvection_down] at this
  have hPn : Group.IsPerfect SL(2 + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hdet0 : ∀ g' : GL (Fin (2 + 1)) F, (g' : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F).det ≠ 0 :=
    fun g' => det_ne_zero_of_gl g'
  cases ε
  ·
    simp only [Bool.false_eq_true, ↓reduceIte] at hαmat
    obtain ⟨hφ, hc1⟩ := fixed_transvection_false α g φ hαmat _ hup
    have hc2 := (fixed_transvection_false α g φ hαmat _ hdown).2
    obtain ⟨h00, hcol0, hcol1, hrow0, hrow1⟩ := block_of_commute_single _ hc1 hc2
    have hoff : ∀ i j : Fin (2 + 1), i ≠ j →
        (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact hrow0 1 (by decide)
      · exact hrow0 2 (by decide)
      · exact hcol0 1 (by decide)
      · exact hrow1 2 (by decide)
      · exact hcol0 2 (by decide)
      · exact hcol1 2 (by decide)
    obtain ⟨u, rfl⟩ := exists_diagGL_of_offdiag_zero g hoff
    have hu01 : u 0 = u 1 := by
      have := h00
      rw [coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
      exact Units.ext this
    have hαconj : ∀ x, α x = slConjugation (2 + 1) F (diagGL u) x := by
      intro x
      refine Subtype.ext ?_
      rw [hαmat x, slConjugation_matrix]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    have hsq : ∀ x : SL(2 + 1, F), slConjugation (2 + 1) F (diagGL u)
        (slConjugation (2 + 1) F (diagGL u) x) = x := by
      have := hom_eq_of_central_ker θ hker (L := SL(2 + 1, F))
        ((slConjugation (2 + 1) F (diagGL u)).toMonoidHom.comp
          (slConjugation (2 + 1) F (diagGL u)).toMonoidHom) (MonoidHom.id _)
        (fun x => by
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
          rw [← hαconj, ← hαconj, hαθ, hαθ, hσ])
      intro x
      exact DFunLike.congr_fun this x
    have hsqe := sq_eq_of_conj_sq u (i := 2) (j := 0) (by decide) hsq
    set μ : Fˣ := u 2 * (u 0)⁻¹ with hμdef
    have hμ : μ = 1 ∨ μ = -1 := by
      have h1' : (μ : F) * (μ : F) = 1 := by
        have hu1 : ((u 0 : Fˣ) : F) ≠ 0 := (u 0).ne_zero
        rw [hμdef, Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
        linear_combination hsqe
      rcases mul_self_eq_one_iff.mp h1' with h3 | h3
      · exact Or.inl (Units.ext h3)
      · exact Or.inr (Units.ext (by rw [Units.val_neg]; exact h3))
    have hentry : ∀ i : Fin (2 + 1), u i = u 0 * twoOneEnt3 μ i := by
      intro i
      fin_cases i
      · simp [twoOneEnt3]
      · simp [twoOneEnt3, hu01]
      · simp [twoOneEnt3, hμdef]
    refine ⟨μ, hμ, fun x => ?_⟩
    rw [← hαθ, hαconj]
    congr 1
    exact slConjugation_diagGL_congr u _ (u 0) hentry x
  ·
    exfalso
    simp only [↓reduceIte] at hαmat
    obtain ⟨hφ, h1⟩ := fixed_transvection_true α g φ hαmat _ hup
    obtain ⟨-, h2'⟩ := fixed_transvection_true α g φ hαmat _ hdown
    have hαmat' : ∀ x, ((α x : SL(2 + 1, F)) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) =
        (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) * (((x⁻¹ : SL(2 + 1, F)) :
          Matrix (Fin (2 + 1)) (Fin (2 + 1)) F))ᵀ *
          ((g⁻¹ : GL (Fin (2 + 1)) F) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) := by
      intro x
      rw [hαmat x]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    obtain ⟨-, -, hcol, -, hij⟩ := block_of_graph_commute _ h1 h2'
    have hsq : ∀ x, α (α x) = x := by
      intro x
      have := hom_eq_of_central_ker θ hker (L := SL(2 + 1, F)) (α.comp α) (MonoidHom.id _)
        (fun x => by rw [MonoidHom.comp_apply, hαθ, hαθ, hσ]; rfl)
      exact DFunLike.congr_fun this x
    obtain ⟨c, hgc⟩ := exists_eq_smul_transpose (n := 2 + 1) (by omega) α g hαmat' hsq
    have hskew := eq_neg_transpose_of_graph_block g c hgc hcol hij
    apply hdet0 g
    have h1' := congrArg Matrix.det hskew
    rw [Matrix.det_neg, Matrix.det_transpose] at h1'
    simp only [Fintype.card_fin] at h1'
    have h6 : (2 : F) * (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F).det = 0 := by
      linear_combination h1'
    rcases mul_eq_zero.mp h6 with h7 | h7
    · exact absurd h7 h2
    · exact h7

theorem innerDiag_three_amb3 [Finite F] (hF3 : Nat.card F = 3)
    (hcl : LinearAutClassification F (2 + 1)) {Y : Type} [Group Y] (θ : SL(2 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(2 + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 2 0 A)) = θ (blockSL2 F 2 0 A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      ∀ x, σ (θ x) = θ (slConjugation (2 + 1) F (diagGL (twoOneEnt3 μ)) x) := by
  have hQ : θ.range.map σ.toMonoidHom = θ.range :=
    map_eq_of_involutive σ hσ θ.range (by rintro _ ⟨x, rfl⟩; exact hstab x)
  have hcoe : ∀ x, ((θ.rangeRestrict x : θ.range) : Y) = θ x := fun x => rfl
  obtain ⟨μ, hμ, h⟩ := innerDiag_three3 hF3 hcl θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictAut σ θ.range hQ)
    (fun x => Subtype.ext (by simp only [coe_restrictAut]; exact hσ _))
    (fun A => Subtype.ext (by simp only [coe_restrictAut, hcoe]; exact hfix A))
  exact ⟨μ, hμ, fun x => by
    have := congrArg Subtype.val (h x)
    simpa [coe_restrictAut, hcoe] using this⟩

end InnerDiag

section Partner

variable {F : Type} [Field F]

theorem exists_partner_two3 (h2 : (2 : F) ≠ 0) {R : Subgroup SL(2 + 1, F)} {i : SL(2 + 1, F)}
    (h : IsLongRootSL2 (by omega : 2 ≤ 2 + 1) R i) :
    ∃ (R' : Subgroup SL(2 + 1, F)) (i' : SL(2 + 1, F)),
      IsLongRootSL2 (by omega : 2 ≤ 2 + 1) R' i' ∧
      Commute i i' ∧ i ≠ i' ∧ ¬ Commutes R R' :=
  CFSG.ClassicalInvolution.RouteD.exists_partner_two h2 h

end Partner

section Layer

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.conjSub_eq_of_commute_roots (c : ACtx3 m Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup SL(m + 1, GaloisField 3 1)} {i i' : SL(m + 1, GaloisField 3 1)}
    (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (hcomm : Commute i i') {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    conjSub w L' = L' := by
  have hwY : w ∈ locLayer Ω z := le_centralizingLayer hL hw
  have hψi : c.d.ψ i = locMk Ω z ⟨w, hwY⟩ :=
    psi_root_inv c.hm odd_gf3 c.d hRi hLR (le_centralizingLayer hL) hw hw2
  have hcm : (i : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 3 1)) *
      (i' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 3 1)) =
      (i' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 3 1)) *
        (i : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 3 1)) := by
    have := congrArg (fun x : SL(m + 1, GaloisField 3 1) =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 3 1))) hcomm
    simpa using this
  have hle : conjSub i R' ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hRi'.eq_longRootGroup two_ne_zero_gf3] at hy ⊢
    exact conj_mem_longRootGroup_of_commute hcm hy
  have hnormR : conjSub i R' = R' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj i).injective]
  have himg : locImg Ω z (conjSub w L') = locImg Ω z L' := by
    have h := locImg_conjSub_layer (Ω := Ω) (x := z) L' ⟨w, hwY⟩
    rw [show ((⟨w, hwY⟩ : ↥(locLayer Ω z)) : G) = w from rfl] at h
    rw [h, hLR', ← hψi]
    have h' := map_conjSub_hom3 c.d.ψ i R'
    rw [hnormR] at h'
    exact h'.symm
  have hmem : conjSub w L' ∈ centralizingMembers Ω {z} := by
    refine ⟨c.hΩ.conjInvariant w L' hL'.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL'.2 ha
    have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := hL.2 hw
    have : a = w * (w⁻¹ * a * w) * w⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hwC hx') (inv_mem hwC)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hmem hL' himg

end Layer

section Dichotomy

variable {F : Type} [Field F]

theorem Lc_node_sup_eq_top3 (h2 : (2 : F) ≠ 0) :
    Lc F (nodePair 2 0 (by omega)) ⊔ Lc F (nodePair 2 1 (by omega)) = ⊤ := by
  have h0 : Lc F (nodePair 2 0 (by omega)) = CFSG.ClassicalInvolution.WeakCT.B12 F :=
    (blockSL2_range_eq_Lc h2 (m := 2) (a := 0) (by omega)).symm
  have h1 : Lc F (nodePair 2 1 (by omega)) = CFSG.ClassicalInvolution.WeakCT.B23 F :=
    (blockSL2_range_eq_Lc h2 (m := 2) (a := 1) (by omega)).symm
  rw [h0, h1]
  exact CFSG.ClassicalInvolution.WeakCT.B12_sup_B23

theorem conj_negOne_block3 (x : SL(2 + 1, F)) :
    slConjugation (2 + 1) F (diagGL (twoOneEnt3 (-1)))
      (blockSL2 F 2 0 (-1) * x * (blockSL2 F 2 0 (-1))⁻¹) = x := by
  have hr : (blockSL2 F 2 0 (-1))⁻¹ = blockSL2 F 2 0 (-1) := by
    rw [← map_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right (by simp)
  rw [hr]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  have hc : ((blockSL2 F 2 0 (-1) : SL(2 + 1, F)) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) =
      Matrix.diagonal (fun a : Fin (2 + 1) => if a.val < 2 then (-1 : F) else 1) := by
    rw [show blockSL2 F 2 0 (-1) = blockSL F (2 + 1) 2 0 (by omega) (-1) from rfl,
      coe_blockSL_neg_one (by omega), negBlock_eq_diagonal]
    congr 1
    funext a
    simp
  rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [twoOneEnt3]

end Dichotomy

section LeLocImg

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_of_locImg_le3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {L N : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (h : locImg Ω x L ≤ locImg Ω x N) : L ≤ N := by
  obtain ⟨z₀, hz₀⟩ := hΩ.classical L hL.1
  obtain ⟨eL⟩ := hz₀.nonempty_equiv_sl2 (hex L hL.1)
  have hle : L ≤ locLayer Ω x := le_centralizingLayer hL
  have hpow : Pow3 (L.subgroupOf (locLayer Ω x)) := by
    intro l hl
    exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp)
      ((Subgroup.subgroupOfEquivOfLe hle).trans eL) l hl
  have hker0 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).ker ≤
      Subgroup.center ↥(locLayer Ω x) := by
    rw [QuotientGroup.ker_mk']
    exact hP1
  have hcop : ∀ n ∈ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).ker,
      ¬ 3 ∣ orderOf n := by
    intro n hn h3
    rw [QuotientGroup.ker_mk'] at hn
    have h1 : orderOf (⟨n, hn⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) ∣
        Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hO3 (h3.trans h1)
  unfold locImg at h
  have h1 := le_of_map_le_of_pow3 _ hker0 hcop hpow h
  intro l hl
  exact Subgroup.mem_subgroupOf.mp
    (h1 (Subgroup.mem_subgroupOf.mpr hl : (⟨l, hle hl⟩ : ↥(locLayer Ω x)) ∈
      L.subgroupOf (locLayer Ω x)))

end LeLocImg


section Member

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_lieSystemData_congr_kind3 {ι X X' : Type} [Group X] [Group X']
    {Φ : Set (Subgroup X)} {Φ' : Set (Subgroup X')} (e : X ≃* X')
    (hΦ : Subgroup.map e.toMonoidHom '' Φ = Φ') (D : LieSystemData3 ι X Φ) :
    ∃ D' : LieSystemData3 ι X' Φ', D'.kind = D.kind := by
  subst hΦ
  refine ⟨{ kind := D.kind
            valid := D.valid
            hom := fun i => e.toMonoidHom.comp (D.hom i)
            ker_le_center := fun i x hx => ?_
            commute := fun i j h x y => ?_
            generate := ?_
            fundamental := ?_
            meets := fun i => ?_
            card_eq := ?_ }, rfl⟩
  · have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  · have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  · obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩
  · rintro _ ⟨L, hL, rfl⟩
    rw [← D.card_eq L hL]
    exact Nat.card_congr (L.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm

theorem LocalShapeC3.conjShape3 {a : ℕ} {c : CompData} {x : G} (hΩ : ConjInvariant Ω) (g : G)
    (h : LocalShapeC3 a c Ω x) : LocalShapeC3 a c Ω (g * x * g⁻¹) := by
  obtain ⟨ι, hι, D, hcard, i₁, hi₁, hrest⟩ := h
  obtain ⟨D', hD'⟩ := exists_lieSystemData_congr_kind3 (locQuotConj hΩ g x)
    (Gaps.locFamily_conj hΩ g x) D
  refine ⟨ι, hι, D', hcard, i₁, ?_, fun i hi => ?_⟩
  · rw [hD']
    exact hi₁
  · rw [hD']
    exact hrest i hi

theorem exists_actx3_member (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K : Subgroup G}
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember3 K z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (hshape : LocalShapeC3 1 (CompData.model .PSL (2 + 1)) Ω z) {J : Subgroup G} {w : G}
    (hJ : J ∈ Ω) (hw : IsClassicalMember3 J w) : Nonempty (ACtx3 2 Ω J w) := by
  obtain ⟨g, hg⟩ := hsingle J hJ
  have hw' : w = g * z * g⁻¹ := involution_unique3 hw (hg ▸ hz.conj g)
  subst hw'
  have hshape' := hshape.conjShape3 hΩ.conjInvariant g
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (m := 2) (by omega) hΩ hJ hw hshape'
  exact ⟨{ hm := le_rfl
           hΩ := hΩ
           hex := hex
           hK := hJ
           hz := hw
           hP1 := localOddCentral_conj hΩ.conjInvariant g z hP1
           hO3 := localOddThreeFree3_conj hΩ.conjInvariant g z hO3
           d := d
           hlift := Or.inl (by omega) }⟩

end Member

section LayerDich

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ACtx3.layer_dichotomy {J : Subgroup G} {w : G} (c : ACtx3 2 Ω J w) {K : Subgroup G}
    {z : G} (hK : K ∈ centralizingMembers Ω {w}) (hKJ : K ≠ J) (hz : IsClassicalMember3 K z)
    {t : G} (ht1 : t * w * t⁻¹ = w) (ht2 : t * t = 1)
    (htK : K ≤ Subgroup.centralizer ({t} : Set G)) (htJ : conjSub t J = J) :
    (∀ N ∈ centralizingMembers Ω {w}, N ≠ J → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w}, N ≠ J →
        N ≤ Subgroup.centralizer ({t * z} : Set G)) := by
  have hcl : LinearAutClassification (GaloisField 3 1) (2 + 1) :=
    linearAutClassification3 (by omega)
  obtain ⟨R, i, hRi, hKR, hψi⟩ := c.exists_rootData hK hKJ hz
  obtain ⟨g, hRg, hig⟩ := hRi
  let θ : SL(2 + 1, GaloisField 3 1) →* locQuot Ω w :=
    c.d.ψ.comp (MulAut.conj g).toMonoidHom
  have hθx : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => rfl
  have hθker : θ.ker ≤ Subgroup.center SL(2 + 1, GaloisField 3 1) := by
    intro x hx
    have hc := c.d.ker_le (show g * x * g⁻¹ ∈ c.d.ψ.ker from hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have h1 := hc (g * y * g⁻¹)
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    have := congrArg (fun u => g⁻¹ * u * g) h2
    simpa [mul_assoc] using this
  have hψθ : ∀ r, c.d.ψ r ∈ θ.range := fun r =>
    ⟨g⁻¹ * r * g, by rw [hθx]; congr 1; group⟩
  let σ := locAut c.hΩ.conjInvariant ht1
  have hσσ : ∀ a, σ (σ a) = a := locAut_locAut c.hΩ.conjInvariant ht1 ht2
  have hlayerσ : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N,
      σ a ∈ c.d.ψ.range := by
    intro N hN hNJ a ha
    have h1 : σ a ∈ locImg Ω w (conjSub t N) := by
      rw [← locAut_locImg c.hΩ.conjInvariant ht1 N]
      exact ⟨a, ha, rfl⟩
    have hN' : conjSub t N ∈ centralizingMembers Ω {w} :=
      conjSub_mem_centralizingMembers3 c.hΩ.conjInvariant ht1 hN
    have hN'J : conjSub t N ≠ J := by
      intro h
      apply hNJ
      apply conjSub_injective t
      rw [h, htJ]
    obtain ⟨zN, hzN⟩ := c.hΩ.classical _ hN'.1
    obtain ⟨R'', i'', -, hR'', -⟩ := c.exists_rootData hN' hN'J hzN
    rw [hR''] at h1
    obtain ⟨r, -, hr⟩ := h1
    exact ⟨r, hr⟩
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hstabψ : ∀ x, σ (c.d.ψ x) ∈ c.d.ψ.range := by
    have hsub : ∀ (a : ℕ) (ha : a < 2), Lc (GaloisField 3 1) (nodePair 2 a ha) ≤
        c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by
      intro a ha y hy
      exact hlayerσ (nd.j a) (nd.mem a ha) (nd.ne_K a ha) _
        (by rw [nd.img a ha]; exact ⟨y, hy, rfl⟩)
    have htop : c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) = ⊤ := by
      rw [eq_top_iff, ← Lc_node_sup_eq_top3 two_ne_zero_gf3]
      exact sup_le (hsub 0 (by omega)) (hsub 1 (by omega))
    intro x
    have : x ∈ c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by rw [htop]; trivial
    exact this
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x => by
    obtain ⟨r, hr⟩ := hstabψ (g * x * g⁻¹)
    rw [hθx, ← hr]
    exact hψθ r
  have hfix : ∀ A : SL(2, GaloisField 3 1), σ (θ (blockSL2 (GaloisField 3 1) 2 0 A)) =
      θ (blockSL2 (GaloisField 3 1) 2 0 A) := by
    intro A
    have hmem : θ (blockSL2 (GaloisField 3 1) 2 0 A) ∈ locImg Ω w K := by
      rw [hKR]
      refine ⟨g * blockSL2 (GaloisField 3 1) 2 0 A * g⁻¹, ?_, rfl⟩
      rw [hRg]
      exact ⟨blockSL2 (GaloisField 3 1) 2 0 A, ⟨A, rfl⟩, rfl⟩
    exact ((locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hK).mp htK) _ hmem
  obtain ⟨μ, hμ, hσθ⟩ := innerDiag_three_amb3 card_gf3 hcl θ hθker σ hσσ hstab hfix
  have hlocal : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N, ∃ x, a = θ x := by
    intro N hN hNJ a ha
    obtain ⟨zN, hzN⟩ := c.hΩ.classical N hN.1
    obtain ⟨R', i', -, hR', -⟩ := c.exists_rootData hN hNJ hzN
    rw [hR'] at ha
    obtain ⟨r, -, rfl⟩ := ha
    obtain ⟨x, hx⟩ := hψθ r
    exact ⟨x, hx.symm⟩
  rcases hμ with rfl | rfl
  · left
    intro N hN hNJ
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    have : slConjugation (2 + 1) (GaloisField 3 1) (diagGL (twoOneEnt3 1)) x = x := by
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      rw [slConjugation_diagGL_apply]
      simp [twoOneEnt3]
    exact (hσθ x).trans (by rw [this])
  · right
    intro N hN hNJ
    have hzY : z ∈ locLayer Ω w := le_centralizingLayer hK hz.mem
    have hzw : z * w * z⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hK.2 hz.mem)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have htz : (t * z) * w * (t * z)⁻¹ = w := by
      calc (t * z) * w * (t * z)⁻¹ = t * (z * w * z⁻¹) * t⁻¹ := by group
        _ = w := by rw [hzw, ht1]
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    rw [locAut_mul3 c.hΩ.conjInvariant ht1 hzw htz, locAut_eq_conj3 c.hΩ.conjInvariant hzY hzw]
    have hzbar : locMk Ω w ⟨z, hzY⟩ = θ (blockSL2 (GaloisField 3 1) 2 0 (-1)) := by
      rw [hθx]
      have : g * blockSL2 (GaloisField 3 1) 2 0 (-1) * g⁻¹ = i := by rw [hig]; rfl
      rw [this]
      exact hψi.symm
    rw [hzbar, ← map_inv, ← map_mul, ← map_mul]
    show σ (θ _) = _
    rw [hσθ, conj_negOne_block3]

end LayerDich

end CFSG.ClassicalInvolution.Q3.Q3W
