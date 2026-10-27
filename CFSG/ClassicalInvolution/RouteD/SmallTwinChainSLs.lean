module

public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainAssembly
public import CFSG.ClassicalInvolution.RouteD.SmallTwinSLs
public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL blockSL2
  blockSL2_transvection_up blockSL2_transvection_down)
open scoped MatrixGroups Matrix

section InnerDiag

variable {F : Type} [Field F]

@[expose] def twoOneEnt (μ : Fˣ) (i : Fin (2 + 1)) : Fˣ := if i.val = 2 then μ else 1

theorem innerDiag_three [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (2 + 1)) {X : Type} [Group X] (θ : SL(2 + 1, F) →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(2 + 1, F)) (σ : X ≃* X)
    (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 2 0 A)) =
      θ (blockSL2 F 2 0 A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      ∀ x, σ (θ x) = θ (slConjugation (2 + 1) F (diagGL (twoOneEnt μ)) x) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  obtain ⟨α, g, φ, ε, hαθ, hαmat⟩ := hcl X θ hθ hker σ
  have hαfix : ∀ A : SL(2, F), α (blockSL2 F 2 0 A) = blockSL2 F 2 0 A := by
    intro A
    have := hom_eq_of_central_ker θ hker (L := SL(2, F)) (α.comp (blockSL2 F 2 0))
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
    have hentry : ∀ i : Fin (2 + 1), u i = u 0 * twoOneEnt μ i := by
      intro i
      fin_cases i
      · simp [twoOneEnt]
      · simp [twoOneEnt, hu01]
      · simp [twoOneEnt, hμdef]
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

theorem innerDiag_three_amb [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (2 + 1)) {Y : Type} [Group Y] (θ : SL(2 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(2 + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 2 0 A)) = θ (blockSL2 F 2 0 A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      ∀ x, σ (θ x) = θ (slConjugation (2 + 1) F (diagGL (twoOneEnt μ)) x) := by
  have hQ : θ.range.map σ.toMonoidHom = θ.range :=
    map_eq_of_involutive σ hσ θ.range (by rintro _ ⟨x, rfl⟩; exact hstab x)
  have hcoe : ∀ x, ((θ.rangeRestrict x : θ.range) : Y) = θ x := fun x => rfl
  obtain ⟨μ, hμ, h⟩ := innerDiag_three hodd h5 hcl θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictAut σ θ.range hQ)
    (fun x => Subtype.ext (by simp only [coe_restrictAut]; exact hσ _))
    (fun A => Subtype.ext (by simp only [coe_restrictAut, hcoe]; exact hfix A))
  exact ⟨μ, hμ, fun x => by
    have := congrArg Subtype.val (h x)
    simpa [coe_restrictAut, hcoe] using this⟩

end InnerDiag

section Partner

variable {F : Type} [Field F]

theorem exists_partner_two (h2 : (2 : F) ≠ 0) {R : Subgroup SL(2 + 1, F)} {i : SL(2 + 1, F)}
    (h : IsLongRootSL2 (by omega : 2 ≤ 2 + 1) R i) :
    ∃ (R' : Subgroup SL(2 + 1, F)) (i' : SL(2 + 1, F)),
      IsLongRootSL2 (by omega : 2 ≤ 2 + 1) R' i' ∧
      Commute i i' ∧ i ≠ i' ∧ ¬ Commutes R R' := by
  obtain ⟨g, hR, hi⟩ := h
  let T₀ : Pair (2 + 1) := nodePair 2 0 (by omega)
  let T₁ : Pair (2 + 1) := nodePair 2 1 (by omega)
  have hn : (2 : ℕ) ≤ 2 + 1 := by omega
  have hroot : rootSL2 F hn = Lc F T₀ := by
    rw [rootSL2_eq_longRootGroup h2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]
    rfl
  have hinv : rootInv F hn = zElt F T₀ :=
    Subtype.ext (by rw [coe_rootInv, coe_zElt, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]; rfl)
  have hc : zElt F T₀ * zElt F T₁ = zElt F T₁ * zElt F T₀ :=
    signGroup_comm (zElt_mem_signGroup T₀) (zElt_mem_signGroup T₁)
  have hT : T₀ ≠ T₁ := by
    intro h'
    have := (nodePair_eq_iff (m := 2) (a := 0) (b := 1) (by omega) (by omega)).mp h'
    omega
  refine ⟨(Lc F T₁).map (MulAut.conj g).toMonoidHom, g * zElt F T₁ * g⁻¹,
    (isLongRootSL2_Lc h2 hn T₁).conj g, ?_, ?_, ?_⟩
  · rw [hi, hinv]
    show g * zElt F T₀ * g⁻¹ * (g * zElt F T₁ * g⁻¹) = g * zElt F T₁ * g⁻¹ * (g * zElt F T₀ * g⁻¹)
    calc g * zElt F T₀ * g⁻¹ * (g * zElt F T₁ * g⁻¹) = g * (zElt F T₀ * zElt F T₁) * g⁻¹ := by
          group
      _ = g * (zElt F T₁ * zElt F T₀) * g⁻¹ := by rw [hc]
      _ = g * zElt F T₁ * g⁻¹ * (g * zElt F T₀ * g⁻¹) := by group
  · intro h'
    rw [hi, hinv] at h'
    have h3 : zElt F T₀ = zElt F T₁ := by
      have := congrArg (fun y => g⁻¹ * y * g) h'
      simpa [mul_assoc] using this
    exact hT (zElt_injective h2 h3)
  · rw [hR, hroot]
    intro hcm
    have h4 : Commutes (Lc F T₀) (Lc F T₁) := (commutes_conjSub_iff g).mp hcm
    exact not_commutes_Lc_overlap h2 (by omega : 3 ≤ 2 + 1) (i := ⟨0, by omega⟩)
      (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (by simp) (by simp)
      (by simp) h4

end Partner

section Layer

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx.conjSub_eq_of_commute_roots (c : ACtx p f m Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup SL(m + 1, GaloisField p f)} {i i' : SL(m + 1, GaloisField p f)}
    (hRi : IsLongRootSL2 c.hn R i)
    (hRi' : IsLongRootSL2 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (hcomm : Commute i i') {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    conjSub w L' = L' := by
  have hwY : w ∈ locLayer Ω z := le_centralizingLayer hL hw
  have hψi : c.d.ψ i = locMk Ω z ⟨w, hwY⟩ :=
    psi_root_inv c.hm c.hodd c.d hRi hLR (le_centralizingLayer hL) hw hw2
  have hcm : (i : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *
      (i' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) =
      (i' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *
        (i : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) := by
    have := congrArg (fun x : SL(m + 1, GaloisField p f) =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f))) hcomm
    simpa using this
  have hle : conjSub i R' ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hRi'.eq_longRootGroup c.two_ne_zero] at hy ⊢
    exact conj_mem_longRootGroup_of_commute hcm hy
  have hnormR : conjSub i R' = R' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj i).injective]
  have himg : locImg Ω z (conjSub w L') = locImg Ω z L' := by
    have h := locImg_conjSub_layer (Ω := Ω) (x := z) L' ⟨w, hwY⟩
    rw [show ((⟨w, hwY⟩ : ↥(locLayer Ω z)) : G) = w from rfl] at h
    rw [h, hLR', ← hψi]
    have h' := map_conjSub_hom c.d.ψ i R'
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
  exact locImg_injOn c.hΩ c.hP1 hmem hL' himg

end Layer

section Dichotomy

variable {F : Type} [Field F]

theorem Lc_node_sup_eq_top (h2 : (2 : F) ≠ 0) :
    Lc F (nodePair 2 0 (by omega)) ⊔ Lc F (nodePair 2 1 (by omega)) = ⊤ := by
  have h0 : Lc F (nodePair 2 0 (by omega)) = CFSG.ClassicalInvolution.WeakCT.B12 F :=
    (blockSL2_range_eq_Lc h2 (m := 2) (a := 0) (by omega)).symm
  have h1 : Lc F (nodePair 2 1 (by omega)) = CFSG.ClassicalInvolution.WeakCT.B23 F :=
    (blockSL2_range_eq_Lc h2 (m := 2) (a := 1) (by omega)).symm
  rw [h0, h1]
  exact CFSG.ClassicalInvolution.WeakCT.B12_sup_B23

theorem conj_negOne_block (x : SL(2 + 1, F)) :
    slConjugation (2 + 1) F (diagGL (twoOneEnt (-1)))
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
  fin_cases i <;> fin_cases j <;> simp [twoOneEnt]

end Dichotomy

section LayerDich

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ACtx.layer_dichotomy {J : Subgroup G} {w : G} (c : ACtx p f 2 Ω J w) {K : Subgroup G}
    {z : G} (hK : K ∈ centralizingMembers Ω {w}) (hKJ : K ≠ J) (hz : IsClassicalMember p f K z)
    {t : G} (ht1 : t * w * t⁻¹ = w) (ht2 : t * t = 1)
    (htK : K ≤ Subgroup.centralizer ({t} : Set G)) (htJ : conjSub t J = J) :
    (∀ N ∈ centralizingMembers Ω {w}, N ≠ J → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w}, N ≠ J →
        N ≤ Subgroup.centralizer ({t * z} : Set G)) := by
  have hcl : LinearAutClassification (GaloisField p f) (2 + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification c.hp2 c.hq (by omega)
  obtain ⟨R, i, hRi, hKR, hψi⟩ := c.exists_rootData hK hKJ hz
  obtain ⟨g, hRg, hig⟩ := hRi
  let θ : SL(2 + 1, GaloisField p f) →* locQuot Ω w := c.d.ψ.comp (MulAut.conj g).toMonoidHom
  have hθx : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => rfl
  have hθker : θ.ker ≤ Subgroup.center SL(2 + 1, GaloisField p f) := by
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
    have hN' : conjSub t N ∈ centralizingMembers Ω {w} := by
      have : conjSub t N ∈ centralizingMembers Ω {t * w * t⁻¹} := by
        rw [centralizingMembers_conj c.hΩ.conjInvariant]
        exact ⟨N, hN, rfl⟩
      rwa [ht1] at this
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
    have hsub : ∀ (a : ℕ) (ha : a < 2), Lc (GaloisField p f) (nodePair 2 a ha) ≤
        c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by
      intro a ha y hy
      exact hlayerσ (nd.j a) (nd.mem a ha) (nd.ne_K a ha) _
        (by rw [nd.img a ha]; exact ⟨y, hy, rfl⟩)
    have htop : c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) = ⊤ := by
      rw [eq_top_iff, ← Lc_node_sup_eq_top c.two_ne_zero]
      exact sup_le (hsub 0 (by omega)) (hsub 1 (by omega))
    intro x
    have : x ∈ c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by rw [htop]; trivial
    exact this
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x => by
    obtain ⟨r, hr⟩ := hstabψ (g * x * g⁻¹)
    rw [hθx, ← hr]
    exact hψθ r
  have hfix : ∀ A : SL(2, GaloisField p f), σ (θ (blockSL2 (GaloisField p f) 2 0 A)) =
      θ (blockSL2 (GaloisField p f) 2 0 A) := by
    intro A
    have hmem : θ (blockSL2 (GaloisField p f) 2 0 A) ∈ locImg Ω w K := by
      rw [hKR]
      refine ⟨g * blockSL2 (GaloisField p f) 2 0 A * g⁻¹, ?_, rfl⟩
      rw [hRg]
      exact ⟨blockSL2 (GaloisField p f) 2 0 A, ⟨A, rfl⟩, rfl⟩
    exact ((locAut_fixed_iff c.hΩ c.hP1 ht1 hK).mp htK) _ hmem
  obtain ⟨μ, hμ, hσθ⟩ := innerDiag_three_amb c.hodd c.h5 hcl θ hθker σ hσσ hstab hfix
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
    refine (locAut_fixed_iff c.hΩ c.hP1 ht1 hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    have : slConjugation (2 + 1) (GaloisField p f) (diagGL (twoOneEnt 1)) x = x := by
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      rw [slConjugation_diagGL_apply]
      simp [twoOneEnt]
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
    refine (locAut_fixed_iff c.hΩ c.hP1 htz hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    rw [locAut_mul c.hΩ.conjInvariant ht1 hzw htz, locAut_eq_conj c.hΩ.conjInvariant hzY hzw]
    have hzbar : locMk Ω w ⟨z, hzY⟩ = θ (blockSL2 (GaloisField p f) 2 0 (-1)) := by
      rw [hθx]
      have : g * blockSL2 (GaloisField p f) 2 0 (-1) * g⁻¹ = i := by rw [hig]; rfl
      rw [this]
      exact hψi.symm
    rw [hzbar, ← map_inv, ← map_mul, ← map_mul]
    show σ (θ _) = _
    rw [hσθ, conj_negOne_block]

end LayerDich

section Final

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem localShapeT_of_shapeA {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeA p f 2 Ω x) :
    LocalShapeT p f 1 .PSL 3 Ω x := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  refine ⟨D, by omega, i₁, ht₁, hr₁, fun i hi => ?_⟩
  have hi' : i = i₀ := by
    have h1 := i.isLt
    have h2 := i₀.isLt
    have h3 := i₁.isLt
    have h4 : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have h5 : i.val ≠ i₁.val := fun e => hi (Fin.ext e)
    exact Fin.ext (by omega)
  rw [hi']
  exact ⟨ht₀, hr₀⟩

theorem exists_actx_member (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeA p f 2 Ω z) {J : Subgroup G} {w : G} (hJ : J ∈ Ω)
    (hw : IsClassicalMember p f J w) : Nonempty (ACtx p f 2 Ω J w) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  obtain ⟨g, hg⟩ := hsingle J hJ
  have hw' : w = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex J hJ) hw (hg ▸ hz.conj g)
  subst hw'
  have hshape' : LocalShapeA p f 2 Ω (g * z * g⁻¹) :=
    localShapeA_of_T (LocalShapeT.conj hΩ.conjInvariant g (localShapeT_of_shapeA hshape))
  have hP1' : LocalOddCentral Ω {g * z * g⁻¹} := localOddCentral_conj hΩ.conjInvariant g z hP1
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (m := 2) (by omega) hΩ hJ hw hshape'
  exact ⟨{ hm := le_rfl
           hp2 := hp2
           hq := hq
           hΩ := hΩ
           hex := hex
           hK := hJ
           hz := hw
           hP1 := hP1'
           d := d
           hF := NonClassical.oddCoverSL3 hq
           hlift := Or.inl (by omega) }⟩

theorem chainPieceSLsTwo_of_twinP1A (hP : TwinP1A p f) : ChainPieceSLsTwo p f := by
  intro G _ _ _ hnab K z S hshape
  have hp2 := S.odd
  have hq := S.five
  have hΩ := S.inClass
  have hex := S.exact
  have hsingle := single_class K
  have hK : K ∈ conjClass K := mem_conjClass_self K
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  obtain ⟨c⟩ := exists_actx_member hp2 hq hΩ hex hsingle S.cls S.p1 hshape hK S.cls
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hj₀z := nd.mem 0 (by omega)
  have hj₁z := nd.mem 1 (by omega)
  have hw₀ := nd.isCl 0 (by omega)
  have hw₁ := nd.isCl 1 (by omega)
  have hKj₀ : Commutes K (nd.j 0) := nd.commK 0 (by omega)
  have hKj₁ : Commutes K (nd.j 1) := nd.commK 1 (by omega)
  have hnc : ¬ Commutes (nd.j 0) (nd.j 1) := nd.adj 0 (by omega)
  have hinj : nd.j 0 ≠ nd.j 1 := nd.inj 0 (by omega) 1 (by omega) (by omega)
  have hlayer : ∀ N ∈ conjClass K, Commutes K N → N ≤ nd.j 0 ⊔ nd.j 1 := by
    intro N hN hKN
    have hNz : N ∈ centralizingMembers (conjClass K) {z} :=
      ⟨hN, NonClassical.le_centralizer_of_commutes hKN.symm S.cls.mem⟩
    have hNK : N ≠ K := fun h => not_commutes_self_of_isClassicalMember S.cls (h ▸ hKN)
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    obtain ⟨R, i, hRi, hNR, -⟩ := c.exists_rootData hNz hNK hzN
    refine le_of_locImg_le hΩ c.hP1 hNz (N := nd.j 0 ⊔ nd.j 1) ?_
    rw [hNR, locImg_sup (le_centralizingLayer hj₀z) (le_centralizingLayer hj₁z),
      nd.img 0 (by omega), nd.img 1 (by omega), ← Subgroup.map_sup, Lc_node_sup_eq_top h2]
    exact Subgroup.map_mono le_top
  have hnorm : conjSub (nd.w 0) (nd.j 1) = nd.j 1 :=
    c.conjSub_eq_of_commute_roots hj₀z hj₁z
      (isLongRootSL2_Lc h2 c.hn (nodePair 2 0 (by omega)))
      (isLongRootSL2_Lc h2 c.hn (nodePair 2 1 (by omega))) (nd.img 0 (by omega))
      (nd.img 1 (by omega))
      (signGroup_comm (zElt_mem_signGroup _) (zElt_mem_signGroup _)) hw₀.mem hw₀.orderOf_eq_two
  obtain ⟨c'⟩ := exists_actx_member hp2 hq hΩ hex hsingle S.cls S.p1 hshape hj₁z.1 hw₁
  have hKw₁ : K ∈ centralizingMembers (conjClass K) {nd.w 1} :=
    ⟨hK, NonClassical.le_centralizer_of_commutes hKj₁ hw₁.mem⟩
  have hKj₁' : K ≠ nd.j 1 := (nd.ne_K 1 (by omega)).symm
  obtain ⟨R, i, hRi, hKR, -⟩ := c'.exists_rootData hKw₁ hKj₁' S.cls
  obtain ⟨R', i', hRi', hcomm', hne', hnc'⟩ := exists_partner_two c'.two_ne_zero hRi
  obtain ⟨β, hβ, hβJ, hβR⟩ := exists_member_of_root c'.hm c'.hodd c'.hΩ c'.hK c'.hz c'.hP1 c'.d
    (R := R') ⟨i', hRi'⟩
  obtain ⟨v, hv⟩ := hΩ.classical β hβ.1
  have hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β :=
    c'.stdpair_of_root hKw₁ hβ hRi hRi' hKR hβR hcomm' hne' hnc'
  have hnKβ : ¬ Commutes K β := fun h => hnc' ((c'.commutes_iff_root hKw₁ hβ hRi hKR hβR).mp h)
  have hKβne : K ≠ β := fun h =>
    hne' (c'.rootInv_eq_of_locImg_eq hRi hRi' hKR hβR (congrArg (locImg _ _) h))
  have hvK : conjSub v K = K :=
    c'.conjSub_eq_of_commute_roots hβ hKw₁ hRi' hRi hβR hKR hcomm'.symm hv.mem hv.orderOf_eq_two
  have hP1x := hP G hnab K z S hshape (nd.j 0) hj₀z (nd.ne_K 0 (by omega)) (nd.w 0) hw₀
  obtain ⟨U, hUΩ, hUc, hUp⟩ := exists_twin_chain (PairT := fun A B =>
      ∃ W, LinearBlockStandardPair (GaloisField p f) W A B) hnab hp2 hq hΩ S.conn hex S.ih hsingle
    hK S.cls (fun L hL hLK => commutes_K_of_ne le_rfl hodd hΩ hex hK S.cls S.p1 c.d hL hLK)
    hj₀z.1 hj₁z.1 hw₀ hw₁ (nd.ne_K 0 (by omega)) hinj hKj₀ hKj₁ hnc (nd.wcomm 0 (by omega) 1
      (by omega)) hlayer hnorm
    (fun t ht1 ht2 htK htJ => c'.layer_dichotomy hKw₁ hKj₁' S.cls ht1 ht2 htK htJ) hP1x hβ hβJ
    hv hnKβ hKβne hvK hKβ (nd.pair 0 (by omega))
    (fun hKx hβx hMx hs h => linear_of_chainSign_images hp2 hq hΩ hP1x hKx hβx hMx hs h)
  exact ⟨U, hUΩ, hUc, hUp⟩

end Final

end CFSG.ClassicalInvolution.RouteD
