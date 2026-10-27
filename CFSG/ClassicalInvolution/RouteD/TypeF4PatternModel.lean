module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPlane
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.ClassicalInvolution.RouteD.GapsAut

public section

namespace CFSG.ClassicalInvolution.RouteD.SpAdapt

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LieType.Steinberg.Sp (blockMat blockMat_injective blockMat_mul)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation conjAut_mul_fieldAut_mul_self
    conjAut_mul_fieldAut_eq_one_iff)
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.RouteD (le_of_perfect_of_le_sup_center)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mat6_eq_of_basis {M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (h : ∀ c, M *ᵥ Pi.single c 1 = N *ᵥ Pi.single c 1) : M = N := by
  ext r c
  have := congrFun (h c) r
  simpa [Matrix.mulVec_single_one] using this

theorem diag_mul_shortBlock {i j : Fin 3} (hij : i ≠ j) (S : SL(2, F)) :
    Matrix.diagonal (sgn F) * mat 3 F (shortBlock F hij S) =
      mat 3 F (shortBlock F hij S) * Matrix.diagonal (sgn F) := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mat_shortBlock]
  rcases r with r | r <;> rcases c with c | c <;> simp [sgn]

theorem diag_mulVec_single (c : Fin 3 ⊕ Fin 3) :
    (Matrix.diagonal (sgn F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ Pi.single c 1 =
      sgn F c • Pi.single c 1 := by
  funext a
  rw [Matrix.mulVec_diagonal]
  by_cases h : a = c
  · subst h; simp
  · simp [h]

theorem exists_g_of_frame {Am Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hBA : Bm * Am = 1) {κ : F} (h : EigData Am κ)
    {u w : Fin 3 → Fin 3 ⊕ Fin 3 → F} (hfr : IsPlaneFrame u w)
    (hu : ∀ k, Am *ᵥ u k = κ • u k) (hw : ∀ k, Am *ᵥ w k = (-κ) • w k)
    (hu2 : IsPV (u 2)) (hw2 : IsPV (w 2)) :
    ∃ g : StatedSp 3 F, (longBlock F 3 2).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F 3 2).range ∧
      ∀ (i j : Fin 3) (hij : i ≠ j) (S : SL(2, F)),
        Am * mat 3 F (g * shortBlock F hij S * g⁻¹) * Bm =
          mat 3 F (g * shortBlock F hij S * g⁻¹) := by
  obtain ⟨g, hg⟩ := hfr.exists_sp_apply
  refine ⟨g, ?_, ?_⟩
  ·
    have hform : form (u 2) (w 2) = 1 := by simpa using hfr.pair 2 2
    have hle : Submodule.span F {u 2, w 2} ≤ stdPlane F 3 2 := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact (mem_stdPlane_iff 2).2 hu2
      · exact (mem_stdPlane_iff 2).2 hw2
    have hspan : Submodule.span F {u 2, w 2} = stdPlane F 3 2 := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [finrank_span_pair hform]
      exact (finrank_span_pair (form_single_inl_inr (K := F) (2 : Fin 3))).symm
    have h1 := planeGroup_span_conj g (Pi.single (Sum.inl 2) (1 : F)) (Pi.single (Sum.inr 2) 1)
    rw [(hg 2).1, (hg 2).2, hspan] at h1
    have h2 : stdPlane F 3 2 =
        Submodule.span F {Pi.single (Sum.inl 2) (1 : F), Pi.single (Sum.inr 2) 1} := rfl
    have hL : planeGroup (stdPlane F 3 2) = (longBlock F 3 2).range := planeGroup_stdPlane 2
    rw [← hL]
    rw [← h2] at h1
    exact h1.symm
  · intro i j hij S
    obtain ⟨Mg, hMg⟩ : ∃ M, M = mat 3 F g := ⟨_, rfl⟩
    obtain ⟨Mi, hMi⟩ : ∃ M, M = mat 3 F g⁻¹ := ⟨_, rfl⟩
    simp only [← hMg] at hg
    have hMM : Mi * Mg = 1 := by rw [hMi, hMg, ← map_mul, inv_mul_cancel, map_one]
    have hMM' : Mg * Mi = 1 := by rw [hMi, hMg, ← map_mul, mul_inv_cancel, map_one]
    obtain ⟨Dm, hDm⟩ : ∃ D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
        D = Matrix.diagonal (sgn F) := ⟨_, rfl⟩
    have hDD : Dm * Dm = 1 := by
      rw [hDm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rcases a with a | a <;> simp [sgn]
    have hAMg : Am * Mg = κ • (Mg * Dm) := by
      apply mat6_eq_of_basis
      intro c
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDm,
        diag_mulVec_single]
      rcases c with k | k
      · rw [(hg k).1, sgn_inl, one_smul, (hg k).1, hu k]
      · rw [(hg k).2, sgn_inr, Matrix.mulVec_smul, (hg k).2, hw k]
        simp
    have hA : Am = κ • (Mg * Dm * Mi) := by
      calc Am = Am * (Mg * Mi) := by rw [hMM', Matrix.mul_one]
        _ = (Am * Mg) * Mi := by rw [Matrix.mul_assoc]
        _ = κ • (Mg * Dm * Mi) := by rw [hAMg, Matrix.smul_mul]
    have hB : Bm = κ⁻¹ • (Mg * Dm * Mi) := by
      have h1 : (κ ^ 2)⁻¹ • (Am * Am) = 1 := by
        rw [h.sq, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 h.ne), one_smul]
      have h2 : Bm = (κ ^ 2)⁻¹ • Am := by
        calc Bm = Bm * ((κ ^ 2)⁻¹ • (Am * Am)) := by rw [h1, Matrix.mul_one]
          _ = (κ ^ 2)⁻¹ • ((Bm * Am) * Am) := by rw [Matrix.mul_smul, ← Matrix.mul_assoc]
          _ = (κ ^ 2)⁻¹ • Am := by rw [hBA, Matrix.one_mul]
      rw [h2, hA, smul_smul]
      congr 1
      field_simp [h.ne]
    have hmat : mat 3 F (g * shortBlock F hij S * g⁻¹) =
        Mg * mat 3 F (shortBlock F hij S) * Mi := by rw [map_mul, map_mul, hMg, hMi]
    have hDS : Dm * mat 3 F (shortBlock F hij S) = mat 3 F (shortBlock F hij S) * Dm := by
      rw [hDm]; exact diag_mul_shortBlock hij S
    rw [hmat, hA, hB]
    obtain ⟨Ssh, hSsh⟩ : ∃ M, M = mat 3 F (shortBlock F hij S) := ⟨_, rfl⟩
    rw [← hSsh] at hDS ⊢
    calc κ • (Mg * Dm * Mi) * (Mg * Ssh * Mi) * (κ⁻¹ • (Mg * Dm * Mi))
        = (κ⁻¹ * κ) • (Mg * Dm * (Mi * Mg) * Ssh * (Mi * Mg) * Dm * Mi) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = Mg * (Dm * Ssh * Dm) * Mi := by
          rw [hMM, inv_mul_cancel₀ h.ne, one_smul]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Mg * Ssh * Mi := by
          rw [hDS, Matrix.mul_assoc Ssh Dm Dm, hDD, Matrix.mul_one]

theorem exists_semilinear_lift3 [Finite F] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] (ψ : StatedSp 3 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (hstab : ∀ x, τ (ψ x) ∈ ψ.range) :
    ∃ (A : gsp 3 F) (σ : F ≃+* F), ∀ x : StatedSp 3 F,
      τ (ψ x) = ψ (conjSp 3 F A (fieldSp 3 F σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 3 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hmem : ∀ y : X, y ∈ ψ.range → τ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  let τC : ψ.range ≃* ψ.range :=
    { toFun := fun y => ⟨τ y, hmem y y.2⟩
      invFun := fun y => ⟨τ y, hmem y y.2⟩
      left_inv := fun y => Subtype.ext (hτ y)
      right_inv := fun y => Subtype.ext (hτ y)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : X) (b : X)) }
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 3 F) (proj_surjective)
    (CFSG.ClassicalInvolution.RouteD.ker_proj_eq_center 3) (θ := ψ.rangeRestrict)
    ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) τC
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 3) hodd
    (by norm_num)
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 3 F →* StatedSp 3 F :=
    (conjSp 3 F A).toMonoidHom.comp (fieldSp 3 F σ).toMonoidHom
  have hα : ∀ x, proj 3 F (α x) = β (proj 3 F x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have := congrArg Subtype.val (hβ α hα x)
  exact this.symm

theorem form_mulVec_of_sim {n : ℕ} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {m : F}
    (h : Mᵀ * gram F n * M = m • gram F n) (u v : Fin n ⊕ Fin n → F) :
    form (M *ᵥ u) (M *ᵥ v) = m * form u v := by
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h, Matrix.smul_mulVec, dotProduct_smul]
  rfl

theorem mat_conjSp_fieldSp {r : ℕ} (A : gsp r F) (σ : F ≃+* F) (x : StatedSp r F) :
    mat r F (conjSp r F A (fieldSp r F σ x)) =
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) * (mat r F x).map σ *
        (((A : GL (Fin r ⊕ Fin r) F)⁻¹ : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, mat_apply]

theorem map_blockMat {r : ℕ} (σ : F ≃+* F) (k : Fin r) (S : Matrix (Fin 2) (Fin 2) F) :
    (blockMat (Sum.inl k) (Sum.inr k) S : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).map σ =
      blockMat (Sum.inl k) (Sum.inr k) (S.map σ) := by
  ext a b
  simp only [Matrix.map_apply, blockMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp [*]

theorem range_le_commutator_aux {L H : Type*} [Group L] [Group H] [Group.IsPerfect L]
    (f : L →* H) : f.range ≤ ⁅f.range, f.range⁆ := by
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top
  have h : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  exact h.ge

theorem eq_top_of_normal_of_not_le_center3 (h4 : 4 ≤ Nat.card F)
    {N : Subgroup (StatedSp 3 F)} [N.Normal] (hN : ¬ N ≤ Subgroup.center (StatedSp 3 F)) :
    N = ⊤ := by
  classical
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 3 F (by norm_num)
    (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedSp 3 F) := hq.1
  have hsimple : IsSimpleGroup (StatedSp 3 F ⧸ Subgroup.center (StatedSp 3 F)) := hq.2.1
  set Z : Subgroup (StatedSp 3 F) := Subgroup.center (StatedSp 3 F) with hZ
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hN
    intro n hn
    have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · have hsup : (⊤ : Subgroup (StatedSp 3 F)) ≤ N ⊔ Z := by
      intro g _
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hmem : n⁻¹ * g ∈ Z := QuotientGroup.eq.mp hng
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hmem)
    have htop : (⊤ : Subgroup (StatedSp 3 F)) ≤ ⁅(⊤ : Subgroup (StatedSp 3 F)), ⊤⁆ :=
      (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (StatedSp 3 F)))).ge
    exact eq_top_iff.2 (le_of_perfect_of_le_sup_center le_rfl htop hsup)

theorem comp_longBlock_injective {X : Type} [Group X] (ψ : StatedSp 3 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F)) :
    Function.Injective (ψ.comp (longBlock F 3 2)) := by
  intro s t hst
  apply longBlock_injective (2 : Fin 3)
  have h1 : ψ ((longBlock F 3 2 t)⁻¹ * longBlock F 3 2 s) = 1 := by
    rw [map_mul, map_inv]
    exact inv_mul_eq_one.2 hst.symm
  have h2' : (longBlock F 3 2 t)⁻¹ * longBlock F 3 2 s ∈ suppGroup (coords (2 : Fin 3)) := by
    rw [← range_longBlock]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨t, rfl⟩) ⟨s, rfl⟩
  have h3 := injOn_suppGroup_of_ker_le_center ψ hker (S := coords (2 : Fin 3))
    (t := Sum.inl (0 : Fin 3)) (by simp [mem_coords]) _ h2' h1
  exact (inv_mul_eq_one.1 h3).symm

theorem stab_of_normal [Finite F] (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 3 F →* X) (hnorm : ψ.range.Normal) (τ : X ≃* X) (θ : SL(2, F) →* X)
    (hθ : θ.range = (longBlock F 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) : ∀ x, τ (ψ x) ∈ ψ.range := by
  classical
  have hθ₂range : (ψ.comp (longBlock F 3 2)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp]
  set N : Subgroup (StatedSp 3 F) := ψ.range.comap (τ.toMonoidHom.comp ψ) with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : τ (ψ n) ∈ ψ.range := hn
    show τ (ψ (g * n * g⁻¹)) ∈ ψ.range
    simp only [map_mul, map_inv]
    exact hnorm.conj_mem _ hn' _⟩
  have hy₀ : longBlock F 3 2 (sl2Upper 1) ∈ N := by
    show τ (ψ (longBlock F 3 2 (sl2Upper 1))) ∈ ψ.range
    have : (ψ.comp (longBlock F 3 2)) (sl2Upper 1) ∈ θ.range := hθ₂range ▸ ⟨_, rfl⟩
    obtain ⟨s₁, hs₁⟩ := this
    show τ ((ψ.comp (longBlock F 3 2)) (sl2Upper 1)) ∈ ψ.range
    rw [← hs₁, hθτ]
    have : θ (diagConj2 (-1) 1 s₁) ∈ (longBlock F 3 2).range.map ψ := hθ ▸ ⟨_, rfl⟩
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  have hN : ¬ N ≤ Subgroup.center (StatedSp 3 F) := fun hle => by
    have hc := hle hy₀
    have hs : longBlock F 3 2 (sl2Upper 1) ∈ suppGroup (coords (2 : Fin 3)) := by
      rw [← range_longBlock]
      exact ⟨_, rfl⟩
    have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl (0 : Fin 3))
      (by simp [mem_coords])
    have h2' := longBlock_injective (K := F) (n := 3) (2 : Fin 3) (h1.trans (map_one _).symm)
    have := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F) 0 1) h2'
    simp [CFSG.LieType.Steinberg.coe_sl2Upper] at this
  have hNtop := eq_top_of_normal_of_not_le_center3 h4 hN
  intro x
  have : x ∈ N := by rw [hNtop]; trivial
  exact this

theorem exists_gamma [Finite F] {X : Type} [Group X] (ψ : StatedSp 3 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F)) (θ : SL(2, F) →* X)
    (hθ : θ.range = (longBlock F 3 2).range.map ψ) :
    ∃ γ : SL(2, F) ≃* SL(2, F), ∀ s, ψ (longBlock F 3 2 (γ s)) = θ s := by
  classical
  have hθ₂inj := comp_longBlock_injective ψ hker
  have hθ₂range : (ψ.comp (longBlock F 3 2)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp]
  have hex : ∀ s : SL(2, F), ∃ s' : SL(2, F), (ψ.comp (longBlock F 3 2)) s' = θ s := fun s => by
    have : θ s ∈ (ψ.comp (longBlock F 3 2)).range := hθ₂range ▸ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  choose γf hγf using hex
  let γ0 : SL(2, F) →* SL(2, F) :=
    { toFun := γf
      map_one' := hθ₂inj (by rw [hγf, map_one, map_one])
      map_mul' := fun s t => hθ₂inj (by rw [hγf, map_mul, map_mul, hγf, hγf]) }
  have hγsurj : Function.Surjective γ0 := fun t => by
    have : (ψ.comp (longBlock F 3 2)) t ∈ θ.range := hθ₂range ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hθ₂inj (by show (ψ.comp (longBlock F 3 2)) (γf s) = _; rw [hγf]; exact hs)⟩
  exact ⟨MulEquiv.ofBijective γ0 ⟨Finite.injective_iff_surjective.2 hγsurj, hγsurj⟩,
    fun s => hγf s⟩

theorem rho_mem_longBlock [Finite F] (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 3 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F)) (τ : X ≃* X)
    (θ : SL(2, F) →* X) (hθ : θ.range = (longBlock F 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (ρ : StatedSp 3 F ≃* StatedSp 3 F)
    (hρψ : ∀ x, ψ (ρ x) = τ (ψ x)) :
    ∀ s : SL(2, F), ρ (longBlock F 3 2 s) ∈ (longBlock F 3 2).range := by
  classical
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hθ₂range : (ψ.comp (longBlock F 3 2)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp]
  have hAperf : (ρ.toMonoidHom.comp (longBlock F 3 2)).range ≤
      ⁅(ρ.toMonoidHom.comp (longBlock F 3 2)).range,
        (ρ.toMonoidHom.comp (longBlock F 3 2)).range⁆ :=
    range_le_commutator_aux _
  have hsup : (ρ.toMonoidHom.comp (longBlock F 3 2)).range ≤
      (longBlock F 3 2).range ⊔ ψ.ker := by
    rintro _ ⟨s, rfl⟩
    have h1 : τ ((ψ.comp (longBlock F 3 2)) s) ∈ (ψ.comp (longBlock F 3 2)).range := by
      have : (ψ.comp (longBlock F 3 2)) s ∈ θ.range := hθ₂range ▸ ⟨s, rfl⟩
      obtain ⟨s₁, hs₁⟩ := this
      rw [← hs₁, hθτ]
      exact hθ₂range ▸ ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ := h1
    have hz : (longBlock F 3 2 s')⁻¹ * ρ (longBlock F 3 2 s) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρψ]
      show (ψ (longBlock F 3 2 s'))⁻¹ * τ (ψ (longBlock F 3 2 s)) = 1
      have hs'' : ψ (longBlock F 3 2 s') = τ (ψ (longBlock F 3 2 s)) := hs'
      rw [hs'', inv_mul_cancel]
    have : ρ (longBlock F 3 2 s) =
        longBlock F 3 2 s' * ((longBlock F 3 2 s')⁻¹ * ρ (longBlock F 3 2 s)) := by group
    show ρ (longBlock F 3 2 s) ∈ _
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s', rfl⟩) (Subgroup.mem_sup_right hz)
  exact fun s => le_of_perfect_of_le_sup_center hker hAperf hsup ⟨s, rfl⟩

theorem rho_chart [Finite F] (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 3 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F)) (τ : X ≃* X)
    (θ : SL(2, F) →* X) (hθ : θ.range = (longBlock F 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (ρ : StatedSp 3 F ≃* StatedSp 3 F)
    (hρψ : ∀ x, ψ (ρ x) = τ (ψ x)) (γ : SL(2, F) ≃* SL(2, F))
    (hγθ : ∀ s, ψ (longBlock F 3 2 (γ s)) = θ s) (s : SL(2, F)) :
    ρ (longBlock F 3 2 (γ s)) = longBlock F 3 2 (γ (diagConj2 (-1) 1 s)) := by
  have hθ₂inj := comp_longBlock_injective ψ hker
  obtain ⟨s'', hs''⟩ := rho_mem_longBlock h4 ψ hker τ θ hθ hθτ ρ hρψ (γ s)
  have hs : s'' = γ (diagConj2 (-1) 1 s) := by
    apply hθ₂inj
    calc (ψ.comp (longBlock F 3 2)) s'' = ψ (longBlock F 3 2 s'') := rfl
      _ = ψ (ρ (longBlock F 3 2 (γ s))) := by rw [hs'']
      _ = τ (ψ (longBlock F 3 2 (γ s))) := hρψ _
      _ = τ (θ s) := by rw [hγθ]
      _ = θ (diagConj2 (-1) 1 s) := hθτ s
      _ = ψ (longBlock F 3 2 (γ (diagConj2 (-1) 1 s))) := (hγθ _).symm
  rw [← hs'', hs]

theorem rho_rho {X : Type} [Group X] (ψ : StatedSp 3 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F)) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    (hPsp : Group.IsPerfect (StatedSp 3 F)) (ρ : StatedSp 3 F ≃* StatedSp 3 F)
    (hρψ : ∀ x, ψ (ρ x) = τ (ψ x)) : ∀ x : StatedSp 3 F, ρ (ρ x) = x := by
  let ρ2 : StatedSp 3 F →* StatedSp 3 F := ρ.toMonoidHom.comp ρ.toMonoidHom
  have key := CFSG.ClassicalInvolution.RouteD.Gaps.fixed_of_perfect_of_central ρ2 (N := ⊤)
    inferInstance (Z := ψ.ker) hker
    (fun n _ => by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (ψ n)⁻¹ * ψ (ρ (ρ n)) = 1
      rw [hρψ, hρψ, hτ, inv_mul_cancel])
  exact fun x => key x trivial

theorem rho_longInv (h2 : (2 : F) ≠ 0) (ρ : StatedSp 3 F ≃* StatedSp 3 F)
    (hρL : ∀ s : SL(2, F), ρ (longBlock F 3 2 s) ∈ (longBlock F 3 2).range) :
    ρ (longInv F 3 2) = longInv F 3 2 := by
  obtain ⟨s₀, hs₀⟩ := hρL (-1)
  have hsq' : s₀ * s₀ = 1 := by
    apply longBlock_injective (2 : Fin 3)
    have h1 : ρ (longBlock F 3 2 (-1)) * ρ (longBlock F 3 2 (-1)) = 1 := by
      rw [← map_mul, ← map_mul]
      have : ((-1 : SL(2, F)) * (-1)) = 1 := by ext; simp
      rw [this, map_one, map_one]
    rw [map_mul, hs₀, h1, map_one]
  rcases CFSG.ClassicalInvolution.Generic.sl2_sq_eq_one h2 hsq' with h | h
  · exfalso
    subst h
    have h1 : ρ (longBlock F 3 2 (-1)) = ρ 1 := by rw [← hs₀, map_one, map_one]
    have h3 := longBlock_injective (K := F) (n := 3) (2 : Fin 3)
      ((ρ.injective h1).trans (map_one (longBlock F 3 2)).symm)
    have := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F) 0 0) h3
    simp at this
    apply h2
    linear_combination -this
  · subst h
    exact hs₀.symm

theorem comm_longInv_of_rho (A : gsp 3 F) (σ : F ≃+* F)
    (hinv : conjSp 3 F A (fieldSp 3 F σ (longInv F 3 2)) = longInv F 3 2) :
    ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * longInvMat F =
      longInvMat F *
        ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  obtain ⟨Am, hAm⟩ : ∃ M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
      M = ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
      M = (((A : GL (Fin 3 ⊕ Fin 3) F)⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := ⟨_, rfl⟩
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 := congrArg (mat 3 F) hinv
  rw [mat_conjSp_fieldSp, mat_longInv, Matrix.diagonal_map (map_zero σ), ← hAm, ← hBm] at h1
  have hd : (fun a : Fin 3 ⊕ Fin 3 => σ (if a ∈ coords (2 : Fin 3) then (-1 : F) else 1)) =
      fun a => if a ∈ coords (2 : Fin 3) then (-1 : F) else 1 := by
    funext a
    split_ifs <;> simp
  rw [hd] at h1
  rw [← hAm]
  calc Am * longInvMat F = Am * longInvMat F * (Bm * Am) := by rw [hBA, Matrix.mul_one]
    _ = (Am * longInvMat F * Bm) * Am := by simp only [Matrix.mul_assoc]
    _ = longInvMat F * Am := by rw [show Am * longInvMat F * Bm = longInvMat F from h1]

theorem sq_scalar_of_rho [Finite F] (A : gsp 3 F) (σ : F ≃+* F)
    (hρρ : ∀ x : StatedSp 3 F, conjSp 3 F A (fieldSp 3 F σ (conjSp 3 F A (fieldSp 3 F σ x))) = x) :
    ∃ d : F, ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
        ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).map σ =
      d • (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  have hα : ∀ x : StatedSp 3 F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F x) =
      proj 3 F (conjSp 3 F A (fieldSp 3 F σ x)) := fun x => by
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  have hαα : conjAut 3 F A * fieldAut 3 F σ * (conjAut 3 F A * fieldAut 3 F σ) = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := proj_surjective y
    rw [MulAut.mul_apply, hα, hα, hρρ]
    rfl
  rw [conjAut_mul_fieldAut_mul_self] at hαα
  obtain ⟨-, c, hc⟩ := (conjAut_mul_fieldAut_eq_one_iff (by norm_num : 1 ≤ 3) _ _).mp hαα
  refine ⟨c, ?_⟩
  have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) F => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F))
    hc
  simp [coe_gspFieldMap] at this
  rw [Matrix.smul_one_eq_diagonal]
  exact this

theorem exists_fixed_shortRoots [Finite F] (hodd : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F)
    {X : Type} [Group X] (ψ : StatedSp 3 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 F))
    (hnorm : ψ.range.Normal) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (θ : SL(2, F) →* X)
    (hθ : θ.range = (longBlock F 3 2).range.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) :
    ∃ g : StatedSp 3 F, (longBlock F 3 2).range.map (MulAut.conj g).toMonoidHom =
        (longBlock F 3 2).range ∧
      (∀ x ∈ (shortBlock F (by decide : (1 : Fin 3) ≠ 2)).range.map
          (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x) ∧
      (∀ x ∈ (shortBlock F (by decide : (0 : Fin 3) ≠ 1)).range.map
          (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x) := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hPsp : Group.IsPerfect (StatedSp 3 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hstab := stab_of_normal h4 ψ hnorm τ θ hθ hθτ
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift3 hodd h4 ψ hker τ hτ hstab
  let ρ : StatedSp 3 F ≃* StatedSp 3 F := (fieldSp 3 F σ).trans (conjSp 3 F A)
  have hρψ : ∀ x, ψ (ρ x) = τ (ψ x) := fun x => (hAσ x).symm
  obtain ⟨γ, hγθ⟩ := exists_gamma ψ hker θ hθ
  have hρL := rho_mem_longBlock h4 ψ hker τ θ hθ hθτ ρ hρψ
  have hρρ : ∀ x : StatedSp 3 F, conjSp 3 F A (fieldSp 3 F σ (conjSp 3 F A (fieldSp 3 F σ x))) =
      x := rho_rho ψ hker τ hτ hPsp ρ hρψ
  have hD := comm_longInv_of_rho A σ (rho_longInv h2 ρ hρL)
  have hsq := sq_scalar_of_rho A σ hρρ
  set Am : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    ((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) with hAm
  set Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    (((A : GL (Fin 3 ⊕ Fin 3) F)⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) with hBm
  have hAB : Am * Bm = 1 := by
    rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = ((multiplier 3 F A : Fˣ) : F) * form u v :=
    form_mulVec_of_sim (multiplier_spec A)
  have hγm : ∀ s : SL(2, F), Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
      (((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
      blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro s
    have h := congrArg (mat 3 F) (rho_chart h4 ψ hker τ θ hθ hθτ ρ hρψ γ hγθ s)
    have e : mat 3 F (ρ (longBlock F 3 2 (γ s))) =
        Am * (mat 3 F (longBlock F 3 2 (γ s))).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, mat_longBlock, mat_longBlock, map_blockMat] at h
    exact h
  obtain ⟨hσ, κ, h, hAV, u₂, w₂, hu₂, hw₂, hAu, hAw, huw⟩ :=
    core_three h2 hAB hBA σ hsim hD hsq γ hγm
  obtain ⟨u, w, hfr, hAu', hAw', hu2, hw2⟩ := exists_frame_three h hAV hu₂ hw₂ hAu hAw huw
  obtain ⟨g, hg1, hg2⟩ := exists_g_of_frame hBA h hfr hAu' hAw' (hu2 ▸ hu₂) (hw2 ▸ hw₂)
  have hmapid : ∀ M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hfix : ∀ (i j : Fin 3) (hij : i ≠ j) (s : SL(2, F)),
      τ (ψ (g * shortBlock F hij s * g⁻¹)) = ψ (g * shortBlock F hij s * g⁻¹) := by
    intro i j hij s
    have hρx : ρ (g * shortBlock F hij s * g⁻¹) = g * shortBlock F hij s * g⁻¹ := by
      apply mat_injective
      have e : mat 3 F (ρ (g * shortBlock F hij s * g⁻¹)) =
          Am * (mat 3 F (g * shortBlock F hij s * g⁻¹)).map σ * Bm :=
        mat_conjSp_fieldSp A σ _
      rw [e, hmapid]
      exact hg2 i j hij s
    rw [← hρψ, hρx]
  refine ⟨g, hg1, ?_, ?_⟩
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s

end CFSG.ClassicalInvolution.RouteD.SpAdapt
