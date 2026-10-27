module

public import CFSG.ClassicalInvolution.RouteD.GapsLocal
public import CFSG.ClassicalInvolution.RouteD.GapsD4A

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups Matrix commutatorElement

variable {F : Type} [Field F]

theorem range_le_commutator_of_perfect {L H : Type*} [Group L] [Group H] [Group.IsPerfect L]
    (f : L →* H) : f.range ≤ ⁅f.range, f.range⁆ := by
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top
  have h : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  exact h.ge

theorem exists_diag_of_fixed_block_three [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hcl : LinearAutClassification F 3) {X : Type} [Group X]
    (θ : SL(2 + 1, F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(2 + 1, F)) (γ : X ≃* X)
    (h₀ : ∀ A : SL(2, F), γ (θ (blockSL2 F 2 ⟨0, by omega⟩ A)) = θ (blockSL2 F 2 ⟨0, by omega⟩ A))
    (h₁ : ∀ A : SL(2, F), ∃ B : SL(2, F),
      γ (θ (blockSL2 F 2 ⟨1, by omega⟩ A)) = θ (blockSL2 F 2 ⟨1, by omega⟩ B)) :
    ∃ u : Fin (2 + 1) → Fˣ, ∀ x, γ (θ x) = θ (slConjugation (2 + 1) F (diagGL u) x) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  obtain ⟨α, g, φ, ε, hαθ, hαmat⟩ := hcl X θ hθ hker γ
  have hα₀ : ∀ A : SL(2, F), α (blockSL2 F 2 ⟨0, by omega⟩ A) = blockSL2 F 2 ⟨0, by omega⟩ A := by
    intro A
    have := hom_eq_of_central_ker θ hker (L := SL(2, F))
      (α.comp (blockSL2 F 2 ⟨0, by omega⟩)) (blockSL2 F 2 ⟨0, by omega⟩)
      (fun A => by rw [MonoidHom.comp_apply, hαθ, h₀])
    exact DFunLike.congr_fun this A
  have hα₁ : ∀ A : SL(2, F), ∃ B : SL(2, F),
      α (blockSL2 F 2 ⟨1, by omega⟩ A) = blockSL2 F 2 ⟨1, by omega⟩ B := by
    have hPL : (α.comp (blockSL2 F 2 ⟨1, by omega⟩)).range ≤
        (blockSL2 F 2 ⟨1, by omega⟩).range ⊔ θ.ker := by
      rintro _ ⟨A₀, rfl⟩
      obtain ⟨B, hB⟩ := h₁ A₀
      have hmem : (blockSL2 F 2 ⟨1, by omega⟩ B)⁻¹ * α (blockSL2 F 2 ⟨1, by omega⟩ A₀) ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hB, inv_mul_cancel]
      have : α (blockSL2 F 2 ⟨1, by omega⟩ A₀) = blockSL2 F 2 ⟨1, by omega⟩ B *
          ((blockSL2 F 2 ⟨1, by omega⟩ B)⁻¹ * α (blockSL2 F 2 ⟨1, by omega⟩ A₀)) := by group
      show α (blockSL2 F 2 ⟨1, by omega⟩ A₀) ∈ _
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨B, rfl⟩) (Subgroup.mem_sup_right hmem)
    have hle := le_of_perfect_of_le_sup_center hker
      (range_le_commutator_of_perfect (α.comp (blockSL2 F 2 ⟨1, by omega⟩))) hPL
    intro A
    obtain ⟨B, hB⟩ := hle ⟨A, rfl⟩
    exact ⟨B, hB.symm⟩
  have hup : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ.ne : (⟨0, by omega⟩ : Fin 2).castSucc ≠ (⟨0, by omega⟩ : Fin 2).succ)
      c) = Matrix.SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ.ne : (⟨0, by omega⟩ : Fin 2).castSucc ≠ (⟨0, by omega⟩ : Fin 2).succ)
      c := by
    intro c
    have := hα₀ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
    rwa [blockSL2_transvection_up] at this
  have hdown : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ.ne' : (⟨0, by omega⟩ : Fin 2).succ ≠ (⟨0, by omega⟩ : Fin 2).castSucc)
      c) = Matrix.SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ.ne' : (⟨0, by omega⟩ : Fin 2).succ ≠ (⟨0, by omega⟩ : Fin 2).castSucc)
      c := by
    intro c
    have := hα₀ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)
    rwa [blockSL2_transvection_down] at this
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte] at hαmat
    obtain ⟨hφ, h1⟩ := fixed_transvection_false α g φ hαmat _ (hup)
    obtain ⟨-, h2⟩ := fixed_transvection_false α g φ hαmat _ (hdown)
    obtain ⟨e1, e2, e3, e4, e5⟩ := block_of_commute_single _ h1 h2
    have eC : (⟨0, by omega⟩ : Fin 2).castSucc = (0 : Fin (2 + 1)) := rfl
    have eS : (⟨0, by omega⟩ : Fin 2).succ = (1 : Fin (2 + 1)) := rfl
    simp only [eC, eS] at e1 e2 e3 e4 e5
    have hoff : ∀ i j : Fin (2 + 1), i ≠ j → (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
      · exact e4 1 (by decide)
      · exact e4 2 (by decide)
      · exact e5 0 (by decide)
      · exact e5 2 (by decide)
      · exact e2 2 (by decide)
      · exact e3 2 (by decide)
    obtain ⟨u, rfl⟩ := exists_diagGL_of_offdiag_zero g hoff
    refine ⟨u, fun x => ?_⟩
    rw [← hαθ]
    congr 1
    refine Subtype.ext ?_
    rw [hαmat x, slConjugation_matrix]
    congr 2
    ext a b
    simp [RingEquiv.mapMatrix_apply, hφ]
  · exfalso
    simp only [↓reduceIte] at hαmat
    obtain ⟨hφ, h1⟩ := fixed_transvection_true α g φ hαmat _ (hup)
    obtain ⟨-, h2⟩ := fixed_transvection_true α g φ hαmat _ (hdown)
    have hαmat' : ∀ x, ((α x : SL(2 + 1, F)) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) =
        (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) * (((x⁻¹ : SL(2 + 1, F)) :
          Matrix (Fin (2 + 1)) (Fin (2 + 1)) F))ᵀ *
          ((g⁻¹ : GL (Fin (2 + 1)) F) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) := by
      intro x
      rw [hαmat x]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    obtain ⟨k1, k2, k3, k4, k5⟩ := block_of_graph_commute _ h1 h2
    have eC : (⟨0, by omega⟩ : Fin 2).castSucc = (0 : Fin (2 + 1)) := rfl
    have eS : (⟨0, by omega⟩ : Fin 2).succ = (1 : Fin (2 + 1)) := rfl
    simp only [eC, eS] at k1 k2 k3 k4 k5
    obtain ⟨B, hB⟩ := hα₁ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1)
    rw [blockSL2_transvection_up] at hB
    have hmat := congrArg (fun x : SL(2 + 1, F) => (x : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F)) hB
    simp only at hmat
    rw [hαmat', coe_transvection_inv_eq] at hmat
    have eC1 : (⟨1, by omega⟩ : Fin 2).castSucc = (1 : Fin (2 + 1)) := rfl
    have eS1 : (⟨1, by omega⟩ : Fin 2).succ = (2 : Fin (2 + 1)) := rfl
    simp only [eC1, eS1, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single] at hmat
    have key := mul_eq_of_conj_eq g hmat
    have hy20 : ((blockSL2 F 2 ⟨1, by omega⟩ B : SL(2 + 1, F)) :
        Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) 2 0 = 0 := by
      show blockMat 3 1 (B : Matrix (Fin 2) (Fin 2) F) 2 0 = 0
      rw [CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_right _ _ (by decide)]
      rfl
    have e21 := congrFun (congrFun key 2) 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_single_apply_same] at e21
    rw [Matrix.mul_apply, Fin.sum_univ_three, hy20, k1 1 (by decide), k1 2 (by decide)] at e21
    have g22 : (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) 2 2 = 0 := by
      linear_combination -e21
    apply det_ne_zero_of_gl g
    refine Matrix.det_eq_zero_of_row_eq_zero (2 : Fin (2 + 1)) fun l => ?_
    fin_cases l
    · exact k3 2 (by decide)
    · exact k1 2 (by decide)
    · exact g22

@[expose] def flipSL (A : SL(2, F)) : SL(2, F) :=
  ⟨!![A 1 1, A 1 0; A 0 1, A 0 0], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

theorem flipSL_flipSL (A : SL(2, F)) : flipSL (flipSL A) = A := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipSL]

theorem coe_blockSL2' {n : ℕ} (i : Fin n) (A : SL(2, F)) :
    ((blockSL2 F n i A : SL(n + 1, F)) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      blockMat (n + 1) i.val (A : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] noncomputable def swapGL : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (!![0, 0, 1; 0, 1, 0; 1, 0, 0]) (by
    rw [Matrix.det_fin_three]; simp)

theorem coe_swapGL : ((swapGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem conj_swap_zero (A : SL(2, F)) :
    slConjugation 3 F swapGL (blockSL2 F 2 ⟨0, by omega⟩ A) =
      blockSL2 F 2 ⟨1, by omega⟩ (flipSL A) := by
  refine Subtype.ext ?_
  rw [slConjugation_matrix]
  apply conj_eq_of_mul_eq
  rw [coe_swapGL, coe_blockSL2', coe_blockSL2']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, blockMat_apply, flipSL]

theorem conj_swap_one (A : SL(2, F)) :
    slConjugation 3 F swapGL (blockSL2 F 2 ⟨1, by omega⟩ A) =
      blockSL2 F 2 ⟨0, by omega⟩ (flipSL A) := by
  refine Subtype.ext ?_
  rw [slConjugation_matrix]
  apply conj_eq_of_mul_eq
  rw [coe_swapGL, coe_blockSL2', coe_blockSL2']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, blockMat_apply, flipSL]

theorem slConjugation_diagGL_comm {n : ℕ} (u v : Fin n → Fˣ) (x : SL(n, F)) :
    slConjugation n F (diagGL u) (slConjugation n F (diagGL v) x) =
      slConjugation n F (diagGL v) (slConjugation n F (diagGL u) x) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, slConjugation_diagGL_apply, slConjugation_diagGL_apply,
    slConjugation_diagGL_apply]
  ring

theorem aut_commute_of_chart [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F 3) {X : Type} [Group X] (Wr : Subgroup X)
    (ψ : SL(2 + 1, F) →* ↥Wr) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(2 + 1, F)) (K₀ K : Subgroup X)
    (C₀ : ∀ A : SL(2, F), ((ψ (blockSL2 F 2 ⟨0, by omega⟩ A) : ↥Wr) : X) ∈ K₀)
    (C₁ : ∀ A : SL(2, F), ((ψ (blockSL2 F 2 ⟨1, by omega⟩ A) : ↥Wr) : X) ∈ K)
    (C₁' : ∀ w : ↥Wr, (w : X) ∈ K → ∃ B : SL(2, F), w = ψ (blockSL2 F 2 ⟨1, by omega⟩ B))
    (α β : MulAut ↥Wr) (hα₀ : ∀ w : ↥Wr, (w : X) ∈ K₀ → α w = w)
    (hβ₀ : ∀ w : ↥Wr, (w : X) ∈ K₀ → β w = w)
    (hαK : ∀ w : ↥Wr, (w : X) ∈ K → ((α w : ↥Wr) : X) ∈ K)
    (hβK : ∀ w : ↥Wr, (w : X) ∈ K → ((β w : ↥Wr) : X) ∈ K) : α * β = β * α := by
  have key : ∀ γ : MulAut ↥Wr, (∀ w : ↥Wr, (w : X) ∈ K₀ → γ w = w) →
      (∀ w : ↥Wr, (w : X) ∈ K → ((γ w : ↥Wr) : X) ∈ K) →
      ∃ u : Fin (2 + 1) → Fˣ, ∀ x, γ (ψ x) = ψ (slConjugation (2 + 1) F (diagGL u) x) :=
    fun γ h0 h1 => exists_diag_of_fixed_block_three hodd h5 hcl ψ hψ hker γ
      (fun A => h0 _ (C₀ A))
      (fun A => C₁' _ (h1 _ (C₁ A)))
  obtain ⟨u, hu⟩ := key α hα₀ hαK
  obtain ⟨v, hv⟩ := key β hβ₀ hβK
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := hψ w
  show α (β (ψ x)) = β (α (ψ x))
  rw [hv, hu, hu, hv, slConjugation_diagGL_comm]

theorem mem_center_of_map_mem_center {G : Type*} [Group G] (e : G ≃* G) {x : G}
    (hx : e x ∈ Subgroup.center G) : x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact hx (e g)

theorem standardPairAutAbelian_of_classification [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hcl : LinearAutClassification F 3) : StandardPairAutAbelian F := by
  intro X _ W K₀ K hWK α β hα₀ hβ₀ hαK hβK
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hWK
  subst hrange
  set ψ₁ : SL(2 + 1, F) →* ↥θ.range :=
    θ.rangeRestrict.comp (MulAut.conj c⁻¹).toMonoidHom with hψ₁def
  have hψ₁ : Function.Surjective ψ₁ :=
    θ.rangeRestrict_surjective.comp (MulAut.conj c⁻¹).surjective
  have hker₁ : ψ₁.ker ≤ Subgroup.center SL(2 + 1, F) := by
    intro x hx
    have h1 : θ (c⁻¹ * x * c) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [hψ₁def, MulAut.conj_apply] using this
    have h2 := hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    have h3 := h2 (c⁻¹ * y * c)
    have e1 : y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
    have e2 : x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
    rw [e1, e2, h3]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine aut_commute_of_chart hodd h5 hcl θ.range ψ₁ hψ₁ hker₁ K₀ K ?_ ?_ ?_ α β hα₀ hβ₀ hαK
      hβK
    · intro A
      rw [← h1]
      exact ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    · intro A
      rw [← h2]
      exact ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    · intro w hw
      rw [← h2] at hw
      obtain ⟨y, ⟨b, ⟨B, rfl⟩, rfl⟩, hy⟩ := hw
      exact ⟨B, Subtype.ext hy.symm⟩
  · set ψ₂ : SL(2 + 1, F) →* ↥θ.range := ψ₁.comp (slConjugation 3 F swapGL).toMonoidHom with hψ₂def
    have hψ₂ : Function.Surjective ψ₂ := hψ₁.comp (slConjugation 3 F swapGL).surjective
    have hker₂ : ψ₂.ker ≤ Subgroup.center SL(2 + 1, F) := fun x hx =>
      mem_center_of_map_mem_center (slConjugation 3 F swapGL)
        (hker₁ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)))
    refine aut_commute_of_chart hodd h5 hcl θ.range ψ₂ hψ₂ hker₂ K₀ K ?_ ?_ ?_ α β hα₀ hβ₀ hαK hβK
    · intro A
      rw [← h2]
      show θ ((MulAut.conj c⁻¹).toMonoidHom (slConjugation 3 F swapGL (blockSL2 F 2 ⟨0, by omega⟩ A)))
        ∈ _
      rw [conj_swap_zero]
      exact ⟨_, ⟨_, ⟨flipSL A, rfl⟩, rfl⟩, rfl⟩
    · intro A
      rw [← h1]
      show θ ((MulAut.conj c⁻¹).toMonoidHom (slConjugation 3 F swapGL (blockSL2 F 2 ⟨1, by omega⟩ A)))
        ∈ _
      rw [conj_swap_one]
      exact ⟨_, ⟨_, ⟨flipSL A, rfl⟩, rfl⟩, rfl⟩
    · intro w hw
      rw [← h1] at hw
      obtain ⟨y, ⟨b, ⟨B, rfl⟩, rfl⟩, hy⟩ := hw
      refine ⟨flipSL B, Subtype.ext ?_⟩
      rw [← hy]
      show θ ((MulAut.conj c⁻¹).toMonoidHom (blockSL2 F 2 ⟨0, by omega⟩ B)) =
        θ ((MulAut.conj c⁻¹).toMonoidHom
          (slConjugation 3 F swapGL (blockSL2 F 2 ⟨1, by omega⟩ (flipSL B))))
      rw [conj_swap_one, flipSL_flipSL]

theorem perfect_le_centralizer_of_partner_of_classification {p f : ℕ} [Fact p.Prime]
    (hMFZ : FundNoncentral p) {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hcl : LinearAutClassification F 3)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {t : G} (hP1 : LocalOddCentral Ω {t})
    (D : LieSystemData p f (locQuot Ω t) (locFamily Ω t)) (hD : D.card ≤ 4)
    {W K₀ K : Subgroup G} (hK : K ∈ Ω) (hxK : IsClassicalMember p f K t)
    (hWK : LinearBlockStandardPair F W K₀ K) {S : Subgroup G} (hS : ⁅S, S⁆ = S)
    (hSt : S ≤ Subgroup.centralizer ({t} : Set G))
    (hS₀ : S ≤ Subgroup.centralizer (K₀ : Set G)) : S ≤ Subgroup.centralizer (K : Set G) :=
  perfect_le_centralizer_of_partner hMFZ (standardPairAutAbelian_of_classification hodd h5 hcl) hΩ
    hP1 D hD hK hxK hWK hS hSt hS₀


end CFSG.ClassicalInvolution.RouteD.Gaps
