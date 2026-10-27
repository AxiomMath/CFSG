module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallEven

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.Quasithin (perfectCore map_perfectCore)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem map_coreRadicalP_eq_of_map_eq (hq : 4 ≤ Nat.card K) (hk : 0 < k) (hJ : P.free = ∅)
    (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))) :
    (P.coreRadicalP K).map β.toMonoidHom = P.coreRadicalP K := by
  obtain ⟨hQp, hQΛ, hΛN, hmax, -, -, -⟩ := P.coreRadicalP_spec hq hk hJ
  have hle : (P.coreRadicalP K).map β.toMonoidHom ≤ P.coreRadicalP K := by
    refine hmax _ (hQp.map _) ?_ ?_
    · rw [← hβ]
      exact map_mono hQΛ
    · rw [← hβ]
      exact (map_mono hΛN).trans (le_normalizer_map _)
  exact eq_of_le_of_card_ge hle (card_map_of_injective β.injective).ge

theorem projFieldPart_congr_eq_of_twist_of_free_eq_empty (hq : 4 ≤ Nat.card K) (hk : 2 ≤ k)
    (hJ : P.free = ∅) (F : MulAut (projectiveSL k K) →* (K ≃+* K))
    (hF : ∀ A : GL (Fin k) K, F (conjAut k K A) = 1) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (P.leviOneP K))
    (hβbar : ∀ s : P.leviOneP K,
      ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.coreRadicalP K)
    (κ : P.leviOneP K ≃* projectiveSL k K)
    (B : GL (Fin n) K) (τ : MulAut (projectiveSL n K))
    (τk : MulAut (SpecialLinearGroup (Fin k) K))
    (hβτ : β = conjAut n K B * τ) (hτQ : ∀ x ∈ P.radicalP K, τ x ∈ P.radicalP K)
    (hτe : τ (P.elt K) = P.elt K)
    (hτS : ∀ a : SpecialLinearGroup (Fin k) K,
      τ (proj n K (P.leviOneHom K a)) = proj n K (P.leviOneHom K (τk a))) :
    F (MulAut.congr κ βbar) = F (descendAut k K τk) := by
  have hk0 : 0 < k := by omega
  have hlev : ∀ l, P.level l ≠ 1 := fun l h => by
    have := P.mem_free.2 h
    rw [hJ] at this
    exact Finset.notMem_empty l this
  obtain ⟨-, hQΛ, -, -, -, -, hdisj⟩ := P.coreRadicalP_spec hq hk0 hJ
  set Λ := perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) with hΛdef
  have hβQ := P.map_coreRadicalP_eq_of_map_eq hq hk0 hJ β hβ
  have hτΛ := P.map_perfectCore_eq_of_apply_elt τ hτe
  have hτR : (P.radicalP K).map τ.toMonoidHom = P.radicalP K := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective τ.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hτQ x hx
  have hτinvQ : ∀ x ∈ P.coreRadicalP K, τ⁻¹ x ∈ P.coreRadicalP K := by
    rintro x ⟨hxΛ, hxR⟩
    refine ⟨?_, ?_⟩
    · rw [← hτΛ] at hxΛ
      obtain ⟨y, hy, rfl⟩ := hxΛ
      simpa using hy
    · rw [← hτR] at hxR
      obtain ⟨y, hy, rfl⟩ := hxR
      simpa using hy
  have hβmem : ∀ x ∈ P.coreRadicalP K, β x ∈ P.coreRadicalP K := fun x hx => by
    rw [← hβQ]
    exact ⟨x, hx, rfl⟩
  have hcB : conjAut n K B = β * τ⁻¹ := by rw [hβτ, mul_inv_cancel_right]
  have hB : ∀ a b : Fin k, a ≠ b → ∀ c : K,
      conjAut n K B (proj n K (SpecialLinearGroup.transvection (P.u_ne_w a b) c)) ∈
        P.radicalP K := by
    intro a b hab c
    rw [hcB, MulAut.mul_apply]
    exact (hβmem _ (hτinvQ _ (P.proj_transvection_u_w_mem_coreRadicalP hq hab c))).2
  have hBt := P.blockTriangular_of_conjAut_of_free_eq_empty hk hJ B hB
  have hBi : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level := by
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hBt
  set Bu : Matrix (Fin k) (Fin k) K := (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u with hBu
  set Bu' : Matrix (Fin k) (Fin k) K :=
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u with hBu'
  have hBB' : Bu * Bu' = 1 := by
    rw [hBu, hBu', ← P.submatrix_mul_u hBt hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      submatrix_one _ P.u_injective]
  have hB'B : Bu' * Bu = 1 := by
    rw [hBu, hBu', ← P.submatrix_mul_u hBi hBt, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      submatrix_one _ P.u_injective]
  set B'' : GL (Fin k) K := ⟨Bu, Bu', hBB', hB'B⟩ with hB''
  set γ₁ : MulAut (SpecialLinearGroup (Fin k) K) := slConjugation k K B'' * τk with hγ₁
  set δ₁ : MulAut (projectiveSL k K) := descendAut k K γ₁ with hδ₁
  set κ₀ := P.leviOnePEquivPSL K hJ with hκ₀
  set ψ : MulAut (P.leviOneP K) := MulAut.congr κ₀ δ₁ with hψdef
  have hψx : ∀ x, ψ (κ₀ x) = κ₀ (δ₁ x) := fun x => by
    show κ₀ (δ₁ (κ₀.symm (κ₀ x))) = κ₀ (δ₁ x)
    rw [MulEquiv.symm_apply_apply]
  have hΛC : Λ ≤ (centralizer {P.mat K}).map (proj n K) := by
    rw [← P.centralizer_elt]
    exact CFSG.Quasithin.perfectCore_le _
  have hMΛ : P.leviOneP K ≤ Λ := leviOneP_le_perfectCore hq P
  have hψ : ∀ s : P.leviOneP K,
      ((ψ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.coreRadicalP K := by
    intro s
    obtain ⟨x, rfl⟩ := κ₀.surjective s
    obtain ⟨a, rfl⟩ := proj_surjective k K x
    rw [hψx, hδ₁, descendAut_proj, hκ₀, P.coe_leviOnePEquivPSL, P.coe_leviOnePEquivPSL,
      hγ₁, MulAut.mul_apply]
    set L := P.leviOneHom K (τk a) with hL
    set X := slConjugation n K B L with hX
    have hβa : β (proj n K (P.leviOneHom K a)) = proj n K X := by
      rw [hβτ, MulAut.mul_apply, hτS, conjAut_proj]
    have hXΛ : proj n K X ∈ Λ := by
      rw [← hβa, ← hβ]
      exact ⟨_, hMΛ ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨x', hx'C, hx'X⟩ := hΛC hXΛ
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hx'X)
    have hXx' : (X : Matrix (Fin n) (Fin n) K) = (x' : Matrix (Fin n) (Fin n) K) *
        scalar (Fin n) (c : K) := by
      rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have hx'uw := (P.mem_centralizer_mat_iff.1 hx'C).2
    have hXuw : ∀ x y, (X : Matrix (Fin n) (Fin n) K) (P.w x) (P.w y) =
        (X : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) := fun x y => by
      rw [hXx', scalar_apply, mul_diagonal, mul_diagonal, hx'uw]
    have hLt : (L : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
      P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag _)
    have hXmat : (X : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) *
        ((L : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hX, coe_slConjugation, Matrix.mul_assoc]
    have hXt : X ∈ P.parabolic K := by
      change (X : Matrix (Fin n) (Fin n) K).BlockTriangular P.level
      rw [hXmat]
      exact hBt.mul (hLt.mul hBi)
    have hXu : (X : Matrix (Fin n) (Fin n) K).submatrix P.u P.u =
        Bu * (τk a : Matrix (Fin k) (Fin k) K) * Bu' := by
      rw [hXmat, P.submatrix_mul_u hBt (hLt.mul hBi), P.submatrix_mul_u hLt hBi,
        P.submatrix_u_leviOneHom, Matrix.mul_assoc]
    set N := P.leviOneHom K (slConjugation k K B'' (τk a)) with hN
    have hNt : N ∈ P.parabolic K := P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag _)
    have hNu : ∀ x y, (N : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) =
        (Bu * (τk a : Matrix (Fin k) (Fin k) K) * Bu') x y := fun x y => by
      rw [hN, leviOneHom_apply_u_u, coe_slConjugation]
      rfl
    have hNw : ∀ x y, (N : Matrix (Fin n) (Fin n) K) (P.w x) (P.w y) =
        (N : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) := fun x y => by
      rw [hN, leviOneHom_apply_w_w, leviOneHom_apply_u_u]
    have hmem : N⁻¹ * X ∈ P.radical K := by
      refine P.inv_mul_mem_radical_of_eq hXt hNt fun i j hij => ?_
      have hi2 := P.level_le_two i
      have hi1 := hlev i
      rcases (by omega : P.level i = 0 ∨ P.level i = 2) with h0 | h2
      · obtain ⟨x, rfl⟩ := P.level_eq_zero_iff.1 h0
        obtain ⟨y, rfl⟩ := P.level_eq_zero_iff.1 (hij.symm.trans h0)
        rw [hNu, ← hXu]
        rfl
      · obtain ⟨x, rfl⟩ := P.level_eq_two_iff.1 h2
        obtain ⟨y, rfl⟩ := P.level_eq_two_iff.1 (hij.symm.trans h2)
        rw [hXuw, hNw, hNu, ← hXu]
        rfl
    have hNΛ : proj n K N ∈ Λ := hMΛ ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [hβa]
    refine ⟨Λ.mul_mem (Λ.inv_mem hNΛ) hXΛ, ?_⟩
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  have hβbarψ : βbar = ψ := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    have hmem : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
        ((ψ s : P.leviOneP K) : projectiveSL n K) ∈ P.coreRadicalP K := by
      have h : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
          ((ψ s : P.leviOneP K) : projectiveSL n K) =
          (((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s) *
            (((ψ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s)⁻¹ := by group
      rw [h]
      exact mul_mem (hβbar s) (inv_mem (hψ s))
    have hmemS : ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ *
        ((ψ s : P.leviOneP K) : projectiveSL n K) ∈ P.leviOneP K :=
      mul_mem (inv_mem (βbar s).2) (ψ s).2
    exact inv_mul_eq_one.1 (Subgroup.disjoint_def.1 hdisj hmem hmemS)
  rw [hβbarψ, ← mulAutHom_congr_eq_of_intertwine F (fun a b => ringEquiv_mul_comm _ _)
    (MulEquiv.refl _) κ κ₀ δ₁ ψ hψx]
  have hrefl : MulAut.congr (MulEquiv.refl (projectiveSL k K)) δ₁ = δ₁ := by
    ext x
    rfl
  rw [hrefl, hδ₁, hγ₁, map_mul, map_mul]
  change F (conjAut k K B'') * F (descendAut k K τk) = F (descendAut k K τk)
  rw [hF, one_mul]

theorem projFieldPart_congr_eq_linearFieldPart_of_free_eq_empty (hq : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) (hk : 2 ≤ k) (hJ : P.free = ∅) (F : MulAut (projectiveSL k K) →* (K ≃+* K))
    (hF : ∀ A : GL (Fin k) K, F (conjAut k K A) = 1)
    (hFσ : ∀ σ : K ≃+* K, F (fieldAut k K σ) = σ) (hFδ : F (dualAut k K) = 1)
    (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
    (βbar : MulAut (P.leviOneP K))
    (hβbar : ∀ s : P.leviOneP K,
      ((βbar s : P.leviOneP K) : projectiveSL n K)⁻¹ * β s ∈ P.coreRadicalP K)
    (κ : P.leviOneP K ≃* projectiveSL k K) :
    F (MulAut.congr κ βbar) = linearFieldPart K hn β := by
  obtain ⟨σ, A, e, he, hβeq⟩ := ProjectivePlane.exists_standard_form K n hn β
  rw [hβeq, linearFieldPart_eq hn he]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [P.projFieldPart_congr_eq_of_twist_of_free_eq_empty hq hk hJ F hF β hβ βbar hβbar κ A
      (fieldAut n K σ)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin k) K σ)
      (by rw [hβeq, pow_zero, mul_one]) (fun x hx => P.fieldAut_mem_radicalP σ hx)
      (P.fieldAut_elt σ) (fun a => by rw [P.fieldAut_proj_leviOneHom]; rfl)]
    exact hFσ σ
  · rw [P.projFieldPart_congr_eq_of_twist_of_free_eq_empty hq hk hJ F hF β hβ βbar hβbar κ
      (A * (P.outerSwapGL K)⁻¹) (conjAut n K (P.outerSwapGL K) * fieldAut n K σ * dualAut n K)
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin k) K σ *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut k K)
      (by rw [hβeq, pow_one, map_mul, map_inv]; group)
      (fun x hx => P.graphTwist_mem_radicalP σ hx) (P.graphTwist_elt σ)
      (fun a => by rw [P.graphTwist_proj_leviOneHom]; rfl), map_mul, map_mul]
    change F (fieldAut k K σ) * F (dualAut k K) = σ
    rw [hFσ, hFδ, mul_one]

end InvPlacement

end CFSG.SeitzReduction.LinearPilot

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore)

variable {n k k' : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem map_coreRadicalP_eq_of_free_eq_empty {G : Type*} [Group G] {φ φ' : projectiveSL n K →* G}
    (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (P : InvPlacement n k) (P' : InvPlacement n k') (hk : 0 < k) (hk' : 0 < k')
    (hJ : P.free = ∅) (hJ' : P'.free = ∅)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P'.coreRadicalP K).map φ' = (P.coreRadicalP K).map φ := by
  obtain ⟨hQp, hQΛ, hΛN, hmax, -⟩ := P.coreRadicalP_spec hq hk hJ
  obtain ⟨hQp', hQ'Λ, hΛN', hmax', -⟩ := P'.coreRadicalP_spec hq hk' hJ'
  have heq : P'.coreRadicalP K = ((P.coreRadicalP K).map φ).comap φ' := by
    apply le_antisymm
    · exact le_comap_map_of_forall hφ hΛ hmax hQp' hQ'Λ hΛN'
    · exact hmax' _ (isPGroup_comap_map hφ' hQp) (comap_map_le hφ' hΛ hQΛ)
        (le_normalizer_comap_map hΛ hΛN)
  rw [heq, map_comap_map_eq hΛ hQΛ]

theorem fieldRigidIn_inner_of_free_eq_empty (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (P : InvPlacement n k) (P' : InvPlacement n k') (hJ : P.free = ∅) (hJ' : P'.free = ∅) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  have hcard := P.card_free
  have hcard' := P'.card_free
  rw [hJ, Finset.card_empty] at hcard
  rw [hJ', Finset.card_empty] at hcard'
  have h2k : 2 * k ≤ n := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  have h2k' : 2 * k' ≤ n := by
    have := Fintype.card_le_of_injective P'.supp P'.supp_injective
    simpa [two_mul] using this
  have hk : 2 ≤ k := by omega
  have hkk' : k = k' := by omega
  subst hkk'
  have hk0 : 0 < k := by omega
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hc₁ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₁).map (MulAut.conj γ).toMonoidHom = (X.map β₁.toMonoidHom).map φ₁ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₁ x).symm
  have hc₂ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₂).map (MulAut.conj γ).toMonoidHom = (X.map β₂.toMonoidHom).map φ₂ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₂ x).symm
  have hβ₁Λ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β₁.toMonoidHom = perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have hβ₂Λ : (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))).map
      β₂.toMonoidHom = perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K))) := by
    apply Subgroup.map_injective hφ₂
    rw [← hc₂, ← hX, hc₁, hβ₁Λ]
  have hQ := map_coreRadicalP_eq_of_free_eq_empty hq hφ₁ hφ₂ P P' hk0 hk0 hJ hJ' hX
  obtain ⟨-, -, -, -, hΛ₁, hMN₁, hdisj₁⟩ := P.coreRadicalP_spec hq hk0 hJ
  obtain ⟨-, -, -, -, hΛ₂, hMN₂, hdisj₂⟩ := P'.coreRadicalP_spec hq hk0 hJ'
  have hSN : (P.leviOneP K).map φ₁ ≤
      normalizer (((P.coreRadicalP K).map φ₁ : Subgroup Γ) : Set Γ) :=
    (map_mono hMN₁).trans (le_normalizer_map φ₁)
  have hS'N : (P'.leviOneP K).map φ₂ ≤
      normalizer (((P.coreRadicalP K).map φ₁ : Subgroup Γ) : Set Γ) := by
    rw [← hQ]
    exact (map_mono hMN₂).trans (le_normalizer_map φ₂)
  have hQS : Disjoint ((P.coreRadicalP K).map φ₁) ((P.leviOneP K).map φ₁) :=
    disjoint_map_of_injective hφ₁ hdisj₁
  have hQS' : Disjoint ((P.coreRadicalP K).map φ₁) ((P'.leviOneP K).map φ₂) := by
    rw [← hQ]
    exact disjoint_map_of_injective hφ₂ hdisj₂
  have hSS' : (P.coreRadicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁ =
      (P.coreRadicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hX, hΛ₂, Subgroup.map_sup, hQ]
  have hγQ : ((P.coreRadicalP K).map φ₁).map (MulAut.conj γ).toMonoidHom =
      (P.coreRadicalP K).map φ₁ := by
    rw [hc₁, P.map_coreRadicalP_eq_of_map_eq hq hk0 hJ β₁ hβ₁Λ]
  have hγM : ((P.coreRadicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁).map
      (MulAut.conj γ).toMonoidHom = (P.coreRadicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hc₁, hβ₁Λ]
  have hγM' : ((P.coreRadicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂).map
      (MulAut.conj γ).toMonoidHom = (P.coreRadicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂ := by
    rw [← hSS']
    exact hγM
  obtain ⟨γ₁, hγ₁⟩ := exists_mulAut_complement hSN hQS γ hγQ hγM
  obtain ⟨γ₂, hγ₂⟩ := exists_mulAut_complement hS'N hQS' γ hγQ hγM'
  have hint := complement_intertwine hSN hQS hQS' hSS' hγQ γ₁ γ₂ hγ₁ hγ₂
  set κ₁ := (P.leviOnePEquivPSL K hJ).symm with hκ₁
  set κ₂ := (P'.leviOnePEquivPSL K hJ').symm with hκ₂
  set e₁ := (P.leviOneP K).equivMapOfInjective φ₁ hφ₁ with he₁
  set e₂ := (P'.leviOneP K).equivMapOfInjective φ₂ hφ₂ with he₂
  set βbar₁ : MulAut (P.leviOneP K) := e₁.trans (γ₁.trans e₁.symm) with hβbar₁
  set βbar₂ : MulAut (P'.leviOneP K) := e₂.trans (γ₂.trans e₂.symm) with hβbar₂
  have hcond₁ : ∀ s : P.leviOneP K,
      ((βbar₁ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β₁ s ∈ P.coreRadicalP K := by
    intro s
    have he : φ₁ ((βbar₁ s : P.leviOneP K) : projectiveSL n K) =
        ((γ₁ (e₁ s) : (P.leviOneP K).map φ₁) : Γ) := by
      have : e₁ (βbar₁ s) = γ₁ (e₁ s) := by
        rw [hβbar₁, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₁ (((βbar₁ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β₁ s) ∈
        (P.coreRadicalP K).map φ₁ := by
      rw [map_mul, map_inv, he, h₁]
      exact hγ₁ (e₁ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₁ hqe]
    exact hq'
  have hcond₂ : ∀ s : P'.leviOneP K,
      ((βbar₂ s : P'.leviOneP K) : projectiveSL n K)⁻¹ * β₂ s ∈ P'.coreRadicalP K := by
    intro s
    have he : φ₂ ((βbar₂ s : P'.leviOneP K) : projectiveSL n K) =
        ((γ₂ (e₂ s) : (P'.leviOneP K).map φ₂) : Γ) := by
      have : e₂ (βbar₂ s) = γ₂ (e₂ s) := by
        rw [hβbar₂, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₂ (((βbar₂ s : P'.leviOneP K) : projectiveSL n K)⁻¹ * β₂ s) ∈
        (P'.coreRadicalP K).map φ₂ := by
      rw [map_mul, map_inv, he, h₂, hQ]
      exact hγ₂ (e₂ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₂ hqe]
    exact hq'
  obtain ⟨F, hF, hFσ, hFδ⟩ := exists_projFieldPart (K := K) hk
  have hF₁ := P.projFieldPart_congr_eq_linearFieldPart_of_free_eq_empty hq (Nat.le_of_succ_le hn)
    hk hJ F hF hFσ hFδ β₁ hβ₁Λ βbar₁ hcond₁ κ₁
  have hF₂ := P'.projFieldPart_congr_eq_linearFieldPart_of_free_eq_empty hq
    (Nat.le_of_succ_le hn) hk hJ' F hF hFσ hFδ β₂ hβ₂Λ βbar₂ hcond₂ κ₂
  have hT := mulAutHom_congr_eq_of_intertwine F (fun a b => ringEquiv_mul_comm _ _)
    (e₁.symm.trans κ₁) (e₂.symm.trans κ₂) (EPilot.mulEquivOfComplements hSN hQS hQS' hSS')
    γ₁ γ₂ hint
  have hA : MulAut.congr κ₁ βbar₁ = MulAut.congr (e₁.symm.trans κ₁) γ₁ := by
    ext A
    rfl
  have hB : MulAut.congr κ₂ βbar₂ = MulAut.congr (e₂.symm.trans κ₂) γ₂ := by
    ext A
    rfl
  rw [← hF₁, ← hF₂, hA, hB, hT]

end CFSG.SeitzReduction.LinearPilot
