module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOuter
public import CFSG.Assembly.GL83LieDefs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Proj

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open scoped commutatorElement

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

variable (H) in
abbrev projH : H →* StatedProj H := QuotientGroup.mk' _

variable (H) in
abbrev conjProjH : H →* MulAut (StatedProj H) :=
  (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).comp (projH H)

theorem projH_surjective : Function.Surjective (projH H) := QuotientGroup.mk'_surjective _

theorem projH_eq_projH_iff {g h : H} :
    projH H g = projH H h ↔ g⁻¹ * h ∈ (StatedScalars ι K).subgroupOf H :=
  QuotientGroup.eq

theorem scalars_subgroupOf_le_center :
    (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem eq_of_projH_eq_of_pow_char {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Nonempty ι]
    {x y : H} (hx : x ^ p = 1) (hy : y ^ p = 1) (h : projH H x = projH H y) : x = y := by
  rw [projH_eq_projH_iff] at h
  set z := x⁻¹ * y with hz
  have hzc : z ∈ center H := scalars_subgroupOf_le_center h
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : (x * z) ^ p = x ^ p * z ^ p := (Commute.mul_pow (mem_center_iff.mp hzc x) p)
    rw [← hyz, hy, hx, one_mul] at h1
    exact h1.symm
  rw [mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hcp : (c : K) ^ p = 1 := by
    have h2 := congrArg (fun g : H => ((g : GL ι K) : Matrix ι ι K) i i) hzp
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hc, Subgroup.coe_one,
      Units.val_one, one_apply_eq] at h2
    rw [← h2]
    simp [GeneralLinearGroup.scalar, Matrix.diagonal_pow]
  have hc1 : (c : K) = 1 := by
    have h3 : ((c : K) - 1) ^ p = 0 := by rw [sub_pow_char, hcp, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h3)
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [← hc, show c = 1 from Units.ext hc1, map_one]
    rfl
  rw [hyz, hz1, mul_one]

theorem isSubnormal_map_fixedH
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    {t : MulAut (StatedProj H)} (φ : H →* H) (hφ : ∀ g, t (projH H g) = projH H (φ g))
    {F : Subgroup H} (hF1 : ∀ g ∈ F, φ g = g)
    (hF2 : ∀ h : H, h⁻¹ * φ h ∈ (StatedScalars ι K).subgroupOf H → ∀ g ∈ F, h * g * h⁻¹ ∈ F) :
    F.map (conjProjH H) ≤ B ⊓ centralizer ({t} : Set _) ∧
      ((F.map (conjProjH H)).subgroupOf (B ⊓ centralizer ({t} : Set _))).IsSubnormal := by
  set C := B ⊓ centralizer ({t} : Set (MulAut (StatedProj H))) with hC
  set Inn := (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range with hInn
  have hInnN : Inn.Normal := conj_range_normal
  have hFC : F.map (conjProjH H) ≤ Inn ⊓ C := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨_, rfl⟩, hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : t * conjProjH H g * t⁻¹ = conjProjH H g := by
      rw [MonoidHom.comp_apply, mul_conj_mul_inv, hφ, hF1 g hg]
    calc conjProjH H g * t = t * conjProjH H g * t⁻¹ * t := by rw [h1]
      _ = t * conjProjH H g := by group
  have hnF : ∀ c ∈ Inn ⊓ C, ∀ x ∈ F.map (conjProjH H), c * x * c⁻¹ ∈ F.map (conjProjH H) := by
    rintro c ⟨⟨y, rfl⟩, -, hct⟩ _ ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ := projH_surjective y
    have hct' := mem_centralizer_singleton_iff.1 hct
    have h1 : MulAut.conj (t (projH H h)) = MulAut.conj (projH H h) := by
      have h0 : t * MulAut.conj (projH H h) * t⁻¹ = MulAut.conj (projH H h) := by
        have : MulAut.conj (projH H h) * t = t * MulAut.conj (projH H h) := hct'
        rw [← this, mul_inv_cancel_right]
      rwa [mul_conj_mul_inv] at h0
    have h2 : projH H h = projH H (φ h) := by rw [← hφ]; exact (hinj h1).symm
    refine ⟨h * g * h⁻¹, hF2 h (projH_eq_projH_iff.1 h2) g hg, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hCs : ((Inn ⊓ C).subgroupOf C).IsSubnormal := isSubnormal_inf_subgroupOf C
  exact ⟨hFC.trans inf_le_right, isSubnormal_subgroupOf_of_normalizes hFC hnF hCs⟩

theorem commute_oddCoreIn_of_fixedH [Finite (StatedProj H)]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    {t : MulAut (StatedProj H)} (φ : H →* H) (hφ : ∀ g, t (projH H g) = projH H (φ g))
    {F : Subgroup H} (hF1 : ∀ g ∈ F, φ g = g)
    (hF2 : ∀ h : H, h⁻¹ * φ h ∈ (StatedScalars ι K).subgroupOf H → ∀ g ∈ F, h * g * h⁻¹ ∈ F)
    (hq : IsQuasisimple (F.map (conjProjH H))) {y : MulAut (StatedProj H)}
    (hy : y ∈ oddCoreIn B t) {g : H} (hg : g ∈ F) : y (projH H g) = projH H g := by
  obtain ⟨hle, hs⟩ := isSubnormal_map_fixedH hinj hB φ hφ hF1 hF2
  have h := commute_of_mem_pPrimeCore hle hq hs (even_card_of_isQuasisimple hq) hy ⟨g, hg, rfl⟩
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProjH H g * y⁻¹ = conjProjH H g
  rw [h, mul_inv_cancel_right]

theorem conj_mem_eqLocus_of_scalarH (φ : H →* H) {h : H}
    (hh : h⁻¹ * φ h ∈ (StatedScalars ι K).subgroupOf H) {g : H}
    (hg : g ∈ MonoidHom.eqLocus φ (MonoidHom.id _)) :
    h * g * h⁻¹ ∈ MonoidHom.eqLocus φ (MonoidHom.id _) := by
  have hz := mem_center_iff.1 (scalars_subgroupOf_le_center hh)
  have hg' : φ g = g := hg
  have hφh : φ h = h * (h⁻¹ * φ h) := by rw [mul_inv_cancel_left]
  change φ (h * g * h⁻¹) = h * g * h⁻¹
  rw [map_mul, map_mul, map_inv, hg', hφh]
  set z := h⁻¹ * φ h
  calc h * z * g * (h * z)⁻¹ = h * (z * g) * z⁻¹ * h⁻¹ := by group
    _ = h * (g * z) * z⁻¹ * h⁻¹ := by rw [hz g]
    _ = h * g * h⁻¹ := by group

theorem lift_eq_of_commutator_eq {y : MulAut (StatedProj H)} (ψ : H →* H)
    (hψ : ∀ g, y (projH H g) = projH H (ψ g)) {F : Subgroup H} (hF : ⁅F, F⁆ = F)
    (h : ∀ g ∈ F, y (projH H g) = projH H g) {g : H} (hg : g ∈ F) : ψ g = g := by
  have hz : ∀ a ∈ F, a⁻¹ * ψ a ∈ Subgroup.center H := by
    intro a ha
    apply scalars_subgroupOf_le_center
    rw [← projH_eq_projH_iff, ← hψ]
    exact (h a ha).symm
  have hle : ⁅F, F⁆ ≤ MonoidHom.eqLocus ψ (MonoidHom.id _) := by
    rw [commutator_le]
    intro a ha b hb
    change ψ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ← mul_inv_cancel_left a (ψ a), ← mul_inv_cancel_left b (ψ b)]
    exact commutatorElement_mul_mem_center a b (hz a ha) (hz b hb)
  exact hle (hF.symm ▸ hg)

theorem fix_unipotent_family_matrix {N : Matrix ι ι K} {a b : ι} (hab : N a b ≠ 0)
    {D : GL ι K} {τ : K ≃+* K}
    (h : ∀ c : K, (D : Matrix ι ι K) * (1 + τ c • N.map τ) * ((D⁻¹ : GL ι K) : Matrix ι ι K) =
      1 + c • N) :
    τ = 1 ∧ (D : Matrix ι ι K) * N = N * (D : Matrix ι ι K) := by
  set M : Matrix ι ι K := (D : Matrix ι ι K) with hM
  set Mi : Matrix ι ι K := ((D⁻¹ : GL ι K) : Matrix ι ι K) with hMi
  have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ c : K, M * (τ c • N.map τ) * Mi = c • N := by
    intro c
    have h4 := h c
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M] at h4
    exact add_left_cancel h4
  have e1 := key 1
  rw [map_one, one_smul, one_smul] at e1
  have hτ : ∀ c, τ c = c := by
    intro c
    have e2 := key c
    rw [Matrix.mul_smul, Matrix.smul_mul, e1] at e2
    have := congrFun (congrFun e2 a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hab this
  have hτ1 : τ = 1 := RingEquiv.ext hτ
  refine ⟨hτ1, ?_⟩
  have hNτ : N.map τ = N := by
    ext x y
    simp [hτ]
  rw [hNτ] at e1
  calc M * N = M * N * Mi * M := by rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
    _ = N * M := by rw [e1]

end CFSG.ComponentClassification.Burgoyne.Proj
