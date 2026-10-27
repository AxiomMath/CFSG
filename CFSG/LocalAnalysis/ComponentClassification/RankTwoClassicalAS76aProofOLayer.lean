module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCommute
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Normal

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem conj_mem_statedOmega {R : (κ → K) → K} {Y : GL κ K}
    (hY : ∀ w, R ((Y : Matrix κ κ K) *ᵥ w) = R w) {Z : GL κ K} (hZ : Z ∈ StatedOmega R) :
    Y * Z * Y⁻¹ ∈ StatedOmega R := by
  set C := closure {A : GL κ K | ∀ v, R ((A : Matrix κ κ K) *ᵥ v) = R v} with hC
  have hYC : Y ∈ C := subset_closure hY
  have hmap : C.map (MulAut.conj Y).toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hYC hy) (inv_mem hYC)
    · intro hx
      refine ⟨Y⁻¹ * x * Y, mul_mem (mul_mem (inv_mem hYC) hx) hYC, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h1 : Y * Z * Y⁻¹ ∈ (StatedOmega R).map (MulAut.conj Y).toMonoidHom :=
    ⟨Z, hZ, rfl⟩
  unfold StatedOmega at h1 ⊢
  rwa [Subgroup.map_commutator, hmap] at h1

end Normal

section Bars

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}

omit [CharP K 2] in
theorem oKappaGL_conj (Y Z : GL ι₂ K) :
    oKappaGL oe Y * oKappaGL oe Z * (oKappaGL oe Y)⁻¹ = oKappaGL oe (Y * Z * Y⁻¹) := by
  rw [map_mul, map_mul, map_inv]

omit [CharP K 2] in
theorem exists_conj_oKappa {g : StatedOmega Q} {Y : GL ι₂ K}
    (hg : (g : GL ι K) = oKappaGL oe Y) (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (Z : StatedOmega Q₂) : ∃ Z' : StatedOmega Q₂, g * oKappa oe hQ Z * g⁻¹ = oKappa oe hQ Z' := by
  refine ⟨⟨Y * Z * Y⁻¹, conj_mem_statedOmega hY Z.2⟩, Subtype.ext ?_⟩
  change (g : GL ι K) * oKappaGL oe (Z : GL ι₂ K) * (g : GL ι K)⁻¹ =
    oKappaGL oe (Y * (Z : GL ι₂ K) * Y⁻¹)
  rw [hg, oKappaGL_conj]

omit [CharP K 2] in
theorem isometry_inv {Y : GL ι₂ K} (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) :
    ∀ w, Q₂ (((Y⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := by
  intro w
  have h1 := hY (((Y⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w)
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h1
  exact h1.symm

omit [CharP K 2] in
theorem oProj_mem_normalizer_oBarL {g : StatedOmega Q} {Y : GL ι₂ K}
    (hg : (g : GL ι K) = oKappaGL oe Y) (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) :
    oProj Q g ∈ normalizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))) := by
  have key : ∀ {g' : StatedOmega Q} {Y' : GL ι₂ K}, (g' : GL ι K) = oKappaGL oe Y' →
      (∀ w, Q₂ ((Y' : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) →
      ∀ y ∈ oBarL oe hQ, oProj Q g' * y * (oProj Q g')⁻¹ ∈ oBarL oe hQ := by
    rintro g' Y' hg' hY' _ ⟨Z, rfl⟩
    obtain ⟨Z', hZ'⟩ := exists_conj_oKappa hg' hY' Z
    refine ⟨Z', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← hZ', map_mul, map_mul, map_inv]
  have hgi : ((g⁻¹ : StatedOmega Q) : GL ι K) = oKappaGL oe Y⁻¹ := by
    rw [Subgroup.coe_inv, hg, map_inv]
  refine mem_normalizer_iff.mpr fun y => ⟨key hg hY y, fun hy => ?_⟩
  have h1 := key hgi (isometry_inv hY) _ hy
  rwa [map_inv, inv_inv, show (oProj Q g)⁻¹ * (oProj Q g * y * (oProj Q g)⁻¹) * oProj Q g = y by
    group] at h1

omit [CharP K 2] in
theorem commutatorElement_mem_oBarL {g g' : StatedOmega Q} {Y Y' : GL ι₂ K}
    (hg : (g : GL ι K) = oKappaGL oe Y) (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (hg' : (g' : GL ι K) = oKappaGL oe Y') (hY' : ∀ w, Q₂ ((Y' : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) :
    ⁅oProj Q g, oProj Q g'⁆ ∈ oBarL oe hQ := by
  have hc : ⁅Y, Y'⁆ ∈ StatedOmega Q₂ := by
    unfold StatedOmega
    exact commutator_mem_commutator (subset_closure hY) (subset_closure hY')
  refine ⟨⟨_, hc⟩, ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_commutatorElement]
  congr 1
  apply Subtype.ext
  change oKappaGL oe ⁅Y, Y'⁆ = ((⁅g, g'⁆ : StatedOmega Q) : GL ι K)
  rw [map_commutatorElement, commutatorElement_def, commutatorElement_def, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hg, hg']

end Bars

section Layer

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

theorem exists_oKappaGL_of_mem_centralizer (hθ : Function.Surjective θ)
    (hinj : Function.Injective (oProj Q)) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {Y : Subgroup G} (hWY : levLift θ (oBarTwo oe hQ hSL) ≤ Y)
    (hW₂Y : levLift θ (oBarOne oe hQ hSL) ≤ Y) {m : G}
    (hmM : m ∈ A ⊓ centralizer (Y : Set G)) (hm : m ∈ A) :
    ∃ g : StatedOmega Q, oProj Q g = θ ⟨m, hm⟩ ∧ ∃ Y' : GL ι₂ K,
      (g : GL ι K) = oKappaGL oe Y' ∧ ∀ w, Q₂ ((Y' : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := by
  obtain ⟨g, hg⟩ := oProj_surjective Q (θ ⟨m, hm⟩)
  refine ⟨g, hg, ?_⟩
  have hc : ∀ S : Subgroup (StatedProj (StatedOmega Q)), ⁅S, S⁆ = S → levLift θ S ≤ Y →
      ∀ x ∈ S, θ ⟨m, hm⟩ * x = x * θ ⟨m, hm⟩ := by
    intro S hS hSY x hx
    obtain ⟨w', hw', rfl⟩ := exists_mem_levLift hθ hS hx
    have h1 := (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (hSY hw')).symm
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1)
  refine exists_oKappaGL_of_commute (hQ := hQ) (hSL := hSL) ht0 ht1 (fun A' => hinj ?_)
    (fun B => hinj ?_)
  · rw [map_mul, map_mul, hg]
    exact hc _ (commutator_range_of_perfect _ hSL) hWY _ ⟨A', rfl⟩
  · rw [map_mul, map_mul, hg]
    exact hc _ (commutator_range_of_perfect _ hSL) hW₂Y _ ⟨B, rfl⟩

theorem layerCentralizer_eq_oLeviL (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hinj : Function.Injective (oProj Q)) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hperfL : ⁅oBarL oe hQ, oBarL oe hQ⁆ = oBarL oe hQ)
    (hqL : CFSG.IsQuasisimple ↥(oBarL oe hQ)) {Y : Subgroup G}
    (hWY : levLift θ (oBarTwo oe hQ hSL) ≤ Y) (hW₂Y : levLift θ (oBarOne oe hQ hSL) ≤ Y)
    (hLY : levLift θ (oBarL oe hQ) ≤ A ⊓ centralizer (Y : Set G)) :
    AS76b.layerCentralizer A Y = levLift θ (oBarL oe hQ) := by
  refine layerCentralizer_eq_levLift hker hθ hperfL hqL hLY (fun m hmM hm => ?_) ?_
  · obtain ⟨g, hg, Y', hgY, hY'⟩ :=
      exists_oKappaGL_of_mem_centralizer hθ hinj ht0 ht1 hWY hW₂Y hmM hm
    rw [← hg]
    exact oProj_mem_normalizer_oBarL hgY hY'
  · intro a ha b hb haA hbA
    obtain ⟨g, hg, Y', hgY, hY'⟩ :=
      exists_oKappaGL_of_mem_centralizer hθ hinj ht0 ht1 hWY hW₂Y ha haA
    obtain ⟨g', hg', Y'', hgY', hY''⟩ :=
      exists_oKappaGL_of_mem_centralizer hθ hinj ht0 ht1 hWY hW₂Y hb hbA
    rw [← hg, ← hg']
    exact commutatorElement_mem_oBarL hgY hY' hgY' hY''

end Layer

end CFSG.ComponentClassification.RankTwoClassical
