module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

set_option linter.unusedSectionVars false


section RankOne

variable {τ : Tag} {L : Type} [Field L]

theorem WSL_mul_uSL (c : L) : (WSL : SL2 L) * uSL c = vSL (-c) * WSL := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rank_one_scalar_compat_root {β β' : Fin τ.rank → ℤ} (hβ' : IsRoot τ β')
    (ψ : ModGL τ L →* ModGL τ L) (σ : L →+* L) {a b : L} (ha : a ≠ 0)
    (hu : ∀ c, ψ (rootSL2 τ L β (uSL c)) = rootSL2 τ L β' (uSL (a * σ c)))
    (hv : ∀ c, ψ (rootSL2 τ L β (vSL c)) = rootSL2 τ L β' (vSL (b * σ c))) : a * b = 1 := by
  have hinj : Function.Injective (rootSL2 τ L β') :=
    CFSG.RankThree.PartTwo.Census.Exceptional.rootSL2_injective hβ'
  have hN : (WSL : SL2 L) = uSL 1 * vSL (-1) * uSL 1 := WSL_eq_uSL_mul_vSL_mul_uSL
  set M : SL2 L := uSL a * vSL (-b) * uSL a with hM
  have hψN : ψ (rootSL2 τ L β WSL) = rootSL2 τ L β' M := by
    rw [hN, map_mul, map_mul, map_mul, map_mul, hu, hv]
    simp [hM, map_mul]
  have h1 : ψ (rootSL2 τ L β WSL) * ψ (rootSL2 τ L β (uSL 1)) =
      ψ (rootSL2 τ L β (vSL (-1))) * ψ (rootSL2 τ L β WSL) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, WSL_mul_uSL]
  rw [hψN, hu, hv] at h1
  simp only [map_one, mul_one, map_neg, mul_neg] at h1
  rw [← map_mul, ← map_mul] at h1
  have h2 := hinj h1
  have h3 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 1) h2
  simp [hM, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL, coe_vSL] at h3
  rcases h3 with h | h
  · linear_combination -h
  · exact absurd h ha

theorem rank_one_scalar_compat {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (ψ : ModGL τ L →* ModGL τ L) (σ : L →+* L) {a b : L} (ha : a ≠ 0)
    (hu : ∀ c, ψ (rootSL2 τ L β (uSL c)) = rootSL2 τ L β (uSL (a * σ c)))
    (hv : ∀ c, ψ (rootSL2 τ L β (vSL c)) = rootSL2 τ L β (vSL (b * σ c))) : a * b = 1 :=
  rank_one_scalar_compat_root hβ ψ σ ha hu hv


theorem frobGL_rootSL2 (σ : L ≃+* L) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 L) :
    frobGL σ (rootSL2 τ L β A) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  have hση : σ η = η := sq_eq_one_fixed σ hη
  have h := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
    (f := (frobGL σ).comp (rootSL2 τ L β))
    (g := (rootSL2 τ L β).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)) ?_
  · exact DFunLike.congr_fun h A
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change frobGL σ (rootSL2 τ L β (uSL c)) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c))
    rw [map_uSL, rootSL2_uSL_eq, rootSL2_uSL_eq, frobGL_pinnedX, map_zsmul]
    rfl
  · change frobGL σ (rootSL2 τ L β (vSL c)) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c))
    rw [map_vSL, hv, hv, frobGL_pinnedX, map_mul, hση]
    rfl

end RankOne

section Generation

variable {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_mem_iSup_rootRankOne_mapsRootLines (i : KernelComponent χ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i)) :
    ∃ n ∈ ⨆ β ∈ (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)),
        rootRankOneGroup τ L β, n ∈ monomialSubgroup τ L ∧ MapsRootLines n w := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    have hβi : β ∈ simpleRoots (componentRoots χ i) := hβ
    obtain ⟨-, -, hn, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L
      (simpleRoots_isRoot hβi)
    obtain ⟨hnN, hπ⟩ := hn 1
    refine ⟨rootWeylSL2 τ L β 1, ?_, hnN, ?_⟩
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ (simpleRoots (componentRoots χ i) :
        Set (Fin τ.rank → ℤ))) => rootRankOneGroup τ L β) β hβi le_rfl ⟨nSL 1, rfl⟩
    · have h := mapsRootLines_weylQuotientHom (R := L) ⟨_, hnN⟩
      rwa [hπ] at h
  | one => exact ⟨1, one_mem _, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    obtain ⟨n', hn', hn'N, hn'y⟩ := hy
    exact ⟨n * n', mul_mem hn hn', mul_mem hnN hn'N, hnx.mul hn'y⟩
  | inv x _ hx =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    exact ⟨n⁻¹, inv_mem hn, inv_mem hnN, hnx.inv⟩

theorem rootSubgroup_le_iSup_rootRankOne (i : KernelComponent χ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) :
    rootSubgroup τ L α ≤ ⨆ β ∈ (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)),
      rootRankOneGroup τ L β := by
  obtain ⟨w, hw, β₀, hβ₀, rfl⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hα
  obtain ⟨n, hn, hnN, hnw⟩ := exists_mem_iSup_rootRankOne_mapsRootLines (L := L) i hw
  have hβ₀r : IsRoot τ β₀ := simpleRoots_isRoot hβ₀
  have hL : rootSubgroup τ L β₀ ≤
      ⨆ β ∈ (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ L β := by
    refine le_trans ?_ (le_iSup₂_of_le (f := fun β (_ : β ∈ (simpleRoots (componentRoots χ i) :
      Set (Fin τ.rank → ℤ))) => rootRankOneGroup τ L β) β₀ hβ₀ le_rfl)
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hβ₀r).1]
    exact le_sup_left
  intro y hy
  have h1 := conj_mem_rootSpan_of_mapsRootLines (inv_mem hnN) hnw.inv (S := {w • β₀})
    (by rintro _ rfl; exact IsRoot.smul hβ₀r w) (by rwa [rootSpan_singleton])
  rw [Set.image_singleton, inv_smul_smul, inv_inv, rootSpan_singleton] at h1
  have h2 := mul_mem (mul_mem hn (hL h1)) (inv_mem hn)
  simpa [mul_assoc] using h2

theorem rootSpan_le_iSup_rootRankOne (i : KernelComponent χ) :
    rootSpan τ L (componentRoots χ i) ≤
      ⨆ β ∈ (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ L β :=
  iSup₂_le fun _ hα => rootSubgroup_le_iSup_rootRankOne i hα

theorem exists_lift_mem_closure_reflections (i : KernelComponent χ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots χ i, s = rootReflection γ}) :
    ∃ g ∈ rootSpan τ L (componentRoots χ i), g ∈ monomialSubgroup τ L ∧ MapsRootLines g w := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
    have hneg : -γ ∈ componentRoots χ i := (isRootComponent_componentRoots i).neg_mem γ hγ
    obtain ⟨hsup, hmon, hmaps⟩ := rootWeylOne_spec (K := L) hγr
    refine ⟨rootWeylOne τ L γ, ?_, hmon, hmaps⟩
    exact sup_le (rootSubgroup_le_rootSpan hγ) (rootSubgroup_le_rootSpan hneg) hsup
  | one => exact ⟨1, one_mem _, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    obtain ⟨n', hn', hn'N, hn'y⟩ := hy
    exact ⟨n * n', mul_mem hn hn', mul_mem hnN hn'N, hnx.mul hn'y⟩
  | inv x _ hx =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    exact ⟨n⁻¹, inv_mem hn, inv_mem hnN, hnx.inv⟩

end Generation


section Pin

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_pin (i : KernelComponent χ) (σ : L ≃+* L) (φ : ModGL τ L →* ModGL τ L)
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ γ ∈ componentRoots χ i, s = rootReflection γ})
    (hφ : ∀ γ ∈ componentRoots χ i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, φ (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m * σ c)) :
    ∃ y ∈ torusGroup τ L ⊔ rootSpan τ L (componentRoots χ i),
      ∀ g ∈ rootSpan τ L (componentRoots χ i), y * φ g * y⁻¹ = frobGL σ g := by
  classical
  obtain ⟨gw, hgwS, hgwM, hgwmaps⟩ := exists_lift_mem_closure_reflections (L := L) i hw
  set h : ModGL τ L := gw⁻¹ with hh
  have hhM : h ∈ monomialSubgroup τ L := inv_mem hgwM
  have hhmaps : MapsRootLines h w⁻¹ := hgwmaps.inv
  have hπ : weylQuotientHom τ L ⟨h, hhM⟩ = w⁻¹ := weylQuotientHom_eq hhmaps
  have hscal : ∀ β ∈ simpleRoots (componentRoots χ i), ∃ a b : L, a ≠ 0 ∧ a * b = 1 ∧ ∀ c,
      h * φ (rootSL2 τ L β (uSL c)) * h⁻¹ = rootSL2 τ L β (uSL (a * σ c)) ∧
      h * φ (rootSL2 τ L β (vSL c)) * h⁻¹ = rootSL2 τ L β (vSL (b * σ c)) := by
    intro β hβ
    have hβΨ : β ∈ componentRoots χ i := simpleRoots_subset hβ
    have hβr : IsRoot τ β := simpleRoots_isRoot hβ
    have hnegΨ : -β ∈ componentRoots χ i := (isRootComponent_componentRoots i).neg_mem β hβΨ
    obtain ⟨m, hm0, hmφ⟩ := hφ β hβΨ
    obtain ⟨m', hm'0, hm'φ⟩ := hφ (-β) hnegΨ
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hhM (IsRoot.smul hβr w)
    obtain ⟨μ', hμ'⟩ := monomial_conj_pinnedX hhM (IsRoot.smul (IsRoot.neg hβr) w)
    rw [hπ, inv_smul_smul] at hμ hμ'
    obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβr
    have hση : σ η = η := sq_eq_one_fixed σ hη
    have hu : ∀ c, h * φ (rootSL2 τ L β (uSL c)) * h⁻¹ =
        rootSL2 τ L β (uSL (((μ : L) * m) * σ c)) := by
      intro c
      rw [rootSL2_uSL_eq, hmφ, hμ, rootSL2_uSL_eq, map_zsmul]
      congr 1
      simp only [zsmul_eq_mul]
      ring
    have hv' : ∀ c, h * φ (rootSL2 τ L β (vSL c)) * h⁻¹ =
        rootSL2 τ L β (vSL (((μ' : L) * m') * σ c)) := by
      intro c
      rw [hv, hm'φ, hμ', hv, map_mul, hση]
      congr 1
      ring
    have hab : ((μ : L) * m) * ((μ' : L) * m') = 1 := by
      refine rank_one_scalar_compat hβr ((MulAut.conj h).toMonoidHom.comp φ) σ.toRingHom
        (mul_ne_zero μ.ne_zero hm0) (fun c => ?_) (fun c => ?_)
      · simpa [MulAut.conj_apply] using hu c
      · simpa [MulAut.conj_apply] using hv' c
    exact ⟨_, _, mul_ne_zero μ.ne_zero hm0, hab, fun c => ⟨hu c, hv' c⟩⟩
  choose! a b ha0 hab hconj using hscal
  set Δ := simpleRoots (componentRoots χ i) with hΔ
  let ν : Fin Δ.card → Fin τ.rank → ℤ := fun k => (Δ.equivFin.symm k : Fin τ.rank → ℤ)
  have hνinj : Function.Injective ν := Subtype.val_injective.comp Δ.equivFin.symm.injective
  have hνΔ : ∀ k, ν k ∈ simpleRoots (kernelRoots χ) := by
    intro k
    have hβi : ν k ∈ Δ := (Δ.equivFin.symm k).2
    obtain ⟨hβk, hi⟩ := simpleRoots_subset hβi
    rw [mem_simpleRoots_kernelRoots_iff hβk, hi]
    exact hβi
  obtain ⟨cT, hcT⟩ := algebraically_closed_lattice_character_interpolation L τ.rank Δ.card ν
    (linearIndependent_simpleRoots_kernelRoots hνinj hνΔ)
    fun k => (Units.mk0 (a (ν k)) (ha0 _ (Δ.equivFin.symm k).2))⁻¹
  have hχ : ∀ β ∈ Δ, (rootChar cT β : L) = (a β)⁻¹ := by
    intro β hβ
    have hk := hcT (Δ.equivFin ⟨β, hβ⟩)
    have hν : ν (Δ.equivFin ⟨β, hβ⟩) = β := by
      simp only [ν, Equiv.symm_apply_apply]
    have hk' : ((∏ j, cT j ^ ν (Δ.equivFin ⟨β, hβ⟩) j : Lˣ) : L) =
        (a (ν (Δ.equivFin ⟨β, hβ⟩)))⁻¹ := by
      rw [hk]
      simp
    rw [hν] at hk'
    exact hk'
  set y : ModGL τ L := rootDiagUnit τ cT * h with hy
  have hpin : ∀ β ∈ Δ, ∀ A : SL2 L, y * φ (rootSL2 τ L β A) * y⁻¹ =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
    intro β hβ A
    have hβr : IsRoot τ β := simpleRoots_isRoot hβ
    have heq := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
      (f := ((MulAut.conj y).toMonoidHom.comp φ).comp (rootSL2 τ L β))
      (g := (rootSL2 τ L β).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)) ?_
    · exact DFunLike.congr_fun heq A
    have hyφ : ∀ x : ModGL τ L, y * φ x * y⁻¹ =
        rootDiagUnit τ cT * (h * φ x * h⁻¹) * (rootDiagUnit τ cT)⁻¹ := by
      intro x
      rw [hy]
      group
    rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change y * φ (rootSL2 τ L β (uSL z)) * y⁻¹ =
        rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL z))
      rw [hyφ, (hconj β hβ z).1, (rootDiagUnit_conj_rootSL2 cT hβr _).1, map_uSL, hχ β hβ,
        ← mul_assoc, inv_mul_cancel₀ (ha0 β hβ), one_mul]
      rfl
    · change y * φ (rootSL2 τ L β (vSL z)) * y⁻¹ =
        rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL z))
      rw [hyφ, (hconj β hβ z).2, (rootDiagUnit_conj_rootSL2 cT hβr _).2, map_vSL]
      have hχ' : (((rootChar cT β)⁻¹ : Lˣ) : L) = a β := by
        rw [Units.val_inv_eq_inv_val, hχ β hβ, inv_inv]
      rw [hχ', ← mul_assoc, hab β hβ, one_mul]
      rfl
  refine ⟨y, mul_mem (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup cT))
    (Subgroup.mem_sup_right (inv_mem hgwS)), fun g hg => ?_⟩
  have hle : ⨆ β ∈ (Δ : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ L β ≤
      ((MulAut.conj y).toMonoidHom.comp φ).eqLocus (frobGL σ) := by
    refine iSup₂_le fun β hβ => ?_
    rintro _ ⟨A, rfl⟩
    have hβr : IsRoot τ β := simpleRoots_isRoot hβ
    change y * φ (rootSL2 τ L β A) * y⁻¹ = frobGL σ (rootSL2 τ L β A)
    rw [hpin β hβ A, frobGL_rootSL2 σ hβr]
  exact hle (rootSpan_le_iSup_rootRankOne i hg)

end Pin

end CFSG.HardMathSupport.Timmesfeld.LangTorus
