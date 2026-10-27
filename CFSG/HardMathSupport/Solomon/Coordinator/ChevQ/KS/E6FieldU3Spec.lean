module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Pin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Quot
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Torus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Misc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Lang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar OuterFourInAux CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_mk)
open scoped MatrixGroups

section Spectral

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem zpow_ne_of_not_dvd {ζ : Lˣ} (hζ : orderOf ζ = 9) {n m : ℤ} (h : ¬ (9 : ℤ) ∣ n - m) :
    ζ ^ n ≠ ζ ^ m := by
  intro hnm
  apply h
  have h1 : ζ ^ (n - m) = 1 := by rw [zpow_sub, hnm, mul_inv_cancel]
  have h2 := (orderOf_dvd_iff_zpow_eq_one).2 h1
  rw [hζ] at h2
  exact_mod_cast h2

theorem iform_frame_adjacent {ψ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hn : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2) : iform (σ 0 1) (σ 0 2) = 1 := by
  have h012 := hψ.add 0 1 2
  have h1 := hn 0 1 (by decide)
  have h2 := hn 1 2 (by decide)
  have h3 := hn 0 2 (by decide)
  have e1 : iform (σ 0 2) (σ 0 2) =
      iform (σ 0 1) (σ 0 1) + 2 * iform (σ 0 1) (σ 1 2) + iform (σ 1 2) (σ 1 2) := by
    rw [← h012, iform_add_left, iform_add_right, iform_add_right, iform_comm (σ 1 2) (σ 0 1)]
    ring
  have e2 : iform (σ 0 1) (σ 0 2) = iform (σ 0 1) (σ 0 1) + iform (σ 0 1) (σ 1 2) := by
    rw [← h012, iform_add_right]
  omega

theorem no_entrywise_conj_rootSL2_HSL {α a₂ : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (ha₂ : IsRoot Tag.E6 a₂) (hαα : iform α α = 2) (hαa₂ : iform α a₂ = 1) (η : L ≃+* L)
    {ζ : Lˣ} (hζ : orderOf ζ = 9)
    (hη : Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 4 ∨ Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 7)
    (u : ModGL Tag.E6 L) :
    Units.map (entrywiseHom η.toRingHom) (rootSL2 Tag.E6 L α (HSL ζ)) ≠
      u * rootSL2 Tag.E6 L α (HSL ζ) * u⁻¹ := by
  intro hconj
  set r := rootSL2 Tag.E6 L α (HSL ζ) with hr
  set η' : Lˣ →* Lˣ := Units.map η.toRingHom.toMonoidHom with hη'
  have hr' : r = rootDiagUnit Tag.E6 (fun j => ζ ^ iform α (Pi.single j 1)) :=
    rootSL2_HSL_eq_rootDiagUnit' hα ζ
  have hmap : Units.map (entrywiseHom η.toRingHom) r =
      rootDiagUnit Tag.E6 (fun j => (η' ζ) ^ iform α (Pi.single j 1)) := by
    rw [hr', units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext j
    exact map_zpow η' ζ _
  have hspec : ∀ {w : RootModule Tag.E6 L} {c : L}, w ≠ 0 →
      (r : Module.End L (RootModule Tag.E6 L)) w = c • w →
        ∃ m : ℤ, |m| ≤ 2 ∧ c = ((ζ ^ m : Lˣ) : L) := by
    intro w c hw hrw
    rw [hr'] at hrw
    obtain ⟨γ, hγ, rfl⟩ := eigenvalue_rootDiagUnit _ hw hrw
    rw [rootChar_hsl]
    refine ⟨iform α γ, ?_, rfl⟩
    rcases hγ with hγ | rfl
    · exact abs_iform_le_two hα hγ
    · have : iform α (0 : Fin Tag.E6.rank → ℤ) = 0 := by
        have := iform_smul_right 0 α α
        simpa using this
      rw [this]
      simp
  have key : ∀ a, IsRoot Tag.E6 a → ∃ m : ℤ, |m| ≤ 2 ∧
      (((η' ζ) ^ iform α a : Lˣ) : L) = ((ζ ^ m : Lˣ) : L) := by
    intro a ha
    have h1 : ((Units.map (entrywiseHom η.toRingHom) r : ModGL Tag.E6 L) :
        Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L a) =
          (((η' ζ) ^ iform α a : Lˣ) : L) • rootVec Tag.E6 L a := by
      rw [hmap, rootDiagUnit_rootVec _ ha, rootChar_hsl]
    rw [hconj] at h1
    have hv0 : rootVec Tag.E6 L a ≠ 0 := rootVec_ne_zero ha
    set c : L := (((η' ζ) ^ iform α a : Lˣ) : L) with hc
    have h2 : (r : Module.End L (RootModule Tag.E6 L))
        (((u⁻¹ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L a)) =
          c • ((u⁻¹ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
            (rootVec Tag.E6 L a) := by
      have hinv : ∀ w : RootModule Tag.E6 L,
          ((u⁻¹ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
            (((u : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) w) = w := fun w => by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]
      have h3 := congrArg (((u⁻¹ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))) h1
      rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hinv,
        map_smul] at h3
      exact h3
    have hw0 : ((u⁻¹ : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
        (rootVec Tag.E6 L a) ≠ 0 := by
      intro h0
      apply hv0
      have := congrArg ((u : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) h0
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply, map_zero] at this
      exact this
    exact hspec hw0 h2
  rcases hη with h4 | h7
  · obtain ⟨m, hm, hmeq⟩ := key a₂ ha₂
    rw [hαa₂, h4] at hmeq
    have hmeq' : ζ ^ (4 : ℤ) = ζ ^ m := by
      have := Units.ext hmeq
      rw [zpow_one] at this
      simpa using this
    refine zpow_ne_of_not_dvd hζ ?_ hmeq'
    rw [abs_le] at hm
    omega
  · obtain ⟨m, hm, hmeq⟩ := key α hα
    rw [hαα, h7] at hmeq
    have hmeq' : ζ ^ (14 : ℤ) = ζ ^ m := by
      have h14 : (ζ ^ 7) ^ (2 : ℤ) = ζ ^ (14 : ℤ) := by
        rw [← zpow_natCast ζ 7, ← zpow_mul]
        norm_num
      rw [← h14]
      exact Units.ext hmeq
    refine zpow_ne_of_not_dvd hζ ?_ hmeq'
    rw [abs_le] at hm
    omega

end Spectral

section LayerR

set_option linter.unusedSectionVars false

open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem Std8.fieldAutU_rationalComponent
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω)))
    {R : Subgroup (ModGL Tag.E6 L)} (hRi : R = rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i)
    (η : L ≃+* L) {ζ : Lˣ} (hζ : orderOf ζ = 9)
    (hη : Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 4 ∨
      Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 7)
    (h : ModGL Tag.E6 L) (β : MulAut ↥R) (hβ3 : β ^ 3 = 1)
    (hβ : ∀ r, ((β r : ↥R) : ModGL Tag.E6 L) =
      h * Units.map (entrywiseHom η.toRingHom) (r : ModGL Tag.E6 L) * h⁻¹) :
    FieldAutU 3 (↥R ⧸ Subgroup.center ↥R) (autCenterQuot ↥R β) := by
  classical
  obtain ⟨F, ψ, σ, z, hFcard, hψ, hnorm, hΨ, hQ, hR, hker⟩ := D.exists_pinned_su3 hω i
  rw [← hRi] at hR
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  have hUF : UnitaryFieldData 2 3 ↥F := ⟨Nat.prime_two, by norm_num, by rw [hFcard]; norm_num⟩
  set G₀ := StatedSU 3 (2 ^ 3) ↥F with hG₀
  set π₀ : ↥G₀ →* ModGL Tag.E6 L :=
    (MulAut.conj z).toMonoidHom.comp (ψ.comp (statedSUToSL F 3 (2 ^ 3))) with hπ₀
  have hπ₀R : ∀ g, π₀ g ∈ R := fun g => by rw [hR]; exact ⟨g, rfl⟩
  let π₁ : ↥G₀ →* ↥R := π₀.codRestrict R hπ₀R
  have hπ₁surj : Function.Surjective π₁ := by
    intro r
    obtain ⟨g, hg⟩ : (r : ModGL Tag.E6 L) ∈ π₀.range := by rw [← hR]; exact r.2
    exact ⟨g, Subtype.ext hg⟩
  have hπ₁ker : π₁.ker ≤ Subgroup.center ↥G₀ := by
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker] at hg ⊢
    exact congrArg Subtype.val hg
  have hZ0 : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := center_quot_eq_bot hQ
  have hZ' : Subgroup.center ↥G₀ = (StatedScalars (Fin 3) ↥F).subgroupOf G₀ :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hFcard (by norm_num)
      (by decide)).2
  let E₀ := centralQuotEquiv π₁ hπ₁surj hπ₁ker hZ0
  let q₀ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* StatedProj G₀ := QuotientGroup.quotientMulEquivOfEq hZ'
  let e : (↥R ⧸ Subgroup.center ↥R) ≃* StatedProj G₀ := E₀.symm.trans q₀
  have he : ∀ g : ↥G₀, e (QuotientGroup.mk (π₁ g)) = projH _ g := by
    intro g
    have h1 : E₀.symm (QuotientGroup.mk (π₁ g)) = QuotientGroup.mk g := by
      rw [MulEquiv.symm_apply_eq]
      exact (centralQuotEquiv_mk π₁ hπ₁surj hπ₁ker hZ0 g).symm
    show q₀ (E₀.symm (QuotientGroup.mk (π₁ g))) = _
    rw [h1]
    exact QuotientGroup.quotientMulEquivOfEq_mk hZ' g
  refine fieldAutU_three_of_uFactor_ne_one hUF e (by rw [← map_pow, hβ3, map_one]) ?_
  intro hone
  obtain ⟨A, hA⟩ := (uFactor_eq_one_iff_exists_uConjAut hUF _).1 hone
  let cA : ↥G₀ →* ↥G₀ :=
    { toFun := fun g => ⟨_, uConjSU_mem hUF A g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hkey : ∀ g : ↥G₀, (β (π₁ g))⁻¹ * π₁ (cA g) ∈ Subgroup.center ↥R := by
    intro g
    have h1 : e (autCenterQuot ↥R β (QuotientGroup.mk (π₁ g))) = projH _ (cA g) := by
      have := DFunLike.congr_fun hA (e (QuotientGroup.mk (π₁ g)))
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
      rw [this, he, uConjAut_proj]
      rfl
    have h2 : autCenterQuot ↥R β (QuotientGroup.mk (π₁ g)) = QuotientGroup.mk (π₁ (cA g)) := by
      apply e.injective
      rw [h1, he]
    rw [autCenterQuot_mk] at h2
    exact QuotientGroup.eq.1 h2
  have hcomp : β.toMonoidHom.comp π₁ = π₁.comp cA :=
    eq_of_mul_mem_center_of_perfect hQ.1 _ _ hkey
  have hβπ : ∀ g : ↥G₀, β (π₁ g) = π₁ (cA g) := fun g => DFunLike.congr_fun hcomp g
  obtain ⟨a, ha⟩ := exists_sl_conj_statedSU F (A : GL (Fin 3) ↥F) (fun g => uConjSU_mem hUF A g)
  have hα : σ 0 1 ∈ componentRoots (rootCharHom (a0 ω)) i := by
    rw [hΨ]
    exact ⟨0, 1, by decide, rfl⟩
  have hαroot : IsRoot Tag.E6 (σ 0 1) := hψ.isRoot 0 1 (by decide)
  have ha₂root : IsRoot Tag.E6 (σ 0 2) := hψ.isRoot 0 2 (by decide)
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hrR : rootSL2 Tag.E6 L (σ 0 1) (HSL ζ) ∈ R := by
    rw [hRi]
    exact D.rootSL2_HSL_mem_rationalComponent hα hζ9
  obtain ⟨g₀, hg₀⟩ : rootSL2 Tag.E6 L (σ 0 1) (HSL ζ) ∈ π₀.range := by rw [← hR]; exact hrR
  set r := rootSL2 Tag.E6 L (σ 0 1) (HSL ζ) with hr
  set u : ModGL Tag.E6 L := z * ψ a * z⁻¹ with hu
  have hβr : ((β ⟨r, hrR⟩ : ↥R) : ModGL Tag.E6 L) = u * r * u⁻¹ := by
    have h1 : (⟨r, hrR⟩ : ↥R) = π₁ g₀ := Subtype.ext hg₀.symm
    rw [h1, hβπ]
    change π₀ (cA g₀) = _
    have h2 : statedSUToSL F 3 (2 ^ 3) (cA g₀) =
        a * statedSUToSL F 3 (2 ^ 3) g₀ * a⁻¹ := ha g₀
    have h3 : π₀ (cA g₀) = z * ψ (statedSUToSL F 3 (2 ^ 3) (cA g₀)) * z⁻¹ := rfl
    have h4 : r = z * ψ (statedSUToSL F 3 (2 ^ 3) g₀) * z⁻¹ := hg₀.symm
    rw [h3, h2, map_mul, map_mul, map_inv, h4, hu]
    group
  have hconj : Units.map (entrywiseHom η.toRingHom) r = (h⁻¹ * u) * r * (h⁻¹ * u)⁻¹ := by
    have h1 := hβ ⟨r, hrR⟩
    rw [hβr] at h1
    calc Units.map (entrywiseHom η.toRingHom) r
        = h⁻¹ * (h * Units.map (entrywiseHom η.toRingHom) r * h⁻¹) * h := by group
      _ = h⁻¹ * (u * r * u⁻¹) * h := by rw [← h1]
      _ = (h⁻¹ * u) * r * (h⁻¹ * u)⁻¹ := by group
  exact no_entrywise_conj_rootSL2_HSL hαroot ha₂root (hnorm 0 1 (by decide))
    (iform_frame_adjacent hψ hnorm) η hζ hη (h⁻¹ * u) hconj

theorem Std8.fieldAutU_of_hom
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω)))
    (η : L ≃+* L) {ζ : Lˣ} (hζ : orderOf ζ = 9)
    (hη : Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 4 ∨
      Units.map η.toRingHom.toMonoidHom ζ = ζ ^ 7)
    (h : ModGL Tag.E6 L) {G : Type} [Group G] (hG : CFSG.Open.IsQuasisimple G)
    (p : G →* ModGL Tag.E6 L)
    (hrange : p.range = rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i)
    (hker : p.ker ≤ Subgroup.center G) (α : MulAut G) (hα3 : α ^ 3 = 1)
    (hα : ∀ g, p (α g) = h * Units.map (entrywiseHom η.toRingHom) (p g) * h⁻¹) :
    FieldAutU 3 (G ⧸ Subgroup.center G) (autCenterQuot G α) := by
  let ϕ₀ : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
    (MulAut.conj h).toMonoidHom.comp (Units.map (entrywiseHom η.toRingHom))
  have hϕ₀ : ∀ u, ϕ₀ u = h * Units.map (entrywiseHom η.toRingHom) u * h⁻¹ := fun u => rfl
  have hϕinj : Function.Injective ϕ₀ :=
    (MulAut.conj h).injective.comp (Units.map_injective (entrywise_injective η.toRingHom))
  obtain ⟨β, hβ, hβpow⟩ := exists_mulAut_range_restrict p ϕ₀ hϕinj α (fun g => by
    rw [hα g, hϕ₀])
  have hβ3 : β ^ 3 = 1 := hβpow 3 hα3
  have hFA := Std8.fieldAutU_rationalComponent D hω i hrange η hζ hη h β hβ3 (fun r => by
    rw [hβ, hϕ₀])
  refine fieldAutU_of_central_epi p.rangeRestrict p.rangeRestrict_surjective ?_
    (center_quot_eq_bot hG) α β (fun g => ?_) hFA
  · intro g hg
    apply hker
    rw [MonoidHom.mem_ker] at hg ⊢
    exact congrArg Subtype.val hg
  · apply Subtype.ext
    rw [hβ]
    change p (α g) = ϕ₀ (p g)
    rw [hα g, hϕ₀]

end LayerR

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
