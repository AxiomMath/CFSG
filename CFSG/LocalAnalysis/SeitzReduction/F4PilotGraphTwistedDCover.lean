module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTables

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotGraphTwistedDCoverNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_omegaMinus_cover_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .omegaMinus8)
    {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ f) {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ∃ Φ : StatedOmega (StatedQuadMinus 4 k b c) →* G, Function.Injective Φ ∧
      Φ.range = neighbourCore e .X ∧ ∀ g, t * Φ g * t⁻¹ = Φ (omegaMinusBetaC k b c g) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Group.IsPerfect (StatedOmega (StatedQuadMinus 4 k b c)) := isPerfect_omegaMinus8 k hirr
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* StatedOmega (StatedQuadMinus 4 k b c)), Function.Surjective π' →
        π'.ker ≤ center E' → ∃ s : StatedOmega (StatedQuadMinus 4 k b c) →* E',
          ∀ g, π' (s g) = g :=
    fun E' _ _ π' hπ' hc => omegaMinus8_exists_section k hk4 hirr E' π' hπ' hc
  obtain ⟨S, _, hS, ρ, hρs, hρker⟩ := exists_surjective_neighbourCore_of_hr8Kind_graph hw hf e
    (N := .X) (κ := .omegaMinus8) (by decide) (by decide) (by decide) hX
  obtain ⟨π, hπ, hπker⟩ := omegaMinus8_covers k hk hirr S hS
  have : Group.IsPerfect (neighbourCore e .X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central π hπ hsplit ρ hρs hρker
  set Φ₁ : StatedOmega (StatedQuadMinus 4 k b c) →* G :=
    (neighbourCore e .X).subtype.comp Φ₀ with hΦ₁
  have hE₁ : Φ₁.range = neighbourCore e .X := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  have hker₁ : Φ₁.ker ≤ center (StatedOmega (StatedQuadMinus 4 k b c)) := by
    intro g hg
    have hg₀ : Φ₀ g = 1 := (neighbourCore e .X).subtype_injective (by rw [map_one]; exact hg)
    apply hπker
    rw [MonoidHom.mem_ker, ← hΦ₀, hg₀, map_one]
  have hinj₁ : Function.Injective Φ₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker₁.trans (center_omegaMinus8 k hirr).le
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ := exists_graphLift_of_closed_X hw hf e (κ := .omegaMinus8)
    (by decide) (by decide) hX hsplit Φ₁ hE₁ hker₁
  obtain ⟨Ψ, hΨ⟩ := exists_conj_omegaMinusBetaC k hw.one_le hk hirr β hβ2 hβo hβfix
  refine ⟨Φ₁.comp Ψ.toMonoidHom, hinj₁.comp Ψ.injective, ?_, fun g => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective, ← MonoidHom.range_eq_map,
      hE₁]
  · change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (omegaMinusBetaC k b c g))
    rw [← hβ, hΨ]

theorem exists_comm_omegaMinusBetaC_normalized_X {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2 ^ f) {c : k} (hc : ∀ s : k, s ^ 2 + 1 * s + c ≠ 0) (ε : k ≃+* K)
    {Φ : StatedOmega (StatedQuadMinus 4 k 1 c) →* G} (hr : Φ.range = neighbourCore e .X)
    (hi : Function.Injective Φ) (ht : ∀ g, t * Φ g * t⁻¹ = Φ (omegaMinusBetaC k 1 c g)) :
    ∃ δ : MulAut (StatedOmega (StatedQuadMinus 4 k 1 c)),
      (∀ g, δ (omegaMinusBetaC k 1 c g) = omegaMinusBetaC k 1 c (δ g)) ∧
        ∀ s, Φ (δ (omegaMinusIota hk hf hc s)) = levi6Hom e ε s := by
  set ι := omegaMinusIota hk hf hc with hιdef
  have hker : Φ.ker ≤ center (StatedOmega (StatedQuadMinus 4 k 1 c)) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ).2 hi]
    exact bot_le
  have hβ : ∀ A, Φ (omegaMinusBetaC k 1 c A) = t * Φ A * t⁻¹ := fun A => (ht A).symm
  have hιperf : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hfixr : fixedSubgroup (omegaMinusBetaC k 1 c) = ι.range :=
    (range_omegaMinusIota hk hf hc).symm
  have hcore : perfectCore (fixedSubgroup (omegaMinusBetaC k 1 c)) = ι.range := by
    rw [hfixr]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hmap := map_perfectCore_fixedSubgroup_eq Φ hker hβ
  rw [hcore, hr, perfectCore_neighbourCore_inf_centralizer_X hw hf e,
    ← neighbourLeviG_eq_modelToG] at hmap
  set κ : StatedSp 3 k →* G := Φ.comp ι with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := hi.comp (omegaMinusIota_injective hk hf hc)
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by
    rw [range_levi6Hom, hκr]
  set δ₀ : MulAut (StatedSp 3 k) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ₀ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ₀
  obtain ⟨s', hs'⟩ := exists_sq_add_eq_ringEquiv hc ρ
  set δ : MulAut (StatedOmega (StatedQuadMinus 4 k 1 c)) :=
    MulAut.conj (ι s) * omegaMinusFieldAut k c ρ s' hs' with hδ
  have hιs : omegaMinusBetaC k 1 c (ι s) = ι s := by
    have hs : ι s ∈ fixedSubgroup (omegaMinusBetaC k 1 c) := hfixr ▸ ⟨s, rfl⟩
    exact hs
  refine ⟨δ, fun A => ?_, fun g => ?_⟩
  · rw [hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, hιs, omegaMinusBetaC_omegaMinusFieldAut]
  · rw [← hκδ, hsρ]
    change Φ (δ (ι g)) = Φ (ι (s * statedSpMap (ρ : k →+* k) 3 g * s⁻¹))
    rw [hδ, MulAut.mul_apply, MulAut.conj_apply, omegaMinusFieldAut_iota hc hk hf ρ s' hs' g]
    simp only [map_mul, map_inv]
    rfl

theorem exists_omegaMinus_cover_normalized_X {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .omegaMinus8)
    {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ f) {c : k}
    (hc : ∀ s : k, s ^ 2 + 1 * s + c ≠ 0) (ε : k ≃+* K) :
    ∃ Φ : StatedOmega (StatedQuadMinus 4 k 1 c) →* G, Function.Injective Φ ∧
      Φ.range = neighbourCore e .X ∧ (∀ g, t * Φ g * t⁻¹ = Φ (omegaMinusBetaC k 1 c g)) ∧
        ∀ s, Φ (omegaMinusIota hk hf hc s) = levi6Hom e ε s := by
  obtain ⟨Φ, hi, hr, ht⟩ := exists_omegaMinus_cover_X hw hf e hX hk hc
  obtain ⟨δ, hδ, hn⟩ := exists_comm_omegaMinusBetaC_normalized_X hw hf e hk hc ε hr hi ht
  refine ⟨Φ.comp δ.toMonoidHom, hi.comp δ.injective, ?_, fun g => ?_, hn⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 δ.surjective, ← MonoidHom.range_eq_map, hr]
  · change t * Φ (δ g) * t⁻¹ = Φ (δ (omegaMinusBetaC k 1 c g))
    rw [ht, hδ]

theorem exists_omegaMinus_cover_normalized {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour}
    {e₂ : L ≃* adjointGroup .F4 K} (he₂ : IsNeighbourFrame e e₂ N)
    (h : HR8Kind e t f N .omegaMinus8) {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2 ^ f) {c : k} (hc : ∀ s : k, s ^ 2 + 1 * s + c ≠ 0) (ε : k ≃+* K) :
    ∃ Φ : StatedOmega (StatedQuadMinus 4 k 1 c) →* G, Function.Injective Φ ∧
      Φ.range = neighbourCore e N ∧ (∀ g, t * Φ g * t⁻¹ = Φ (omegaMinusBetaC k 1 c g)) ∧
        ∀ s, Φ (omegaMinusIota hk hf hc s) = levi6Hom e₂ ε s := by
  cases N with
  | X =>
    have h' : e₂ = e := he₂
    subst h'
    exact exists_omegaMinus_cover_normalized_X hw hf e₂ h hk hc ε
  | Y =>
    obtain ⟨hc', rfl⟩ := he₂
    obtain ⟨Φ, hi, hr, ht, hn⟩ :=
      exists_omegaMinus_cover_normalized_X hw hf _ ((hr8Kind_Y_iff_X e).1 h) hk hc ε
    exact ⟨Φ, hi, hr.trans (neighbourCore_Y_eq_X e).symm, ht, hn⟩
  | X' => exact he₂.elim

end Cover

end CFSG.SeitzReduction.F4Pilot
