module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)

local instance f4PilotGraphTwistedNormNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Field

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem primeFormFieldSU_barSU6 (ρ : F ≃+* F) (g : uGroup6 h) :
    primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ (barSU6 h g) =
      barSU6 h (primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ g) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_primeFormFieldSU, coe_barSU6, coe_barSU6, coe_primeFormFieldSU, Matrix.map_map,
    Matrix.map_map]
  ext i j
  exact map_bar_comm h ρ _

end Field

section Norm


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_normalized_coverU {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (e : L ≃* adjointGroup .F4 K) (ε : h.fixedField ≃+* K) {t : G} (Φ₁ : uGroup6 h →* G)
    (hker : Φ₁.ker ≤ center (uGroup6 h)) (hc : ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ (barSU6 h g))
    (hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X) :
    ∃ Φ' : uGroup6 h →* G, Φ'.range = Φ₁.range ∧ Φ'.ker ≤ center (uGroup6 h) ∧
      (∀ g, t * Φ' g * t⁻¹ = Φ' (barSU6 h g)) ∧
      ∀ s : StatedSp 3 h.fixedField, Φ' (uEmbed6 h s) = levi6Hom e ε s := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := finite_gramSU h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hfix : fixedSubgroup (barSU6 h) = (uEmbed6 h).range := fixedSubgroup_barSU6 h
  have hιperf : ⁅(uEmbed6 h).range, (uEmbed6 h).range⁆ = (uEmbed6 h).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hcore : perfectCore (fixedSubgroup (barSU6 h)) = (uEmbed6 h).range := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hβ : ∀ g, Φ₁ (barSU6 h g) = t * Φ₁ g * t⁻¹ := fun g => (hc g).symm
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₁ hker hβ
  rw [hcore, hD] at hmap
  set κ : StatedSp 3 h.fixedField →* G := Φ₁.comp (uEmbed6 h) with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : uEmbed6 h g ∈ center (uGroup6 h) := hker hg
    have hgc' : g ∈ center (StatedSp 3 h.fixedField) := by
      rw [mem_center_iff]
      intro x
      apply uEmbed6_injective h
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hgc (uEmbed6 h x)
    rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot] at hgc'
    exact mem_bot.mp hgc'
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 h.fixedField) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  obtain ⟨ρ'', hρ''⟩ := exists_ringEquiv_extend h ρ
  set δh : MulAut (uGroup6 h) :=
    MulAut.conj (uEmbed6 h s) * primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ'' with hδh
  have hβs : barSU6 h (uEmbed6 h s) = uEmbed6 h s := by
    have : uEmbed6 h s ∈ fixedSubgroup (barSU6 h) := by
      rw [hfix]
      exact ⟨s, rfl⟩
    exact this
  have hβδ : ∀ g, barSU6 h (δh g) = δh (barSU6 h g) := by
    intro g
    change barSU6 h (uEmbed6 h s * primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ'' g *
        (uEmbed6 h s)⁻¹) = uEmbed6 h s *
      primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ'' (barSU6 h g) * (uEmbed6 h s)⁻¹
    rw [map_mul, map_mul, map_inv, hβs, primeFormFieldSU_barSU6]
  set Φ' : uGroup6 h →* G := Φ₁.comp δh.toMonoidHom with hΦ'
  have hΦ'ι : ∀ g, Φ' (uEmbed6 h g) = levi6Hom e ε g := by
    intro g
    rw [← hκδ, hsρ, hκdef]
    change Φ₁ (uEmbed6 h s * primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ'' (uEmbed6 h g) *
        (uEmbed6 h s)⁻¹) =
      Φ₁ (uEmbed6 h (s * statedSpMap ((ρ : h.fixedField ≃+* h.fixedField) :
        h.fixedField →+* h.fixedField) 3 g * s⁻¹))
    rw [primeFormFieldSU_uEmbed6 h hρ'']
    simp only [map_mul, map_inv]
  refine ⟨Φ', ?_, ?_, fun g => ?_, hΦ'ι⟩
  · rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 δh.surjective,
      ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : δh g ∈ center (uGroup6 h) := hker hg
    rw [← Subgroup.map_center_eq (δh.symm : uGroup6 h ≃* uGroup6 h)]
    exact ⟨δh g, h1, δh.symm_apply_apply g⟩
  · change t * Φ₁ (δh g) * t⁻¹ = Φ₁ (δh (barSU6 h g))
    rw [hc, hβδ]

end Norm

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

variable [CharP K 2]

omit [Finite G]
  in
@[expose] def IsLeviNormalizedU {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 f F) (ε : h.fixedField ≃+* K) (e₁ : L ≃* adjointGroup .F4 K)
    (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G) : Prop :=
  ∀ s : StatedSp 3 h.fixedField, ΦX (twParamEquiv h (uEmbed6 h s)) = levi6Hom e₁ ε s

theorem exists_twParamX_normalized_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      ΦX.range = neighbourCore e .X ∧
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) ∧
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) ∧
      IsLeviNormalizedU h ε e ΦX := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F, _, _, hF, Φ₀, hE₀, hker₀⟩ := exists_su6_cover_neighbourCore hw hf e (by decide) hX
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * f) (by
    rw [hF, ← pow_mul, mul_comm])
  have h : UnitaryFieldData 2 f F := unitaryFieldData_of_card (by omega) hF
  have eS : StatedSU 6 (2 ^ f) F = gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h 6
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = neighbourCore e .X := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 6) (by norm_num) (by omega)
  have hsplit := forall_exists_section_of_mulEquiv eM.symm
    (statedSU_even_split hF (by decide) (by norm_num) hq4)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ :=
    exists_graphLift_of_closed_X hw hf e (by decide) (by decide) hX hsplit Φ₁ hE₁ hker₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary6_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = neighbourCore e .X := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ = Φ₂ (barSU6 h g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr', hk', hc', hn'⟩ := exists_normalized_coverU h e ε Φ₂ hker₂ hc hD
  refine ⟨F, inferInstance, inferInstance, inferInstance, h, ε,
    Φ'.comp (twParamEquiv h).symm.toMonoidHom, ?_, ?_, conj_comp_twParamEquiv_symm h hc', ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (twParamEquiv h).symm.surjective,
      ← MonoidHom.range_eq_map, hr', hE₂]
  · exact ker_comp_mulEquiv_le_center Φ' hk' (twParamEquiv h).symm
  · intro s
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hn']

theorem exists_twParamX_normalized {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N = .X ∨ N = .Y)
    (hk : HR8Kind e t f N .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K) (e₁ : L ≃* adjointGroup .F4 K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      IsNeighbourFrame e e₁ N ∧ ΦX.range = neighbourCore e N ∧
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) ∧
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) ∧
      IsLeviNormalizedU h ε e₁ ΦX := by
  rcases hN with rfl | rfl
  · obtain ⟨F, i1, i2, i3, h, ε, ΦX, hr, hk', hc, hn⟩ := exists_twParamX_normalized_X hw hf e hk
    exact ⟨F, i1, i2, i3, h, ε, e, ΦX, rfl, hr, hk', hc, hn⟩
  · have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
    obtain ⟨F, i1, i2, i3, h, ε, ΦX, hr, hk', hc, hn⟩ :=
      exists_twParamX_normalized_X hw hf _ ((hr8Kind_Y_iff_X e).1 hk)
    exact ⟨F, i1, i2, i3, h, ε, _, ΦX, ⟨inferInstance, rfl⟩, by rw [hr, neighbourCore_Y_eq_X],
      hk', hc, hn⟩

end Setting

end CFSG.SeitzReduction.F4Pilot
