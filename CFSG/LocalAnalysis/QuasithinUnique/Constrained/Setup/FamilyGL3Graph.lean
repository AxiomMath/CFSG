module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Section
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Component
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Permutation.AlternatingAutomorphism

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.ComponentClassification Matrix
open scoped commutatorElement

section GraphElement

variable {X : Type*} [Group X] {L : Subgroup X}

@[expose] def conjAutOfNormalizer (e : GL32 ≃* ↥L) {g : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) : MulAut GL32 where
  toFun s := e.symm ⟨g * (e s : X) * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg _).1 (e s).2⟩
  invFun s := e.symm ⟨g⁻¹ * (e s : X) * g, by
    have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1 (e s).2
    simpa using h⟩
  left_inv s := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply]
    group
  right_inv s := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply]
    group
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group

theorem conjAutOfNormalizer_val (e : GL32 ≃* ↥L) {g : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) (s : GL32) :
    (e (conjAutOfNormalizer e hg s) : X) = g * (e s : X) * g⁻¹ := by
  show ((e (e.symm _) : ↥L) : X) = _
  rw [MulEquiv.apply_symm_apply]

theorem exists_graph_element (e : GL32 ≃* ↥L) {g : X}
    (hgN : g ∈ Subgroup.normalizer (L : Set X))
    (hgout : ∀ l ∈ L, ¬ ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) :
    ∃ g' : X, g' ∈ Subgroup.normalizer (L : Set X) ∧
      ∀ s : GL32, g' * (e s : X) * g'⁻¹ = (e (tauHom s) : X) := by
  rcases aut_GL32_cases (conjAutOfNormalizer e hgN) with ⟨s₀, hs⟩ | ⟨s₀, hs⟩
  · exfalso
    refine hgout (e s₀ : X) (e s₀).2 fun x hx => ?_
    obtain ⟨s, rfl⟩ : ∃ s, (e s : X) = x := ⟨e.symm ⟨x, hx⟩, by simp⟩
    have h1 := conjAutOfNormalizer_val e hgN s
    rw [hs, MulAut.conj_apply] at h1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  · refine ⟨((e s₀ : ↥L) : X)⁻¹ * g, ?_, fun s => ?_⟩
    · exact Subgroup.mul_mem _ ((Subgroup.inv_mem _ (Subgroup.le_normalizer (e s₀).2)))
        hgN
    · have h1 := conjAutOfNormalizer_val e hgN s
      rw [hs, MulAut.mul_apply, glGraphAut_eq_tauAut, MulAut.conj_apply, tauAut_apply] at h1
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : g * (e s : X) * g⁻¹ = (e s₀ : X) * (e (tauHom s) : X) * (e s₀ : X)⁻¹ := h1.symm
      calc ((e s₀ : ↥L) : X)⁻¹ * g * (e s : X) * (((e s₀ : ↥L) : X)⁻¹ * g)⁻¹
          = ((e s₀ : ↥L) : X)⁻¹ * (g * (e s : X) * g⁻¹) * (e s₀ : X) := by group
        _ = (e (tauHom s) : X) := by rw [h2]; group

end GraphElement

section Twist

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}

local notation "ρ₀" => MonoidHom.id (V ≃ₗ[ZMod 2] V)

theorem fixIn_map_twist {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) (I : Submodule (ZMod 2) V) :
    (Layer.fixIn L I).map
        (Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective I :
          ↥I →ₗ[ZMod 2] ↥(I.map (g : V →ₗ[ZMod 2] V))) =
      Layer.fixIn L (I.map (g : V →ₗ[ZMod 2] V)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩ l hl
    have hl' : g⁻¹ * l * g ∈ L := Layer.conj_inv_mem_of_mem_normalizer hg hl
    have h1 : (g⁻¹ * l * g) (w : V) = w := hw _ hl'
    show l (g (w : V)) = g (w : V)
    calc l (g (w : V)) = g ((g⁻¹ * l * g) (w : V)) := by simp [LinearEquiv.mul_apply]
      _ = g (w : V) := by rw [h1]
  · intro hz
    refine ⟨(Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective I).symm z, ?_,
      LinearEquiv.apply_symm_apply _ _⟩
    intro l hl
    have hgl : g * l * g⁻¹ ∈ L := Layer.conj_mem_of_mem_normalizer hg hl
    have hz' : (g * l * g⁻¹) (z : V) = z := hz _ hgl
    have hzw : g (((Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective I).symm z :
        ↥I) : V) = (z : V) := by
      have := congrArg Subtype.val (LinearEquiv.apply_symm_apply
        (Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective I) z)
      exact this
    apply g.injective
    rw [← hzw] at hz'
    simpa [LinearEquiv.mul_apply] using hz'

@[expose] noncomputable def secTwist (g : V ≃ₗ[ZMod 2] V)
    (hg : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) (I : Submodule (ZMod 2) V) :
    (↥I ⧸ Layer.fixIn L I) ≃ₗ[ZMod 2]
      (↥(I.map (g : V →ₗ[ZMod 2] V)) ⧸ Layer.fixIn L (I.map (g : V →ₗ[ZMod 2] V))) :=
  Submodule.Quotient.equiv _ _
    (Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective I) (fixIn_map_twist hg I)

theorem secTwist_mk (g : V ≃ₗ[ZMod 2] V)
    (hg : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) (u : ↥I) :
    secTwist g hg I (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (⟨g (u : V), ⟨u, u.2, rfl⟩⟩ : ↥(I.map (g : V →ₗ[ZMod 2] V))) := rfl

theorem secTwist_equivariant (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) {g : V ≃ₗ[ZMod 2] V}
    (hgN : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hgτ : ∀ s : GL32, g * (e s : V ≃ₗ[ZMod 2] V) * g⁻¹ = (e (tauHom s) : V ≃ₗ[ZMod 2] V))
    (hI : Offender.IsInvariant ρ₀ (L ⊔ A) I)
    (hJ : Offender.IsInvariant ρ₀ (L ⊔ A) (I.map (g : V →ₗ[ZMod 2] V)))
    (s : GL32) (w : ↥I ⧸ Layer.fixIn L I) :
    secTwist g hgN I (secRep e hAn hI s w) =
      secRep e hAn hJ (tauHom s) (secTwist g hgN I w) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  unfold secRep
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Lift.actOn_L_mk hAn hI, secTwist_mk,
    secTwist_mk, Lift.actOn_L_mk hAn hJ]
  congr 1
  apply Subtype.ext
  simp only [Layer.resSub_apply, MonoidHom.id_apply]
  show g ((e s : V ≃ₗ[ZMod 2] V) (u : V)) = (e (tauHom s) : V ≃ₗ[ZMod 2] V) (g (u : V))
  rw [← hgτ s]
  simp [LinearEquiv.mul_apply]

theorem modIso_twist {E : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)} (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) {g : V ≃ₗ[ZMod 2] V}
    (hgN : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hgτ : ∀ s : GL32, g * (e s : V ≃ₗ[ZMod 2] V) * g⁻¹ = (e (tauHom s) : V ≃ₗ[ZMod 2] V))
    (hI : Offender.IsInvariant ρ₀ (L ⊔ A) I)
    (hJ : Offender.IsInvariant ρ₀ (L ⊔ A) (I.map (g : V →ₗ[ZMod 2] V)))
    (h : ModIso ρ (secRep e hAn hI)) : ModIso (ρ.comp tauHom) (secRep e hAn hJ) := by
  obtain ⟨Φ, hΦ⟩ := h
  refine ⟨Φ.trans (secTwist g hgN I), fun s x => ?_⟩
  show secTwist g hgN I (Φ (ρ (tauHom s) x)) = secRep e hAn hJ s (secTwist g hgN I (Φ x))
  have h1 : Φ (ρ (tauHom s) x) = secRep e hAn hI (tauHom s) (Φ x) := hΦ (tauHom s) x
  rw [h1, secTwist_equivariant e hAn hgN hgτ hI hJ, tauHom_tauHom]

end Twist

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

local notation "ρ₀" => MonoidHom.id (V ≃ₗ[ZMod 2] V)

theorem repDual_comp_tauHom : repDual.comp tauHom = repV :=
  MonoidHom.ext fun s => by
    show repV (tauHom (tauHom s)) = repV s
    rw [tauHom_tauHom]

theorem commutator_eq_bot_of_graph_normalizer {G L A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : IsComponentIn L G) (e : GL32 ≃* ↥L) {g : V ≃ₗ[ZMod 2] V}
    (hgN : g ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hgout : ∀ l ∈ L, ¬ ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹)
    (hAG : A ≤ G) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ Offender.weight ρ₀ A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      Offender.weight ρ₀ B < Offender.weight ρ₀ A) :
    ⁅L, A⁆ = ⊥ := by
  by_contra hcomm
  obtain ⟨I, hcs⟩ := Layer.Final.component_section hL hAG hAel hAne hoff hstrict hcomm
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  obtain ⟨hno, hch⟩ := Layer.noPQuotient_centralPChief_of_quasisimple hLq Nat.prime_two
  have hmax : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ A →
      Offender.weight ρ₀ B ≤ Offender.weight ρ₀ A := by
    intro B hB
    rcases hB.lt_or_eq with hlt | heq
    · by_cases hbot : B = ⊥
      · rw [hbot, Offender.weight_bot]
        exact hoff
      · exact (hstrict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
    · rw [heq]
  have hAn := hcs.A_norm
  have hLA := Layer.isInvariant_sup_subgroup hcs.inv_L hcs.inv_A
  have hgood : Layer.IsGoodModule ρ₀ L I := ⟨hcs.inv_L, hcs.comm, hcs.irr⟩
  have hirr := secRep_isIrr e hAn hLA hcs.irr
  obtain ⟨g', hg'N, hg'⟩ := exists_graph_element e hgN hgout
  have hJ : Layer.IsGoodModule ρ₀ L (I.map (ρ₀ g' : V →ₗ[ZMod 2] V)) := hgood.map hg'N
  have hJA : Offender.IsInvariant ρ₀ A (I.map (ρ₀ g' : V →ₗ[ZMod 2] V)) :=
    Layer.bestOffender_invariance_strict ρ₀ L A hAn hAel hcs.L_perf hno hch hmax hstrict hJ.inv
      hJ.comm hJ.irr
  have hLAJ := Layer.isInvariant_sup_subgroup hJ.inv hJA
  rcases irreducible_binary_GL3_classification (secRep e hAn hLA) hirr with h | h | h | h
  ·
    obtain ⟨Φ, hΦ⟩ := h
    apply hcs.Lbar_ne
    have hr : (secRep e hAn hLA).range = ⊥ := by
      refine MonoidHom.range_eq_bot_iff.2 (MonoidHom.ext fun s => LinearEquiv.ext fun y => ?_)
      have h1 : Φ ((repTriv s) (Φ.symm y)) = secRep e hAn hLA s (Φ (Φ.symm y)) := hΦ s _
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : (repTriv s) (Φ.symm y) = Φ.symm y := rfl
      rw [h2, LinearEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [secRep_range e hAn hLA] at hr
    exact hr
  ·
    have hJty : ModIso repDual (secRep e hAn hLAJ) :=
      modIso_twist (ρ := repV) e hAn hg'N hg' hLA hLAJ h
    exact false_of_natDual e hno hch hAn hAel hcs.L_perf hmax hgood hJ hcs.inv_A hJA h hJty
  ·
    have hJty : ModIso repV (secRep e hAn hLAJ) := by
      have := modIso_twist (ρ := repDual) e hAn hg'N hg' hLA hLAJ h
      rwa [repDual_comp_tauHom] at this
    exact false_of_natDual e hno hch hAn hAel hcs.L_perf hmax hJ hgood hJA hcs.inv_A hJty h
  · exact false_of_section_Q e hcs h

end Linear

section Actor

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

theorem gl3GraphNormalizerExclusion : GL3GraphNormalizerExclusionProp := by
  rintro V _ _ hV G L hL ⟨e⟩ ⟨g, -, hgN, hgout⟩ A hA
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hV
  have hinj : Function.Injective (binPsi θ).toMonoidHom := (binPsi θ).injective
  have hL' : IsComponentIn (L.map (binPsi θ).toMonoidHom) (G.map (binPsi θ).toMonoidHom) :=
    (Layer.Actor.isComponentIn_map_iff (binPsi θ)).2 ((Layer.Actor.isComp_iff L G).1 hL)
  have hA' := (Layer.Actor.isMinOffender_map_iff θ G A).2 hA
  have hgN' : binPsi θ g ∈ Subgroup.normalizer
      ((L.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) : Set (W ≃ₗ[ZMod 2] W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := (binPsi θ).surjective y
    have e1 : binPsi θ g * binPsi θ x * (binPsi θ g)⁻¹ = binPsi θ (g * x * g⁻¹) := by simp
    rw [e1, Layer.Actor.mem_map_equiv_iff, Layer.Actor.mem_map_equiv_iff]
    exact Subgroup.mem_normalizer_iff.1 hgN x
  have hgout' : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ¬ ∀ x ∈ L.map (binPsi θ).toMonoidHom,
      binPsi θ g * x * (binPsi θ g)⁻¹ = l * x * l⁻¹ := by
    rintro _ ⟨l₀, hl₀, rfl⟩ hall
    refine hgout l₀ hl₀ fun x₀ hx₀ => ?_
    apply hinj
    have := hall (binPsi θ x₀) ⟨x₀, hx₀, rfl⟩
    simpa using this
  have key := commutator_eq_bot_of_graph_normalizer hL'
    (e.symm.trans (Layer.Actor.mapEquiv (binPsi θ) L)) hgN' hgout' hA'.1 hA'.2.2.1 hA'.2.1
    hA'.2.2.2.1 hA'.2.2.2.2
  apply Subgroup.map_injective hinj
  rw [Layer.Actor.map_commutator_mulEquiv, key, Subgroup.map_bot]

end Actor

end CFSG.QuasithinUnique.Setup.Family
