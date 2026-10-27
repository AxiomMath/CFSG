module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open scoped commutatorElement

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem oddOrderIsometry_three (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[ZMod 2] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1) :
    OddOrderIsometry Q 3 x :=
  ⟨hxO, hx3, by decide, fun v hv => hQ.1 v fun w => by
    simpa [QuadraticMap.polarBilin_apply_apply] using hv w⟩

theorem isQuasisimple_supportedFixedDerived_of_finrank
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : V ≃ₗ[ZMod 2] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    (h8 : 8 ≤ finrank (ZMod 2) (fixedSpace x)) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
  (oddOrderIsometry_three hQ hxO hx3).isQuasisimple_supportedFixedDerived
    (CFSG.StandardType.OrthRestOdd.exists_totallySingular_three _
      (oddOrderIsometry_three hQ hxO hx3).polarBilin_fixed_nondegenerate h8)

@[expose] noncomputable def restrictDerived (Q : QuadraticForm (ZMod 2) V) (x : V ≃ₗ[ZMod 2] V) :
    ↥(supportedFixedDerived Q x) →*
      ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  ((restrictFixed Q x).comp (Subgroup.inclusion supportedFixedDerived_le_supportedBlock)).codRestrict _
    (fun g => (mem_supportedFixedDerived.1 g.2).choose_spec)

@[expose] noncomputable def restrictDerivedEquiv {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry Q 3 x) :
    ↥(supportedFixedDerived Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  MulEquiv.ofBijective (restrictDerived Q x)
    ⟨fun g g' h => by
      have h1 : (⟨g.1, supportedFixedDerived_le_supportedBlock g.2⟩ :
          ↥(supportedBlock Q x (X - 1))) =
          ⟨g'.1, supportedFixedDerived_le_supportedBlock g'.2⟩ :=
        restrictFixed_injective hx (congrArg Subtype.val h)
      exact Subtype.ext (Subtype.mk.inj h1),
     fun y => by
      obtain ⟨g, hg⟩ := restrictFixed_surjective hx y.1 (orthDerived_le_orthogonalGroup y.2)
      refine ⟨⟨g.1, mem_supportedFixedDerived.2 ⟨g.2, ?_⟩⟩, Subtype.ext ?_⟩
      · rw [show (⟨g.1, g.2⟩ : ↥(supportedBlock Q x (X - 1))) = g from rfl, hg]
        exact y.2
      · exact hg⟩

theorem coe_restrictDerivedEquiv {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry Q 3 x)
    (g : ↥(supportedFixedDerived Q x)) (w : fixedSpace x) :
    (((restrictDerivedEquiv hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[ZMod 2] fixedSpace x) w : V) = (g : V ≃ₗ[ZMod 2] V) (w : V) := rfl

theorem mem_supportedFixedDerived_of_fixes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[ZMod 2] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    (h8 : 8 ≤ finrank (ZMod 2) (fixedSpace x)) {g : V ≃ₗ[ZMod 2] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) (hgx : g * x = x * g)
    (hg : ∀ v : V, x (x v) + x v + v = 0 → g v = v) : g ∈ supportedFixedDerived Q x := by
  have hx := oddOrderIsometry_three hQ hxO hx3
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hT := CFSG.StandardType.OrthRestOdd.exists_totallySingular_three _
    hx.polarBilin_fixed_nondegenerate h8
  refine hx.mem_supportedFixedDerived_of_odd_pow hT ?_ (n := 3) (by decide) hg3
  refine mem_supportedBlock.2 ⟨mem_isometryCentralizer.2
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO, fun v => ?_⟩, fun v hv => ?_⟩
  · exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hgx
  · rw [CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.othersSpace_eq_cyc3 hK hx] at hv
    apply hg
    have := mem_primaryComponent.1 hv
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.aeval_cyc3] at this
    simpa [pow_two] using this

theorem apply_eq_of_commute_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[ZMod 2] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    (h5 : 5 ≤ finrank (ZMod 2) (fixedSpace x)) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ isometryCentralizer Q x)
    (hc : ∀ g ∈ supportedFixedDerived Q x, t * g = g * t) : ∀ w ∈ fixedSpace x, t w = w := by
  have hx := oddOrderIsometry_three hQ hxO hx3
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hTO := isometryRestrictFixed_mem_orthogonalGroup (Q := Q) (x := x) ⟨t, ht⟩
  have hT1 : isometryRestrictFixed Q x ⟨t, ht⟩ = 1 := by
    refine CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_isometry_eq_one hK
      hx.polarBilin_fixed_nondegenerate h5 hTO (fun y => ?_)
    obtain ⟨g, rfl⟩ := (restrictDerivedEquiv hx).surjective y
    have hcomm : isometryRestrictFixed Q x ⟨t, ht⟩ *
        ((restrictDerivedEquiv hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
          fixedSpace x ≃ₗ[ZMod 2] fixedSpace x) =
        ((restrictDerivedEquiv hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
          fixedSpace x ≃ₗ[ZMod 2] fixedSpace x) * isometryRestrictFixed Q x ⟨t, ht⟩ := by
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      have h1 := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (w : V)) (hc g g.2)
      simpa [coe_isometryRestrictFixed, coe_restrictDerivedEquiv] using h1
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  intro w hw
  have h1 := congrArg (fun f : fixedSpace x ≃ₗ[ZMod 2] fixedSpace x => (f ⟨w, hw⟩ : V)) hT1
  simpa [coe_isometryRestrictFixed] using h1

theorem finrank_fixedSpace_restrictDerivedEquiv {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry Q 3 x)
    (g : ↥(supportedFixedDerived Q x)) :
    finrank (ZMod 2) (fixedSpace
        ((restrictDerivedEquiv hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
          fixedSpace x ≃ₗ[ZMod 2] fixedSpace x)) =
      finrank (ZMod 2) ↥(fixedSpace (g : V ≃ₗ[ZMod 2] V) ⊓ fixedSpace x) := by
  have hmap : Submodule.map (fixedSpace x).subtype (fixedSpace
      ((restrictDerivedEquiv hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[ZMod 2] fixedSpace x)) = fixedSpace (g : V ≃ₗ[ZMod 2] V) ⊓ fixedSpace x := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf, mem_fixedSpace, Submodule.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, mem_fixedSpace.1 w.2⟩
      have := congrArg Subtype.val hw
      simpa [coe_restrictDerivedEquiv] using this
    · rintro ⟨hg, hv⟩
      refine ⟨⟨v, mem_fixedSpace.2 hv⟩, ?_, rfl⟩
      exact Subtype.ext (by simpa [coe_restrictDerivedEquiv] using hg)
  rw [← hmap]
  exact (Submodule.finrank_map_subtype_eq _ _).symm

open CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem apply_comm_of_mem_centralizer_of_finrank {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry Q 3 x)
    (hdim : finrank (ZMod 2) V = finrank (ZMod 2) (fixedSpace x) + 2) {g h : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)))
    (hh : h ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))) :
    ∀ v : V, x (x v) + x v + v = 0 → g (h v) = h (g v) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hirr := irreducible_cyc3 hK
  have : Fact (Irreducible (cyc3 (ZMod 2))) := ⟨hirr⟩
  set Vh := primaryComponent x.toLinearMap (cyc3 (ZMod 2)) with hVh
  have hc := isCompl_fixedSpace_cyc3 hK hx
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  have h2 := finrank_cyc3 (x := x) hK
  have hm1 : finrank (AdjoinRoot (cyc3 (ZMod 2))) Vh = 1 := by
    have : primaryMultiplicity x.toLinearMap (cyc3 (ZMod 2)) =
      finrank (AdjoinRoot (cyc3 (ZMod 2))) Vh := rfl
    omega
  have hscalar : ∀ G : V ≃ₗ[ZMod 2] V,
      G ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) →
      ∃ c : AdjoinRoot (cyc3 (ZMod 2)), ∀ w : Vh, (G (w : V) : V) = ((c • w : Vh) : V) := by
    intro G hG
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm1
      ((centralizerGL x (cyc3 (ZMod 2)) ⟨G, hG⟩ : BlockGL x (cyc3 (ZMod 2))) :
        Module.End (AdjoinRoot (cyc3 (ZMod 2))) Vh)
    refine ⟨c, fun w => ?_⟩
    have h1 := coe_centralizerGL x (cyc3 (ZMod 2)) ⟨G, hG⟩ w
    rw [hc] at h1
    exact h1.symm
  intro v hv
  have hvP : v ∈ Vh := by
    rw [hVh, mem_primaryComponent, aeval_cyc3]
    simpa [pow_two] using hv
  obtain ⟨cg, hcg⟩ := hscalar g hg
  obtain ⟨ch, hch⟩ := hscalar h hh
  have e1 := hch ⟨v, hvP⟩
  have e2 := hcg ⟨v, hvP⟩
  have e3 := hcg (ch • ⟨v, hvP⟩)
  have e4 := hch (cg • ⟨v, hvP⟩)
  simp only at e1 e2 e3 e4
  rw [e1]
  rw [e2]
  rw [e3, e4, smul_comm]

open CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem commutator_mem_supportedFixedDerived {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry Q 3 x)
    (hdim : finrank (ZMod 2) V = finrank (ZMod 2) (fixedSpace x) + 2) {g h : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ isometryCentralizer Q x) (hh : h ∈ isometryCentralizer Q x) :
    ⁅g, h⁆ ∈ supportedFixedDerived Q x := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hgc := (Subgroup.mem_inf.mp hg).2
  have hhc := (Subgroup.mem_inf.mp hh).2
  have hcI : ⁅g, h⁆ ∈ isometryCentralizer Q x := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hrel : ∀ k : V ≃ₗ[ZMod 2] V, k ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) →
      ∀ v : V, x (x v) + x v + v = 0 → x (x (k v)) + x (k v) + k v = 0 := by
    intro k hk v hv
    have hkx : ∀ u, k (x u) = x (k u) := fun u =>
      congrArg (fun f : V ≃ₗ[ZMod 2] V => f u) (Subgroup.mem_centralizer_singleton_iff.1 hk)
    have := congrArg k hv
    rw [map_add, map_add, hkx, hkx, map_zero] at this
    exact this
  have hfix : ∀ v : V, x (x v) + x v + v = 0 → ⁅g, h⁆ v = v := by
    intro v hv
    have hv1 := hrel _ (inv_mem hhc) v hv
    have hv2 := hrel _ (inv_mem hgc) _ hv1
    have hcm := apply_comm_of_mem_centralizer_of_finrank hx hdim hgc hhc _ hv2
    rw [commutatorElement_def]
    show g (h (g⁻¹ (h⁻¹ v))) = v
    rw [hcm]
    show h (g (g⁻¹ (h⁻¹ v))) = v
    rw [show g (g⁻¹ (h⁻¹ v)) = h⁻¹ v from g.apply_symm_apply _]
    exact h.apply_symm_apply v
  have hS : ⁅g, h⁆ ∈ supportedBlock Q x (X - 1) := by
    refine mem_supportedBlock.2 ⟨hcI, fun v hv => hfix v ?_⟩
    rw [othersSpace_eq_cyc3 hK hx] at hv
    have := mem_primaryComponent.1 hv
    rw [aeval_cyc3] at this
    simpa [pow_two] using this
  refine mem_supportedFixedDerived.2 ⟨hS, ?_⟩
  have h1 : restrictFixed Q x ⟨⁅g, h⁆, hS⟩ = ⁅isometryRestrictFixed Q x ⟨g, hg⟩,
      isometryRestrictFixed Q x ⟨h, hh⟩⁆ := by
    rw [← isometryRestrictFixed_restrictFixed]
    rw [← map_commutatorElement]
    rfl
  rw [h1]
  exact Subgroup.commutator_mem_commutator (isometryRestrictFixed_mem_orthogonalGroup _)
    (isometryRestrictFixed_mem_orthogonalGroup _)

theorem commutator_centralizer_le_supportedFixedDerived
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {y : ↥(orthDerived Q)} (hy3 : orderOf y = 3)
    (hdim : finrank (ZMod 2) V = finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) + 2) :
    ⁅Subgroup.centralizer ({y} : Set ↥(orthDerived Q)),
        Subgroup.centralizer ({y} : Set ↥(orthDerived Q))⁆ ≤
      (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) := by
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy3] at this
    exact congrArg Subtype.val this
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hx := oddOrderIsometry_three hQ hyO hy3'
  have hmem : ∀ g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)),
      (g : V ≃ₗ[ZMod 2] V) ∈ isometryCentralizer Q (y : V ≃ₗ[ZMod 2] V) := by
    intro g hg
    refine mem_isometryCentralizer.2
      ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup g.2), fun v => ?_⟩
    exact congrArg (fun f : ↥(orthDerived Q) => (f : V ≃ₗ[ZMod 2] V) v)
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [Subgroup.mem_subgroupOf]
  exact commutator_mem_supportedFixedDerived hx hdim (hmem g hg) (hmem h hh)

theorem mem_isometryCentralizer_of_mem_centralizer {x g : ↥(orthDerived Q)}
    (hg : g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) :
    (g : V ≃ₗ[ZMod 2] V) ∈ isometryCentralizer Q (x : V ≃ₗ[ZMod 2] V) :=
  mem_isometryCentralizer.2
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup g.2), fun v =>
      congrArg (fun f : ↥(orthDerived Q) => (f : V ≃ₗ[ZMod 2] V) v)
        (Subgroup.mem_centralizer_singleton_iff.1 hg)⟩

theorem mem_centralizer_of_mem_isometryCentralizer {x g : ↥(orthDerived Q)}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ isometryCentralizer Q (x : V ≃ₗ[ZMod 2] V)) :
    g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2))

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
