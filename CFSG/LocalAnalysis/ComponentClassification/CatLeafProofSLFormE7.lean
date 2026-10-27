module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Twist

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem e7Word2_1_fix_four : applyWordIdx e7Certificate e7Word2_1 4 = 4 := by
  decide +kernel

theorem thetaMap_e7Word2_1_alpha5 :
    thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 (Pi.single (e7Node 4) 1) =
      Pi.single (e7Node 4) 1 := by
  obtain ⟨hl4, hr4⟩ := root_fin e7Certificate_check (e7Node 4)
  obtain ⟨-, he⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hl4
  rw [thetaMap_one_apply, ← hr4, ← he]
  change e7Certificate.root (applyWordIdx e7Certificate e7Word2_1 4) = _
  rw [e7Word2_1_fix_four]
  rfl

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e7_datum_classes
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ} {l : List (Fin (Tag.rank .E7))}
    (hml : (m = 0 ∧ l = []) ∨ (m = 1 ∧ l = []) ∨ ((m = 2 ∨ m = 3) ∧ (l = [] ∨ l = e7Word2_1)))
    (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 l) 1 γ)) :
    D.θ (toReal (Pi.single (e7Node 4) 1)) = toReal (Pi.single (e7Node 4) 1) ∧
      ∃ S : Set (Fin (Tag.rank .E7) → ℤ), Pi.single (e7Node 4) 1 ∈ S ∧
        ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
          (D.withOrbit J').simpleRootsJ = S ∨
            ∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧ D.θ (toReal β₀) = toReal β₀ := by
  have hne : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      (D.withOrbit J').simpleRootsJ ≠ ∅ := fun J' hq h0 =>
    (Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq)
      (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
  have hone : ∀ {S : Set (Fin (Tag.rank .E7) → ℤ)}, simpleUnion D.χ = S →
      (∀ i : KernelComponent D.χ, simpleUnion D.χ ∩ componentRoots D.χ i = ∅ ∨
        simpleUnion D.χ ∩ componentRoots D.χ i = S) →
      ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
        (D.withOrbit J').simpleRootsJ = S ∨
          ∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧ D.θ (toReal β₀) = toReal β₀ := by
    intro S hS hcls J' hq
    rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hS hcls with h0 | h
    · exact absurd h0 (hne J' hq)
    · exact Or.inl h
  have hfix : D.θ (toReal (Pi.single (e7Node 4) 1)) = toReal (Pi.single (e7Node 4) 1) := by
    rw [hθ]
    rcases hml with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩
    · rw [thetaMap_nil_one]
    · rw [thetaMap_nil_one]
    · rw [thetaMap_nil_one]
    · rw [thetaMap_e7Word2_1_alpha5]
  refine ⟨hfix, ?_⟩
  rcases hml with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨hm, -⟩
  · exact ⟨Set.range e7SimpleRoot, ⟨4, rfl⟩,
      hone (by rw [hχ]; exact simpleUnion_e7_zero) (e7_simple_inter_zero hχ)⟩
  ·
    have hθ1 : ∀ γ, D.θ (toReal γ) = toReal γ := fun γ => by rw [hθ, thetaMap_nil_one]
    refine ⟨Set.range e7D6Root, ⟨2, rfl⟩, fun J' hq => ?_⟩
    obtain ⟨i₀, hi₀⟩ := J'.2
    have hJ : ∀ i, i ∈ (J' : Set (KernelComponent D.χ)) ↔ i = i₀ := fun i => by
      rw [← hi₀, classOrbit_eq_singleton D hθ1, Set.mem_singleton_iff]
    have hS : (D.withOrbit J').simpleRootsJ = simpleUnion D.χ ∩ componentRoots D.χ i₀ := by
      ext β
      constructor
      · rintro ⟨⟨i, -, hβi⟩, h, hJβ⟩
        exact ⟨Set.mem_iUnion.2 ⟨i, hβi⟩, h, (hJ _).1 hJβ⟩
      · rintro ⟨hβ, h, hβi⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hβ
        exact ⟨⟨i, Set.mem_univ _, hi⟩, h, (hJ _).2 hβi⟩
    rcases e7_simple_inter_one hχ i₀ with h | h | h
    · exact absurd (hS.trans h) (hne J' hq)
    · exact Or.inl (hS.trans h)
    · exact Or.inr ⟨e7Theta, hS.trans h, hθ1 e7Theta⟩
  · rcases hm with rfl | rfl
    · exact ⟨Set.range e7A7Root, ⟨3, by decide⟩,
        hone (by rw [hχ]; exact simpleUnion_e7_two) (e7_simple_inter_two hχ)⟩
    · exact ⟨Set.range e7E6Root, ⟨3, by decide⟩,
        hone (by rw [hχ]; exact simpleUnion_e7_three) (e7_simple_inter_three hχ)⟩

theorem oddExcInnerDiagSLForm_E7
    : OddExcInnerDiagSLForm .E7 := by
  intro K _ _ p f hp hp2 hK α g a hαg hαo
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  refine ⟨fun L hL => odd_E7_all_involution_fixed_p_components K hKodd α hα2 2 Nat.prime_two L
    hL, ?_⟩
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hf hK hαg hα2
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure K) p hp2 f hf
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure K) hp2 f hf
  set R := fixedPointsIn (adjointGroup .E7 (AlgebraicClosure K))
    (frobTwistGL .E7 (AlgebraicClosure K) p f 1) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let eA' : fixedSubgroup α ≃* N := eA
  refine slComponentForm_of_mulEquiv eA' ?_
  have h2c : ∀ S' : Subgroup N, IsComponent S' → S'.map N.subtype ≤ N ∧
      CFSG.IsPComponent 2 ((S'.map N.subtype).subgroupOf N) := fun S' hS' => by
    have hsub : (S'.map N.subtype).subgroupOf N = S' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
    refine ⟨Subgroup.map_subtype_le _, ExcSelector.isPComponent_two_subgroupOf ?_⟩
    exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (Subgroup.map_subtype_le _)).2 (by rw [hsub]; exact hS')
  by_cases hex : ∃ L₀ : Subgroup N, IsComponent L₀
  swap
  · intro L hL
    exact absurd ⟨L, hL⟩ hex
  obtain ⟨L₀, hL₀⟩ := hex
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, hall⟩ :=
    exists_datum_uniform_of_twistReduction p hp2 hk hf (Or.inr (Or.inr rfl)) (ρ := 1)
      (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2) _ (h2c L₀ hL₀).1 (h2c L₀ hL₀).2
  have hJ : ∀ L : Subgroup N, IsComponent L → ∃ J' : Set.range Dd.classOrbit,
      IsQuasisimple (Dd.withOrbit J').orbitGroup ∧
        Nonempty (L ≃* (Dd.withOrbit J').orbitGroup) := by
    intro L hL
    obtain ⟨hle, hc⟩ := h2c L hL
    obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall _ hle hc
    obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
    exact ⟨J', hq, ⟨((L.equivMapOfInjective _ N.subtype_injective).trans
      (eL.trans (MulEquiv.subgroupCongr hJ'))).trans
        (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)⟩⟩
  have hKe : Nat.card K = p ^ Dd.e := by
    rw [hDe]
    exact hK
  have hml : (mr.mask = 0 ∧ l = []) ∨ (mr.mask = 1 ∧ l = []) ∨
      ((mr.mask = 2 ∨ mr.mask = 3) ∧ (l = [] ∨ l = e7Word2_1)) := by
    simp only [e7SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
    rcases hmr with rfl | rfl | rfl | rfl
    · simp only [e7OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inl ⟨rfl, hl⟩
    · simp only [e7OmegaWords1, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inl ⟨rfl, hl⟩)
    · simp only [e7OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inr ⟨Or.inl rfl, hl⟩)
    · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inr ⟨Or.inr rfl, hl⟩)
  obtain ⟨hfix, S, hS, hΔ⟩ := e7_datum_classes Dd hml hDχ hDθ
  exact slComponentForm_of_datum_classes Dd hKe hJ hS hfix hΔ

end CFSG.ComponentClassification.CatLeafProof
