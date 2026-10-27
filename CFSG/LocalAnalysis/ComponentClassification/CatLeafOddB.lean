module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieAssembly
public import CFSG.LieType.Chevalley.OddTwistedE6InnerInvolutionComponents
public import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FixedTwoComponentsQuasisimple (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α * α = 1 → α ≠ 1 → ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L →
    IsQuasisimple L

theorem FixedTwoComponentsQuasisimple.of_mulEquiv {S M : Type} [Group S] [Group M] [Finite S]
    [Finite M] (e : S ≃* M) (h : FixedTwoComponentsQuasisimple M) :
    FixedTwoComponentsQuasisimple S := by
  intro α h2 h1 L hL
  have h2' : MulAut.congr e α * MulAut.congr e α = 1 := by
    rw [← map_mul, h2, map_one]
  have h1' : MulAut.congr e α ≠ 1 := by
    intro h
    apply h1
    rw [← map_one (MulAut.congr e)] at h
    exact (MulAut.congr e).injective h
  exact Sporadic.HeldB.pComponent_quasisimple_of_mulEquiv
    (Sporadic.HeldB.fixedSubgroupCongr e α) 2 Nat.prime_two (h _ h2' h1') L hL

theorem fixedTwoComponentsQuasisimple_of_model {S M : Type} [Group S] [Group M] [Finite S]
    (e : S ≃* M)
    (h : ∀ α : MulAut M, α * α = 1 → α ≠ 1 → ∀ r : ℕ, r.Prime →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent r L → IsQuasisimple L) :
    FixedTwoComponentsQuasisimple S := by
  have : Finite M := Finite.of_equiv _ e.toEquiv
  exact FixedTwoComponentsQuasisimple.of_mulEquiv e
    fun α h2 h1 L hL => h α h2 h1 2 Nat.prime_two L hL

theorem fixedTwoComponentsQuasisimple_psl {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (h : StatedClassicalModel S .PSL n p f) :
    FixedTwoComponentsQuasisimple S := by
  have : Fact p.Prime := ⟨h.1.1⟩
  obtain ⟨-, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psl_of_stated h
  let psi :=
    θ.trans (LocalAnalysis.ComponentInitial.LinearFieldFour.pslModelEquivProjectiveSL n p f)
  have : Finite (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n (GaloisField p f)) :=
    Finite.of_equiv _ psi.toEquiv
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  exact fixedTwoComponentsQuasisimple_of_model psi fun α h2 h1 =>
    CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components n (GaloisField p f)
      hchar hn α h1 (by rw [sq]; exact h2)

theorem fixedTwoComponentsQuasisimple_psu {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSU n p f) :
    FixedTwoComponentsQuasisimple S := by
  have : Fact p.Prime := ⟨h.1.1⟩
  have hn : 3 ≤ n := h.1.2.2.1
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psu_of_stated h
  let hU := CatalogueBUnitaryB.galoisField_unitaryFieldData p f hf
  let psi : S ≃* ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    (θ.trans (ClassicalModelStatedBridge.psuModelEquiv n p f)).trans
      (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega : 1 ≤ n)).symm
  exact fixedTwoComponentsQuasisimple_of_model psi fun α h2 h1 r hr L hL =>
    CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components hU hp2 hn α
      (orderOf_eq_prime (by rw [pow_two]; exact h2) h1) r hr L hL

theorem fixedTwoComponentsQuasisimple_psp {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSp n p f) :
    FixedTwoComponentsQuasisimple S := by
  have : Fact p.Prime := ⟨h.1.1⟩
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psp_of_stated h
  let psi : S ≃* StatedProj (StatedSp n (GaloisField p f)) :=
    θ.trans (ClassicalModelStatedBridge.pspModelEquiv n p f)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  exact fixedTwoComponentsQuasisimple_of_model psi fun α h2 h1 =>
    CatalogueBSymplecticB.odd_symplectic_involution_fixed_p_components p f Fact.out hp2 hf
      (GaloisField p f) hcard n hn α h2 h1

theorem fixedTwoComponentsQuasisimple_orthogonal {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel S t n p f) : FixedTwoComponentsQuasisimple S := by
  open CatalogueBOrthogonalInvolutionFixedComponents in
  have hfix := odd_orthogonal_involution_fixed_p_components t ht hp2 h
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact fixedTwoComponentsQuasisimple_of_model
      (CatalogueBOrthogonalPointData.coordinateOddWitnessEquiv K e) (hfix K hK e)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact fixedTwoComponentsQuasisimple_of_model
      (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e) (hfix K hK e)
  · obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h
    have hn : 1 ≤ n := by have := hadm.2.2; omega
    exact fixedTwoComponentsQuasisimple_of_model
      (CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K hn b c e)
      (hfix hn K hK b c hbc e)

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo CatalogueBLinearTwoInvolution in
theorem fixedTwoComponentsQuasisimple_psl_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {p f : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSL 2 p f) : FixedTwoComponentsQuasisimple S := by
  classical
  have : Fact p.Prime := ⟨h.1.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨hadm, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psl_of_stated h
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hsize : 5 ≤ Nat.card (GaloisField p f) :=
    hcard ▸ CatalogueBLinearTwoLocal.odd_rank_one_admissible_card p f hodd hadm
  let ψ : S ≃* coordinateG (GaloisField p f) :=
    θ.trans (CatalogueBLinearTwoModel.pslModelEquivCoordinateG p f)
  have hκ := mulAut_conj_injective_of_simple hna
  have hF : GeneralizedFitting.subgroup (MulAut S) = (MulAut.conj : S →* MulAut S).range := by
    rw [← generalizedFitting_eq_componentClassification]
    exact generalizedFitting_mulAut_eq_range hna
  let eI : GeneralizedFitting.subgroup (MulAut S) ≃* S :=
    (MulEquiv.subgroupCongr hF).trans (MonoidHom.ofInjective hκ).symm
  have heI : ∀ (s : S) (hs : MulAut.conj s ∈ GeneralizedFitting.subgroup (MulAut S)),
      eI ⟨MulAut.conj s, hs⟩ = s := by
    intro s hs
    apply hκ
    change (((MonoidHom.ofInjective hκ).symm (MulEquiv.subgroupCongr hF ⟨_, hs⟩) : S)
      |> MulAut.conj) = MulAut.conj s
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply (MulEquiv.subgroupCongr hF ⟨_, hs⟩)
    exact congrArg Subtype.val h1
  have : IsSimpleGroup (GeneralizedFitting.subgroup (MulAut S)) := eI.isSimpleGroup
  have hnc : ∃ a b : GeneralizedFitting.subgroup (MulAut S), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eI.symm x, eI.symm y, fun h => hxy (eI.symm.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨ρ, hρ, hext, -, -⟩ :=
    CatalogueBLinearTwoModel.generalizedFitting_semilinear_model_of_equiv hnc (eI.trans ψ)
  have hρc : ∀ s : S, ((ρ (MulAut.conj s) : coordinateE (GaloisField p f)) :
      Equiv.Perm (Omega (GaloisField p f))) = ((ψ s : coordinateG (GaloisField p f)) :
      Equiv.Perm (Omega (GaloisField p f))) := by
    intro s
    have hs : MulAut.conj s ∈ GeneralizedFitting.subgroup (MulAut S) := hF ▸ ⟨s, rfl⟩
    have h1 := hext ⟨MulAut.conj s, hs⟩
    rw [MulEquiv.trans_apply, heI s hs] at h1
    exact h1
  have hcomm : ∀ (α : MulAut S) (x : S), α x = x ↔
      ((ψ x : coordinateG (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) *
        ((ρ α : coordinateE (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) =
      ((ρ α : coordinateE (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) *
        ((ψ x : coordinateG (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) := by
    intro α x
    have hconj : MulAut.conj (α x) = α * MulAut.conj x * α⁻¹ := by
      apply MulEquiv.ext
      intro y
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have key : α x = x ↔ MulAut.conj x * α = α * MulAut.conj x := by
      constructor
      · intro hx
        have h1 := hconj
        rw [hx] at h1
        calc MulAut.conj x * α = α * MulAut.conj x * α⁻¹ * α := by rw [← h1]
          _ = α * MulAut.conj x := by group
      · intro hx
        apply hκ
        rw [hconj, ← hx, mul_inv_cancel_right]
    rw [key, ← hρc]
    constructor
    · intro hx
      have h1 := congrArg (fun g => ((ρ g : coordinateE (GaloisField p f)) :
        Equiv.Perm (Omega (GaloisField p f)))) hx
      simpa only [map_mul, Subgroup.coe_mul] using h1
    · intro hx
      apply hρ
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using hx
  intro α h2 h1 L hL
  set a : coordinateE (GaloisField p f) := ρ α with hadef
  have ha : orderOf (a : Equiv.Perm (Omega (GaloisField p f))) = 2 := by
    rw [Subgroup.orderOf_coe, hadef, orderOf_injective ρ hρ,
      orderOf_eq_prime (by rw [sq]; exact h2) h1]
  let φ : fixedSubgroup α →* fixedGroup (GaloisField p f)
      (a : Equiv.Perm (Omega (GaloisField p f))) :=
    (ψ.toMonoidHom.comp (fixedSubgroup α).subtype).codRestrict _ fun x => by
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      exact (hcomm α x).mp x.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => Subtype.ext (ψ.injective (congrArg Subtype.val hxy)), ?_⟩
    intro y
    have hy : ((y : coordinateG (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) *
        (a : Equiv.Perm (Omega (GaloisField p f))) =
        (a : Equiv.Perm (Omega (GaloisField p f))) *
          ((y : coordinateG (GaloisField p f)) : Equiv.Perm (Omega (GaloisField p f))) := by
      have := y.2
      rw [mem_subgroupOf, mem_centralizer_singleton_iff] at this
      exact this
    refine ⟨⟨ψ.symm y, ?_⟩, Subtype.ext (ψ.apply_symm_apply _)⟩
    change α (ψ.symm y) = ψ.symm y
    rw [hcomm, ψ.apply_symm_apply]
    exact hy
  exact Sporadic.HeldB.pComponent_quasisimple_of_mulEquiv (MulEquiv.ofBijective φ hφ) 2
    Nat.prime_two (fun L' hL' => ((linear_two_involution_fixed_p_components (GaloisField p f) p f
      Fact.out hodd hadm.2.1 hcard hsize a ha 2).1 L' hL').1) L hL

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem fixedTwoComponentsQuasisimple_exceptional {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ChevalleyExceptionalModel S t p f) : FixedTwoComponentsQuasisimple S := by
  have hf : 1 ≤ f := h.1.2.1
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .G2 (Or.inl rfl) K
        (hK ▸ hodd) α (by rw [pow_two]; exact h2) r hr L hL
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .F4
        (Or.inr (Or.inl rfl)) K (hK ▸ hodd) α (by rw [pow_two]; exact h2) r hr L hL
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      odd_E6_all_involution_fixed_p_components K (hK ▸ hodd) α (by rw [pow_two]; exact h2) r hr
        L hL
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      LieType.AlgebraicGroups.odd_E7_all_involution_fixed_p_components K (hK ▸ hodd) α
        (by rw [pow_two]; exact h2) r hr L hL
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .E8
        (Or.inr (Or.inr rfl)) K (hK ▸ hodd) α (by rw [pow_two]; exact h2) r hr L hL
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      odd_twisted_E6_all_involution_fixed_p_components hp hf hodd K hK σ hσ α
        (by rw [pow_two]; exact h2) r hr L hL
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf h.2
    exact fixedTwoComponentsQuasisimple_of_model e fun α h2 _ r hr L hL =>
      odd_triality_all_involution_fixed_p_components hp hp2 hf K hK σ hσ α
        (by rw [pow_two]; exact h2) r hr L hL

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem fixedTwoComponentsQuasisimple_smallRee {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) : FixedTwoComponentsQuasisimple S := by
  obtain ⟨-, -, hp, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := small_Ree_model_Schreier _ p f h
  subst hp
  obtain ⟨-, a, hfa, hrel⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨psi⟩ := hiso a K hfa hK ⟨e⟩
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := hfa ▸ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fixedTwoComponentsQuasisimple_of_model psi fun α h2 h1 r hr L hL =>
    CatalogueBSmallRee.small_Ree_involution_fixed_p_components a ha K hK' α
      (orderOf_eq_prime (by rw [pow_two]; exact h2) h1) r hr L hL

theorem fixedTwoComponentsQuasisimple_of_oddLieType {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (h : OddLieType S) :
    FixedTwoComponentsQuasisimple S := by
  rcases CatalogueBOddLie.oddLieType_cases h with ⟨t, n, p, f, hp2, hcl⟩ | ⟨p, f, hree⟩ |
      ⟨t, p, f, ht, hp, hp2, hex⟩
  · cases t with
    | PSL =>
      have hn : 2 ≤ n := hcl.1.2.2.1
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · exact fixedTwoComponentsQuasisimple_psl_two hna hp2 hcl
      · exact fixedTwoComponentsQuasisimple_psl hp2 h3 hcl
    | PSU => exact fixedTwoComponentsQuasisimple_psu hp2 hcl
    | PSp => exact fixedTwoComponentsQuasisimple_psp hp2 hcl
    | POmegaOdd => exact fixedTwoComponentsQuasisimple_orthogonal (Or.inl rfl) hp2 hcl
    | POmegaPlus => exact fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inl rfl)) hp2 hcl
    | POmegaMinus =>
      exact fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inr rfl)) hp2 hcl
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hcl.2.elim
  · exact fixedTwoComponentsQuasisimple_smallRee hree
  · exact fixedTwoComponentsQuasisimple_exceptional ht hp hp2 hex

end CFSG.ComponentClassification.CatLeaf
