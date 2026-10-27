module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearTwoSocle
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open FourGroupEvenCanonical CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open LinearMap (BilinForm)

section Tools

theorem map_commutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map (e : G →* H) = commutator H := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]

theorem nonabelian_of_isQuasisimple {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) : ∃ x y : L, x * y ≠ y * x := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.2
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_contra hc
  push Not at hc
  exact Group.IsPerfect.not_isMulCommutative L (isMulCommutative_iff.mpr hc)

theorem socle_images {A Q : Type*} [Group A] [Group Q] {W : Subgroup A} {ρ : A →* MulAut Q}
    (hinj : Function.Injective ρ) (φ : W ≃* Q) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (a : A) :
    W.map ρ = inner Q ∧ (W ⊓ centralizer {a}).map ρ = inner Q ⊓ centralizer {ρ a} ∧
      (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a} := by
  have h1 : W.map ρ = inner Q := map_eq_range_conj φ hρW
  have h3 := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hle : inner Q ≤ ρ.range := h1 ▸ Subgroup.map_le_range ρ W
  refine ⟨h1, ?_, h3⟩
  rw [Subgroup.map_inf_eq _ _ _ hinj, h1, h3, ← inf_assoc, inf_eq_left.mpr hle]

theorem card_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have h6 : Nat.factorial 6 = 720 := rfl
  omega

end Tools

section Sources

variable {X : Type} [Group X] {p f : ℕ}

theorem source_of_symplectic {k : Type} [Field k] [Finite k] {e r : ℕ} (hk : Nat.card k = 2 ^ e)
    (hr : 1 ≤ r) (eX : X ≃* StatedSp r k) (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel X .PSL 2 p f ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel X .PSL 3 2 2) :
    r = 1 ∧ e = 2 ∧ p = 5 ∧ f = 1 ∧ StatedClassicalModel X .PSL 2 p f ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  obtain ⟨hpar, hA7, hP34, -, -⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated hk hr ⟨eX⟩
  have h2 : StatedClassicalModel X .PSL 2 p f := by
    rcases hsrc with h2 | ⟨e7⟩ | h322
    · exact h2
    · exact (not_nonempty_iff.mpr hA7 e7).elim
    · exact (hP34 h322).elim
  obtain ⟨hr1, he2, hp5, hf1⟩ := hpar p f hp2 h2
  exact ⟨hr1, he2, hp5, hf1, h2, hA7, hP34⟩

theorem source_of_alternating_six (eX : X ≃* alternatingGroup (Fin 6)) (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel X .PSL 2 p f ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel X .PSL 3 2 2) :
    p = 3 ∧ f = 2 ∧ StatedClassicalModel X .PSL 2 p f ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  have hX : Nat.card X = 360 := (Nat.card_congr eX.toEquiv).trans card_alternatingGroup_fin_six
  have hA7 : IsEmpty (X ≃* alternatingGroup (Fin 7)) := ⟨fun e7 => by
    have h1 := (Nat.card_congr e7.toEquiv).symm.trans hX
    rw [UnbalancingLocal.card_alternating_seven] at h1
    omega⟩
  have hP34 : ¬ StatedClassicalModel X .PSL 3 2 2 := by
    rintro ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩
    have h1 := (Nat.card_congr χ.toEquiv).symm.trans hX
    rw [UnbalancingLocal.card_psl_three_four K₃ (by rw [hK₃]; norm_num)] at h1
    omega
  have h2 : StatedClassicalModel X .PSL 2 p f := by
    rcases hsrc with h2 | ⟨e7⟩ | h322
    · exact h2
    · exact (not_nonempty_iff.mpr hA7 e7).elim
    · exact (hP34 h322).elim
  obtain ⟨hpar, -⟩ := SymmetricLocal.alternating_psl_two_parameters_and_degree_seven_stated
    (Ω := Fin 6) (by simp) ⟨eX⟩
  rcases hpar p f hp2 h2 with ⟨h5, -, -⟩ | ⟨-, hp3, hf2⟩
  · simp at h5
  · exact ⟨hp3, hf2, h2, hA7, hP34⟩

theorem nonempty_quotient_center_mulEquiv {L S : Type*} [Group L] [Group S] [IsSimpleGroup L]
    (hnab : ∃ x y : L, x * y ≠ y * x) (e : L ≃* S) : Nonempty (L ⧸ center L ≃* S) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hnab)).trans
    QuotientGroup.quotientBot).trans e⟩

end Sources

theorem symplectic_component_dichotomy {G O : Type*} [Group G] [Group O] [Finite O]
    {c : O →* G} (hc : Function.Injective c) {X : Subgroup G}
    (hX : CFSG.Assembly.IsComponentOf X c.range) {k : Type} [Field k] [Finite k] [CharP k 2]
    {e r : ℕ} (hk : Nat.card k = 2 ^ e) (hr : 1 ≤ r) (hr1 : ¬ (r = 1 ∧ e = 1))
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (B : BilinForm k V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : Module.finrank k V = 2 * r)
    (eO : O ≃* isometryGroup B) :
    (¬ (e = 1 ∧ r = 2) ∧ X = c.range ∧ IsSimpleGroup X ∧ Nonempty (X ≃* isometryGroup B) ∧
      Nonempty (X ≃* StatedSp r k)) ∨
    (e = 1 ∧ r = 2 ∧ X = ⁅c.range, c.range⁆ ∧
      (∃ E : c.range ≃* PresentationLocal.sympFour, ∀ x : c.range,
        (x : G) ∈ ⁅c.range, c.range⁆ ↔
          PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
      Nonempty (c.range ≃* Equiv.Perm (Fin 6)) ∧
      Nonempty (↥(⁅c.range, c.range⁆ : Subgroup G) ≃* alternatingGroup (Fin 6))) := by
  obtain ⟨hX0, hXmap⟩ := SymmetricLocal.isComponent_comap_of_isComponentOf_range c hc hX
  obtain ⟨eSp⟩ := nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdim
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, pow_zero] at hk
      omega
    · exact h0
  have hNc : ⁅c.range, c.range⁆ = (commutator O).map c := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  by_cases h22 : e = 1 ∧ r = 2
  · right
    obtain ⟨rfl, rfl⟩ := h22
    obtain ⟨E₁⟩ := nonempty_altIsometry_mulEquiv_sympFour (by rw [hk, pow_one]) B hB hnd
      (by rw [hdim])
    set E₀ : O ≃* PresentationLocal.sympFour := eO.trans E₁ with hE₀
    have hcomm := map_commutator_of_mulEquiv E₀
    have eC : commutator O ≃* commutator PresentationLocal.sympFour :=
      (E₀.subgroupMap (commutator O)).trans (MulEquiv.subgroupCongr hcomm)
    have : IsSimpleGroup (commutator PresentationLocal.sympFour) :=
      PresentationLocal.isSimpleGroup_commutator_sympFour
    have : IsSimpleGroup (commutator O) := eC.isSimpleGroup
    have hab : IsMulCommutative (O ⧸ commutator O) :=
      inferInstanceAs (IsMulCommutative (Abelianization O))
    have hX₀ : X.comap c = commutator O :=
      SymmetricLocal.isComponent_eq_of_simple_normal (commutator O) hab ‹_› hX0
    have hXc : X = ⁅c.range, c.range⁆ := by rw [← hXmap, hX₀, hNc]
    set E : c.range ≃* PresentationLocal.sympFour := (MonoidHom.ofInjective hc).symm.trans E₀
      with hE
    refine ⟨rfl, rfl, hXc, ⟨E, fun x => ?_⟩, ⟨E.trans (MulEquiv.ofBijective _
      ⟨PresentationLocal.omegaPerm_injective, PresentationLocal.omegaPerm_surjective⟩)⟩,
      ⟨(MulEquiv.subgroupCongr hNc).trans (((commutator O).equivMapOfInjective c hc).symm.trans
        (eC.trans PresentationLocal.commutatorEquivAlternating))⟩⟩
    obtain ⟨g, rfl⟩ := (MonoidHom.ofInjective hc).surjective x
    have hEg : E (MonoidHom.ofInjective hc g) = E₀ g := by
      rw [hE, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hEg, hNc, MonoidHom.ofInjective_apply, Subgroup.mem_map_iff_mem hc,
      ← Subgroup.mem_map_iff_mem (f := (E₀ : O →* PresentationLocal.sympFour)) E₀.injective,
      hcomm, PresentationLocal.commutator_sympFour, Subgroup.mem_comap]
    rfl
  · left
    refine ⟨h22, ?_⟩
    have hsimp : IsSimpleGroup (StatedSp r k) := by
      have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        by_cases he : e = 1
        · right
          right
          refine ⟨by rw [hk, he, pow_one], ?_⟩
          by_contra hr3
          push Not at hr3
          interval_cases r
          · exact hr1 ⟨rfl, he⟩
          · exact h22 ⟨he, rfl⟩
        · left
          right
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : IsSimpleGroup (StatedProj (StatedSp r k)) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r hr hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk hr ⟨MulEquiv.refl _⟩
      exact eProj.symm.isSimpleGroup
    have : IsSimpleGroup O := (eO.trans eSp).isSimpleGroup
    have hX₀ : X.comap c = ⊤ := isComponent_eq_top_of_isSimpleGroup hX0
    have hXc : X = c.range := by rw [← hXmap, hX₀, ← MonoidHom.range_eq_map]
    have eX : X ≃* O := (MulEquiv.subgroupCongr hXc).trans (MonoidHom.ofInjective hc).symm
    exact ⟨hXc, eX.isSimpleGroup, ⟨eX.trans eO⟩, ⟨eX.trans (eO.trans eSp)⟩⟩

section Socle

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
  {e n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
  (hq : ¬(n = 3 ∧ 2 ^ e = 2))

include hn hq in
theorem socle_field_factor_bar (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    {ρ₁ : A →* MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hρ₁inj : Function.Injective ρ₁)
    (φ₁ : W ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hρ₁W : ∀ w : W, ρ₁ w = MulAut.conj (φ₁ w)) :
    orderOf (ρ₁ a) = 2 ∧
      ∀ x, primeFormFieldFactor h isPrimeFormGram_one hn hq (ρ₁ a) x = h.bar x := by
  have hα₁ : orderOf (ρ₁ a) = 2 := by rw [orderOf_injective ρ₁ hρ₁inj a]; exact ha
  obtain ⟨-, hρ₁CW, -⟩ := socle_images hρ₁inj φ₁ hρ₁W a
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ₁) (inner _ ⊓ centralizer {ρ₁ a}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ₁ hρ₁inj hLCW
    rwa [hρ₁CW] at this
  obtain ⟨hcases, hrefl, -, -⟩ :=
    even_unitary_involution_matrix_lifts h isPrimeFormGram_one hn hq (ρ₁ a) hα₁
  refine ⟨hα₁, ?_⟩
  rcases hcases with hF | hF
  · exfalso
    obtain ⟨s, hs1, hss, hαs⟩ := hrefl hF
    rw [hαs] at hL₁
    exact UnbalancingLocal.EvenUnitaryComponents.no_component_inf_centralizer_conj h
      isPrimeFormGram_one hn hq le_rfl s hs1 hss _
      ((isComponentOf_iff_isComponent_subgroupOf hL₁.1).1 hL₁)
  · exact hF

include hn hq in
theorem socle_descent [W.Normal] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (φ : W ≃* unitaryPSU h n)
    {ρ : A →* MulAut (unitaryPSU h n)} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) :
    ∃ (H₀ C : GL (Fin n) K) (hC : IsPrimeFormGram C),
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∧
      ((H₀ : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (H₀ : Matrix (Fin n) (Fin n) K) = C ∧
      ∃ θ : primeFormP h (C : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n,
        (∀ (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) (g' : unitarySU 2 e K n),
          (g' : GL (Fin n) K) = H₀ * g * H₀⁻¹ →
            θ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = unitaryProj h n g') ∧
        ∃ ρC : A →* MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
          (∀ (t : A) (x : primeFormP h (C : Matrix (Fin n) (Fin n) K)),
            ρC t x = θ.symm (ρ t (θ x))) ∧ Function.Injective ρC ∧
          (∀ w : W, ρC w = MulAut.conj ((φ.trans θ.symm) w)) ∧
          ∃ σ : K ≃+* K, (∀ x, σ x = h.bar x) ∧ ρC a = primeFormFieldHom h hC σ ∧
            ρ a ∉ inner (unitaryPSU h n) := by
  have htransport : ∀ {Q : Type} [Group Q] (ψ : unitaryPSU h n ≃* Q),
      Function.Injective ((MulAut.congr ψ).toMonoidHom.comp ρ) ∧
        ∀ w : W, (MulAut.congr ψ).toMonoidHom.comp ρ w = MulAut.conj ((φ.trans ψ) w) := by
    intro Q _ ψ
    refine ⟨(MulAut.congr ψ).injective.comp hinj, fun w => ?_⟩
    rw [MonoidHom.comp_apply, hρW, MulEquiv.coe_toMonoidHom, mulAut_congr_conj]
    rfl
  obtain ⟨ι, hιdef⟩ : ∃ ι, ι = primeFormOneEquiv h n := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁, ρ₁ = (MulAut.congr ι.symm).toMonoidHom.comp ρ := ⟨_, rfl⟩
  have htr₁ := htransport ι.symm
  rw [← hρ₁def] at htr₁
  obtain ⟨hρ₁inj, hρ₁W⟩ := htr₁
  obtain ⟨hα₁, hF⟩ := socle_field_factor_bar h hn hq ha hLCW hρ₁inj _ hρ₁W
  obtain ⟨-, H₀, C, hC, hcase, -, -, hH₀, -, ⟨θ₁, hθ₁mk, hθ₁α⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h isPrimeFormGram_one hn hq (ρ₁ a) hα₁ hF
  generalize hσdef : primeFormFieldFactor h isPrimeFormGram_one hn hq (ρ₁ a) = σ at hF hθ₁α
  have hH₀' : ((H₀ : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (H₀ : Matrix (Fin n) (Fin n) K) =
      C := by
    rw [← hH₀, Units.val_one, Matrix.mul_one]
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = θ₁.trans ι := ⟨_, rfl⟩
  have hθapp : ∀ x, θ x = ι (θ₁ x) := fun x => by rw [hθdef]; rfl
  have hθsymm : ∀ y, θ.symm y = θ₁.symm (ι.symm y) := fun y => by rw [hθdef]; rfl
  obtain ⟨ρC, hρCdef⟩ : ∃ ρC, ρC = (MulAut.congr θ.symm).toMonoidHom.comp ρ := ⟨_, rfl⟩
  have htr := htransport θ.symm
  rw [← hρCdef] at htr
  obtain ⟨hρCinj, hρCW⟩ := htr
  have hρCapp : ∀ (t : A) (x : primeFormP h (C : Matrix (Fin n) (Fin n) K)),
      ρC t x = θ.symm (ρ t (θ x)) := fun t x => by rw [hρCdef]; rfl
  have hρ₁app : ∀ y, ρ₁ a y = ι.symm (ρ a (ι y)) := fun y => by rw [hρ₁def]; rfl
  have hρCa : ρC a = primeFormFieldHom h hC σ := by
    ext x
    rw [hρCapp, hθapp, hθsymm, ← hρ₁app, hθ₁α, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
    rfl
  have hθmk : ∀ (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) (g' : unitarySU 2 e K n),
      (g' : GL (Fin n) K) = H₀ * g * H₀⁻¹ →
        θ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = unitaryProj h n g' := by
    intro g g' hg'
    have hmem : (g' : GL (Fin n) K) ∈
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [gramSU_one_eq]
      exact g'.2
    rw [hθapp, hθ₁mk g ⟨g', hmem⟩ hg', hιdef]
    exact primeFormOneEquiv_mk h (n := n) ⟨g', hmem⟩ g' rfl
  have hnotinner : ρ a ∉ inner (unitaryPSU h n) := by
    rintro ⟨y, hy⟩
    have h1 : ρC a = MulAut.conj (θ.symm y) := by
      rw [hρCdef, MonoidHom.comp_apply, ← hy, MulEquiv.coe_toMonoidHom, mulAut_congr_conj]
    have h2 : primeFormFieldHom h hC σ ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
      rw [← hρCa, h1]
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (θ.symm y)
      rw [← hs]
      exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h _ s⟩
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at h2
    have h3 := primeFormFieldFactor_apply h hC hn hq 1 σ
    rw [map_one, one_mul, h2] at h3
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    rw [← hF c, ← h3]
    rfl
  exact ⟨H₀, C, hC, hcase, hH₀', θ, hθmk, ρC, hρCapp, hρCinj, hρCW, σ, hF, hρCa, hnotinner⟩

include hn hq in
theorem socle_transfer (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (Cl : GL (Fin n) h.fixedField)
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    {ρC : A →* MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hρCinj : Function.Injective ρC) (ψ : W ≃* primeFormP h (C : Matrix (Fin n) (Fin n) K))
    (hρCW : ∀ w : W, ρC w = MulAut.conj (ψ w)) (hρCa : ρC a = primeFormFieldHom h hC σ) :
    (∀ α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
      α ∈ centralizer {primeFormFieldHom h hC σ} ↔
        ∃ (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) (τ : K ≃+* K),
          α = primeFormPsi h hC ⟨fixedIsometryHom h hCl g, τ⟩) ∧
    (∀ (g g' : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))
      (τ τ' : K ≃+* K), primeFormPsi h hC ⟨fixedIsometryHom h hCl g, τ⟩ =
        primeFormPsi h hC ⟨fixedIsometryHom h hCl g', τ'⟩ → g = g' ∧ τ = τ') ∧
    Function.Injective ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)) ∧
    ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range ≤
      inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∧
    ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range ≤
      centralizer {primeFormFieldHom h hC σ} ∧
    (((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)).range.subgroupOf (centralizer {primeFormFieldHom h hC σ})).Normal ∧
    (centralizer {a}).map ρC = ρC.range ⊓ centralizer {primeFormFieldHom h hC σ} ∧
    (W ⊓ centralizer {a}).map ρC =
      ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range ∧
    CFSG.Assembly.IsComponentOf (L.map ρC)
      ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
        (fixedIsometryHom h hCl)).range := by
  obtain ⟨-, hρCCW, hρCC⟩ := socle_images hρCinj ψ hρCW a
  obtain ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hInnM : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h hC σ} =
        ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    apply le_antisymm
    · rintro x ⟨hxi, hxM⟩
      obtain ⟨g, τ, rfl⟩ := (hM x).mp hxM
      have hD : primeFormPsi h hC ⟨fixedIsometryHom h hCl g, τ⟩ ∈
          primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
        obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxi
        exact ⟨_, hs.symm⟩
      rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker,
        primeFormFieldFactor_psi] at hD
      refine ⟨g, ?_⟩
      change primeFormConjHom h _ (fixedIsometryHom h hCl g) = _
      rw [primeFormPsi_apply, show τ = 1 from hD, map_one, mul_one]
    · exact le_inf hNinner hNM
  have hCWN : (W ⊓ centralizer {a}).map ρC = ((primeFormConjHom h (C : Matrix (Fin n) (Fin n)
      K)).comp (fixedIsometryHom h hCl)).range := by
    rw [hρCCW, hρCa, hInnM]
  refine ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, by rw [hρCC, hρCa], hCWN, ?_⟩
  have := SymmetricLocal.isComponentOf_map_of_injective ρC hρCinj hLCW
  rwa [hCWN] at this

end Socle

section Rows

variable {G : Type*} [Group G] {k : Type} [Field k] [Finite k] [CharP k 2] {e n r : ℕ}
  {Y : Type} [Group Y] {p f : ℕ}

theorem socle_rows_one (hk : Nat.card k = 2 ^ e) (hr : n = 2 * r + 1) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ e = 2))
    {c : matrixIsometryGroup ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) →* G}
    (hc : Function.Injective c) {X : Subgroup G} (hX : CFSG.Assembly.IsComponentOf X c.range)
    (eY : Y ≃* X) (hYnab : ∃ x y : Y, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (Y ⧸ center Y) .PSL 2 p f ∨
      Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (Y ⧸ center Y) .PSL 3 2 2) :
    ((n = 3 ∧ e = 2 ∧ p = 5 ∧ f = 1 ∧
        Nonempty (isometryGroup ((Matrix.toBilin' ((1 : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k)).restrict (LinearMap.ker (Matrix.toBilin'
            ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) fun _ => 1))) ≃* StatedSp 1 k) ∧
        Nonempty (isometryGroup ((Matrix.toBilin' ((1 : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k)).restrict (LinearMap.ker (Matrix.toBilin'
            ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) fun _ => 1))) ≃*
              Matrix.SpecialLinearGroup (Fin 2) k) ∧
        X = c.range ∧ Nonempty (Y ≃* StatedSp 1 k) ∧
        Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) k)) ∨
      (n = 5 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧
        Nonempty (isometryGroup ((Matrix.toBilin' ((1 : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k)).restrict (LinearMap.ker (Matrix.toBilin'
            ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) fun _ => 1))) ≃* StatedSp 2 k) ∧
        (∃ E : c.range ≃* PresentationLocal.sympFour, ∀ x : c.range,
          (x : G) ∈ ⁅c.range, c.range⁆ ↔
            PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
        Nonempty (c.range ≃* Equiv.Perm (Fin 6)) ∧
        Nonempty (↥(⁅c.range, c.range⁆ : Subgroup G) ≃* alternatingGroup (Fin 6)) ∧
        X = ⁅c.range, c.range⁆ ∧ Nonempty (Y ≃* alternatingGroup (Fin 6)))) ∧
    IsSimpleGroup Y ∧ StatedClassicalModel (Y ⧸ center Y) .PSL 2 p f ∧
      IsEmpty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (Y ⧸ center Y) .PSL 3 2 2 := by
  have : Finite (GL (Fin n) k) := Finite.of_injective Units.val Units.val_injective
  have hr1 : 1 ≤ r := by omega
  have hr1' : ¬ (r = 1 ∧ e = 1) := by
    rintro ⟨rfl, rfl⟩
    exact hq ⟨by omega, by norm_num⟩
  have hdim := finrank_dotForm_ker (k := k) hr
  have hBalt := dotForm_restrict_isAlt (k := k) (n := n)
  have hBnd := dotForm_restrict_nondegenerate (k := k) hr
  rcases symplectic_component_dichotomy hc hX hk hr1 hr1' _ hBalt hBnd hdim
      (oneRestrictEquiv hr) with
    ⟨-, hXc, hXs, ⟨eXB⟩, ⟨eXSp⟩⟩ | ⟨rfl, rfl, hXc, hE, hP6, ⟨eA6⟩⟩
  · have : IsSimpleGroup X := hXs
    have : IsSimpleGroup Y := eY.isSimpleGroup
    obtain ⟨eQ⟩ := nonempty_quotient_center_mulEquiv hYnab (eY.trans eXSp)
    obtain ⟨rfl, he2, hp5, hf1, hPSL, hA7, hP34⟩ := source_of_symplectic hk hr1 eQ hp2 hsrc
    obtain ⟨eSL⟩ := exists_planeIsometryEquivSL _ hBalt hBnd (by rw [hdim])
    exact ⟨Or.inl ⟨by omega, he2, hp5, hf1,
      nonempty_altIsometry_mulEquiv_statedSp _ hBalt hBnd hdim, ⟨eSL⟩, hXc, ⟨eY.trans eXSp⟩,
      ⟨(eY.trans eXB).trans eSL⟩⟩, ‹IsSimpleGroup Y›, hPSL, hA7, hP34⟩
  · have eY6 : Y ≃* alternatingGroup (Fin 6) := (eY.trans (MulEquiv.subgroupCongr hXc)).trans eA6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Y := eY6.isSimpleGroup
    obtain ⟨eQ⟩ := nonempty_quotient_center_mulEquiv hYnab eY6
    obtain ⟨hp3, hf2, hPSL, hA7, hP34⟩ := source_of_alternating_six eQ hp2 hsrc
    exact ⟨Or.inr ⟨by omega, rfl, hp3, hf2,
      nonempty_altIsometry_mulEquiv_statedSp _ hBalt hBnd hdim, hE, hP6, ⟨eA6⟩, hXc, ⟨eY6⟩⟩,
      ‹IsSimpleGroup Y›, hPSL, hA7, hP34⟩

theorem socle_rows_blockSwap (hk : Nat.card k = 2 ^ e) (hr : n = 2 * r) (hn : 3 ≤ n)
    {Cl : GL (Fin n) k} (hClJ : (Cl : Matrix (Fin n) (Fin n) k) = blockSwapJ n r)
    {c : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) k) →* G}
    (hc : Function.Injective c) {X : Subgroup G} (hX : CFSG.Assembly.IsComponentOf X c.range)
    (eY : Y ≃* X) (hYnab : ∃ x y : Y, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (Y ⧸ center Y) .PSL 2 p f ∨
      Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (Y ⧸ center Y) .PSL 3 2 2) :
    n = 4 ∧ r = 2 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧
      (∃ E : c.range ≃* PresentationLocal.sympFour, ∀ x : c.range,
        (x : G) ∈ ⁅c.range, c.range⁆ ↔
          PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
      Nonempty (c.range ≃* Equiv.Perm (Fin 6)) ∧
      Nonempty (↥(⁅c.range, c.range⁆ : Subgroup G) ≃* alternatingGroup (Fin 6)) ∧
      X = ⁅c.range, c.range⁆ ∧ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∧
      IsSimpleGroup Y ∧ StatedClassicalModel (Y ⧸ center Y) .PSL 2 p f ∧
      IsEmpty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (Y ⧸ center Y) .PSL 3 2 2 := by
  have : Finite (GL (Fin n) k) := Finite.of_injective Units.val Units.val_injective
  have hr2 : 2 ≤ r := by omega
  have hBalt : (Matrix.toBilin' (Cl : Matrix (Fin n) (Fin n) k)).IsAlt := fun x => by
    rw [Matrix.toBilin'_apply', hClJ]
    exact dotProduct_mulVec_self_eq_zero blockSwapJ_transpose
      (fun i => blockSwapJ_apply_self (by omega) i) x
  have hBnd := CatalogueBLinearHigherB.matrixForm_nondegenerate Cl
  have hdim : Module.finrank k (Fin n → k) = 2 * r := by
    rw [Module.finrank_fin_fun]
    exact hr
  rcases symplectic_component_dichotomy hc hX hk (by omega) (fun h' => by omega) _ hBalt hBnd
      hdim (matrixIsometryGroupEquiv Cl) with
    ⟨-, -, hXs, -, ⟨eXSp⟩⟩ | ⟨rfl, rfl, hXc, hE, hP6, ⟨eA6⟩⟩
  · exfalso
    have : IsSimpleGroup X := hXs
    have : IsSimpleGroup Y := eY.isSimpleGroup
    obtain ⟨eQ⟩ := nonempty_quotient_center_mulEquiv hYnab (eY.trans eXSp)
    obtain ⟨hr1, -⟩ := source_of_symplectic hk (by omega) eQ hp2 hsrc
    omega
  · have eY6 : Y ≃* alternatingGroup (Fin 6) := (eY.trans (MulEquiv.subgroupCongr hXc)).trans eA6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Y := eY6.isSimpleGroup
    obtain ⟨eQ⟩ := nonempty_quotient_center_mulEquiv hYnab eY6
    obtain ⟨hp3, hf2, hPSL, hA7, hP34⟩ := source_of_alternating_six eQ hp2 hsrc
    exact ⟨by omega, rfl, rfl, hp3, hf2, hE, hP6, ⟨eA6⟩, hXc, ⟨eY6⟩, ‹IsSimpleGroup Y›, hPSL,
      hA7, hP34⟩

end Rows

end CFSG.ComponentClassification.OutcomeLocal
