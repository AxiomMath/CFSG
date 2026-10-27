module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Lin
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBConjugate
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUDesc
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem center_psl2_eq_bot {F₀ : Type} [Field F₀] [Finite F₀] (h3 : 3 < Nat.card F₀) :
    center (GorensteinWalter.PSL2 F₀) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  exact (mem_bot).mpr
    (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 h3 (MulEquiv.refl _) hz)

theorem center_quotient_equiv_of_sl {Y X : Type*} [Group Y] [Group X] {F₀ : Type} [Field F₀]
    (σ : Y →* X) (hσs : Function.Surjective σ) (hσk : σ.ker ≤ center Y)
    (eY : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F₀) [Group.IsPerfect Y] :
    Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 F₀) :=
  ⟨(ShultStronglyClosedTI.centralLiftCenterQuotientEquiv σ hσs hσk).symm.trans
    (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))⟩

theorem center_quotient_equiv_of_psl {Y X : Type*} [Group Y] [Group X] {F₀ : Type} [Field F₀]
    [Finite F₀] (h3 : 3 < Nat.card F₀) (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (eY : Y ≃* GorensteinWalter.PSL2 F₀) [Group.IsPerfect Y] :
    Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 F₀) := by
  have hZ : center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).mpr (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 h3 eY hz)
  exact ⟨(ShultStronglyClosedTI.centralLiftCenterQuotientEquiv σ hσs hσk).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eY))⟩

theorem eq_or_eq_of_isComponent {G : Type*} [Group G] [Finite G] {L R Y : Subgroup G}
    (hL : CFSG.IsComponent L) (hR : CFSG.IsComponent R) (hsup : commutator G = L ⊔ R)
    (hY : CFSG.IsComponent Y) : Y = L ∨ Y = R := by
  rcases CFSG.LocalCores.distinct_components_commute hY hL with h1 | h1
  · exact Or.inl h1
  rcases CFSG.LocalCores.distinct_components_commute hY hR with h2 | h2
  · exact Or.inr h2
  exfalso
  have : Group.IsPerfect Y := hY.1.1
  have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
  have hYp : ⁅Y, Y⁆ = Y := Subgroup.commutator_eq_self (H := Y)
  have hYC : Y ≤ commutator G := by
    rw [← hYp]
    exact Subgroup.commutator_mono le_top le_top
  have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have h2' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    have hle : L ⊔ R ≤ centralizer {x} :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h1' hx)) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h2' hx)) z hz))
    have hy' := hle (hsup ▸ hYC hy)
    exact (mem_centralizer_singleton_iff.mp hy').symm
  have hbot : ⁅Y, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  rw [hYp] at hbot
  have := Y.nontrivial_iff_ne_bot.mp inferInstance
  exact this hbot

theorem specialRho_inl_injective (k : Type*) [Field k] :
    Function.Injective ((specialRho (K := k)).comp (MonoidHom.inl _ _)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  have h1 := congrArg (fun g : DeterminantIsometries k => g.val 1) hU
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, specialRho_apply] at h1
  apply Subtype.ext
  simpa using h1

theorem specialRho_inr_injective (k : Type*) [Field k] :
    Function.Injective ((specialRho (K := k)).comp (MonoidHom.inr _ _)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  have h1 := congrArg (fun g : DeterminantIsometries k => g.val 1) hU
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, specialRho_apply] at h1
  have h2 : ((U⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    simpa using h1
  have h3 : U⁻¹ = 1 := Subtype.ext h2
  rw [inv_eq_one] at h3
  exact h3

section Orth

variable {k : Type} [Field k] [Finite k] {W : Type} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

theorem component_equiv_sl_of_split (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (hodd : Odd (Nat.card k)) (hdim : finrank k W = 4)
    (hsplit : ∃ S : Submodule k W, finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {Y : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hY : CFSG.IsComponent Y) :
    5 ≤ Nat.card k ∧ Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
  classical
  obtain ⟨hexc, -, -, hsplitm, -, -, -⟩ :=
    orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
      (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
  have hq2 : Nat.card k ≠ 2 := fun h' => by
    rw [h'] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hq3 : Nat.card k ≠ 3 := by
    intro hq3
    obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hdim, hsplit⟩, Or.inr hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable Y :=
      Group.isSolvable_of_isSolvable_injective (f := Y.subtype) Y.subtype_injective
    have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
    have : Group.IsPerfect Y := hY.1.1
    exact Group.IsPerfect.not_isSolvable Y inferInstance
  have hq5 : 5 ≤ Nat.card k := by
    have h1 : 2 ≤ Nat.card k := Finite.one_lt_card
    have h4 : Nat.card k ≠ 4 := fun h' => by
      rw [h'] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    omega
  obtain ⟨-, e₀, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ := hsplitm hdim hsplit hq2 hq3
  have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), CFSG.IsQuasisimple M →
      M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
      (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
      CFSG.IsComponent M := fun M hMq hMle hMn =>
    ⟨hMq, Subgroup.IsSubnormal.trans hMle hMn.isSubnormal
      (Subgroup.Normal.isSubnormal inferInstance)⟩
  have hL := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
  have hR := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
  refine ⟨hq5, ?_⟩
  rcases eq_or_eq_of_isComponent hL hR hsup hY with hYL | hYR
  · exact ⟨(MulEquiv.subgroupCongr hYL).trans
      (((determinantLeftFactor k).equivMapOfInjective e₀.symm.toMonoidHom
        e₀.symm.injective).symm.trans (MonoidHom.ofInjective (specialRho_inl_injective k)).symm)⟩
  · exact ⟨(MulEquiv.subgroupCongr hYR).trans
      (((determinantRightFactor k).equivMapOfInjective e₀.symm.toMonoidHom
        e₀.symm.injective).symm.trans (MonoidHom.ofInjective (specialRho_inr_injective k)).symm)⟩

theorem commutator_equiv_psl_of_nonsplit (Q : QuadraticForm k W)
    (hQ : Q.polarBilin.Nondegenerate) (hodd : Odd (Nat.card k)) (hdim : finrank k W = 4)
    (hns : ¬ ∃ S : Submodule k W, finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card k ^ 2 ∧
        Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃*
          GorensteinWalter.PSL2 E') := by
  classical
  obtain ⟨-, -, -, -, hnon, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
    Q hQ (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
  obtain ⟨δ, hδ, -, -, e₁, -, -, hc, hquasi⟩ := hnon hodd hdim hns
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  have : Finite (CatalogueBOrthogonalFourNonsplit.extension (δ : k)) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (δ : k) 0).symm
  have hker : (CatalogueBOrthogonalFourNonsplit.specialRho (δ : k)
      (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).ker =
      center (Matrix.SpecialLinearGroup (Fin 2) (CatalogueBOrthogonalFourNonsplit.extension
        (δ : k))) := by
    ext A
    rw [MonoidHom.mem_ker, CatalogueBOrthogonalFourNonsplit.specialRho_eq_one_iff_sign,
      OddSelector.mem_center_sl_two_iff]
  refine ⟨hquasi, CatalogueBOrthogonalFourNonsplit.extension (δ : k), inferInstance, inferInstance,
    CatalogueBOrthogonalFourNonsplit.extension_card _, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hc).trans
    ((((CatalogueBOrthogonalFourNonsplit.specialImage (δ : k)
      (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).equivMapOfInjective
        e₁.symm.toMonoidHom e₁.symm.injective).symm.trans
      (QuotientGroup.quotientKerEquivRange _).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker))

end Orth

section Std

variable {K : Type} [Field K] (h : UnitaryFieldData p f K)

open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)
open CFSG.LinearGroups Matrix

abbrev antiConjA {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) :
    MulAut (sesqUnitaryGroup (stdHermForm h 4)) :=
  antiConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))
    (CatFactsL4U4.StabU.antiunitaryMap_bijective h A)
    (CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu)

theorem anti_type (hp : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {z : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = z • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y (fixedSubgroup (antiConjA h hAu)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) :
    z = 1 ∧
      ((5 ≤ Nat.card h.fixedField ∧
          Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 h.fixedField) ∧
          (∃ u : K, h.norm u = 1 ∧ (A : Matrix (Fin 4) (Fin 4) K).det = u ^ 2) ∧
          ∃ φq : QuaternionGroup 2 →* Y, Function.Injective φq) ∨
        ((∃ (E' : Type) (_ : Field E') (_ : Finite E'),
            Nat.card E' = Nat.card h.fixedField ^ 2 ∧
            Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 E')) ∧
          ∀ Y₁ : Subgroup (sesqUnitaryGroup (stdHermForm h 4)), ⁅Y₁, Y₁⁆ = Y₁ →
            Y₁ ≤ fixedSubgroup (antiConjA h hAu) →
            ∀ φq : QuaternionGroup 2 →* Y₁, ¬ Function.Injective φq)) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτ₀B := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hμ : ∀ v, antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 z hz0 : Kˣ) : K) • v :=
    CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 z hz0) hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
    finite_conjFixed
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp h1
  have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    exfalso
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    exact OddClassSelector.sp_component_false h.prime hp h.one_le hK B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun]) ((fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ) hY₁
      (σ.comp eY.toMonoidHom) hσ₁k hs
  have hz1 : z = 1 := by
    have := congrArg Units.val hμ1
    simpa using this
  refine ⟨hz1, ?_⟩
  have hb1 : h.norm (b : K) = 1 := by rw [hb, hμ1, inv_one, Units.val_one]
  obtain ⟨B', hB'v, hsym, hnd, Φ, -⟩ := hB1 hμ1
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  have hdim : Module.finrank h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  let Φ' : fixedSubgroup (antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B') :=
    (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  let eYY' : Y ≃* (Y.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom :=
    eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
  by_cases hsplit : ∃ S : Submodule h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))),
      Module.finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  · left
    obtain ⟨hq5, ⟨eSL⟩⟩ := component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
    let eYS : Y ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField := eYY'.trans eSL
    refine ⟨hq5, center_quotient_equiv_of_sl σ hσs hσk eYS, ?_, ?_⟩
    · obtain ⟨-, -, -, hsplitm, -, -, -⟩ :=
        orthogonal_low_dimensional_fixed_derived_component_coverage _ hQ'
          (Or.inl ⟨hKodd, Or.inr (Or.inl hdim)⟩)
      obtain ⟨ψ₀, -, hQψ, -⟩ := hsplitm hdim hsplit (by omega) (by omega)
      exact det_sq_of_split_descent h hp (fun v => rfl) hb1 ht hdim B' hB'v hsym ψ₀ hQψ
    · obtain ⟨a', b', hab⟩ := OddClassSelector.exists_sq_add_sq hKodd (-1)
      have hk2' : ringChar h.fixedField ≠ 2 := by
        intro hc
        apply h2
        have h0 := ringChar.Nat.cast_ringChar (R := h.fixedField)
        rw [hc] at h0
        exact_mod_cast h0
      exact ⟨eYS.symm.toMonoidHom.comp (QuaternionMatrices.quatHom hab),
        eYS.symm.injective.comp (QuaternionMatrices.quatHom_injective hk2' hab)⟩
  · right
    obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
      commutator_equiv_psl_of_nonsplit _ hQ' hKodd hdim hsplit
    have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
    have h3K : 3 ≤ Nat.card h.fixedField := by
      rw [hK]
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h3 : 3 < Nat.card E' := by rw [hE']; nlinarith
    refine ⟨⟨E', inferInstance, inferInstance, hE', center_quotient_equiv_of_psl h3 σ hσs hσk
      ((eYY'.trans (MulEquiv.subgroupCongr hYeq)).trans eC)⟩, ?_⟩
    intro Y₁ hY₁p hY₁le φq hφq
    have hZ₁p : ⁅Y₁.subgroupOf (fixedSubgroup (antiConjA h hAu)),
        Y₁.subgroupOf (fixedSubgroup (antiConjA h hAu))⁆ =
          Y₁.subgroupOf (fixedSubgroup (antiConjA h hAu)) := by
      apply Subgroup.map_injective (fixedSubgroup (antiConjA h hAu)).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hY₁le, hY₁p]
    have hmapC : (Y₁.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom ≤
        commutator (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')) := by
      rw [← hZ₁p, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    let χ : QuaternionGroup 2 →* TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBOrthogonalDescent.originalQuadratic B') :=
      Φ'.toMonoidHom.comp ((Subgroup.inclusion hY₁le).comp φq)
    have hχ : Function.Injective χ :=
      Φ'.injective.comp ((Subgroup.inclusion_injective hY₁le).comp hφq)
    have hχr : ∀ w, χ w ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBOrthogonalDescent.originalQuadratic B')) := fun w =>
      hmapC ⟨Subgroup.inclusion hY₁le (φq w), mem_subgroupOf.mpr (φq w).2, rfl⟩
    let χ' := χ.codRestrict _ hχr
    have hχ' : Function.Injective χ' := fun x y hxy => hχ (congrArg Subtype.val hxy)
    have hE'p : Nat.card E' = p ^ (2 * f) := by rw [hE', hK, ← pow_mul, mul_comm]
    have hpf : 3 < p ^ (2 * f) := by rw [← hE'p]; exact h3
    have hmodel := OddSelector.statedClassicalModel_psl_two h.prime (by have := h.one_le; omega)
      hE'p (by omega) (by omega)
    let eP := eC.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 E')
    exact OddSelector.not_psl_two_odd_of_quaternion (eP.toMonoidHom.comp χ')
      (eP.injective.comp hχ') hp hmodel

end Std

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
