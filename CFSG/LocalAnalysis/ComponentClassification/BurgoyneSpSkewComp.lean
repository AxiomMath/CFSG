module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensions
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_of_pow_char {E : Type*} [Field E] {ℓ : ℕ} [Fact ℓ.Prime] [CharP E ℓ] {x : Eˣ}
    (hx : x ^ ℓ = 1) : x = 1 := by
  apply Units.ext
  have h1 : ((x : E) - 1) ^ ℓ = 0 := by
    rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  rw [Units.val_one]
  exact sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : ℓ.Prime).ne_zero |>.1 h1)

section Abstract

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem conj_mem_map_subtype {G : Type*} [Group G] {H : Subgroup G} {L : Subgroup H}
    (hL : L.Normal) {g : G} (hg : g ∈ H) {x : G} (hx : x ∈ L.map H.subtype) :
    g * x * g⁻¹ ∈ L.map H.subtype := by
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹, hL.conj_mem q hq _, rfl⟩

theorem isQuasisimple_comap_equiv {G Q : Type*} [Group G] [Group Q] (e : G ≃* Q)
    {S : Subgroup Q} (hS : IsQuasisimple S) : IsQuasisimple (S.comap e.toMonoidHom) := by
  have e2 := e.subgroupMap (S.comap e.toMonoidHom)
  have e3 : (S.comap e.toMonoidHom).map e.toMonoidHom = S :=
    map_comap_eq_self_of_surjective e.surjective S
  exact LocalCores.isQuasisimple_of_mulEquiv (e2.trans (MulEquiv.subgroupCongr e3)).symm hS

theorem isQuasisimple_map_subtype_comap {G Q : Type*} [Group G] [Group Q] {H : Subgroup G}
    (e : H ≃* Q) {S : Subgroup Q} (hS : IsQuasisimple S) :
    IsQuasisimple ((S.comap e.toMonoidHom).map H.subtype) :=
  LocalCores.isQuasisimple_of_mulEquiv
    ((S.comap e.toMonoidHom).equivMapOfInjective _ H.subtype_injective)
    (isQuasisimple_comap_equiv e hS)

theorem exists_unitary_component_abstract {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) [CharP K ℓ] (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f)
    (hdim : Module.finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1)
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = (-d) * B v w) :
    ∃ L : Subgroup (UnitaryHigher.similitudeCentralizer B A), L.Normal ∧ IsQuasisimple L ∧
      ∀ g : UnitaryHigher.similitudeCentralizer B A, g ^ ℓ = 1 → g ∈ L := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKc]; exact (pow_pos hℓ.pos f).ne')
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hodd : Odd (Nat.card K) := by rw [hKc]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure hℓ
    hℓ2 hf hKc (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, -, hneg⟩ := hnonsplit hd
  obtain ⟨hh, -, hsymm, hsep, hiff⟩ := hneg (by rw [neg_div, div_self hd0])
  let : Field (UnitaryHigher.scalarSquareField (A : Module.End K V)) := hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField (A : Module.End K V))) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (A : Module.End K V)) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hcharE : CharP (UnitaryHigher.scalarSquareField (A : Module.End K V)) ℓ :=
    UnitaryHigher.charP_scalarSquareField (A := (A : Module.End K V)) (ℓ := ℓ)
  let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
  let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[UnitaryHigher.scalarSquareField (A : Module.End K V)]
    UnitaryHigher.scalarSquareField (A : Module.End K V) := hh
  have hnd : h'.Nondegenerate :=
    ⟨hsep, fun y hy => hsep y fun x => by
      rw [← hsymm.eq x y]
      exact (congrArg bar (hy x)).trans (map_zero bar)⟩
  have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
  have hne : sigma ≠ 1 := by
    intro heq
    let x : UnitaryHigher.scalarSquareField (A : Module.End K V) :=
      ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
    have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
    have hfix : bar x = x := DFunLike.congr_fun heq x
    rw [hfix] at hx
    simp only [zero_smul, zero_sub, one_smul, x] at hx
    have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx]
      exact add_neg_cancel _
    apply hAns 0
    rw [zero_smul]
    calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hA2, smul_zero]
  have hfixcard : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma) = ℓ ^ f := by
    have h1 := CatalogueBLinearTwoDescent.fixedSubfield_finrank _ sigma hsigma hne
    let _ : Fintype (UnitaryHigher.scalarSquareField (A : Module.End K V)) := Fintype.ofFinite _
    let _ : Fintype (CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma) := Fintype.ofFinite _
    have h2 := Module.card_eq_pow_finrank (K := CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma)
      (V := UnitaryHigher.scalarSquareField (A : Module.End K V))
    rw [h1, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard] at h2
    exact (Nat.pow_left_injective two_ne_zero h2).symm
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hquasi : IsQuasisimple (CatalogueBUnitaryIsometry.specialIsometry h') :=
    (CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall h' hsymm hnd hsigma hne
      (by rw [hfinrank]; omega) (by rw [hfixcard]; omega) (by rw [hfinrank]; omega)
      (by
        rw [hfinrank, hfixcard]
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only at h1 h2
        omega)).1
  obtain ⟨Φ⟩ : Nonempty (UnitaryHigher.similitudeCentralizer B A ≃*
      CatalogueBUnitaryIsometry.isometryGroup h') :=
    ⟨(CatalogueBSymplecticB.centralizerSimilitudeEquiv B A).symm.trans
      (CatalogueBSymplecticB.evaluationIsometryEquiv B A
        (CatalogueBUnitaryIsometry.isometryGroup h') (fun φ => ∀ v w, hh (φ v) (φ w) = hh v w)
        (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)⟩
  refine ⟨(CatalogueBUnitaryIsometry.specialIsometry h').comap Φ.toMonoidHom,
    Subgroup.Normal.comap (MonoidHom.normal_ker _) _, ?_, fun g hg => ?_⟩
  · exact isQuasisimple_comap_equiv Φ hquasi
  · rw [mem_comap, MonoidHom.mem_ker]
    apply eq_one_of_pow_char (ℓ := ℓ)
    rw [← map_pow, ← map_pow, hg, map_one, map_one]

end Abstract

theorem exists_unitary_component [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) [CharP K ℓ] (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f) {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-d) • formJ r K) :
    ∃ L : Subgroup (StatedSp r K), L ≤ spCent r K A ∧
      (∀ g ∈ spCent r K A, ∀ q ∈ L, g * q * g⁻¹ ∈ L) ∧ IsQuasisimple L ∧
      ∀ g ∈ spCent r K A, g ^ ℓ = 1 → g ∈ L := by
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = (-d) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJ]
  obtain ⟨L, hLn, hLq, hLp⟩ := exists_unitary_component_abstract hℓ hℓ2 hf hKc hr hrq
    finrank_standard pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hAns' hd
    (linA_mul_self hAA) hAμ
  refine ⟨(L.comap (spCentEquiv A).toMonoidHom).map (spCent r K A).subtype, map_subtype_le _,
    fun g hg x hx => conj_mem_map_subtype (Subgroup.Normal.comap hLn _) hg hx,
    isQuasisimple_map_subtype_comap (spCentEquiv A) hLq, fun g hg hgl => ?_⟩
  refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [mem_comap]
  apply hLp
  rw [← map_pow]
  have : (⟨g, hg⟩ : spCent r K A) ^ ℓ = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hgl)
  rw [this, map_one]

end CFSG.ComponentClassification.Burgoyne.Sp
