module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CharacterTransport
public import CFSG.CharacterTheory.KleinFourBlocks.ProductBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.ControlledDefectCorrespondence
public import CFSG.CharacterTheory.Wreathed.NormalCentralizerBlockOrbits

public section

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.DirectProduct CFSG.TwoRankLowerBound.Helpers

namespace CFSG.KleinFourBlocks

section LinearCharacters

variable {G : Type} [Group G]

noncomputable def linearCharRep (lam : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (lam g : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro v
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mul_apply, smul_eq_mul]
    ring

theorem linearCharRep_character (lam : G →* ℂˣ) (g : G) :
    (linearCharRep lam).character g = (lam g : ℂ) := by
  simp [Representation.character, linearCharRep, LinearMap.trace_id]

theorem linearChar_mem_blocksIrr (lam : G →* ℂˣ) :
    (fun g => (lam g : ℂ)) ∈ BlocksIrr G := by
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, linearCharRep lam, ?_, ?_⟩
  · change IsSimpleOrder (Subrepresentation (linearCharRep lam))
    let _ : Nontrivial (Subrepresentation (linearCharRep lam)) := ⟨⟨⊥, ⊤, by
      intro hequal
      have hsubmodule := congrArg Subrepresentation.toSubmodule hequal
      change (⊥ : Submodule ℂ ℂ) = ⊤ at hsubmodule
      have hmem : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := by rw [hsubmodule]; trivial
      exact one_ne_zero ((Submodule.mem_bot ℂ).mp hmem)⟩⟩
    refine IsSimpleOrder.mk ?_
    intro s
    rcases IsSimpleOrder.eq_bot_or_eq_top s.toSubmodule with hbot | htop
    · left; exact Subrepresentation.toSubmodule_injective hbot
    · right; exact Subrepresentation.toSubmodule_injective htop
  · funext g
    exact linearCharRep_character lam g

theorem exists_hom_of_mem_blocksIrr [IsMulCommutative G] {ε : G → ℂ} (hε : ε ∈ BlocksIrr G) :
    ∃ lam : G →* ℂˣ, ∀ g, (lam g : ℂ) = ε g := by
  obtain ⟨W, _, _, _, ρ, hirr, rfl⟩ := hε
  have hdim : Module.finrank ℂ W = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hscalar : ∀ g, ρ g = ρ.character g • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
    have hchar : ρ.character g = c := by
      rw [Representation.character, hc]
      simp [LinearMap.trace_id, hdim]
    rw [hchar]
    exact hc
  have hmul : ∀ a b, ρ.character (a * b) = ρ.character a * ρ.character b := by
    intro a b
    have hab : ρ (a * b) = (ρ.character a * ρ.character b) • LinearMap.id := by
      rw [map_mul, hscalar a, hscalar b]
      apply LinearMap.ext
      intro v
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        mul_smul]
      exact smul_comm _ _ _
    rw [Representation.character, hab]
    simp [LinearMap.trace_id, hdim]
  have hone : ρ.character 1 = 1 := by
    rw [Representation.char_one, hdim]
    simp
  let f : G →* ℂ := { toFun := ρ.character, map_one' := hone, map_mul' := hmul }
  exact ⟨f.toHomUnits, fun g => rfl⟩

end LinearCharacters

structure ElemAbelianFactor {X : Type} [Group X] (V R : Subgroup X) : Prop where
  sq_eq_one : ∀ v ∈ V, v * v = 1
  comm_V : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  comm : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v
  inf_eq_bot : V ⊓ R = ⊥
  prod_eq : ∀ x : X, ∃ v ∈ V, ∃ r ∈ R, x = v * r

namespace ElemAbelianFactor

variable {X : Type} [Group X] {V R : Subgroup X} (h : ElemAbelianFactor V R)

@[expose] def hom : ↥V × ↥R →* X where
  toFun p := (p.1 : X) * (p.2 : X)
  map_one' := by simp
  map_mul' p q := by
    have hc := h.comm (q.1 : X) q.1.2 (p.2 : X) p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : X) * q.1 * ((p.2 : X) * q.2) = p.1 * ((q.1 : X) * p.2) * q.2 := by group
      _ = p.1 * ((p.2 : X) * q.1) * q.2 := by rw [hc]
      _ = p.1 * p.2 * (q.1 * q.2) := by group

theorem hom_apply (p : ↥V × ↥R) : h.hom p = (p.1 : X) * (p.2 : X) := rfl

theorem hom_injective : Function.Injective h.hom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨v, r⟩ hvr
  rw [hom_apply] at hvr
  have hv : (v : X) = (r : X)⁻¹ := eq_inv_of_mul_eq_one_left hvr
  have hmem : (v : X) ∈ V ⊓ R := ⟨v.2, by rw [hv]; exact R.inv_mem r.2⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hr : (r : X) = 1 := by
    have := hvr
    simp only [hmem, one_mul] at this
    exact this
  exact Prod.ext (Subtype.ext hmem) (Subtype.ext hr)

theorem hom_surjective : Function.Surjective h.hom := by
  intro x
  obtain ⟨v, hv, r, hr, rfl⟩ := h.prod_eq x
  exact ⟨(⟨v, hv⟩, ⟨r, hr⟩), rfl⟩

@[expose] noncomputable def equiv : ↥V × ↥R ≃* X :=
  MulEquiv.ofBijective h.hom ⟨h.hom_injective, h.hom_surjective⟩

theorem equiv_apply (p : ↥V × ↥R) : h.equiv p = (p.1 : X) * (p.2 : X) := rfl

include h in
theorem isMulCommutative_V : IsMulCommutative ↥V :=
  isMulCommutative_iff.mpr fun a b => Subtype.ext (h.comm_V a a.2 b b.2)

include h in
theorem isPGroup_V : IsPGroup 2 ↥V := fun g => ⟨1, by
  rw [pow_one, pow_two]
  exact Subtype.ext (h.sq_eq_one g g.2)⟩

include h in
theorem signed_of_mem_blocksIrr {ε : ↥V → ℂ} (hε : ε ∈ BlocksIrr ↥V) :
    ε 1 = 1 ∧ ∀ a, ε a = 1 ∨ ε a = -1 := by
  have := h.isMulCommutative_V
  obtain ⟨lam, hlam⟩ := exists_hom_of_mem_blocksIrr hε
  refine ⟨by rw [← hlam, map_one, Units.val_one], fun a => ?_⟩
  have hsq : ε a * ε a = 1 := by
    rw [← hlam, ← Units.val_mul, ← map_mul]
    have : a * a = 1 := Subtype.ext (h.sq_eq_one a a.2)
    rw [this, map_one, Units.val_one]
  exact mul_self_eq_one_iff.mp hsq

end ElemAbelianFactor

theorem mem_blockOf_comp_equiv_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {K K' : Type}
    [Group K] [Group K'] [Finite K] [Finite K'] (e : K ≃* K') {left right : K' → ℂ}
    (hleft : left ∈ BlocksIrr K') :
    right ∘ e ∈ BlocksBlockOf m K (left ∘ e) ↔ right ∈ BlocksBlockOf m K' left := by
  constructor
  · intro hsame
    have h1 := mem_blockOf_comp_equiv m hm e.symm (irr_comp_equiv e hleft) hsame
    have h2 : (right ∘ e) ∘ e.symm = right := by funext y; simp
    have h3 : (left ∘ e) ∘ e.symm = left := by funext y; simp
    rwa [h2, h3] at h1
  · intro hsame
    exact mem_blockOf_comp_equiv m hm e hleft hsame

theorem two_mem_of_charP_quotient (m : Ideal BlocksAlgInt) [h2 : CharP (BlocksAlgInt ⧸ m) 2] :
    (2 : BlocksAlgInt) ∈ m := by
  have h0 : ((2 : ℕ) : BlocksAlgInt ⧸ m) = 0 := CharP.cast_eq_zero _ 2
  have h0' : (Ideal.Quotient.mk m) ((2 : ℕ) : BlocksAlgInt) = 0 := by
    rw [map_natCast]; exact h0
  exact_mod_cast Ideal.Quotient.eq_zero_iff_mem.mp h0'

theorem mem_blockOf_prod_defectZero_iff (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]
    [CharP (BlocksAlgInt ⧸ m) 2] {Z L : Type} [Group Z] [Fintype Z] [Group L] [Fintype L]
    (hZ : ∀ ε ∈ BlocksIrr Z, ε 1 = 1 ∧ ∀ a, ε a = 1 ∨ ε a = -1) {ε : Z → ℂ}
    (hε : ε ∈ BlocksIrr Z) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hdeg : ∃ d : ℕ, θ 1 = d ∧ 2 ^ (Nat.card L).factorization 2 ∣ d) (χ : Z × L → ℂ) :
    χ ∈ BlocksBlockOf m (Z × L) (outerProductCharacter ε θ) ↔
      ∃ ε' ∈ BlocksIrr Z, χ = outerProductCharacter ε' θ := by
  classical
  rw [blockOf_prod_of_signed m hm (two_mem_of_charP_quotient m) hZ hε hθ,
    blockOf_eq_singleton_of_defect_zero m hθ hdeg]
  simp

section Twist

variable {X : Type} [Group X] [Fintype X]

structure DefectZeroTwistHyp (wb : FiniteIrreducibleCharacterBasis X) (V R : Subgroup X)
    (n₀ : wb.index) : Prop extends ElemAbelianFactor V R where
  trivial_on_V : ∀ (x x' v : X), v ∈ V → x = v * x' → x' ∈ R →
    (wb.representation n₀).character x = (wb.representation n₀).character x'
  deg : ∃ d : ℕ, (wb.representation n₀).character 1 = d ∧
    2 ^ (Nat.card R).factorization 2 ∣ d

noncomputable def defectZeroTwistChar (wb : FiniteIrreducibleCharacterBasis X) (R : Subgroup X)
    (n₀ : wb.index) : ↥R → ℂ := fun r => (wb.representation n₀).character (r : X)

variable {wb : FiniteIrreducibleCharacterBasis X} {V R : Subgroup X} {n₀ : wb.index}

theorem defectZeroTwist_equiv_char (T : DefectZeroTwistHyp wb V R n₀) :
    (wb.representation n₀).character ∘ T.equiv =
      outerProductCharacter (fun _ : ↥V => (1 : ℂ)) (defectZeroTwistChar wb R n₀) := by
  funext p
  obtain ⟨v, r⟩ := p
  simp only [Function.comp_apply, outerProductCharacter, defectZeroTwistChar, one_mul]
  exact T.trivial_on_V _ _ v v.2 rfl r.2

theorem defectZeroTwistChar_mem_blocksIrr (T : DefectZeroTwistHyp wb V R n₀) :
    defectZeroTwistChar wb R n₀ ∈ BlocksIrr ↥R := by
  let _ : Fintype ↥V := Fintype.ofFinite _
  let _ : Fintype ↥R := Fintype.ofFinite _
  have hχ : (wb.representation n₀).character ∘ T.equiv ∈ BlocksIrr (↥V × ↥R) :=
    irr_comp_equiv T.equiv (CFSG.BlockBasics.basis_character_mem_irr wb n₀)
  obtain ⟨⟨ε, θ⟩, ⟨hε, hθ⟩, hεθ⟩ := outerProductCharacter_surjOn hχ
  have h1 : ε 1 = 1 := (T.toElemAbelianFactor.signed_of_mem_blocksIrr hε).1
  have hθeq : θ = defectZeroTwistChar wb R n₀ := by
    funext r
    have hr := congrFun hεθ (1, r)
    simp only [outerProductCharacter, h1, one_mul, Function.comp_apply] at hr
    rw [hr]
    simp [defectZeroTwistChar, ElemAbelianFactor.equiv_apply]
  rw [← hθeq]
  exact hθ

theorem defectZeroTwistChar_deg (T : DefectZeroTwistHyp wb V R n₀) :
    ∃ d : ℕ, defectZeroTwistChar wb R n₀ 1 = d ∧ 2 ^ (Nat.card ↥R).factorization 2 ∣ d :=
  T.deg

theorem mem_blockOf_defectZeroTwist_iff (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (χ : ↥V × ↥R → ℂ) :
    χ ∈ BlocksBlockOf ideal (↥V × ↥R)
        (outerProductCharacter (fun _ : ↥V => (1 : ℂ)) (defectZeroTwistChar wb R n₀)) ↔
      ∃ ε' ∈ BlocksIrr ↥V, χ = outerProductCharacter ε' (defectZeroTwistChar wb R n₀) := by
  let _ : Fintype ↥V := Fintype.ofFinite _
  let _ : Fintype ↥R := Fintype.ofFinite _
  exact mem_blockOf_prod_defectZero_iff ideal
    (fun ε hε => T.toElemAbelianFactor.signed_of_mem_blocksIrr hε)
    (one_mem_blocksIrr ↥V) (defectZeroTwistChar_mem_blocksIrr T) (defectZeroTwistChar_deg T) χ

theorem mem_coefficientBlock_iff_char_mem_blockOf (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ψ : wb.index) :
    ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀ ↔
      (wb.representation ψ).character ∈
        BlocksBlockOf ideal X (wb.representation n₀).character :=
  (coefficientBlock_mem_iff wb _ n₀ ψ).trans
    (CFSG.BlockBasics.sameCoefficientBlock_iff wb ideal n₀ ψ)

theorem mem_coefficientBlock_iff_exists_prod (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (ψ : wb.index) :
    ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀ ↔
      ∃ ε' ∈ BlocksIrr ↥V, ∀ p : ↥V × ↥R,
        (wb.representation ψ).character (T.equiv p) =
          ε' p.1 * defectZeroTwistChar wb R n₀ p.2 := by
  rw [mem_coefficientBlock_iff_char_mem_blockOf, ← mem_blockOf_comp_equiv_iff ideal inferInstance
    T.equiv (CFSG.BlockBasics.basis_character_mem_irr wb n₀), defectZeroTwist_equiv_char T,
    mem_blockOf_defectZeroTwist_iff T ideal]
  constructor
  · rintro ⟨ε', hε', hψ⟩
    exact ⟨ε', hε', fun p => congrFun hψ p⟩
  · rintro ⟨ε', hε', hψ⟩
    exact ⟨ε', hε', funext hψ⟩

theorem exists_coefficientBlock_label_of_irr (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {ε' : ↥V → ℂ} (hε' : ε' ∈ BlocksIrr ↥V) :
    ∃ ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀, ∀ p : ↥V × ↥R,
      (wb.representation ψ).character (T.equiv p) =
        ε' p.1 * defectZeroTwistChar wb R n₀ p.2 := by
  let _ : Fintype ↥V := Fintype.ofFinite _
  let _ : Fintype ↥R := Fintype.ofFinite _
  have hirr : outerProductCharacter ε' (defectZeroTwistChar wb R n₀) ∘ T.equiv.symm ∈
      BlocksIrr X :=
    irr_comp_equiv T.equiv.symm
      (outerProductCharacter_mem_blocksIrr hε' (defectZeroTwistChar_mem_blocksIrr T))
  obtain ⟨ψ, hψ⟩ := CFSG.BlockBasics.exists_label_of_mem_irr wb hirr
  have hform : ∀ p : ↥V × ↥R, (wb.representation ψ).character (T.equiv p) =
      ε' p.1 * defectZeroTwistChar wb R n₀ p.2 := by
    intro p
    rw [hψ]
    simp [outerProductCharacter]
  exact ⟨ψ, (mem_coefficientBlock_iff_exists_prod T ideal ψ).mpr ⟨ε', hε', hform⟩, hform⟩

theorem forall_equiv_iff_forall_decomposition (T : DefectZeroTwistHyp wb V R n₀) (g : X → ℂ)
    (F : ↥V → ℂ) :
    (∀ p : ↥V × ↥R, g (T.equiv p) = F p.1 * defectZeroTwistChar wb R n₀ p.2) ↔
      ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        g x = (wb.representation n₀).character x' * F v := by
  constructor
  · intro hg x x' v hx hx'
    subst hx
    exact (hg (v, ⟨x', hx'⟩)).trans (mul_comm _ _)
  · intro hg p
    exact (hg (T.equiv p) p.2 p.1 rfl p.2.2).trans (mul_comm _ _)

theorem mem_coefficientBlock_iff_exists_hom (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (ψ : wb.index) :
    ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀ ↔
      ∃ lam : ↥V →* ℂˣ, ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        (wb.representation ψ).character x =
          (wb.representation n₀).character x' * (lam v : ℂ) := by
  have := T.toElemAbelianFactor.isMulCommutative_V
  rw [mem_coefficientBlock_iff_exists_prod T ideal]
  constructor
  · rintro ⟨ε', hε', hψ⟩
    obtain ⟨lam, hlam⟩ := exists_hom_of_mem_blocksIrr hε'
    exact ⟨lam, (forall_equiv_iff_forall_decomposition T (wb.representation ψ).character
      fun v => (lam v : ℂ)).mp (fun p => by rw [hψ p, hlam])⟩
  · rintro ⟨lam, hlam⟩
    exact ⟨fun v => (lam v : ℂ), linearChar_mem_blocksIrr lam,
      (forall_equiv_iff_forall_decomposition T (wb.representation ψ).character
        fun v => (lam v : ℂ)).mpr hlam⟩

theorem exists_coefficientBlock_label_of_hom (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (lam : ↥V →* ℂˣ) :
    ∃ ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀,
      ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        (wb.representation ψ).character x =
          (wb.representation n₀).character x' * (lam v : ℂ) := by
  obtain ⟨ψ, hψblock, hψ⟩ :=
    exists_coefficientBlock_label_of_irr T ideal (linearChar_mem_blocksIrr lam)
  exact ⟨ψ, hψblock, (forall_equiv_iff_forall_decomposition T _ fun v => (lam v : ℂ)).mp hψ⟩

theorem mem_coefficientCharacterSpace_iff (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (f : X → ℂ) :
    f ∈ coefficientCharacterSpace wb
        (coefficientBlock wb (localizedComplexIntegerRing ideal) n₀) ↔
      ∃ F : ↥V → ℂ, ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        f x = (wb.representation n₀).character x' * F v := by
  simp only [← forall_equiv_iff_forall_decomposition T f]
  constructor
  · intro hf
    unfold coefficientCharacterSpace at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, rfl⟩ := hg
      obtain ⟨ε', -, hε'⟩ :=
        (mem_coefficientBlock_iff_exists_prod T ideal ψ).mp (Finset.mem_coe.mp hψ)
      exact ⟨ε', hε'⟩
    | zero => exact ⟨0, fun p => by simp⟩
    | add g₁ g₂ _ _ h₁ h₂ =>
      obtain ⟨F₁, hF₁⟩ := h₁
      obtain ⟨F₂, hF₂⟩ := h₂
      exact ⟨F₁ + F₂, fun p => by simp [hF₁ p, hF₂ p, add_mul]⟩
    | smul c g _ h₁ =>
      obtain ⟨F₁, hF₁⟩ := h₁
      exact ⟨c • F₁, fun p => by simp [hF₁ p, mul_assoc]⟩
  · rintro ⟨F, hF⟩
    let _ : Fintype ↥V := Fintype.ofFinite _
    have := T.toElemAbelianFactor.isMulCommutative_V
    obtain ⟨vb⟩ := finiteIrreducibleCharacterBasis_exists (G := ↥V)
    have hclass : ∀ a b : ↥V, F (b * a * b⁻¹) = F a := fun a b => by
      rw [mul_comm' b a, mul_inv_cancel_right]
    have hrec := finiteIrreducibleCharacterBasis_reconstruction vb F hclass
    choose ψ hψblock hψ using fun l : vb.index =>
      exists_coefficientBlock_label_of_irr T ideal (CFSG.BlockBasics.basis_character_mem_irr vb l)
    set c : vb.index → ℂ := fun l => characterPairing F (vb.representation l).character with hc
    have hfeq : f = ∑ l, c l • (wb.representation (ψ l)).character := by
      funext x
      obtain ⟨p, rfl⟩ := T.equiv.surjective x
      rw [Finset.sum_apply, hF p, hrec p.1, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hψ l p, mul_assoc]
    rw [hfeq]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨ψ l, hψblock l, rfl⟩)

theorem coefficientBlockDefect_of_defectZeroTwist (T : DefectZeroTwistHyp wb V R n₀)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    coefficientBlockDefect wb ideal 2 n₀ V := by
  let _ : Fintype ↥V := Fintype.ofFinite _
  let _ : Fintype ↥R := Fintype.ofFinite _
  classical
  obtain ⟨vrb⟩ := finiteIrreducibleCharacterBasis_exists (G := ↥V × ↥R)
  have hirr : (wb.representation n₀).character ∘ T.equiv ∈ BlocksIrr (↥V × ↥R) :=
    irr_comp_equiv T.equiv (CFSG.BlockBasics.basis_character_mem_irr wb n₀)
  obtain ⟨ℓ, hℓ⟩ := CFSG.BlockBasics.exists_label_of_mem_irr vrb hirr
  have hLT : CFSG.Wreathed.BlockOrbits.LabelTransport vrb wb T.equiv ℓ n₀ := fun x => by
    rw [hℓ]; rfl
  have hdef : coefficientBlockDefect vrb ideal 2 ℓ
      ((⊤ : Subgroup ↥V).prod (⊥ : Subgroup ↥R)) := by
    rw [CFSG.BlockBasics.coefficientBlockDefect_iff, hℓ, defectZeroTwist_equiv_char T]
    have hε : (fun _ : ↥V => (1 : ℂ)) ∈ BlocksIrr ↥V := one_mem_blocksIrr ↥V
    exact blockDefect_prod_of_defect_zero ideal inferInstance (two_mem_of_charP_quotient ideal)
      T.toElemAbelianFactor.isPGroup_V
      (fun ε hε => T.toElemAbelianFactor.signed_of_mem_blocksIrr hε)
      (defectZeroTwistChar_mem_blocksIrr T) (defectZeroTwistChar_deg T) hε _
      (mem_blockOf_self ideal
        (outerProductCharacter_mem_blocksIrr hε (defectZeroTwistChar_mem_blocksIrr T)))
  have hmap := CFSG.Semidihedral.Principal.ControlledDefect.coefficientBlockDefect_map_equiv vrb
    wb ideal 2 T.equiv
    (fun z => CFSG.Wreathed.BlockOrbits.centralCharacterResidueHom_labelTransport vrb wb ideal
      T.equiv hLT z) hdef
  have hV : ((⊤ : Subgroup ↥V).prod (⊥ : Subgroup ↥R)).map T.equiv.toMonoidHom = V := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp2 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hp).2
      have : (T.equiv.toMonoidHom p : X) = (p.1 : X) := by
        change (p.1 : X) * (p.2 : X) = _
        rw [hp2]
        simp
      rw [this]
      exact p.1.2
    · intro hx
      refine ⟨(⟨x, hx⟩, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, ?_⟩
      change (x : X) * ((1 : ↥R) : X) = x
      simp
  rwa [hV] at hmap

end Twist

theorem defect_zero_twist_block_and_class_functions
    {X : Type} [Group X] [Fintype X] (wb : FiniteIrreducibleCharacterBasis X)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (V R : Subgroup X) (hV2 : ∀ v ∈ V, v * v = 1) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hcomm : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v) (hVR : V ⊓ R = ⊥)
    (hX : ∀ x : X, ∃ v ∈ V, ∃ r ∈ R, x = v * r)
    (n₀ : wb.index)
    (hn₀V : ∀ (x x' : X) (v : X), v ∈ V → x = v * x' → x' ∈ R →
      (wb.representation n₀).character x = (wb.representation n₀).character x')
    (hn₀deg : ∃ d : ℕ, (wb.representation n₀).character 1 = d ∧
      2 ^ (Nat.card R).factorization 2 ∣ d) :
    (∀ ψ : wb.index, ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀ ↔
      ∃ lam : ↥V →* ℂˣ, ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        (wb.representation ψ).character x =
          (wb.representation n₀).character x' * (lam v : ℂ)) ∧
    (∀ lam : ↥V →* ℂˣ, ∃ ψ ∈ coefficientBlock wb (localizedComplexIntegerRing ideal) n₀,
      ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        (wb.representation ψ).character x =
          (wb.representation n₀).character x' * (lam v : ℂ)) ∧
    (∀ f : X → ℂ, f ∈ coefficientCharacterSpace wb
        (coefficientBlock wb (localizedComplexIntegerRing ideal) n₀) ↔
      ∃ F : ↥V → ℂ, ∀ (x x' : X) (v : ↥V), x = (v : X) * x' → x' ∈ R →
        f x = (wb.representation n₀).character x' * F v) ∧
    coefficientBlockDefect wb ideal 2 n₀ V := by
  have T : DefectZeroTwistHyp wb V R n₀ := ⟨⟨hV2, hVab, hcomm, hVR, hX⟩, hn₀V, hn₀deg⟩
  exact ⟨mem_coefficientBlock_iff_exists_hom T ideal, exists_coefficientBlock_label_of_hom T ideal,
    mem_coefficientCharacterSpace_iff T ideal, coefficientBlockDefect_of_defectZeroTwist T ideal⟩

end CFSG.KleinFourBlocks
