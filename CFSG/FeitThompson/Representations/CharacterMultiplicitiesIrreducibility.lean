module

import Mathlib.Algebra.DirectSum.LinearMap
import CFSG.FeitThompson.Representations.SymmetricAlternatingSquareCharacters
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.ComplexCompleteReducibility
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.CharInnerProductIntertwiners
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.TensorAndDualCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

noncomputable section

variable {G : Type*} [Group G] {V W X Y : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem exists_fdRep_equiv [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ X : FDRep ℂ G, Nonempty (ρ.Equiv X.ρ) := by
  classical
  set n := finrank ℂ V with hn
  set e : V ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun with he
  set ρ' : Representation ℂ G (Fin n → ℂ) :=
    ((e.conjAlgEquiv ℂ : Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ))
      : Module.End ℂ V →* Module.End ℂ (Fin n → ℂ)).comp ρ with hρ'
  refine ⟨FDRep.of ρ', ⟨Representation.Equiv.mk e fun g => ?_⟩⟩
  rw [FDRep.of_ρ' ρ']
  ext v
  simp [hρ', LinearEquiv.conjAlgEquiv]

theorem character_mem_Irr_of_isIrreducible [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : ρ.character ∈ Irr G := by
  obtain ⟨X, ⟨e⟩⟩ := exists_fdRep_equiv ρ
  refine mem_Irr.2 ⟨X, Representation.isIrreducible_of_equiv e h, ?_⟩
  rw [fdRepCharacter_eq, ← Representation.char_iso e]

theorem character_eq_sum_of_isInternal [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} {n : ℕ}
    (σ : Fin n → Subrepresentation ρ)
    (h : DirectSum.IsInternal fun i => (σ i).toSubmodule) :
    ρ.character = ∑ i, (σ i).toRepresentation.character := by
  funext g
  have hmaps : ∀ i, Set.MapsTo (ρ g) ((σ i).toSubmodule : Set V) ((σ i).toSubmodule : Set V) :=
    fun i x hx => (σ i).apply_mem_toSubmodule g hx
  rw [show ρ.character g = LinearMap.trace ℂ V (ρ g) from rfl,
    LinearMap.trace_eq_sum_trace_restrict h hmaps, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    (Subrepresentation.character_eq_trace_restrict (σ i) g (hmaps i)).symm

def irrFinset (G : Type*) [Group G] [Finite G] : Finset (G → ℂ) :=
  finite_Irr.toFinset

@[simp]
theorem mem_irrFinset [Finite G] {χ : G → ℂ} : χ ∈ irrFinset G ↔ χ ∈ Irr G :=
  finite_Irr.mem_toFinset

theorem Representation.character_prod [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  have h : (ρ.prod σ) g = LinearMap.prodMap (ρ g) (σ g) := by
    ext x <;> simp [Representation.prod_apply_apply]
  simp [Representation.character, h, LinearMap.trace_prodMap']

def Representation.prodEquivOfIsCompl {ρ : Representation ℂ G V} (p q : Subrepresentation ρ)
    (h : IsCompl p.toSubmodule q.toSubmodule) :
    (p.toRepresentation.prod q.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl _ _ h) fun g => by
    ext x <;> simp [Subrepresentation.toRepresentation]

def Representation.Equiv.prodCongr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G X} {υ : Representation ℂ G Y}
    (e : ρ.Equiv τ) (f : σ.Equiv υ) : (ρ.prod σ).Equiv (τ.prod υ) :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) fun g => by
    ext x <;> simp [Representation.prod_apply_apply, e.isIntertwining, f.isIntertwining]

theorem Representation.character_add_of_isCompl [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (p q : Subrepresentation ρ)
    (h : IsCompl p.toSubmodule q.toSubmodule) :
    ρ.character = p.toRepresentation.character + q.toRepresentation.character := by
  rw [← Representation.character_prod,
    Representation.char_iso (Representation.prodEquivOfIsCompl p q h)]

theorem exists_isCompl_subrepresentation [Finite G] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (p : Subrepresentation ρ) :
    ∃ q : Subrepresentation ρ, IsCompl p.toSubmodule q.toSubmodule := by
  obtain ⟨U, hU, hcompl⟩ := exists_invariant_isCompl_complex ρ p.toSubmodule
    fun g v hv => p.apply_mem_toSubmodule g hv
  exact ⟨⟨U, fun g v hv => hU g v hv⟩, hcompl⟩

theorem exists_isIrreducible_subrepresentation [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Nontrivial V] :
    ∃ p : Subrepresentation ρ, p.toRepresentation.IsIrreducible := by
  classical
  obtain ⟨n, σ, hint, hirr⟩ := exists_directSum_isInternal_isIrreducible ρ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    have htop := hint.submodule_iSup_eq_top
    rw [iSup_of_empty] at htop
    exact bot_ne_top htop
  exact ⟨σ ⟨0, hn⟩, hirr _⟩

def Representation.equivRangeOfInjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    ρ.Equiv (Representation.IntertwiningMap.range ρ σ f).toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g => by
    ext x; exact f.isIntertwining ρ σ g x

def Subrepresentation.inclusionIntertwiningMap {ρ : Representation ℂ G V}
    (p : Subrepresentation ρ) : p.toRepresentation.IntertwiningMap ρ where
  toLinearMap := p.toSubmodule.subtype
  isIntertwining' _ := by ext _; rfl

theorem exists_character_eq_sum_nsmul [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ m : irrFinset G → ℕ, ρ.character = ∑ χ : irrFinset G, (m χ : ℂ) • (χ : G → ℂ) := by
  classical
  obtain ⟨n, σ, hint, hirr⟩ := exists_directSum_isInternal_isIrreducible ρ
  refine ⟨fun χ =>
    (Finset.univ.filter fun i : Fin n => (σ i).toRepresentation.character = (χ : G → ℂ)).card, ?_⟩
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (σ i).toRepresentation.character ∈ irrFinset G := fun i _ =>
    mem_irrFinset.2 (character_mem_Irr_of_isIrreducible _ (hirr i))
  have key : ∑ χ ∈ irrFinset G,
      (((Finset.univ.filter fun i : Fin n =>
        (σ i).toRepresentation.character = χ).card : ℂ) • χ)
      = ∑ i, (σ i).toRepresentation.character := by
    rw [← Finset.sum_fiberwise_of_maps_to hmem fun i => (σ i).toRepresentation.character]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [character_eq_sum_of_isInternal σ hint, ← key,
    Finset.sum_coe_sort (irrFinset G) fun χ =>
      (((Finset.univ.filter fun i : Fin n =>
        (σ i).toRepresentation.character = χ).card : ℂ) • χ)]

theorem cfInner_eq_multiplicity [Fintype G] {θ : G → ℂ} {m : irrFinset G → ℕ}
    (hθ : θ = ∑ χ : irrFinset G, (m χ : ℂ) • (χ : G → ℂ)) (ψ : irrFinset G) :
    cfInner θ (ψ : G → ℂ) = (m ψ : ℂ) := by
  classical
  have h0 : ∀ χ : irrFinset G, χ ≠ ψ →
      cfInner ((m χ : ℂ) • (χ : G → ℂ)) (ψ : G → ℂ) = 0 := by
    intro χ hne
    rw [cfInner_smul_left, cfInner_eq_ite_of_mem_Irr (mem_irrFinset.1 χ.2) (mem_irrFinset.1 ψ.2),
      if_neg fun h => hne (Subtype.ext h), mul_zero]
  rw [hθ, cfInner_sum_left, Finset.sum_eq_single_of_mem ψ (Finset.mem_univ ψ)
      (fun χ _ hne => h0 χ hne), cfInner_smul_left,
    cfInner_eq_ite_of_mem_Irr (mem_irrFinset.1 ψ.2) (mem_irrFinset.1 ψ.2), if_pos rfl, mul_one]

theorem existsUnique_character_eq_sum_nsmul [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃! m : irrFinset G → ℕ, ρ.character = ∑ χ : irrFinset G, (m χ : ℂ) • (χ : G → ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul ρ
  refine ⟨m, hm, fun m' hm' => funext fun χ => ?_⟩
  exact Nat.cast_inj.1 ((cfInner_eq_multiplicity hm' χ).symm.trans (cfInner_eq_multiplicity hm χ))

theorem multiplicity_eq_cfInner_character [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {m : irrFinset G → ℕ}
    (hm : ρ.character = ∑ χ : irrFinset G, (m χ : ℂ) • (χ : G → ℂ)) (χ : irrFinset G) :
    (m χ : ℂ) = cfInner ρ.character (χ : G → ℂ) :=
  (cfInner_eq_multiplicity hm χ).symm

theorem cfInner_self_eq_sum_sq [Fintype G] {θ : G → ℂ} {m : irrFinset G → ℕ}
    (hθ : θ = ∑ χ : irrFinset G, (m χ : ℂ) • (χ : G → ℂ)) :
    cfInner θ θ = ∑ χ : irrFinset G, ((m χ : ℂ)) ^ 2 := by
  nth_rewrite 1 [hθ]
  rw [cfInner_sum_left]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [cfInner_smul_left, ← conj_cfInner θ (χ : G → ℂ), cfInner_eq_multiplicity hθ χ,
    Complex.conj_natCast]
  ring

theorem isIrreducible_iff_cfInner_self_eq_one [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ cfInner ρ.character ρ.character = 1 := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    rw [cfInner_character_character ρ ρ, if_pos ⟨Representation.Equiv.refl ρ⟩]
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul ρ
  have hsum : ∑ χ : irrFinset G, ((m χ : ℂ)) ^ 2 = 1 := by
    rw [← cfInner_self_eq_sum_sq hm]; exact h
  have hnat : ∑ χ : irrFinset G, m χ ^ 2 = 1 := by
    have hcast : ((∑ χ : irrFinset G, m χ ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      simpa using hsum
    exact Nat.cast_inj.1 hcast
  by_cases hall : ∀ χ : irrFinset G, m χ = 0
  · exfalso
    have h0 : ∑ χ : irrFinset G, m χ ^ 2 = 0 :=
      Finset.sum_eq_zero fun χ _ => by rw [hall χ]; ring
    rw [h0] at hnat
    exact zero_ne_one hnat
  push Not at hall
  obtain ⟨χ₀, hχ₀⟩ := hall
  have hsplit : m χ₀ ^ 2 + ∑ χ ∈ (Finset.univ : Finset (irrFinset G)).erase χ₀, m χ ^ 2 = 1 :=
    (Finset.add_sum_erase _ (fun χ => m χ ^ 2) (Finset.mem_univ χ₀)).trans hnat
  have hsq : m χ₀ ^ 2 ≤ 1 := by omega
  have hone : m χ₀ = 1 :=
    Nat.le_antisymm (le_trans (Nat.le_self_pow two_ne_zero _) hsq) (Nat.pos_of_ne_zero hχ₀)
  have hrest : ∀ χ : irrFinset G, χ ≠ χ₀ → m χ = 0 := by
    intro χ hne
    have hz : ∑ χ ∈ (Finset.univ : Finset (irrFinset G)).erase χ₀, m χ ^ 2 = 0 := by
      rw [hone] at hsplit; omega
    have := (Finset.sum_eq_zero_iff.1 hz) χ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ χ⟩)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hIrr : ρ.character ∈ Irr G := by
    have hval : ρ.character = (χ₀ : G → ℂ) := by
      rw [hm, Finset.sum_eq_single_of_mem χ₀ (Finset.mem_univ χ₀)
        (fun χ _ hne => by rw [hrest χ hne]; simp), hone]
      simp
    rw [hval]
    exact mem_irrFinset.1 χ₀.2
  obtain ⟨Z, hZirr, hZchar⟩ := mem_Irr.1 hIrr
  have hZi := hZirr
  have hdim : finrank ℂ V = finrank ℂ (Z.V : Type) := by
    have h1 : FDRep.character Z 1 = ρ.character 1 := congrFun hZchar 1
    rw [FDRep.char_one, Representation.char_one] at h1
    exact (Nat.cast_inj.1 h1).symm
  have hhom : finrank ℂ (ρ.IntertwiningMap Z.ρ) = 1 := by
    have h2 := cfInner_character_eq_finrank_intertwiningMap ρ Z.ρ
    rw [← fdRepCharacter_eq, hZchar, h] at h2
    exact_mod_cast h2.symm
  have : Nontrivial (ρ.IntertwiningMap Z.ρ) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hhom]; norm_num)
  obtain ⟨f, hf⟩ := exists_ne (0 : ρ.IntertwiningMap Z.ρ)
  have hsurj : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hsurj' : Function.Surjective f.toLinearMap := hsurj
  have hinj : Function.Injective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj'
  exact Representation.isIrreducible_of_equiv (f.ofBijective ⟨hinj, hsurj⟩).symm hZi

universe u v

private theorem nonempty_equiv_of_character_eq_aux [Finite G] (n : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
      finrank ℂ V ≤ n → ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V W _ _ _ _ _ _ ρ σ hn hchar
    have : Fintype G := Fintype.ofFinite G
    by_cases hV : Nontrivial V
    · obtain ⟨p, hp⟩ := exists_isIrreducible_subrepresentation ρ
      obtain ⟨q, hq⟩ := exists_isCompl_subrepresentation p
      have hpi := hp
      have hntp : Nontrivial p.toSubmodule := Representation.nontrivial_of_isIrreducible _ hp
      have hincl : Subrepresentation.inclusionIntertwiningMap p ≠ 0 := by
        obtain ⟨x, hx⟩ := exists_ne (0 : p.toSubmodule)
        intro h0
        refine hx (Subtype.ext ?_)
        have := congrArg (fun f : p.toRepresentation.IntertwiningMap ρ => f x) h0
        simpa [Subrepresentation.inclusionIntertwiningMap] using this
      have hposρ : 0 < finrank ℂ (p.toRepresentation.IntertwiningMap ρ) :=
        haveI : Nontrivial (p.toRepresentation.IntertwiningMap ρ) := nontrivial_of_ne _ _ hincl
        finrank_pos
      have heq : finrank ℂ (p.toRepresentation.IntertwiningMap ρ) =
          finrank ℂ (p.toRepresentation.IntertwiningMap σ) := by
        have hc : (finrank ℂ (p.toRepresentation.IntertwiningMap ρ) : ℂ) =
            (finrank ℂ (p.toRepresentation.IntertwiningMap σ) : ℂ) := by
          rw [← cfInner_character_eq_finrank_intertwiningMap p.toRepresentation ρ,
            ← cfInner_character_eq_finrank_intertwiningMap p.toRepresentation σ, hchar]
        exact_mod_cast hc
      have : Nontrivial (p.toRepresentation.IntertwiningMap σ) :=
        Module.nontrivial_of_finrank_pos (R := ℂ) (heq ▸ hposρ)
      obtain ⟨f, hf⟩ := exists_ne (0 : p.toRepresentation.IntertwiningMap σ)
      have hfinj : Function.Injective f :=
        (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
      set p' := Representation.IntertwiningMap.range p.toRepresentation σ f with hp'
      have ep : p.toRepresentation.Equiv p'.toRepresentation :=
        Representation.equivRangeOfInjective f hfinj
      obtain ⟨q', hq'⟩ := exists_isCompl_subrepresentation p'
      have hcq : q.toRepresentation.character = q'.toRepresentation.character := by
        have h1 := Representation.character_add_of_isCompl p q hq
        have h2 := Representation.character_add_of_isCompl p' q' hq'
        rw [hchar, h2, ← Representation.char_iso ep] at h1
        exact (add_left_cancel h1).symm
      have hlt : finrank ℂ q.toSubmodule < finrank ℂ V := by
        have := Submodule.finrank_add_eq_of_isCompl hq
        have hp0 : 0 < finrank ℂ p.toSubmodule := finrank_pos
        omega
      obtain ⟨eq'⟩ := ih (finrank ℂ q.toSubmodule) (lt_of_lt_of_le hlt hn)
        q.toRepresentation q'.toRepresentation le_rfl hcq
      exact ⟨Representation.Equiv.trans
        (Representation.Equiv.symm (Representation.prodEquivOfIsCompl p q hq))
        (Representation.Equiv.trans (Representation.Equiv.prodCongr ep eq')
          (Representation.prodEquivOfIsCompl p' q' hq'))⟩
    ·
      rw [not_nontrivial_iff_subsingleton] at hV
      have hW : Subsingleton W := by
        have h1 : σ.character 1 = ρ.character 1 := congrFun hchar.symm 1
        rw [Representation.char_one, Representation.char_one] at h1
        have h0 : finrank ℂ V = 0 := by rw [finrank_zero_iff (R := ℂ)]; exact hV
        rw [h0] at h1
        exact (finrank_zero_iff (R := ℂ)).1 (Nat.cast_inj.1 h1)
      exact ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W) fun _ => by
        ext _; exact Subsingleton.elim _ _⟩

theorem nonempty_equiv_iff_character_eq' [Finite G] {V : Type u} {W : Type v} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Nonempty (ρ.Equiv σ) ↔ ρ.character = σ.character :=
  ⟨fun ⟨e⟩ => Representation.char_iso e,
    nonempty_equiv_of_character_eq_aux (finrank ℂ V) ρ σ le_rfl⟩

theorem nonempty_iso_iff_character_eq' [Finite G] (Z Z' : FDRep ℂ G) :
    Nonempty (Z ≅ Z') ↔ Z.character = Z'.character := by
  refine ⟨fun ⟨e⟩ => FDRep.char_iso e, fun h => ?_⟩
  obtain ⟨e⟩ := (nonempty_equiv_iff_character_eq'
    (show Representation ℂ G Z.V from Z.ρ) (show Representation ℂ G Z'.V from Z'.ρ)).2 h
  exact ⟨Action.mkIso e.toLinearEquiv.toFGModuleCatIso fun g => by
    ext x; exact e.isIntertwining _ _ g x⟩

end

end CFSG.FeitThompson
