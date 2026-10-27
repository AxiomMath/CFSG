module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslFam

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def ExcInnerNoField (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f →
    t ≠ .Tits → Fam t n p f → LieModel P t n p f →
    ∀ x y : P, x ≠ 1 → x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x →
      ∀ (J : Subgroup P) (q : ℕ), GLAPComponent 3 (fixSub (MulAut.conj x)) J →
        IsTypeL2 q (barOf 3 J) → ¬ 3 ∣ q → q ≠ 8 → 10 ≤ q →
          ¬ (FieldBar 2 J (MulAut.conj y) ∧ ¬ TrivBar J (MulAut.conj y))

@[expose] def ExcResidual (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  OutDerived3At Fam ∧ ExcInnerNoField Fam

theorem s1431_false_of_inner_noField {P : Type} [Group P] [Finite P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    {A : Subgroup (MulAut P)} {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q)
    (hq : 10 ≤ q) (hA : ∀ a ∈ A, IsInnerAut a)
    (R : ∀ x y : P, x ≠ 1 → x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x →
      ∀ (J' : Subgroup P) (q' : ℕ), GLAPComponent 3 (fixSub (MulAut.conj x)) J' →
        IsTypeL2 q' (barOf 3 J') → ¬ 3 ∣ q' → q' ≠ 8 → 10 ≤ q' →
          ¬ (FieldBar 2 J' (MulAut.conj y) ∧ ¬ TrivBar J' (MulAut.conj y))) : False := by
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  obtain ⟨η, hηA, hηψ⟩ := exists_mem_not_zpowers hψ3 c.card
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  obtain ⟨x, hx⟩ := hA ψ c.mem
  obtain ⟨y, hy⟩ := hA η hηA
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hx, hψ3, map_one])
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hy, hη3, map_one])
  have hxy : x * y = y * x := by
    apply hinj
    rw [map_mul, map_mul, hx, hy]
    have := c.elemAbelian.1.is_comm.comm ⟨ψ, c.mem⟩ ⟨η, hηA⟩
    exact congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact c.ne_one (by rw [← hx, map_one])
  have hcomp : GLAPComponent 3 (fixSub (MulAut.conj x)) J := hx ▸ c.comp
  exact R x y hx1 hx3 hy3 hxy J q hcomp c.typeL2 c.not_dvd c.ne_eight hq
    (hy ▸ c.field η hηA hηψ)

theorem y1431_noCfg_of_excResidual {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : ExcResidual Fam) : Y1431NoCfgAt Fam := by
  obtain ⟨hOut, hR⟩ := h
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  have hq : 10 ≤ q := ten_le_of_cube hq0 hqq
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) t n p f hadm ht hF hm)
  have cS := c.descend (MulEquiv.refl (Y ⧸ Subgroup.center Y))
  haveI : Group.IsPerfect Y := ⟨c.quasisimple.1⟩
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  have hinj : Function.Injective
      (MulAut.conj : (Y ⧸ Subgroup.center Y) →* MulAut (Y ⧸ Subgroup.center Y)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
      rw [Subgroup.mem_center_iff]
      intro h'
      have := congrArg (fun a : MulAut (Y ⧸ Subgroup.center Y) => a h') hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hcen] at this
    exact this
  refine s1431_false_of_inner_noField hinj cS hq ?_ (R := hR _ t n p f hadm ht hF hm)
  rintro _ ⟨a', ha', rfl⟩
  exact CFSG.HardMathSupport.Dickson.Sec6.I1431.descendHom_isInnerAut (MulEquiv.refl _) (hin a' ha')

end CFSG.HardMathSupport.Dickson.Sec6.I1431
