module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711b
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)

@[expose] def ChevOuterFacts : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
    ∀ ψ : MulAut S, ψ ^ p = 1 → ψ ∉ (MulAut.conj : S →* MulAut S).range →
      ((∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
          Nonempty ((Y ⧸ Subgroup.center Y) ≃* S) → ¬ p ∣ Nat.card (Subgroup.center Y)) ∧
        5 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) ∨
      Group.IsSolvable ↥(fixSubgroup ψ)

section Elem

variable {X : Type} [Group X] [Finite X] {p : ℕ}

@[expose] noncomputable def prodHom {A C : Subgroup X} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : ↥A × ↥C →* X :=
  MonoidHom.noncommCoprod A.subtype C.subtype fun a c => hAC a a.2 c c.2

theorem prodHom_apply {A C : Subgroup X} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (x : ↥A × ↥C) :
    prodHom hAC x = (x.1 : X) * (x.2 : X) := rfl

theorem card_prodHom_range {A C : Subgroup X} (hA : IsElemAbelian p A) (hC : IsElemAbelian p C)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : ∀ x ∈ A, x ∈ C → x = 1) :
    IsElemAbelian p (prodHom hAC).range ∧
      Nat.card (prodHom hAC).range = Nat.card A * Nat.card C := by
  have hinj : Function.Injective (prodHom hAC) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, c⟩ h
    rw [prodHom_apply] at h
    have hac : (a : X) = (c : X)⁻¹ := eq_inv_of_mul_eq_one_left h
    have ha1 : (a : X) = 1 := hdisj _ a.2 (hac ▸ C.inv_mem c.2)
    have hc1 : (c : X) = 1 := by
      rw [ha1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hc1)
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    change (x : X) * y = y * x
    rw [← hu, ← hv, prodHom_apply, prodHom_apply]
    have h1 := Inputs27.elem_mul_comm hA u.1.2 v.1.2
    have h2 := Inputs27.elem_mul_comm hC u.2.2 v.2.2
    have h3 := hAC _ u.1.2 _ v.2.2
    have h4 := hAC _ v.1.2 _ u.2.2
    calc (u.1 : X) * u.2 * (v.1 * v.2) = (u.1 * v.1) * (u.2 * v.2) := by
          rw [mul_assoc, ← mul_assoc (u.2 : X), ← h4, mul_assoc, mul_assoc]
      _ = (v.1 * u.1) * (v.2 * u.2) := by rw [h1, h2]
      _ = (v.1 : X) * v.2 * (u.1 * u.2) := by
          rw [mul_assoc, ← mul_assoc (u.1 : X), h3, mul_assoc, mul_assoc]
  · obtain ⟨u, rfl⟩ := hz
    rw [prodHom_apply]
    have h4 := hAC _ u.1.2 _ u.2.2
    have hc : Commute (u.1 : X) u.2 := h4
    rw [hc.mul_pow, hA.2 _ u.1.2, hC.2 _ u.2.2, one_mul]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, Nat.card_prod]

end Elem

section Reduction

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem mk_mem_fixSubgroup {L : Subgroup X} {e : X} (heN : e ∈ Subgroup.normalizer (L : Set X)) {x : X}
    (hxL : x ∈ L) (hxe : x ∈ Subgroup.centralizer ({e} : Set X)) :
    (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈
      fixSubgroup (centerQuotientHom ↥L (L.normalizerMonoidHom ⟨e, heN⟩)) := by
  rw [mem_fixSubgroup]
  have h1 := onCenterQuotient_apply_mk (L.normalizerMonoidHom ⟨e, heN⟩) ⟨x, hxL⟩
  refine h1.trans ?_
  change QuotientGroup.mk' (Subgroup.center ↥L) _ = QuotientGroup.mk' (Subgroup.center ↥L) ⟨x, hxL⟩
  congr 1
  apply Subtype.ext
  change e * x * e⁻¹ = x
  rw [Subgroup.mem_centralizer_singleton_iff] at hxe
  rw [hxe.symm, mul_assoc, mul_inv_cancel, mul_one]

theorem isSolvable_inf_centralizer {L : Subgroup X} {e : X}
    (heN : e ∈ Subgroup.normalizer (L : Set X))
    (hsol : Group.IsSolvable ↥(fixSubgroup (centerQuotientHom ↥L (L.normalizerMonoidHom ⟨e, heN⟩)))) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({e} : Set X)) := by
  set F := fixSubgroup (centerQuotientHom ↥L (L.normalizerMonoidHom ⟨e, heN⟩)) with hF
  let g₀ : ↥(L ⊓ Subgroup.centralizer ({e} : Set X)) →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.centralizer ({e} : Set X) ≤ L))
  have hg₀ : ∀ x, g₀ x ∈ F := fun x =>
    mk_mem_fixSubgroup heN (Subgroup.mem_inf.1 x.2).1 (Subgroup.mem_inf.1 x.2).2
  let g : ↥(L ⊓ Subgroup.centralizer ({e} : Set X)) →* ↥F := g₀.codRestrict F hg₀
  haveI : IsMulCommutative ↥g.ker := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : g₀ a.1 = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 a.2)
    have ha' : (⟨(a.1 : X), (Subgroup.mem_inf.1 a.1.2).1⟩ : ↥L) ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff _).1 ha
    have hab := Subgroup.mem_center_iff.1 ha' ⟨(b.1 : X), (Subgroup.mem_inf.1 b.1.2).1⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Subtype.val hab).symm
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem not_glaPComponent_of_solvable {Y I : Subgroup X} (hY : Group.IsSolvable ↥Y)
    (hI : GLAPComponent p Y I) : False := by
  have hIY : I ≤ Y := hI.1
  haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hI)
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIY)
      (Subgroup.inclusion_injective hIY)
  haveI : Nontrivial ↥I :=
    (Subgroup.nontrivial_iff_ne_bot I).2 (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI)
  exact Group.IsPerfect.not_isSolvable (G := ↥I) inferInstance

theorem inputI2711ChevPOuter_of_facts (hF : ChevOuterFacts) : Inputs2711.InputI2711ChevPOuter := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hLie J0 hJ0 hJt hJ5 E hEB hEC hEi
    hEl hE2 hlE hle hout hEcard
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  have heN : e ∈ Subgroup.normalizer (L : Set X) := hBN (hEB he)
  have hep : e ^ p = 1 := hB.2 e (hEB he)
  set ψ := centerQuotientHom ↥L (L.normalizerMonoidHom ⟨e, heN⟩) with hψ
  have hψp : ψ ^ p = 1 := by
    rw [hψ, ← map_pow, Inputs2711.normalizerMonoidHom_pow_eq_one heN hep, map_one]
  have hψo : ψ ∉ (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* MulAut (↥L ⧸ Subgroup.center ↥L)).range := by
    intro h
    obtain ⟨k, hk, hc⟩ := Inputs2711.exists_inner_of_quot hLq heN h
    exact heC (hout e he k hk hc)
  obtain ⟨idx, ⟨f⟩, hch⟩ := hLie
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.exists_noncomm_of_isQuasisimple hLq
  rcases hF (↥L ⧸ Subgroup.center ↥L) hLq.2 hnab idx ⟨f⟩ p hp hp2 hch ψ hψp hψo with ⟨hZ, h5⟩ | hsol
  ·
    have hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L) := hZ ↥L hLq ⟨MulEquiv.refl _⟩
    have hrk : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
      h5.trans (CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd hp hZL)
    obtain ⟨A₀, -, hA₀, hA₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥L)
    set A : Subgroup X := A₀.map L.subtype with hAdef
    have hA : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA₀ L.subtype
    have hAc : Nat.card A = p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
      rw [hAdef, Subgroup.card_map_of_injective L.subtype_injective, hA₀c]
    have hAL : A ≤ L := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    set B₀ := B ⊓ Subgroup.centralizer (L : Set X) with hB₀
    have hB₀el : IsElemAbelian p B₀ := CFSG.Open.IsElemAbelian.mono hB inf_le_left
    have hAC : ∀ a ∈ A, ∀ c ∈ B₀, a * c = c * a := fun a ha c hc =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a (hAL ha))
    have hdisj : ∀ x ∈ A, x ∈ B₀ → x = 1 := by
      intro x hxA hxB
      have hxZ : (⟨x, hAL hxA⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxB).2 y y.2
      have hxp : (⟨⟨x, hAL hxA⟩, hxZ⟩ : ↥(Subgroup.center ↥L)) ^ p = 1 :=
        Subtype.ext (Subtype.ext (hA.2 x hxA))
      have hord : orderOf (⟨⟨x, hAL hxA⟩, hxZ⟩ : ↥(Subgroup.center ↥L)) = 1 := by
        rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
        · exact h
        · exfalso
          apply hZL
          rw [← h]
          exact orderOf_dvd_natCard _
      have := orderOf_eq_one_iff.1 hord
      exact congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : X)) this
    obtain ⟨hPel, hPc⟩ := card_prodHom_range hA hB₀el hAC hdisj
    have hPle : (prodHom hAC).range ≤ B ⊔ L := by
      rintro _ ⟨x, rfl⟩
      rw [prodHom_apply]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAL x.1.2))
        (Subgroup.mem_sup_left (Subgroup.mem_inf.1 x.2.2).1)
    have h1 := hmax _ hPle hPel
    rw [hPc] at h1
    have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
    have h2 : Nat.card A * Nat.card B₀ ≤ p ^ 4 * Nat.card B₀ := by
      calc Nat.card A * Nat.card B₀ ≤ Nat.card B := h1
        _ ≤ p ^ 2 * Nat.card E := hEi
        _ ≤ p ^ 2 * (p ^ 2 * Nat.card B₀) := Nat.mul_le_mul_left _ hEcard
        _ = p ^ 4 * Nat.card B₀ := by ring
    have h3 : Nat.card A ≤ p ^ 4 := Nat.le_of_mul_le_mul_right h2 hB₀pos
    rw [hAc] at h3
    have h4 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
    omega
  ·
    have hsolL := isSolvable_inf_centralizer heN hsol
    obtain ⟨I, hI⟩ := Inputs2711.exists_glaPComponent_of_ne_bot (hle e he)
    exact not_glaPComponent_of_solvable hsolL hI

end Reduction

section Field

@[expose] def fieldDeg : TauCeti.LieTypeIndex → ℕ
  | .A _ q => q.exponent
  | .twistedA _ q => q.exponent
  | .B _ q => q.exponent
  | .C _ q => q.exponent
  | .D _ q => q.exponent
  | .twistedD _ q => q.exponent
  | .E6 q => q.exponent
  | .E7 q => q.exponent
  | .E8 q => q.exponent
  | .F4 q => q.exponent
  | .G2 q => q.exponent
  | .twistedE6 q => q.exponent
  | .trialityD4 q => q.exponent
  | .suzuki m => 2 * m + 1
  | .reeG2 m => 2 * m + 1
  | .reeF4 m => 2 * m + 1
  | .tits => 1

@[expose] def IsTrialityType : TauCeti.LieTypeIndex → Prop
  | .D r _ => r = 4
  | .trialityD4 _ => True
  | _ => False

@[expose] def FieldCond (d : TauCeti.LieTypeIndex) (p : ℕ) : Prop :=
  p ∣ fieldDeg d ∨ (p = 3 ∧ IsTrialityType d)

@[expose] def IsLTwo27 (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.card = 27

end Field

section Multiplier

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (center_dvd_table lieModel_typeA lieModel_lie
  lieModel_of_classical)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (case_of_dvd_table isQuasisimple_of_open')

theorem not_dvd_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f - 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 h
  have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rw [Nat.sub_sub_self hpos] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem not_dvd_pow_add_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f + 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 h
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem not_dvd_table_of_char {t : CFSG.Open.StatedLieTag} {n f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f)
    (hexc : p = 3 → ¬ ((t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1))) :
    ¬ p ∣ (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  intro h
  rcases case_of_dvd_table hp hp2 h with ⟨-, hg⟩ | ⟨-, hg⟩ | ⟨⟨-, hp3, hd⟩ | ⟨-, hp3, hd⟩⟩ |
      ⟨hp3, hx⟩
  · exact not_dvd_pow_sub_one hp hf (hg.trans (Nat.gcd_dvd_right _ _))
  · exact not_dvd_pow_add_one hp hf (hg.trans (Nat.gcd_dvd_right _ _))
  · subst hp3; exact not_dvd_pow_sub_one Nat.prime_three hf hd
  · subst hp3; exact not_dvd_pow_add_one Nat.prime_three hf hd
  · apply hexc hp3
    rcases hx with ⟨h1, h2, -, h4⟩ | ⟨h1, h2, -, h4⟩ | ⟨h1, h2, -, h4⟩ | ⟨h1, h2, -, h4⟩
    · exact Or.inl ⟨h1, h2, h4⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h4⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h4⟩))

theorem three_not_dvd_of_le_two {f : ℕ} (h : 3 ∣ f) (h1 : 1 ≤ f) (h2 : f ≤ 2) : False := by
  have := Nat.le_of_dvd (by omega) h
  omega

theorem not_dvd_center_of_fieldCond (hGA : CFSG.Open.GriessAllModelsStatement)
    {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hch : idx.1.characteristic = p) (hF : FieldCond idx.1 p) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ¬ p ∣ Nat.card (Subgroup.center Y) := by
  intro hdvd
  have hq' := isQuasisimple_of_open' hq
  obtain ⟨d, hv⟩ := idx
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_A] at hch
    subst hch
    have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_typeA r q hv)))
    rintro hp3 (⟨-, -, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · rw [hp3] at hf; exact three_not_dvd_of_le_two hf (by omega) (by omega)
    all_goals exact absurd h (by decide)
  | twistedA r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hch
    subst hch
    have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)))))
    rintro hp3 (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h2⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [hp3] at hf; exact three_not_dvd_of_le_two hf (by omega) (by omega)
  | B r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_B] at hch
    subst hch
    have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
        (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
          (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)))))
      rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
    · refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
        (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3
            (MulEquiv.refl _)))))
      rintro hp3 (⟨h, -⟩ | ⟨-, -, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h (by decide)
      · rw [hp3] at hf; exact three_not_dvd_of_le_two hf (by omega) (by omega)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  | C r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_C] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _)))))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | D r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_D] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)))))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | twistedD r q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_of_classical
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
          (MulEquiv.refl _)))))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | E6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E6] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .E6)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | E7 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E7] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .E7)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | E8 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E8] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .E8)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | F4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_F4] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .F4)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | G2 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_G2] at hch
    subst hch
    have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [TauCeti.PrimePower.card_def] using hrange
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .G2)
        ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro hp3 (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h2⟩ | ⟨h, -⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [hp3] at hf; exact three_not_dvd_of_le_two hf (by omega) (by omega)
    · exact absurd h (by decide)
  | twistedE6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .twistedE6)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | trialityD4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at hch
    subst hch
    refine not_dvd_table_of_char hp hp2 q.exponent_pos ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .trialityD4)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | suzuki m => exact hp2 (by simpa using hch.symm)
  | reeG2 m =>
    simp only [TauCeti.LieTypeIndex.characteristic_reeG2] at hch
    subst hch
    have hm1 : 1 ≤ m := hrange
    refine not_dvd_table_of_char hp hp2 (show 1 ≤ 2 * m + 1 by omega) ?_
      (hdvd.trans (center_dvd_table hGA hq' e (lieModel_lie (t := .twistedG2) (p := 3)
        (f := 2 * m + 1) ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
        ⟨rfl, rfl⟩)))
    rintro - (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
  | reeF4 m => exact hp2 (by simpa using hch.symm)
  | tits => exact hp2 (by simpa using hch.symm)

end Multiplier

section Families

open CFSG.HardMathSupport.Timmesfeld.DefChar (DefCharFamily exists_family_of_characteristic_ne_two)

@[expose] def ChevOuterFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
    ∀ ψ : MulAut S, ψ ^ p = 1 → ψ ∉ (MulAut.conj : S →* MulAut S).range →
      ((∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
          Nonempty ((Y ⧸ Subgroup.center Y) ≃* S) → ¬ p ∣ Nat.card (Subgroup.center Y)) ∧
        5 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) ∨
      Group.IsSolvable ↥(fixSubgroup ψ)

theorem chevOuterFacts_of_families (h : ∀ k, ChevOuterFam k) : ChevOuterFacts := by
  intro S _ _ hS hnab idx he p hp hp2 hch ψ hψp hψo
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 (by rw [hch]; exact hp2)
  exact h k S hS hnab idx hk he p hp hp2 hch ψ hψp hψo

@[expose] def LieOuterFieldFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
    ∀ ψ : MulAut S, ψ ^ p = 1 → ψ ∉ (MulAut.conj : S →* MulAut S).range → FieldCond idx.1 p

@[expose] def LieRankFiveFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p → FieldCond idx.1 p → ¬ IsLTwo27 idx.1 →
      5 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)

@[expose] def L227Fact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ∀ idx : TauCeti.ValidLieTypeIndex, IsLTwo27 idx.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → ∀ ψ : MulAut S, ψ ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup ψ)

theorem chevOuterFam_of (hGA : CFSG.Open.GriessAllModelsStatement) (hL : L227Fact)
    {k : DefCharFamily} (h1 : LieOuterFieldFam k) (h3 : LieRankFiveFam k) : ChevOuterFam k := by
  intro S _ _ hS hnab idx hk he p hp hp2 hch ψ hψp hψo
  have hF := h1 S hS hnab idx hk he p hp hp2 hch ψ hψp hψo
  by_cases h27 : IsLTwo27 idx.1
  · right
    exact hL S idx h27 he ψ (fun h => hψo ⟨1, by rw [map_one, h]⟩)
  · left
    refine ⟨fun Y _ _ hq hY => ?_, h3 S idx hk he p hp hp2 hch hF h27⟩
    obtain ⟨eY⟩ := hY
    exact not_dvd_center_of_fieldCond hGA hp hp2 hch hF hq (eY.trans he.some)

end Families

section Tools

theorem congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply]

theorem congr_not_inner {G H : Type*} [Group G] [Group H] (e : G ≃* H) {ψ : MulAut G}
    (hψ : ψ ∉ (MulAut.conj : G →* MulAut G).range) :
    MulAut.congr e ψ ∉ (MulAut.conj : H →* MulAut H).range := by
  rintro ⟨a, ha⟩
  apply hψ
  refine ⟨e.symm a, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, e.apply_symm_apply]
  exact ha

theorem congr_pow_eq_one {G H : Type*} [Group G] [Group H] (e : G ≃* H) {ψ : MulAut G} {p : ℕ}
    (hψ : ψ ^ p = 1) : MulAut.congr e ψ ^ p = 1 := by
  rw [← map_pow, hψ, map_one]

theorem dvd_of_orderOf_ringAut {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) {σ : RingAut K} (hσ : orderOf σ = p) : p ∣ f := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK).1
  rw [← h, ← hσ]
  exact orderOf_dvd_natCard σ

theorem five_le_of_fieldCond_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : p ∣ f) (hf1 : 1 ≤ f)
    (h3 : ¬ (p = 3 ∧ f = 3)) : 5 ≤ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpf : p ≤ f := Nat.le_of_dvd (by omega) hf
  by_contra hlt
  have hf34 : f = 3 ∨ f = 4 := by omega
  rcases hf34 with rfl | rfl
  · have : p = 3 := by omega
    exact h3 ⟨this, rfl⟩
  · have : p = 3 ∨ p = 4 := by omega
    rcases this with rfl | rfl
    · omega
    · exact absurd hp (by norm_num)

theorem three_le_of_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : p ∣ f) (hf1 : 1 ≤ f) : 3 ≤ f := by
  have := hp.two_le
  have := Nat.le_of_dvd (by omega) hf
  omega

end Tools

section FamilyA

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (relIndex_inner_linearAutGroup_dvd)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Timmesfeld.DefChar (DefCharFamily)

theorem dvd_of_outer_projectiveSL {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {β : MulAut (projectiveSL n K)} (hβ : β ^ p = 1)
    (hout : β ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) : p ∣ f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : β ∈ semilinearAutGroup n K := by
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβ) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  by_cases hD : β ∈ linearAutGroup n K
  · exfalso
    apply hout
    set Dl := linearAutGroup n K with hDl
    have hIN : (inner (projectiveSL n K)).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hIl : (inner (projectiveSL n K)).relIndex Dl ∣ Nat.gcd n (Nat.card K - 1) :=
      relIndex_inner_linearAutGroup_dvd (by omega)
    have hmq : (inner (projectiveSL n K)).relIndex Dl ∣ Nat.card K - 1 :=
      hIl.trans (Nat.gcd_dvd_right _ _)
    have hpq : ¬ p ∣ Nat.card K - 1 := by rw [hK]; exact not_dvd_pow_sub_one hp hf
    have hcop : Nat.Coprime p ((inner (projectiveSL n K)).relIndex Dl) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpq (h.trans hmq)
    have : ((inner (projectiveSL n K)).subgroupOf Dl).Normal := hIN.subgroupOf Dl
    set y : Dl ⧸ (inner (projectiveSL n K)).subgroupOf Dl := QuotientGroup.mk ⟨β, hD⟩ with hy
    have hyp : y ^ p = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨β, hD⟩ : Dl) ^ p = 1 := Subtype.ext hβ
      rw [this]; rfl
    have hcardQ : Nat.card (Dl ⧸ (inner (projectiveSL n K)).subgroupOf Dl) =
        (inner (projectiveSL n K)).relIndex Dl := by
      rw [← Subgroup.index_eq_card]; rfl
    have hyd : orderOf y ∣ (inner (projectiveSL n K)).relIndex Dl := by
      rw [← hcardQ]; exact orderOf_dvd_natCard y
    have hyo : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.symm hcop |>.symm) hyo hyd
    have hy1 : y = 1 := orderOf_eq_one_iff.1 h1
    rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
    exact hy1
  · have hne : β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have hord : orderOf β = p := orderOf_eq_prime hβ hne
    exact (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hp hf hn hK hp β hE hD hord).1

theorem dvd_of_outer_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hK3 : 3 < Nat.card K)
    {β : MulAut (CFSG.GorensteinWalter.PSL2 K)} (hβ : β ^ p = 1)
    (hout : β ∉ (MulAut.conj : CFSG.GorensteinWalter.PSL2 K →* MulAut _).range) : p ∣ f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  have hinj := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective K hodd hK3
  have hsurj := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective K hK hodd hK3
  let Ψe : CFSG.GorensteinWalter.PGammaL2 K ≃* MulAut (CFSG.GorensteinWalter.PSL2 K) :=
    MulEquiv.ofBijective (CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 K hodd hK3) ⟨hinj, hsurj⟩
  set x := Ψe.symm β with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hβ, map_one]
  set σ : K ≃+* K := SemidirectProduct.rightHom x with hσ
  by_cases hσ1 : σ = 1
  · exfalso
    apply hout
    have hxk : x ∈ (SemidirectProduct.rightHom :
        CFSG.GorensteinWalter.PGammaL2 K →* (K ≃+* K)).ker := hσ1
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hxk
    obtain ⟨g, hg⟩ := hxk
    have hgp : g ^ p = 1 := by
      have h1 : (SemidirectProduct.inl (g ^ p) : CFSG.GorensteinWalter.PGammaL2 K) =
          SemidirectProduct.inl 1 := by
        rw [map_pow, hg, hxp, map_one]
      exact SemidirectProduct.inl_injective h1
    obtain ⟨y, hy⟩ := CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd (hp.odd_of_ne_two hp2) hgp
    refine ⟨y, ?_⟩
    have hβx : β = Ψe x := by rw [hx, MulEquiv.apply_symm_apply]
    rw [hβx, ← hg]
    change MulAut.conj y = CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2 K hodd hK3 (SemidirectProduct.inl g)
    rw [CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_inl, ← hy,
      CFSG.GorensteinWalter.pgl2InnerAutPSL2_toPGL]
  · have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hxp, map_one]
    have hord : orderOf σ = p := orderOf_eq_prime hσp hσ1
    exact dvd_of_orderOf_ringAut hp hK hord

theorem lieOuterFieldFamA : LieOuterFieldFam .A := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_A] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  left
  change q.p ∣ q.exponent
  obtain ⟨e0⟩ := hS
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · obtain rfl : r = 1 := by have := hr.1; omega
    have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
    obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
    let e : S ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q.p q.exponent) := e0.trans e1
    have h4 : 4 ≤ q.p ^ q.exponent := by simpa [TauCeti.PrimePower.card_def] using hr.2 rfl
    exact dvd_of_outer_psl2 hp hp2 q.exponent_pos hKq (by rw [hKq]; omega)
      (congr_pow_eq_one e hψp) (congr_not_inner e hψo)
  · let e : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      e0.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
    exact dvd_of_outer_projectiveSL (by omega) hp hp2 q.exponent_pos hKq
      (congr_pow_eq_one e hψp) (congr_not_inner e hψo)

theorem lieRankFiveFamA : LieRankFiveFam .A := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_A] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  obtain ⟨e0⟩ := hS
  have hmod := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r q hv).2.resolve_right
    (fun h => by omega)
  obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ := hmod
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (e0.trans e1)]
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by have := hr.1; omega) with rfl | rfl | hr3
  · have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 2) (a := 1) (b := 1) le_rfl le_rfl hK
    have h5 : 5 ≤ q.exponent := by
      refine five_le_of_fieldCond_one hp hp2 hf q.exponent_pos ?_
      rintro ⟨hp3, hf3⟩
      exact h27 ⟨q, rfl, by rw [TauCeti.PrimePower.card_def, hp3, hf3]; norm_num⟩
    simp only [mul_one] at h
    omega
  · have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 3) (a := 1) (b := 2) le_rfl le_rfl hK
    omega
  · have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := r + 1) (a := 2) (b := 2) (by norm_num)
      (by omega) hK
    omega

end FamilyA

section L227

theorem fixSubgroup_congr_le {G H : Type*} [Group G] [Group H] (e : G ≃* H) (ψ : MulAut G) {x : G}
    (hx : x ∈ fixSubgroup ψ) : e x ∈ fixSubgroup (MulAut.congr e ψ) := by
  rw [mem_fixSubgroup] at hx ⊢
  simp [MulAut.congr_apply, hx]

theorem isSolvable_fixSubgroup_of_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (ψ : MulAut G)
    (h : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e ψ))) : Group.IsSolvable ↥(fixSubgroup ψ) := by
  let f : ↥(fixSubgroup ψ) →* ↥(fixSubgroup (MulAut.congr e ψ)) :=
    { toFun := fun x => ⟨e (x : G), fixSubgroup_congr_le e ψ x.2⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) (y : G)) }
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
  exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

theorem isSolvable_of_ne_top_psl2_27
    (H : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 3 3)))
    (hH : H ≠ ⊤) : Group.IsSolvable ↥H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hE | ⟨z, -, -, hcyc⟩ | ⟨z, hz, -, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨h16, -⟩ | ⟨h5, -⟩ |
    ⟨m, t, -, -, N, C, hNn, hNe, -, hC, -, -, hsup⟩ | ⟨m, hm0, hm3, hP⟩ | ⟨m, hm0, hm3, -⟩
  · haveI := hE
    infer_instance
  · haveI := hcyc
    letI : CommGroup ↥H := IsCyclic.commGroup
    infer_instance
  · rw [hK] at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    haveI : NeZero z := ⟨hz0⟩
    haveI := CFSG.Walter.isSolvable_dihedralGroup' z
    exact Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective
  · haveI : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact Group.isSolvable_of_isSolvable_injective (f := eA.toMonoidHom) eA.injective
  · norm_num at h16
  · norm_num at h5
  · haveI := hNn
    haveI : IsMulCommutative ↥N := hNe.toIsMulCommutative
    haveI : IsMulCommutative ↥C := by
      haveI := hC
      letI : CommGroup ↥C := IsCyclic.commGroup
      infer_instance
    exact CFSG.Walter.isSolvable_of_sup_eq_top (N := N) (C := C) inferInstance inferInstance hsup
  · have hm : m = 1 ∨ m = 3 := by
      have := Nat.le_of_dvd (by norm_num) hm3
      interval_cases m
      · exact absurd rfl hm0
      · exact Or.inl rfl
      · norm_num at hm3
      · exact Or.inr rfl
    obtain ⟨eP⟩ := hP
    rcases hm with rfl | rfl
    ·
      have h3 : Nat.card (GaloisField 3 1) = 3 := by
        rw [GaloisField.card 3 1 (by norm_num)]; norm_num
      have hc := CFSG.Semidihedral.AllPrime.SL2Sections.card_psl2_mul_two (F := GaloisField 3 1)
        (by rw [h3]; decide)
      rw [h3] at hc
      have h12 : Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 3 1)) = 12 := by
        omega
      have hH12 : Nat.card ↥H = 2 ^ 2 * 3 ^ 1 := by
        rw [Nat.card_congr eP.toEquiv, h12]; norm_num
      haveI : Fintype ↥H := Fintype.ofFinite _
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hH12)
    · exfalso
      apply hH
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_congr eP.toEquiv]
  · exfalso
    have := Nat.le_of_dvd (by norm_num) hm3
    have : m = 1 := by omega
    subst this
    norm_num at hm3

theorem l227Fact_holds : L227Fact := by
  intro S _ _ idx h27 hS ψ hψ
  obtain ⟨q, hq, hq27⟩ := h27
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨qp, qe, hqp, hqe⟩ := q
  have h27' : qp ^ qe = 3 ^ 3 := by simpa [TauCeti.PrimePower.card_def] using hq27
  have hqp3 : qp = 3 := by
    have h1 : qp ∣ 3 ^ 3 := by rw [← h27']; exact dvd_pow_self qp (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1 (hqp.dvd_of_dvd_pow h1)
  subst hqp3
  have hqe3 : qe = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h27'
  subst hqe3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex 3 3 ⟨.A 1 ⟨3, 3, hqp, hqe⟩, hv⟩ :=
    ⟨⟨3, 3, hqp, hqe⟩, rfl, rfl, rfl⟩
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  obtain ⟨e0⟩ := hS
  let e : S ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 3 3) := e0.trans e1
  refine isSolvable_fixSubgroup_of_congr e ψ (isSolvable_of_ne_top_psl2_27 _ ?_)
  intro htop
  apply hψ
  ext x
  have hx : e x ∈ fixSubgroup (MulAut.congr e ψ) := htop ▸ Subgroup.mem_top _
  rw [mem_fixSubgroup] at hx
  have hx' : e (ψ x) = e x := by
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hx
  exact e.injective hx'

end L227

section FamilyTwistedA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem dvd_of_dvd_two_mul {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 * f) : p ∣ f :=
  ((Nat.Prime.dvd_mul hp).1 h).resolve_left fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem lieOuterFieldFamTwistedA : LieOuterFieldFam .twistedA := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  left
  change q.p ∣ q.exponent
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hg : ¬ q.p ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := fun hd =>
    not_dvd_pow_add_one hℓ hf (hd.trans (Nat.gcd_dvd_right _ _))
  set β := MulAut.congr e' ψ with hβdef
  have hβ : β ^ q.p = 1 := congr_pow_eq_one e' hψp
  have hβo : β ∉ (MulAut.conj : primeFormP h (idGram K (r + 1)) →* _).range := congr_not_inner e' hψo
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) K) := isPrimeFormGram_idGram
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' β = 1
  · exfalso
    have hβD : β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD] at hβD
    exact hβo (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn3 hq' hℓ hg hβD hβ)
  · have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' β) = q.p :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := h.card
    exact dvd_of_dvd_two_mul hℓ hp2 (dvd_of_orderOf_ringAut hℓ hK2 hσp)

theorem lieRankFiveFamTwistedA : LieRankFiveFam .twistedA := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨hℓ, -, hn3, -⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eT]
  rcases (show r = 2 ∨ 4 ≤ r + 1 by omega) with rfl | h4
  · have := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three hp2 hK
    omega
  · have := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_SU hp2 h4 hK
    omega

end FamilyTwistedA

section FamilySymplectic

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Open (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem dvd_of_outer_sp {r : ℕ} {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSp r K))} (hβ : β ^ p = 1)
    (hout : β ∉ (MulAut.conj : StatedProj (StatedSp r K) →* _).range) : p ∣ f := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf β) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r K
  · exfalso
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two
      hrel hp hp2 hD hβ
    exact hout ⟨t, ht⟩
  · have hne1 : β ≠ 1 := fun h => hD (h ▸ one_mem _)
    exact (hO.descent p hp β hE hD (orderOf_eq_prime hβ hne1)).1

end FamilySymplectic

section FamilyOrthogonal

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

theorem mem_E_of_pow_eq_one_omega' (hg : OrthogonalGates Q f) (hp : p.Prime)
    (h : 3 < p ∨ projectivePointFamilyAut Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)}
    (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
  rcases h with hp3 | htop
  · have hpg : IsPGroup p (Subgroup.zpowers β) := by
      intro g
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hβp, one_zpow]
      rfl
    have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ hpg
    have h1 : β ∈ projectivePointFamilyAut Q := hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β))
    rw [hg.2.2.2.2.2.1] at h1
    exact h1
  · have h1 : β ∈ projectivePointFamilyAut Q := htop ▸ Subgroup.mem_top β
    rwa [hg.2.2.2.2.2.1] at h1

theorem mem_inner_of_mem_D_omega' (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ p = 1) : ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  exact mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hβD hβp

theorem dvd_of_gates_outer {G : Type} [Group G] (e : G ≃* matrixProjectiveDerived Q)
    (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2) (β : MulAut G) (hβ : β ^ p = 1)
    (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = p → p ∣ f) : p ∣ f := by
  have hβ' : MulAut.congr e β ^ p = 1 := congr_pow_eq_one e hβ
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · exfalso
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega' hg hp hp2 hD hβ'
    exact congr_not_inner e hout ⟨t, ht⟩
  · have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
    haveI : Fact p.Prime := ⟨hp⟩
    exact hdesc _ hE hD (orderOf_eq_prime hβ' hne1)

end Gates

theorem dvd_of_outer_omegaOdd {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut G} (hβ : β ^ p = 1) (hout : β ∉ (MulAut.conj : G →* MulAut G).range) : p ∣ f := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n ℓ f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) n ℓ f hG) K hK).2
  refine dvd_of_gates_outer (coordinateOddWitnessEquiv K e) hgates hp hp2 β hβ
    (mem_E_of_pow_eq_one_omega' hgates hp (Or.inr htop) (congr_pow_eq_one _ hβ)) hout ?_
  intro a haE haD hap
  exact (orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f p hG hp hp2 K hK e a haE haD hap).1

theorem dvd_of_outer_omegaPlus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD4 : n = 4 → p ≠ 3) {β : MulAut G} (hβ : β ^ p = 1)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range) : p ∣ f := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  have hEA : 3 < p ∨ projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · left
      have := hD4 h4
      have := hp.two_le
      omega
    · right
      exact (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 h5
  refine dvd_of_gates_outer (coordinatePlusWitnessEquiv K e) hgates hp hp2 β hβ
    (mem_E_of_pow_eq_one_omega' hgates hp hEA (congr_pow_eq_one _ hβ)) hout ?_
  intro a haE haD hap
  exact (orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hG hp hp2 K hK e a haE haD hap).1

theorem dvd_of_outer_omegaMinus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut G} (hβ : β ^ p = 1) (hout : β ∉ (MulAut.conj : G →* MulAut G).range) : p ∣ f := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n ℓ f hG)
      hn1 K hK b c hirr).2
  refine dvd_of_gates_outer (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2 β hβ
    (mem_E_of_pow_eq_one_omega' hgates hp (Or.inr htop) (congr_pow_eq_one _ hβ)) hout ?_
  intro a haE haD hap
  exact (orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hG hp hp2 hn1 K hK b c hirr e a haE haD hap).1

end FamilyOrthogonal

section FamilyBCD

open CFSG.HardMathSupport.Timmesfeld.DefChar (DefCharFamily)

theorem lieOuterFieldFamB : LieOuterFieldFam .B := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_B] at hch
  subst hch
  left
  change q.p ∣ q.exponent
  obtain ⟨e0⟩ := hS
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases (show r = 2 ∨ 3 ≤ r by have := hr.1; omega) with rfl | hr3
  · obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨e1⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
    exact dvd_of_outer_sp hℓ hf le_rfl hK hp hp2 (congr_pow_eq_one e1 hψp) (congr_not_inner e1 hψo)
  · exact dvd_of_outer_omegaOdd
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e0) hp hp2 hψp hψo

theorem lieRankFiveFamB : LieRankFiveFam .B := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_B] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases (show r = 2 ∨ 3 ≤ r by have := hr.1; omega) with rfl | hr3
  · obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
    have := CFSG.SectionRank.ClassicalOdd.le_pRank_Sp (n := 2) le_rfl hK
    omega
  · obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e0
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
    have := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_omegaOdd hr3 hp2 hK
    omega

theorem lieOuterFieldFamC : LieOuterFieldFam .C := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_C] at hch
  subst hch
  left
  change q.p ∣ q.exponent
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨hℓ, hf, hn2, -⟩, K, _, _, hK, ⟨e1⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e0
  exact dvd_of_outer_sp hℓ hf hn2 hK hp hp2 (congr_pow_eq_one e1 hψp) (congr_not_inner e1 hψo)

theorem lieRankFiveFamC : LieRankFiveFam .C := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_C] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨-, -, hn2, -⟩, K, _, _, hK, ⟨e1⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e0
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
  have := CFSG.SectionRank.ClassicalOdd.le_pRank_Sp hn2 hK
  nlinarith

theorem lieOuterFieldFamD : LieOuterFieldFam .D := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_D] at hch
  subst hch
  by_cases h43 : r = 4 ∧ q.p = 3
  · exact Or.inr ⟨h43.2, h43.1⟩
  · left
    change q.p ∣ q.exponent
    obtain ⟨e0⟩ := hS
    exact dvd_of_outer_omegaPlus
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e0) hp hp2
      (fun h4 h3 => h43 ⟨h4, h3⟩) hψp hψo

@[expose] def D43RankFive : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus 4 K))))

theorem lieRankFiveFamD (hD43 : D43RankFive) : LieRankFiveFam .D := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_D] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, ⟨e1⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e0
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
  have h4 := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_omegaPlus hn4 hp2 hK
  rcases hF with hf | ⟨hp3, hr4⟩
  · change q.p ∣ q.exponent at hf
    have := three_le_of_dvd hp hp2 hf q.exponent_pos
    omega
  · change r = 4 at hr4
    subst hr4
    by_cases hf1 : q.exponent = 1
    · rw [hp3]
      rw [hp3, hf1, pow_one] at hK
      exact hD43 K hK
    · have := q.exponent_pos
      omega

theorem lieOuterFieldFamTwistedD : LieOuterFieldFam .twistedD := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at hch
  subst hch
  left
  change q.p ∣ q.exponent
  obtain ⟨e0⟩ := hS
  exact dvd_of_outer_omegaMinus
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e0) hp hp2 hψp hψo

theorem lieRankFiveFamTwistedD : LieRankFiveFam .twistedD := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨r, q, hrq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hrq
  subst hrq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, -, ⟨e1⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e0
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
  have := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_omegaMinus hn4 b c hp2 hK
  omega

end FamilyBCD

section FamilyUntwisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.HardMathSupport.Lang.E6Descent (G2_form_odd G2_form_three exists_conj_entrywise_of_not_innerDiag
  prime_dvd_of_diag_noninner)


theorem exists_adjoint_of_bridge {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c) (q : TauCeti.PrimePower) (hv : (c q).Valid)
    (hq2 : q.p ≠ 2) {S : Type} [Group S] (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
      Nonempty (S ≃* adjointGroup τ K) := by
  obtain ⟨K, _, _, hK, ⟨e1⟩⟩ := CFSG.TauCetiBridge.untwistedModel_of_bridge hbr q hv hq2 e
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e1.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)⟩⟩

theorem dvd_of_outer_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ ℓ = 1) (hα : α ∉ inner (adjointGroup τ K)) : ℓ ∣ f := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hαord : orderOf α = ℓ :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup τ K)).one_mem)
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  rcases hτ with rfl | rfl | hE
  · by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      obtain ⟨x, σ, hσp, -⟩ := G2_form_three hf K hK hℓ hℓ2 α hαord hα
      exact dvd_of_orderOf_ringAut hℓ hK hσp
    · obtain ⟨x, σ, hσp, -⟩ := G2_form_odd hℓ hℓ2 hℓ3 hf K hK hℓ α hαord hα
      exact dvd_of_orderOf_ringAut hℓ hK hσp
  · obtain ⟨x, σ, δ, hσp, -⟩ := odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hℓ α hαord hα
    exact dvd_of_orderOf_ringAut hℓ hK hσp
  · have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        α ≠ MulAut.conj g * rootDiagAut τ K a := by
      intro g a h
      have hdvd := (prime_dvd_of_diag_noninner τ (by rcases hE with h | h | h <;> simp [h]) K hℓ g a α h
        hαp hα).2
      rw [hK] at hdvd
      exact not_dvd_pow_sub_one hℓ hf hdvd
    obtain ⟨d, T, r, j, ψ, hfd, -⟩ :=
      exists_conj_entrywise_of_not_innerDiag τ (by rcases hE with h | h | h <;> simp [h]) hf K hK hℓ hℓ2
        α hαp hnd
    exact ⟨d, hfd⟩

theorem two_mul_le_pRank_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) :
    2 * f ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (adjointGroup τ K)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  rcases hτ with rfl | hτ'
  · exact RootWitness.le_pRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Untw.witnessG2_check hK
  · have := four_mul_le_pRank hτ' hK
    omega

theorem lieOuterFieldFam_of_bridge {k : CFSG.HardMathSupport.Timmesfeld.DefChar.DefCharFamily}
    {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c) (hk : ∀ d, k.Matches d → ∃ q, d = c q)
    (hc : ∀ q, (c q).characteristic = q.p ∧ fieldDeg (c q) = q.exponent) : LieOuterFieldFam k := by
  intro S _ _ _ _ idx hkm hS p hp hp2 hch ψ hψp hψo
  obtain ⟨q, hq⟩ := hk idx.1 hkm
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  rw [(hc q).1] at hch
  subst hch
  left
  rw [(hc q).2]
  obtain ⟨e0⟩ := hS
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := exists_adjoint_of_bridge hbr q hv hp2 e0
  exact dvd_of_outer_adjoint hτ hp hp2 q.exponent_pos K hK _ (congr_pow_eq_one θ hψp)
    (congr_not_inner θ hψo)

theorem lieRankFiveFam_of_bridge {k : CFSG.HardMathSupport.Timmesfeld.DefChar.DefCharFamily}
    {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c) (hk : ∀ d, k.Matches d → ∃ q, d = c q)
    (hc : ∀ q, (c q).characteristic = q.p ∧ fieldDeg (c q) = q.exponent ∧ ¬ IsTrialityType (c q)) :
    LieRankFiveFam k := by
  intro S _ _ idx hkm hS p hp hp2 hch hF h27
  obtain ⟨q, hq⟩ := hk idx.1 hkm
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  rw [(hc q).1] at hch
  subst hch
  have hf : q.p ∣ q.exponent := by
    have := hF.resolve_right fun h => (hc q).2.2 h.2
    rwa [(hc q).2.1] at this
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := exists_adjoint_of_bridge hbr q hv hp2 e0
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt θ]
  have := two_mul_le_pRank_adjoint hτ hp q.exponent_pos K hK
  omega

theorem lieOuterFieldFamG2 : LieOuterFieldFam .G2 :=
  lieOuterFieldFam_of_bridge (Or.inl rfl) CFSG.TauCetiBridge.untwistedBridge_G2
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_G2 q, rfl⟩)

theorem lieRankFiveFamG2 : LieRankFiveFam .G2 :=
  lieRankFiveFam_of_bridge (Or.inl rfl) CFSG.TauCetiBridge.untwistedBridge_G2
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_G2 q, rfl, id⟩)

theorem lieOuterFieldFamF4 : LieOuterFieldFam .F4 :=
  lieOuterFieldFam_of_bridge (Or.inr (Or.inl rfl)) CFSG.TauCetiBridge.untwistedBridge_F4
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_F4 q, rfl⟩)

theorem lieRankFiveFamF4 : LieRankFiveFam .F4 :=
  lieRankFiveFam_of_bridge (Or.inr (Or.inl rfl)) CFSG.TauCetiBridge.untwistedBridge_F4
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_F4 q, rfl, id⟩)

theorem lieOuterFieldFamE6 : LieOuterFieldFam .E6 :=
  lieOuterFieldFam_of_bridge (Or.inr (Or.inr (Or.inl rfl))) CFSG.TauCetiBridge.untwistedBridge_E6
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E6 q, rfl⟩)

theorem lieRankFiveFamE6 : LieRankFiveFam .E6 :=
  lieRankFiveFam_of_bridge (Or.inr (Or.inr (Or.inl rfl))) CFSG.TauCetiBridge.untwistedBridge_E6
    (fun _ h => h) (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E6 q, rfl, id⟩)

theorem lieOuterFieldFamE7 : LieOuterFieldFam .E7 :=
  lieOuterFieldFam_of_bridge (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    CFSG.TauCetiBridge.untwistedBridge_E7 (fun _ h => h)
    (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E7 q, rfl⟩)

theorem lieRankFiveFamE7 : LieRankFiveFam .E7 :=
  lieRankFiveFam_of_bridge (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    CFSG.TauCetiBridge.untwistedBridge_E7 (fun _ h => h)
    (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E7 q, rfl, id⟩)

theorem lieOuterFieldFamE8 : LieOuterFieldFam .E8 :=
  lieOuterFieldFam_of_bridge (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    CFSG.TauCetiBridge.untwistedBridge_E8 (fun _ h => h)
    (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E8 q, rfl⟩)

theorem lieRankFiveFamE8 : LieRankFiveFam .E8 :=
  lieRankFiveFam_of_bridge (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    CFSG.TauCetiBridge.untwistedBridge_E8 (fun _ h => h)
    (fun q => ⟨TauCeti.LieTypeIndex.characteristic_E8 q, rfl, id⟩)

end FamilyUntwisted

section SL2Rank

open scoped MatrixGroups

@[expose] def upperSL2Fun {F : Type} [Field F] (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_upperSL2Fun {F : Type} [Field F] (t : F) :
    ((upperSL2Fun t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

@[expose] def upperSL2 (F : Type) [Field F] : Multiplicative F →* SL(2, F) where
  toFun t := upperSL2Fun t.toAdd
  map_one' := by
    apply Subtype.ext
    rw [coe_upperSL2Fun, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2Fun, coe_upperSL2Fun, coe_upperSL2Fun]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperSL2_apply (F : Type) [Field F] (t : Multiplicative F) :
    upperSL2 F t = upperSL2Fun t.toAdd := rfl

@[expose] def lowerSL2 (F : Type) [Field F] : SL(2, F) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerSL2 (F : Type) [Field F] :
    ((lowerSL2 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl

theorem upperSL2_injective (F : Type) [Field F] : Function.Injective (upperSL2 F) := by
  intro s t h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [upperSL2_apply, coe_upperSL2Fun] at this
  simpa using this

theorem eq_one_of_commute_lowerSL2 {F : Type} [Field F] {t : Multiplicative F}
    (h : upperSL2 F t * lowerSL2 F = lowerSL2 F * upperSL2 F t) : t = 1 := by
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, upperSL2_apply, coe_upperSL2Fun,
    coe_lowerSL2] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  exact this

theorem multiplicative_pow_char {F : Type} [Field F] {p : ℕ} [CharP F p] (t : Multiplicative F) :
    t ^ p = 1 := by
  change Multiplicative.ofAdd (p • Multiplicative.toAdd t) = 1
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rfl

theorem le_pRank_of_sl2 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {p f : ℕ}
    [hp : Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f) (φ : SL(2, F) →* X)
    (hφ : Function.Injective φ) : f ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  refine CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b)
    multiplicative_pow_char ?_ (φ.comp (upperSL2 F)) (hφ.comp (upperSL2_injective F)) le_top
  rw [show Nat.card (Multiplicative F) = Nat.card F from Nat.card_congr Multiplicative.toAdd, hF]

theorem two_mul_le_pRank_of_commuting_sl2 {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f)
    (φ ψ : SL(2, F) →* X) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hc : ∀ A B, Commute (φ A) (ψ B)) : 2 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  let μ : Multiplicative F × Multiplicative F →* X :=
    MonoidHom.noncommCoprod (φ.comp (upperSL2 F)) (ψ.comp (upperSL2 F)) fun s t => hc _ _
  have hμ : ∀ x, μ x = φ (upperSL2 F x.1) * ψ (upperSL2 F x.2) := fun x => rfl
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, t⟩ h
    rw [hμ] at h
    have hst : φ (upperSL2 F s) = (ψ (upperSL2 F t))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hcomm : φ (upperSL2 F s * lowerSL2 F) = φ (lowerSL2 F * upperSL2 F s) := by
      rw [map_mul, map_mul, hst]
      exact ((hc (lowerSL2 F) (upperSL2 F t)).inv_right).eq.symm
    have hs : s = 1 := eq_one_of_commute_lowerSL2 (hφ hcomm)
    subst hs
    rw [map_one, map_one, one_mul] at h
    have ht : upperSL2 F t = upperSL2 F 1 := hψ (by rw [h, map_one, map_one])
    exact Prod.ext rfl (upperSL2_injective F ht)
  refine CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b)
    (fun a => Prod.ext (multiplicative_pow_char a.1) (multiplicative_pow_char a.2)) ?_ μ hinj le_top
  rw [Nat.card_prod, show Nat.card (Multiplicative F) = Nat.card F from
    Nat.card_congr Multiplicative.toAdd, hF, ← pow_add, two_mul]

end SL2Rank

section FamilyTwisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


theorem lieOuterFieldFamTwistedE6 : LieOuterFieldFam .twistedE6 := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨q, hq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at hch
  subst hch
  left
  change q.p ∣ q.exponent
  obtain ⟨e⟩ := hS
  have hchev : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 (by decide) e⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK2f : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hcard, ← pow_mul, mul_comm]
  have hβp : (MulAut.congr e' ψ) ^ q.p = 1 := congr_pow_eq_one e' hψp
  have hout' : MulAut.congr e' ψ ∉ twistedE6Inn K σ := congr_not_inner e' hψo
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hcard σ hσ
  have hpg : ¬ q.p ∣ Nat.gcd 3 (q.p ^ q.exponent + 1) := fun h =>
    not_dvd_pow_add_one hp hf (h.trans (Nat.gcd_dvd_right 3 _))
  have hη1 : Θ (MulAut.congr e' ψ) ≠ 1 := by
    intro h1
    have hmem : MulAut.congr e' ψ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout' (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag hp hcard hσ hpg
      hcube hβp hmem)
  obtain ⟨d, hd, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order
    hp hf K hK2f σ hσ Θ hΘ hp hp2 (MulAut.congr e' ψ) hβp hη1
  exact ⟨d, hd⟩

section RankTwistedE6

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.PartTwo.Census CFSG.TauCetiBridge TauCeti
open scoped MatrixGroups

theorem exists_commuting_injective_sl2_twistedE6_card
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q.p ^ q.exponent ∧
      ∃ φ ψ : SL(2, F) →* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩,
      Function.Injective φ ∧ Function.Injective ψ ∧ ∀ A B, Commute (φ A) (ψ B) := by
  let d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
  have hcardF : Nat.card d.1.fixedField = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    have h : (d.1 : ValidLieTypeIndex).fieldOrder = q.card := LieTypeIndex.fieldOrder_twistedE6 q
    rw [h, TauCeti.PrimePower.card_def]
  have hfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by
    rw [hcardF]
    exact (pow_pos q.prime_p.pos _).ne')
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i : Fin 4, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  refine ⟨d.1.fixedField, inferInstance, hfin, hcardF,
    (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 0),
    (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 1), hinj 0, hinj 1,
    fun A B => ?_⟩
  have h01 : Commute (te6SL2 (quadFrob d) (quadIncl d) hj 0 A)
      (te6SL2 (quadFrob d) (quadIncl d) hj 1 B) :=
    te6SL2_commute (quadFrob d) (quadIncl d) hj (i := 0) (i' := 1) (by decide) A B
  exact h01.map (toQuot (te6Embed d) hC)

theorem lieRankFiveFamTwistedE6 : LieRankFiveFam .twistedE6 := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨q, hq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.p ∣ q.exponent := hF.resolve_right fun h => h.2
  have h3 := three_le_of_dvd hp hp2 hf q.exponent_pos
  obtain ⟨e0⟩ := hS
  obtain ⟨F, _, _, hF', φ, ψ, hφ, hψ, hc⟩ := exists_commuting_injective_sl2_twistedE6_card q hv
  have : CharP F q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hF'
  have h2 := two_mul_le_pRank_of_commuting_sl2 (X := S) hF' (e0.symm.toMonoidHom.comp φ)
    (e0.symm.toMonoidHom.comp ψ) (e0.symm.injective.comp hφ) (e0.symm.injective.comp hψ)
    fun A B => (hc A B).map e0.symm.toMonoidHom
  omega

end RankTwistedE6

section RankTriality

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem twistedModel_of_trialityD4 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p ≠ 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    TwistedChevalleyModel S TwistTag.D4 (q.p ^ q.exponent) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK₀ : Nat.card (GaloisField q.p (3 * q.exponent)) = (q.p ^ q.exponent) ^ 3 := by
    rw [GaloisField.card q.p (3 * q.exponent) (by omega), ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : GaloisField q.p (3 * q.exponent),
      iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent c = c ^ q.p ^ q.exponent :=
    fun c => by rw [iterateFrobenius_def]
  have hqcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2
    (GaloisField q.p (3 * q.exponent)) (by rw [hK₀, hqcard]; rfl)
    (iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent)
    (fun c => by rw [hqcard]; exact hσ₀ c)
  unfold TwistedChevalleyModel
  exact ⟨GaloisField q.p (3 * q.exponent), inferInstance, inferInstance, hK₀,
    iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent, hσ₀, ⟨e.trans b.symm⟩⟩

theorem lieOuterFieldFamTrialityD4 : LieOuterFieldFam .trialityD4 := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨q, hq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at hch
  subst hch
  by_cases hp3 : q.p = 3
  · exact Or.inr ⟨hp3, trivial⟩
  left
  change q.p ∣ q.exponent
  have hp5 : 5 ≤ q.p := by
    have h2 := hp.two_le
    have h4 : q.p ≠ 4 := by
      intro h4
      rw [h4] at hp
      exact absurd hp (by norm_num)
    omega
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hS
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hmodel := twistedModel_of_trialityD4 q hv hp2 e
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hmodel
  have hαp : MulAut.congr e₁ ψ ^ q.p = 1 := congr_pow_eq_one e₁ hψp
  have hαin := congr_not_inner e₁ hψo
  have hαord : orderOf (MulAut.congr e₁ ψ) = q.p :=
    orderOf_eq_prime hαp fun h1 => hαin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨-, -, Θ, hΘ, -⟩ := CFSG.RankThree.Chevalley.triality_normal_form_data hp hf K hK σ hσ
  obtain ⟨-, hpf, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hp hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨MulAut.congr e₁ ψ, Subgroup.mem_top _⟩ hαin
      (by rw [Subgroup.orderOf_mk]; exact hαord)
  exact hpf

@[expose] def TD43RankFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.card = 3 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) →
      5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)

theorem lieRankFiveFamTrialityD4 (hTD : TD43RankFive) :
    LieRankFiveFam .trialityD4 := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨q, hq⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at hch
  subst hch
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases hf1 : q.exponent = 1 ∧ q.p = 3
  · rw [hf1.2]
    refine hTD S q hv ?_ hS
    rw [TauCeti.PrimePower.card_def, hf1.1, hf1.2, pow_one]
  have hf2 : 2 ≤ q.exponent := by
    rcases hF with hf | ⟨hp3, -⟩
    · change q.p ∣ q.exponent at hf
      have := three_le_of_dvd hp hp2 hf q.exponent_pos
      omega
    · have := q.exponent_pos
      by_contra hlt
      exact hf1 ⟨by omega, hp3⟩
  obtain ⟨e⟩ := hS
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * TwistTag.D4.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos TwistTag.D4.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ'', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσo : σ ^ 3 = 1 := by
    rw [show 3 = TwistTag.D4.order from rfl, ← hord]
    exact pow_orderOf_eq_one σ
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv' _ _ hperf.2.2.1 hZ
  let e' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* S :=
    (ψ.symm.trans φ).trans e.symm
  obtain ⟨ι, -, hι, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσo
  have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by
    rw [hK, ← pow_mul, mul_comm]
    rfl
  have h3 := le_pRank_of_sl2 (X := S) (F := K) hK3 (e'.toMonoidHom.comp ι) (e'.injective.comp hι)
  omega

end RankTriality

section FamilyReeG2

open CFSG.LieType.Ree

theorem lieOuterFieldFamReeG2 : LieOuterFieldFam .reeG2 := by
  intro S _ _ _ _ idx hk hS p hp hp2 hch ψ hψp hψo
  obtain ⟨m, hm⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hm
  subst hm
  simp only [TauCeti.LieTypeIndex.characteristic_reeG2] at hch
  subst hch
  left
  change 3 ∣ 2 * m + 1
  have hRT := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, hS⟩
  obtain ⟨-, -, -, -, hiso⟩ := small_Ree_model_Schreier S 3 (2 * m + 1) hRT
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e₀⟩⟩ := hRT
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := 2 * m + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a' K hfa' hK ⟨e₀⟩
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have ha' : 1 ≤ a' := by omega
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa']
  have h := (CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a' ha' K hK' hp hp2
    (MulAut.congr e ψ) (congr_pow_eq_one e hψp) (congr_not_inner e hψo)).1
  rwa [← hfa'] at h

theorem lieRankFiveFamReeG2 : LieRankFiveFam .reeG2 := by
  intro S _ _ idx hk hS p hp hp2 hch hF h27
  obtain ⟨m, hm⟩ := hk
  obtain ⟨d, hv⟩ := idx
  simp only at hm
  subst hm
  simp only [TauCeti.LieTypeIndex.characteristic_reeG2] at hch
  subst hch
  have hRT := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, hS⟩
  obtain ⟨-, h3f, hr⟩ := CFSG.SectionRank.smallReeModel_rank hRT
  omega

end FamilyReeG2

end FamilyTwisted

section D43

open Matrix CFSG.SectionRank.ClassicalOdd
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def skew4 (b : Fin 6 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, b 0, b 1, b 2; -b 0, 0, b 3, b 4; -b 1, -b 3, 0, b 5; -b 2, -b 4, -b 5, 0]

theorem skew4_zero : skew4 (0 : Fin 6 → K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew4]

theorem skew4_add (a b : Fin 6 → K) : skew4 (a + b) = skew4 a + skew4 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew4] <;> ring

@[expose] def siegelMat (b : Fin 6 → K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  fromBlocks 1 (skew4 b) 0 1

theorem siegelMat_zero : siegelMat (0 : Fin 6 → K) = 1 := by
  rw [siegelMat, skew4_zero, fromBlocks_one]

theorem siegelMat_add (a b : Fin 6 → K) : siegelMat (a + b) = siegelMat a * siegelMat b := by
  rw [siegelMat, siegelMat, siegelMat, fromBlocks_multiply, skew4_add]
  simp [add_comm]

theorem siegelMat_injective : Function.Injective (siegelMat (K := K)) := by
  intro a b h
  have h1 : skew4 a = skew4 b := by
    have := congrArg (fun M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K =>
      Matrix.toBlocks₁₂ M) h
    simpa [siegelMat] using this
  funext l
  have := congrFun (congrFun h1 (![0, 0, 0, 1, 1, 2] l)) (![1, 2, 3, 2, 3, 3] l)
  fin_cases l <;> simpa [skew4] using this

@[expose] noncomputable def siegelHom : Multiplicative (Fin 6 → K) →* GL (Fin 4 ⊕ Fin 4) K :=
  glOfAdd siegelMat siegelMat_zero siegelMat_add

theorem statedQuadPlus_four_apply (v : Fin 4 ⊕ Fin 4 → K) :
    CFSG.Open.StatedQuadPlus 4 K v = ∑ i : Fin 4, v (Sum.inl i) * v (Sum.inr i) := rfl

theorem statedQuadPlus_siegelMat (b : Fin 6 → K) (v : Fin 4 ⊕ Fin 4 → K) :
    CFSG.Open.StatedQuadPlus 4 K (siegelMat b *ᵥ v) = CFSG.Open.StatedQuadPlus 4 K v := by
  rw [statedQuadPlus_four_apply, statedQuadPlus_four_apply, siegelMat, fromBlocks_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, one_mulVec, zero_mulVec, zero_add,
    Function.comp_apply]
  simp [Fin.sum_univ_four, mulVec, dotProduct, skew4]
  ring

@[expose] def signDiag (a : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  diagonal fun i => if i = a then -1 else 1

@[expose] def signMat (a : Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  fromBlocks (signDiag a) 0 0 (signDiag a)

theorem signDiag_mul_self (a : Fin 4) : signDiag (K := K) a * signDiag a = 1 := by
  rw [signDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem signMat_mul_self (a : Fin 4) : signMat (K := K) a * signMat a = 1 := by
  rw [signMat, fromBlocks_multiply, signDiag_mul_self]
  simp

@[expose] def signGL (a : Fin 4) : GL (Fin 4 ⊕ Fin 4) K :=
  ⟨signMat a, signMat a, signMat_mul_self a, signMat_mul_self a⟩

theorem statedQuadPlus_signMat (a : Fin 4) (v : Fin 4 ⊕ Fin 4 → K) :
    CFSG.Open.StatedQuadPlus 4 K (signMat a *ᵥ v) = CFSG.Open.StatedQuadPlus 4 K v := by
  rw [statedQuadPlus_four_apply, statedQuadPlus_four_apply, signMat, fromBlocks_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, zero_mulVec, zero_add, add_zero,
    Function.comp_apply, signDiag, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

@[expose] def pairFst (l : Fin 6) : Fin 4 := ![0, 0, 0, 1, 1, 2] l

theorem signMat_siegelMat_single (l : Fin 6) (c : K) :
    signMat (pairFst l) * siegelMat (Pi.single l c) * signMat (pairFst l) =
      siegelMat (Pi.single l (-c)) := by
  rw [signMat, siegelMat, siegelMat, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.one_mul,
    signDiag_mul_self]
  congr 1
  ext i j
  simp only [signDiag, diagonal_mul, mul_diagonal]
  fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [skew4, pairFst, Pi.single_apply]

theorem siegelHom_mem_omega (h2 : (2 : K) ≠ 0) (b : Multiplicative (Fin 6 → K)) :
    siegelHom b ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K) := by
  have hiso : ∀ x, siegelHom (Multiplicative.ofAdd x) ∈
      CFSG.MatrixModel.isometryCore (CFSG.Open.StatedQuadPlus 4 K) := fun x =>
    Subgroup.subset_closure fun v => statedQuadPlus_siegelMat x v
  have hsign : ∀ a, signGL (K := K) a ∈
      CFSG.MatrixModel.isometryCore (CFSG.Open.StatedQuadPlus 4 K) := fun a =>
    Subgroup.subset_closure fun v => statedQuadPlus_signMat a v
  have hsingle : ∀ (l : Fin 6) (c : K), siegelHom (Multiplicative.ofAdd (Pi.single l c)) ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K) := by
    intro l c
    have hcomm := Subgroup.commutator_mem_commutator (hsign (pairFst l))
      (hiso (Pi.single l (-(c / 2))))
    have heq : ⁅signGL (K := K) (pairFst l), siegelHom (Multiplicative.ofAdd (Pi.single l (-(c / 2))))⁆ =
        siegelHom (Multiplicative.ofAdd (Pi.single l c)) := by
      apply Units.ext
      rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
      have hinv : ((signGL (K := K) (pairFst l))⁻¹ : GL (Fin 4 ⊕ Fin 4) K) =
          signGL (pairFst l) := by
        rw [inv_eq_of_mul_eq_one_right]
        exact Units.ext (signMat_mul_self _)
      have hinv' : ((siegelHom (Multiplicative.ofAdd (Pi.single l (-(c / 2)))))⁻¹ :
          GL (Fin 4 ⊕ Fin 4) K) = siegelHom (Multiplicative.ofAdd (Pi.single l (c / 2))) := by
        rw [← map_inv]
        congr 1
        rw [← ofAdd_neg]
        congr 1
        funext m
        simp only [Pi.neg_apply, Pi.single_apply]
        split_ifs <;> simp
      rw [hinv, hinv']
      change signMat (pairFst l) * siegelMat (Pi.single l (-(c / 2))) * signMat (pairFst l) *
        siegelMat (Pi.single l (c / 2)) = siegelMat (Pi.single l c)
      rw [signMat_siegelMat_single, neg_neg, ← siegelMat_add]
      congr 1
      funext m
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs
      · field_simp
        ring
      · simp
    rw [← heq]
    exact hcomm
  have hb : Multiplicative.toAdd b = ∑ l : Fin 6, Pi.single l (Multiplicative.toAdd b l) :=
    (Finset.univ_sum_single _).symm
  have key : ∀ x : Fin 6 → K, x = ∑ l : Fin 6, Pi.single l (x l) →
      siegelHom (Multiplicative.ofAdd x) ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K) := by
    intro x hx
    rw [hx]
    refine Finset.sum_induction _ (fun y => siegelHom (Multiplicative.ofAdd y) ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)) (fun y z hy hz => ?_) ?_
      (fun l _ => hsingle l _)
    · rw [ofAdd_add, map_mul]
      exact Subgroup.mul_mem _ hy hz
    · rw [ofAdd_zero, map_one]
      exact Subgroup.one_mem _
  exact key (Multiplicative.toAdd b) hb

theorem six_mul_le_pRank_omegaPlus_four [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    f * 6 ≤ CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus 4 K)))) := by
  have := charP_of_card hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (p : K) ∣ 2 := by
      rw [CharP.cast_eq_zero]
      exact ⟨0, by rw [h, zero_mul]⟩
    have h2' := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2')
  have hcard := card_multiplicative_fun (P := Fin 6) hK
  rw [Fintype.card_fin] at hcard
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) hcard siegelHom (glOfAdd_injective siegelMat_injective)
    (siegelHom_mem_omega h2) (v := Pi.single (Sum.inl 0) 1) (by simp) ?_
  intro a
  change siegelMat (Multiplicative.toAdd a) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1
  rw [siegelMat, fromBlocks_mulVec]
  ext i
  rcases i with i | i <;> simp [Pi.single_apply, mulVec, dotProduct]

theorem d43RankFive_holds : D43RankFive := by
  intro K _ _ hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := six_mul_le_pRank_omegaPlus_four (K := K) (p := 3) (f := 1) (by norm_num) (by rw [hK]; norm_num)
  omega

end D43

section TD43

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits
open CFSG.GH74.Filter.Lie (eq_one_of_prod_five d4Vec5 d4SepWords5 d4_pair_check5 d4_sep_check5)

@[expose] def d4ThetaWord₂ : List (Fin TwistTag.D4.tag.rank) := ([2, 3, 1, 0] : List (Fin 4))

theorem d4ThetaWord₂_fixed : ∀ k : Fin TwistTag.D4.tag.rank,
    (d4ThetaWord₂.map TwistTag.D4.perm).foldr (reflect TwistTag.D4.tag) (Pi.single k 1) =
      d4ThetaWord₂.foldr (reflect TwistTag.D4.tag) (Pi.single k 1) := by
  decide +kernel

theorem d4ThetaWord₂_smul :
    d4ThetaWord₂.foldr (reflect TwistTag.D4.tag) (Pi.single (2 : Fin 4) 1) = d4Vec5 4 := by
  decide +kernel


theorem le_pRank_commutator_twistFixed_D4_five' {K : Type} [Field K] [Finite K] {p m : ℕ}
    [Fact p.Prime] [CharP K p] (σ : K →+* K) (hK : Nat.card K = p ^ m)
    (hσ : Function.Surjective σ) (hσ3 : ∀ c, σ (σ (σ c)) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    m + 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (commutator (twistFixed .D4 K σ))) := by
  set τ := TwistTag.D4.tag
  set s₂ : WeylGroup τ := (coxeterSystem τ).wordProd d4S2Word
  set n := nrep τ K s₂
  have hs₂ : weylTwist .D4 s₂ = s₂ := weylTwist_wordProd_eq (ω := d4S2Word) d4_s2_fixed
  set w : WeylGroup τ := (coxeterSystem τ).wordProd d4ThetaWord₂
  set n₂ := nrep τ K w
  have hw : weylTwist .D4 w = w := weylTwist_wordProd_eq (ω := d4ThetaWord₂) d4ThetaWord₂_fixed
  set α : Fin 5 → Root τ := ![s₂ • simpleRoot τ d4i0, s₂ • simpleRoot τ d4i1,
    s₂ • simpleRoot τ d4i3, simpleRoot τ d4i2, w • simpleRoot τ d4i2]
  have hαv : ∀ j, (α j).1 = d4Vec5 j := by
    intro j
    match j with
    | 0 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i0).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 1 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i1).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 2 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i3).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 3 => rfl
    | 4 =>
      change ((coxeterSystem τ).wordProd d4ThetaWord₂ • simpleRoot τ d4i2).1 = _
      rw [coe_smul_root, wordProd_smul]
      exact d4ThetaWord₂_smul
  have hpc : ∀ i j, i ≠ j → pairCheck τ (α i).1 (α j).1 = true := fun i j hij => by
    rw [hαv, hαv]; exact d4_pair_check5 i j hij
  have hposα : ∀ j, 0 < height (α j).1 := fun j => by
    have := hpc j (j + 1) (by omega)
    simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1
  have hind : iSupIndep fun j => (nativeRootSubgroups τ K).X (α j) :=
    iSupIndep_X_of_separated (K := K) α hposα
      (fun j => (coxeterSystem τ).wordProd (d4SepWords5 j))
      (fun j => by rw [wordProd_smul, hαv]; exact (d4_sep_check5 j).1)
      (fun i j hij => by rw [wordProd_smul, hαv]; exact (d4_sep_check5 i).2 j hij)
  have hcX : ∀ i j, i ≠ j → ∀ x ∈ (nativeRootSubgroups τ K).X (α i),
      ∀ y ∈ (nativeRootSubgroups τ K).X (α j), Commute x y := fun i j hij x hx y hy =>
    commute_of_mem_X_of_pairCheck (hpc i j hij) hx hy
  have hconjX : ∀ (k : Fin τ.rank) (c : K), n * xElement k c * n⁻¹ ∈
      (nativeRootSubgroups τ K).X (s₂ • simpleRoot τ k) := fun k c => by
    rw [← eltElement_simpleRoot]
    exact nrep_conj_mem_X s₂ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  have hx0 : ∀ c, n * xElement d4i0 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 0) :=
    hconjX d4i0
  have hx1 : ∀ c, n * xElement d4i1 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 1) :=
    hconjX d4i1
  have hx3 : ∀ c, n * xElement d4i3 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 2) :=
    hconjX d4i3
  have hx2 : ∀ c, xElement (τ := τ) d4i2 c ∈ (nativeRootSubgroups τ K).X (α 3) :=
    fun c => xElement_mem_X _ c
  have hxθ : ∀ c, n₂ * xElement (τ := τ) d4i2 c * n₂⁻¹ ∈ (nativeRootSubgroups τ K).X (α 4) := by
    intro c
    rw [← eltElement_simpleRoot]
    exact nrep_conj_mem_X w ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  have hc01 : ∀ a b : K, Commute (xElement (τ := τ) d4i0 a) (xElement d4i1 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  have hc03 : ∀ a b : K, Commute (xElement (τ := τ) d4i0 a) (xElement d4i3 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  have hc13 : ∀ a b : K, Commute (xElement (τ := τ) d4i1 a) (xElement d4i3 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  set y : K → adjointGroup τ K := fun c =>
    xElement d4i0 c * xElement d4i1 (σ c) * xElement d4i3 (σ (σ c))
  have hy_add : ∀ c d, y (c + d) = y c * y d := by
    intro c d
    simp only [y, map_add, xElement_add]
    have e1 := (hc01 d (σ c)).eq
    have e2 := (hc03 d (σ (σ c))).eq
    have e3 := (hc13 (σ d) (σ (σ c))).eq
    set A := xElement (τ := τ) (K := K) d4i0 c
    set A' := xElement (τ := τ) (K := K) d4i0 d
    set B := xElement (τ := τ) (K := K) d4i1 (σ c)
    set B' := xElement (τ := τ) (K := K) d4i1 (σ d)
    set C := xElement (τ := τ) (K := K) d4i3 (σ (σ c))
    set C' := xElement (τ := τ) (K := K) d4i3 (σ (σ d))
    calc A * A' * (B * B') * (C * C') = A * (A' * B) * B' * C * C' := by group
      _ = A * (B * A') * B' * C * C' := by rw [e1]
      _ = A * B * A' * (B' * C) * C' := by group
      _ = A * B * A' * (C * B') * C' := by rw [e3]
      _ = A * B * (A' * C) * B' * C' := by group
      _ = A * B * (C * A') * B' * C' := by rw [e2]
      _ = A * B * C * (A' * B' * C') := by group
  have hyF : ∀ c, twistC .D4 K σ (y c) = y c := by
    intro c
    simp only [y, map_mul, twistC_xElement, d4_perm_0, d4_perm_1, d4_perm_3, hσ3]
    have e1 := (hc01 c (σ c)).eq
    have e2 := (hc03 c (σ (σ c))).eq
    calc xElement (τ := τ) d4i1 (σ c) * xElement d4i3 (σ (σ c)) * xElement d4i0 c
        = xElement d4i1 (σ c) * (xElement d4i3 (σ (σ c)) * xElement d4i0 c) := by group
      _ = xElement d4i1 (σ c) * (xElement d4i0 c * xElement d4i3 (σ (σ c))) := by rw [e2]
      _ = (xElement d4i1 (σ c) * xElement d4i0 c) * xElement d4i3 (σ (σ c)) := by group
      _ = (xElement d4i0 c * xElement d4i1 (σ c)) * xElement d4i3 (σ (σ c)) := by rw [e1]
  set Y : Multiplicative K →* adjointGroup τ K :=
    { toFun := fun c => y (Multiplicative.toAdd c)
      map_one' := by simp only [y, toAdd_one, map_zero, xElement_zero, mul_one]
      map_mul' := fun c d => hy_add _ _ }
  set Z : Multiplicative K →* adjointGroup τ K := (MulAut.conj n).toMonoidHom.comp Y
  set ι : Multiplicative (ZMod p) →* Multiplicative K :=
    (ZMod.castHom (dvd_refl p) K).toAddMonoidHom.toMultiplicative
  set X2 : Multiplicative (ZMod p) →* adjointGroup τ K :=
    (rootHom (simpleRoot τ d4i2)).comp ι
  set Xθ : Multiplicative (ZMod p) →* adjointGroup τ K := (MulAut.conj n₂).toMonoidHom.comp X2
  have hZ : ∀ c : Multiplicative K, Z c = n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ *
      (n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹) *
      (n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹) := fun c => by
    change n * y (Multiplicative.toAdd c) * n⁻¹ = _
    simp only [y]
    group
  have hX2 : ∀ c' : Multiplicative (ZMod p), X2 c' = xElement (τ := τ) d4i2
      (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c')) := fun c' =>
    eltElement_simpleRoot _ _
  have hXθ : ∀ b : Multiplicative (ZMod p), Xθ b = n₂ * xElement (τ := τ) d4i2
      (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd b)) * n₂⁻¹ := fun b => by
    change n₂ * X2 b * n₂⁻¹ = _
    rw [hX2]
  have hZX2 : ∀ c c', Commute (Z c) (X2 c') := by
    intro c c'
    rw [hZ, hX2]
    have h3 := hx2 (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c'))
    exact ((hcX 0 3 (by decide) _ (hx0 _) _ h3).mul_left
      (hcX 1 3 (by decide) _ (hx1 _) _ h3)).mul_left (hcX 2 3 (by decide) _ (hx3 _) _ h3)
  have hZXθ : ∀ c b, Commute (Z c) (Xθ b) := by
    intro c b
    rw [hZ, hXθ]
    have h4 := hxθ (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd b))
    exact ((hcX 0 4 (by decide) _ (hx0 _) _ h4).mul_left
      (hcX 1 4 (by decide) _ (hx1 _) _ h4)).mul_left (hcX 2 4 (by decide) _ (hx3 _) _ h4)
  have hX2Xθ : ∀ c' b, Commute (X2 c') (Xθ b) := by
    intro c' b
    rw [hX2, hXθ]
    exact hcX 3 4 (by decide) _ (hx2 _) _ (hxθ _)
  set Ψ : Multiplicative K × Multiplicative (ZMod p) →* adjointGroup τ K :=
    Z.noncommCoprod X2 hZX2
  have hΨXθ : ∀ (a : Multiplicative K × Multiplicative (ZMod p)) (b : Multiplicative (ZMod p)),
      Commute (Ψ a) (Xθ b) := fun a b => by
    rw [MonoidHom.noncommCoprod_apply]
    exact (hZXθ _ _).mul_left (hX2Xθ _ _)
  set Ψ' : (Multiplicative K × Multiplicative (ZMod p)) × Multiplicative (ZMod p) →*
      adjointGroup τ K := Ψ.noncommCoprod Xθ hΨXθ
  have hΨ'apply : ∀ c c' b, Ψ' ((c, c'), b) = Z c * X2 c' * Xθ b := fun _ _ _ => rfl
  have hΨ' : Function.Injective Ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨c, c'⟩, b⟩ h
    rw [MonoidHom.mem_ker, hΨ'apply, hZ, hX2, hXθ] at h
    have h4 := eq_one_of_prod_five (A := fun j => (nativeRootSubgroups τ K).X (α j)) hind
      (a := ![n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹,
        n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹,
        n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹,
        xElement (τ := τ) d4i2 (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c')),
        n₂ * xElement (τ := τ) d4i2 (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd b)) * n₂⁻¹])
      (fun j => by
        match j with
        | 0 => exact hx0 _
        | 1 => exact hx1 _
        | 2 => exact hx3 _
        | 3 => exact hx2 _
        | 4 => exact hxθ _) h
    have ha0 : n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ = 1 := h4 0
    have ha3 : xElement (τ := τ) d4i2
        (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c')) = 1 := h4 3
    have ha4 : n₂ * xElement (τ := τ) d4i2
        (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd b)) * n₂⁻¹ = 1 := h4 4
    rw [mul_inv_eq_one, mul_eq_left] at ha0 ha4
    have hc : Multiplicative.toAdd c = 0 :=
      xElement_injective _ (ha0.trans (xElement_zero _).symm)
    have hc' : ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c') = 0 :=
      xElement_injective _ (ha3.trans (xElement_zero _).symm)
    have hb : ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd b) = 0 :=
      xElement_injective _ (ha4.trans (xElement_zero _).symm)
    rw [Subgroup.mem_bot, Prod.mk_eq_one, Prod.mk_eq_one]
    exact ⟨⟨hc, Multiplicative.toAdd.injective ((ZMod.castHom_injective K)
      (hc'.trans (map_zero _).symm))⟩, Multiplicative.toAdd.injective ((ZMod.castHom_injective K)
      (hb.trans (map_zero _).symm))⟩
  have hU : ∀ x ∈ (nativeData τ K).U, twistC .D4 K σ x = x → x ∈ twistDerived .D4 K σ :=
    d4_U_le_twistDerived hσ hσ3 hu
  have hUα : ∀ j, (nativeRootSubgroups τ K).X (α j) ≤ (nativeData τ K).U := fun j =>
    RootGroupData.X_le_U (D := nativeData τ K) (hposα j)
  have hn : twistC .D4 K σ n = n := by rw [twistC_nrep, hs₂]
  have hn₂ : twistC .D4 K σ n₂ = n₂ := by rw [twistC_nrep, hw]
  have hFZ : ∀ c, twistC .D4 K σ (Z c) = Z c := fun c => by
    change twistC .D4 K σ (n * y (Multiplicative.toAdd c) * n⁻¹) =
      n * y (Multiplicative.toAdd c) * n⁻¹
    rw [map_mul, map_mul, map_inv, hn, hyF]
  have hF2 : ∀ c', twistC .D4 K σ (X2 c') = X2 c' := fun c' => by
    rw [hX2, twistC_xElement, d4_perm_2, ringHom_zmod_cast]
  have hFθ : ∀ b, twistC .D4 K σ (Xθ b) = Xθ b := fun b => by
    change twistC .D4 K σ (n₂ * X2 b * n₂⁻¹) = n₂ * X2 b * n₂⁻¹
    rw [map_mul, map_mul, map_inv, hn₂, hF2]
  have hrange : Ψ'.range ≤ twistDerived .D4 K σ := by
    rintro _ ⟨⟨⟨c, c'⟩, b⟩, rfl⟩
    rw [hΨ'apply]
    refine hU _ ?_ ?_
    · rw [hZ, hX2, hXθ]
      exact mul_mem (mul_mem (mul_mem (mul_mem (hUα 0 (hx0 _)) (hUα 1 (hx1 _)))
        (hUα 2 (hx3 _))) (hUα 3 (hx2 _))) (hUα 4 (hxθ _))
    · rw [map_mul, map_mul, hFZ c, hF2 c', hFθ b]
  have hpow : ∀ a : (Multiplicative K × Multiplicative (ZMod p)) × Multiplicative (ZMod p),
      a ^ p = 1 := fun a => by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change Multiplicative.ofAdd (p • Multiplicative.toAdd a.1.1) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    · change Multiplicative.ofAdd (p • Multiplicative.toAdd a.1.2) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
    · change Multiplicative.ofAdd (p • Multiplicative.toAdd a.2) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
  exact le_pRank_of_commutator (p := p) hΨ' hrange (fun a b => mul_comm a b) hpow
    (k := m + 2) (by
    rw [Nat.card_prod, Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK,
      show Nat.card (Multiplicative (ZMod p)) = p from by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]]
    ring)

theorem td43RankFive_holds :
    TD43RankFive := by
  intro S _ _ q hv hq3 hS
  obtain ⟨e0⟩ := hS
  have hq3' : q.p ^ q.exponent = 3 ^ 1 := by simpa [TauCeti.PrimePower.card_def] using hq3
  have hqp : q.p = 3 := by
    have h1 : q.p ∣ 3 ^ 1 := by rw [← hq3']; exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (by simpa using h1)
  have hmodel := twistedModel_of_trialityD4 q hv (by rw [hqp]; norm_num) e0
  rw [hq3'] at hmodel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ :=
    CFSG.SectionRank.twistedModel_data (p := 3) (f := 1) le_rfl hmodel
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul, show 3 ^ 1 * (3 ^ 1 * 3 ^ 1) = Nat.card K by
      rw [hK]; rfl, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    CFSG.SectionRank.pRank_twistedDerivedQuotient σ hσ (d4_U_le_twistDerived hσ hσ3 hu)]
  have h1 := le_pRank_commutator_twistFixed_D4_five' σ (m := 3) (by rw [hK]; rfl) hσ hσ3 hu
  omega

end TD43

section Assembly


theorem chevOuterFacts_of_residuals (hGA : CFSG.Open.GriessAllModelsStatement) (hD43 : D43RankFive)
    (hTD : TD43RankFive) : ChevOuterFacts := by
  refine chevOuterFacts_of_families fun k => ?_
  cases k with
  | A => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamA lieRankFiveFamA
  | twistedA =>
    exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamTwistedA lieRankFiveFamTwistedA
  | B => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamB lieRankFiveFamB
  | C => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamC lieRankFiveFamC
  | D => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamD (lieRankFiveFamD hD43)
  | twistedD =>
    exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamTwistedD lieRankFiveFamTwistedD
  | E6 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamE6 lieRankFiveFamE6
  | E7 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamE7 lieRankFiveFamE7
  | E8 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamE8 lieRankFiveFamE8
  | F4 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamF4 lieRankFiveFamF4
  | G2 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamG2 lieRankFiveFamG2
  | twistedE6 =>
    exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamTwistedE6 lieRankFiveFamTwistedE6
  | trialityD4 =>
    exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamTrialityD4
      (lieRankFiveFamTrialityD4 hTD)
  | reeG2 => exact chevOuterFam_of hGA l227Fact_holds lieOuterFieldFamReeG2 lieRankFiveFamReeG2

theorem inputI2711ChevPOuter_of_residuals (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD43 : D43RankFive) (hTD : TD43RankFive) : Inputs2711.InputI2711ChevPOuter :=
  inputI2711ChevPOuter_of_facts (chevOuterFacts_of_residuals hGA hD43 hTD)

theorem inputI2711ChevPOuter_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) :
    Inputs2711.InputI2711ChevPOuter :=
  inputI2711ChevPOuter_of_residuals hGA d43RankFive_holds td43RankFive_holds

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c
