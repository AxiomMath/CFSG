module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.IsPerfect
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.AutTwoGroup
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Sections
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSymp
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix
import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open scoped commutatorElement IsMulCommutative
open FiveTransitive.CharacteristicAutomorphism (quotient quotient_apply_mk)
open CFSG.RankThree.PartTwo.Sec4.Census CFSG.ComponentClassification.PresentationLocal

section Form

variable {C : Type} [Group C]

private lemma eq_of_sq_eq_one {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {c d : Z}
    (hc : c ^ 2 = 1) (hd : d ^ 2 = 1) (hc1 : c ≠ 1) (hd1 : d ≠ 1) : c = d := by
  classical
  have := Fintype.ofFinite Z
  by_contra hcd
  have hle := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) two_pos
  have hsub : ({1, c, d} : Finset Z) ⊆ Finset.univ.filter (fun a : Z => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hc1, Ne.symm hd1]),
    Finset.card_pair hcd] at h3
  omega

open Classical in
private noncomputable def bit (c : C) : ZMod 2 := if c = 1 then 0 else 1

private lemma bit_eq_zero_iff {c : C} : bit c = 0 ↔ c = 1 := by
  unfold bit
  split_ifs with h <;> simp [h]

private lemma bit_one : bit (1 : C) = 0 := bit_eq_zero_iff.2 rfl

private lemma bit_inv (c : C) : bit c⁻¹ = bit c := by
  by_cases h : c = 1 <;> simp [bit, h]

private lemma bit_mul [Finite C] (hZ : IsCyclic (Subgroup.center C)) {c d : C}
    (hc : c ∈ Subgroup.center C) (hd : d ∈ Subgroup.center C) (hc2 : c ^ 2 = 1)
    (hd2 : d ^ 2 = 1) : bit (c * d) = bit c + bit d := by
  by_cases hc1 : c = 1
  · simp [hc1, bit_one]
  by_cases hd1 : d = 1
  · simp [hd1, bit_one]
  have hcd : c = d := congrArg Subtype.val (eq_of_sq_eq_one (c := (⟨c, hc⟩ : Subgroup.center C))
    (d := ⟨d, hd⟩) (Subtype.ext hc2) (Subtype.ext hd2) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hd1 (congrArg Subtype.val h)))
  subst hcd
  rw [← sq, hc2, bit_one]
  simp only [bit, hc1, if_false]
  decide

private lemma commutatorElement_eq_of_mk_eq {x x' y y' : C}
    (hx : (x : C ⧸ Subgroup.center C) = x') (hy : (y : C ⧸ Subgroup.center C) = y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center C, x' = x * z :=
    ⟨_, QuotientGroup.eq.1 hx, by group⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Subgroup.center C, y' = y * w :=
    ⟨_, QuotientGroup.eq.1 hy, by group⟩
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  symm
  calc ⁅x * z, y * w⁆ = x * (z * (y * w)) * (z⁻¹ * x⁻¹) * (w⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = x * ((y * w) * z) * (z⁻¹ * x⁻¹) * (w⁻¹ * y⁻¹) := by rw [← hz' (y * w)]
    _ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [← hw' x⁻¹]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

private lemma commutatorElement_sq (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) (x y : C) :
    ⁅x, y⁆ ^ 2 = 1 := by
  rw [sq, ← commutatorElement_mul_right_of_commutator_mem_center
    (commutatorElement_mem_center_of_sq_mem hsq x y), ← sq, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp (hsq y) x

private noncomputable def commForm (e f : C ⧸ Subgroup.center C) : ZMod 2 :=
  bit ⁅Quotient.out e, Quotient.out f⁆

private lemma commForm_mk (x y : C) :
    commForm (x : C ⧸ Subgroup.center C) (y : C ⧸ Subgroup.center C) = bit ⁅x, y⁆ := by
  unfold commForm
  rw [commutatorElement_eq_of_mk_eq (QuotientGroup.out_eq' _) (QuotientGroup.out_eq' _)]

private lemma commForm_mul_right [Finite C] (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) (u v t : C ⧸ Subgroup.center C) :
    commForm u (v * t) = commForm u v + commForm u t := by
  induction u using QuotientGroup.induction_on with | H x => ?_
  induction v using QuotientGroup.induction_on with | H y => ?_
  induction t using QuotientGroup.induction_on with | H w => ?_
  rw [← QuotientGroup.mk_mul, commForm_mk, commForm_mk, commForm_mk,
    commutatorElement_mul_right_of_commutator_mem_center
      (commutatorElement_mem_center_of_sq_mem hsq x w)]
  exact bit_mul hZ (commutatorElement_mem_center_of_sq_mem hsq x y)
    (commutatorElement_mem_center_of_sq_mem hsq x w) (commutatorElement_sq hsq x y)
    (commutatorElement_sq hsq x w)

private lemma commForm_comm (u v : C ⧸ Subgroup.center C) : commForm u v = commForm v u := by
  induction u using QuotientGroup.induction_on with | H x => ?_
  induction v using QuotientGroup.induction_on with | H y => ?_
  rw [commForm_mk, commForm_mk, ← commutatorElement_inv, bit_inv]

private lemma commForm_mul_left [Finite C] (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) (u v t : C ⧸ Subgroup.center C) :
    commForm (u * v) t = commForm u t + commForm v t := by
  rw [commForm_comm, commForm_mul_right hZ hsq, commForm_comm t, commForm_comm t]

private lemma commForm_self (u : C ⧸ Subgroup.center C) : commForm u u = 0 := by
  induction u using QuotientGroup.induction_on with | H x => ?_
  rw [commForm_mk, commutatorElement_self, bit_one]

private lemma commForm_nondeg (u : C ⧸ Subgroup.center C) (hu : ∀ v, commForm u v = 0) :
    u = 1 := by
  induction u using QuotientGroup.induction_on with | H x => ?_
  refine (QuotientGroup.eq_one_iff x).2 (Subgroup.mem_center_iff.2 fun y => ?_)
  have h := hu y
  rw [commForm_mk, bit_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm] at h
  exact h.symm

private lemma commForm_quotient (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) {G : Subgroup (MulAut C)}
    (hG : Group.IsPerfect G) {σ : MulAut C} (hσ : σ ∈ G) (e f : C ⧸ Subgroup.center C) :
    commForm (quotient (Subgroup.center C) σ e) (quotient (Subgroup.center C) σ f) =
      commForm e f := by
  induction e using QuotientGroup.induction_on with | H x => ?_
  induction f using QuotientGroup.induction_on with | H y => ?_
  have hx := quotient_apply_mk (Subgroup.center C) σ x
  have hy := quotient_apply_mk (Subgroup.center C) σ y
  simp only [QuotientGroup.mk'_apply] at hx hy
  rw [hx, hy, commForm_mk, commForm_mk, ← map_commutatorElement,
    apply_eq_of_mem_center_of_isPerfect hZ hG hσ (commutatorElement_mem_center_of_sq_mem hsq x y)]

end Form

section Assembly

variable {C : Type} [Group C]

private lemma inv_mul_mem_center_of_quotient_eq_one {σ : MulAut C}
    (h : quotient (Subgroup.center C) σ = 1) (x : C) : x⁻¹ * σ x ∈ Subgroup.center C := by
  have h' := quotient_apply_mk (Subgroup.center C) σ x
  rw [h] at h'
  simp only [MulAut.one_apply, QuotientGroup.mk'_apply] at h'
  exact QuotientGroup.eq.1 h'

private lemma ker_le_ker (hZ : IsCyclic (Subgroup.center C)) {G : Subgroup (MulAut C)}
    (hG : Group.IsPerfect G) {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S)
    {ψ : ↥G →* S} (hψ : Function.Surjective ψ) {X : Type*} [Group X] (θ : ↥G →* X)
    (hθ : θ.ker ≤ ((quotient (Subgroup.center C)).comp G.subtype).ker) : θ.ker ≤ ψ.ker := by
  have hcomm : ∀ a b : θ.ker, a * b = b * a := fun a b => Subtype.ext <| Subtype.ext <|
    mul_comm_of_trivial_on_center_quot
      (fun _ hz => apply_eq_of_mem_center_of_isPerfect hZ hG a.1.2 hz)
      (fun _ hz => apply_eq_of_mem_center_of_isPerfect hZ hG b.1.2 hz)
      (inv_mul_mem_center_of_quotient_eq_one (MonoidHom.mem_ker.1 (hθ a.2)))
      (inv_mul_mem_center_of_quotient_eq_one (MonoidHom.mem_ker.1 (hθ b.2)))
  have := map_eq_bot_of_isSolvable hS hψ θ.normal_ker (isSolvable_of_comm hcomm)
  rwa [Subgroup.map_eq_bot_iff] at this

private lemma exists_surjective_of_ker_le {G X S : Type*} [Group G] [Group X] [Group S]
    (θ : G →* X) {ψ : G →* S} (hψ : Function.Surjective ψ) (h : θ.ker ≤ ψ.ker) :
    ∃ χ : θ.range →* S, Function.Surjective χ :=
  ⟨(QuotientGroup.lift θ.ker ψ h).comp (QuotientGroup.quotientKerEquivRange θ).symm.toMonoidHom,
    (QuotientGroup.lift_surjective_of_surjective θ.ker ψ hψ h).comp (MulEquiv.surjective _)⟩

private lemma injective_of_isSimpleGroup {H S : Type*} [Group H] [Group S] [IsSimpleGroup H]
    [Nontrivial S] {χ : H →* S} (hχ : Function.Surjective χ) : Function.Injective χ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff χ).1 h
  · exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨g, rfl⟩ := hχ s
    exact hs (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))

private lemma nonempty_of_perm_six {S : Type} [Group S] [IsSimpleGroup S]
    {H : Subgroup (Equiv.Perm (Fin 6))} (hH : Group.IsPerfect H) {χ : H →* S}
    (hχ : Function.Surjective χ) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  have hne : H ≠ ⊥ := by
    rintro rfl
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨h, rfl⟩ := hχ s
    exact hs (by rw [Subsingleton.elim h 1, map_one])
  rcases perfect_perm_six hH hne with h | h
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup H := (MulEquiv.subgroupCongr h).isSimpleGroup
    exact Or.inr ⟨(MulEquiv.ofBijective χ ⟨injective_of_isSimpleGroup hχ, hχ⟩).symm.trans
      (MulEquiv.subgroupCongr h)⟩
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    have : IsSimpleGroup H := e.isSimpleGroup
    exact Or.inl ⟨(MulEquiv.ofBijective χ ⟨injective_of_isSimpleGroup hχ, hχ⟩).symm.trans e⟩

private lemma false_of_card_le_four {E : Type*} [Group E] [Finite E] (hE : Nat.card E ≤ 4)
    {G : Type*} [Group G] (ρ : G →* MulAut E) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) {ψ : G →* S} (hψ : Function.Surjective ψ)
    (hker : ρ.ker ≤ ψ.ker) : False := by
  obtain ⟨χ, hχ⟩ := exists_surjective_of_ker_le ρ hψ hker
  have : Finite (MulAut E) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have : Finite S := Finite.of_surjective χ hχ
  have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty (G := S) inferInstance
    (by
      by_contra h
      push Not at h
      exact hS ⟨⟨h⟩⟩)
  have h1 := Nat.card_le_card_of_surjective χ hχ
  have h2 := Subgroup.card_le_card_group ρ.range
  have h3 : Nat.card (MulAut E) ≤ Nat.card (Equiv.Perm E) :=
    Nat.card_le_card_of_injective _ MulEquiv.toEquiv_injective
  rw [Nat.card_perm] at h3
  have h4 : (Nat.card E).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hE
  have : (4 : ℕ).factorial = 24 := rfl
  omega

end Assembly

section Cases

variable {C : Type} [Group C]

private lemma card_quot_le_four_or_eq [Finite C] (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) [IsElementaryAbelian 2 (C ⧸ Subgroup.center C)]
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16) :
    Nat.card (C ⧸ Subgroup.center C) ≤ 4 ∨ Nat.card (C ⧸ Subgroup.center C) = 16 := by
  set B := bilinOf commForm (commForm_mul_left hZ hsq) (commForm_mul_right hZ hsq)
  have hBa : B.IsAlt := fun u => commForm_self _
  have hBn : B.Nondegenerate := by
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · exact congrArg Additive.ofMul (commForm_nondeg _ fun v => hu (Additive.ofMul v))
    · refine congrArg Additive.ofMul (commForm_nondeg (Additive.toMul v) fun u => ?_)
      rw [commForm_comm]
      exact hv (Additive.ofMul u)
  have : Finite (Additive (C ⧸ Subgroup.center C)) :=
    inferInstanceAs (Finite (C ⧸ Subgroup.center C))
  have : Module.Finite (ZMod 2) (Additive (C ⧸ Subgroup.center C)) := Module.Finite.of_finite
  obtain ⟨m, hm⟩ := hBa.even_finrank hBn
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (C ⧸ Subgroup.center C))
  rw [show Nat.card (Additive (C ⧸ Subgroup.center C)) = Nat.card (C ⧸ Subgroup.center C) from
    rfl, Nat.card_zmod, hm] at h
  rw [h] at hcard ⊢
  have hm2 : m ≤ 2 := by
    by_contra hm2
    have : 2 ^ 6 ≤ 2 ^ (m + m) := Nat.pow_le_pow_right two_pos (by omega)
    omega
  interval_cases m <;> simp

private lemma nonempty_of_card_eq_sixteen [Finite C] (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C) [IsElementaryAbelian 2 (C ⧸ Subgroup.center C)]
    (h16 : Nat.card (C ⧸ Subgroup.center C) = 16) {G : Subgroup (MulAut C)}
    (hG : Group.IsPerfect G) {S : Type} [Group S] [IsSimpleGroup S] {ψ : ↥G →* S}
    (hψ : Function.Surjective ψ)
    (hker : ((quotient (Subgroup.center C)).comp G.subtype).ker ≤ ψ.ker) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  have hb₁ := commForm_mul_left hZ hsq
  have hb₂ := commForm_mul_right hZ hsq
  obtain ⟨bs, hbs⟩ := exists_basis_antidiag h16 commForm hb₁ hb₂ commForm_self commForm_nondeg
  have hρ : ∀ (γ : G) x y, commForm (((quotient (Subgroup.center C)).comp G.subtype) γ x)
      (((quotient (Subgroup.center C)).comp G.subtype) γ y) = commForm x y :=
    fun γ x y => commForm_quotient hZ hsq hG γ.2 x y
  set θ := omegaPerm.comp (sympRep commForm hb₁ hb₂ bs hbs _ hρ)
  have hθ : θ.ker ≤ ψ.ker := fun g hg => hker (by
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 := omegaPerm_injective (hg.trans omegaPerm.map_one.symm)
    exact (sympRepGL_eq_one_iff bs _ g).1 (congrArg Subtype.val h1))
  obtain ⟨χ, hχ⟩ := exists_surjective_of_ker_le θ hψ hθ
  have := hG
  exact nonempty_of_perm_six (Group.IsPerfect.range θ) hχ

end Cases

theorem nonempty_alt_of_mulAut_two {C : Type} [Group C] [Finite C] (hC : IsPGroup 2 C)
    (hZ : IsCyclic (Subgroup.center C)) (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16) {G : Subgroup (MulAut C)}
    (hG : Group.IsPerfect G) {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S)
    (ψ : ↥G →* S) (hψ : Function.Surjective ψ) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  have _ := hC
  have : IsElementaryAbelian 2 (C ⧸ Subgroup.center C) :=
    { toIsMulCommutative := ⟨⟨center_quot_mul_comm hsq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (center_quot_sq_eq_one hsq) }
  have hker := ker_le_ker hZ hG hS hψ _ le_rfl
  rcases card_quot_le_four_or_eq hZ hsq hcard with h4 | h16
  · exact (false_of_card_le_four h4 _ hS hψ hker).elim
  · exact nonempty_of_card_eq_sixteen hZ hsq h16 hG hψ hker

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
