module

public import CFSG.GH74.Generic.S45.LG4Defs
public import CFSG.GH74.GLS.TwoThin.ClassCongr
public import CFSG.GH74.Generic.S45.PumpTail

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Tail

theorem pump_tail_g4 {X : Type} [Group X] [Finite X] (hX : Gen4 X)
    (h13 : B_III11_13_10_g4) (h21 : B_III11_2_1) (hJ2 : B_IA_5_3g)
    {z x' : X} (hzc : ∀ g : X, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hx2 : x' * x' = 1) (hxc : x' ∈ commutator X)
    (h2sub : ∀ P : Subgroup X, IsPGroup 2 ↥P → P ≤ centralizer ({x'} : Set X) →
      (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧ ∀ a ∈ P, a * a = 1)
    {J W E : Subgroup X} (hJ : IsComponent J) (hJK2 : InCalK2 ↥J) (hWJ : W ≤ J) (hEW : E ≤ W)
    (hWs : IsSimpleGroup ↥W) (hWnab : ∃ a b : ↥W, a * b ≠ b * a) (hWL : HasL2Model ↥W Odd)
    (hWx : W ≤ centralizer ({x'} : Set X))
    (hWn : (W.subgroupOf (centralizer ({x'} : Set X))).Normal)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEsq : ∀ a ∈ E, a * a = 1)
    (hE4 : 4 ≤ Nat.card ↥E)
    (hnoRee : ¬ IsJ1OrRee ↥J) (hnontriv : ¬ J ≤ centralizer ({x'} : Set X)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJn : J.Normal :=
    component_normal_of_gen4 hX hzc hz2 hz1 hJ hWJ hEW hWs hWnab hEcomm hEsq hE4
  let y : MulAut ↥J := MulAut.conjNormal x'
  have hy : ∀ j : ↥J, ((y j : ↥J) : X) = x' * (j : X) * x'⁻¹ := fun j => rfl
  have hy2 : y * y = 1 := by
    show (MulAut.conjNormal x' : MulAut ↥J) * MulAut.conjNormal x' = 1
    rw [← map_mul, hx2, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    apply hnontriv
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg (fun f : MulAut ↥J => ((f ⟨j, hj⟩ : ↥J) : X)) h1
    simp only [hy, MulAut.one_apply] at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  set L : Subgroup ↥J := W.subgroupOf J with hL
  have hLfix : ∀ w ∈ L, y w = w := by
    intro w hw
    apply Subtype.ext
    rw [hy]
    have hwW : (w : X) ∈ W := hw
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hWx hwW)
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  have hLle : L ≤ fixSub (zpowers y) := fun w hw => fix_mem_zpowers (hLfix w hw)
  have hLnorm : (L.subgroupOf (fixSub (zpowers y))).Normal := by
    constructor
    intro n hn g
    have hnL : ((n : ↥J) : X) ∈ W := hn
    have hgy : y (g : ↥J) = (g : ↥J) := g.2 y (mem_zpowers y)
    have hgc : ((g : ↥J) : X) ∈ centralizer ({x'} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := congrArg (fun a : ↥J => (a : X)) hgy
      simp only [hy] at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hnc : ((n : ↥J) : X) ∈ centralizer ({x'} : Set X) := hWx hnL
    have h2 := hWn.conj_mem (⟨((n : ↥J) : X), hnc⟩ : ↥(centralizer ({x'} : Set X))) hnL
      ⟨((g : ↥J) : X), hgc⟩
    exact h2
  have hLsub : (L.subgroupOf (fixSub (zpowers y))).IsSubnormal := hLnorm.isSubnormal
  have hLL2 : HasL2Model ↥L Odd :=
    CFSG.GH74.GLS.TwoThin.hasL2Model_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hWJ).symm hWL
  have hA : ∀ P : Sylow 2 ↥(fixSub (zpowers y)),
      IsElementaryAbelian 2 ↥(P : Subgroup ↥(fixSub (zpowers y))) := by
    intro P
    let P' : Subgroup X :=
      (((P : Subgroup ↥(fixSub (zpowers y))).map (fixSub (zpowers y)).subtype)).map J.subtype
    have hP'2 : IsPGroup 2 ↥P' := (P.isPGroup'.map (fixSub (zpowers y)).subtype).map J.subtype
    have hP'c : P' ≤ centralizer ({x'} : Set X) := by
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpy : y ((p : ↥(fixSub (zpowers y))) : ↥J) = ((p : ↥(fixSub (zpowers y))) : ↥J) :=
        p.2 y (mem_zpowers y)
      have h2 := congrArg (fun a : ↥J => (a : X)) hpy
      simp only [hy] at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    obtain ⟨hcomm, hsq⟩ := h2sub P' hP'2 hP'c
    have hmem : ∀ a : ↥(P : Subgroup ↥(fixSub (zpowers y))),
        ((((a : ↥(fixSub (zpowers y))) : ↥J)) : X) ∈ P' :=
      fun a => ⟨_, ⟨(a : ↥(fixSub (zpowers y))), a.2, rfl⟩, rfl⟩
    have hcomm' : ∀ a b : ↥(P : Subgroup ↥(fixSub (zpowers y))), a * b = b * a := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hcomm _ (hmem a) _ (hmem b)
    refine { toIsMulCommutative := ⟨⟨hcomm'⟩⟩, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    show ((((a : ↥(fixSub (zpowers y))) : ↥J)) : X) ^ 2 = 1
    rw [pow_two]
    exact hsq _ (hmem a)
  have hnoRee1 : ¬ ∃ f : ℕ, LieModel ↥J .twistedG2 0 3 f := fun ⟨f, hf⟩ => hnoRee (Or.inr ⟨f, hf⟩)
  have hnoJ1 : HasL2Model ↥L (fun q => q = 5) → ¬ NativeSporadic.IsSporadic ↥J .J1 :=
    fun _ hJ1 => hnoRee (Or.inl hJ1)
  obtain ⟨-, hout, hinn⟩ := h13 ↥J (Gen4.subgroup J hX) hJK2 y hord L hLle hLsub hLL2 hA hnoRee1 hnoJ1
  have hyinn : y ∈ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    let Φ : X →* Outer ↥J := (QuotientGroup.mk' (inner ↥J)).comp MulAut.conjNormal
    have hΦ : Φ x' ∈ commutator (Outer ↥J) := by
      have h1 : Φ x' ∈ (commutator X).map Φ := ⟨x', hxc, rfl⟩
      have h2 : (commutator X).map Φ ≤ commutator (Outer ↥J) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact h2 h1
    have hodd := h21 ↥J hJK2 hout
    have hd1 : orderOf (Φ x') ∣ Nat.card (commutator (Outer ↥J)) :=
      Subgroup.orderOf_dvd_natCard _ hΦ
    have hd2 : orderOf (Φ x') ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two, ← map_mul, hx2, map_one]
    have hone : orderOf (Φ x') = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hd1
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd1)
    have hΦ1 : Φ x' = 1 := orderOf_eq_one_iff.1 hone
    exact (QuotientGroup.eq_one_iff _).1 hΦ1
  have hJ2' : NativeSporadic.IsSporadic ↥J .J2 := by
    by_contra hnot
    exact hinn hnot hyinn
  obtain ⟨hsimple, E16, hc16, hs16, hcard16⟩ := hJ2 ↥J hJ2'
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hJ.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcon a' b']
  have hzJ : z ∉ J := by
    intro hzJ
    have : (⟨z, hzJ⟩ : ↥J) = 1 := by
      apply eq_one_of_central_of_simple hsimple hnab
      intro w
      exact Subtype.ext (hzc w)
    exact hz1 (congrArg Subtype.val this)
  refine false_of_elementary_sixteen hX hzc hz2 (A := E16.map J.subtype) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hc16 a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hs16 a ha)
  · rw [Nat.card_congr (E16.equivMapOfInjective J.subtype J.subtype_injective).toEquiv.symm, hcard16]
  · rintro ⟨a, _, ha⟩
    exact hzJ (ha ▸ a.2)

end Tail

end CFSG.GH74.Generic.S45
