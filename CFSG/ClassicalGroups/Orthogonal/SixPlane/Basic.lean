module

public import CFSG.LargeExtraspecial.S2OrthGeom
public import CFSG.LieType.Universal.Spin.Forms
public import TauCeti.InformationTheory.Coding.DirectSum

import CFSG.RankThree.OrthogonalInvolutions.DicksonReflect
public import CFSG.LargeExtraspecial.S2Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus
  nondegenerate_polarBilin_quadPlus)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup commSpace mem_commSpace)
open CFSG.LargeExtraspecial.S2 (omegaFix fixGroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable (n : ℕ)

abbrev V : Type := Fin n ⊕ Fin n → ZMod 2

@[expose] def Q : QuadraticForm (ZMod 2) (V n) :=
  quadPlus n (ZMod 2) + ∑ k : Fin n ⊕ Fin n, QuadraticMap.proj (R := ZMod 2) k k

theorem Q_apply (v : V n) :
    Q n v = ∑ i, (v (Sum.inl i) * v (Sum.inr i) +
      (v (Sum.inl i) * v (Sum.inl i) + v (Sum.inr i) * v (Sum.inr i))) := by
  simp only [Q, QuadraticMap.add_apply, quadPlus_apply, QuadraticMap.sum_apply,
    QuadraticMap.proj_apply]
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

theorem polar_Q (v w : V n) :
    QuadraticMap.polar (Q n) v w =
      ∑ i, (v (Sum.inl i) * w (Sum.inr i) + w (Sum.inl i) * v (Sum.inr i)) := by
  have key : ∀ a b c d : ZMod 2,
      (a + c) * (b + d) + ((a + c) * (a + c) + (b + d) * (b + d)) - (a * b + (a * a + b * b)) -
        (c * d + (c * c + d * d)) = a * d + c * b := by decide
  simp only [QuadraticMap.polar, Q_apply, Pi.add_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => key _ _ _ _

theorem nondegenerate_Q : (Q n).polarBilin.Nondegenerate := by
  have h : (Q n).polarBilin = (quadPlus n (ZMod 2)).polarBilin := by
    refine LinearMap.ext₂ fun v w => ?_
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, polar_Q,
      polar_quadPlus]
  rw [h]
  exact nondegenerate_polarBilin_quadPlus n (ZMod 2)

abbrev Om : Subgroup (V n ≃ₗ[ZMod 2] V n) := omegaGroup (Q n) (nondegenerate_Q n)

variable {n}

@[expose] def planeOf : Fin n ⊕ Fin n → Fin n := Sum.elim id id

variable (n) in
@[expose] def planeSpan (S : Finset (Fin n)) : Submodule (ZMod 2) (V n) :=
  Submodule.pi {k | planeOf k ∉ S} fun _ => ⊥

theorem mem_planeSpan {S : Finset (Fin n)} {v : V n} :
    v ∈ planeSpan n S ↔ ∀ k, planeOf k ∉ S → v k = 0 := by
  simp only [planeSpan, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]

theorem single_mem_planeSpan {T : Finset (Fin n)} {k : Fin n ⊕ Fin n}
    (hk : planeOf k ∈ T) : (Pi.single k (1 : ZMod 2) : V n) ∈ planeSpan n T :=
  mem_planeSpan.mpr fun l hl => by
    rw [Pi.single_apply, if_neg]
    rintro rfl
    exact hl hk

variable (n) in
@[expose] def supp (S : Finset (Fin n)) : Subgroup (V n ≃ₗ[ZMod 2] V n) :=
  omegaFix (Q n) (nondegenerate_Q n) (planeSpan n Sᶜ)

theorem mem_supp {S : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n} :
    g ∈ supp n S ↔ g ∈ Om n ∧ ∀ v ∈ planeSpan n Sᶜ, g v = v :=
  Iff.rfl

variable (n) in
theorem supp_le_Om (S : Finset (Fin n)) : supp n S ≤ Om n :=
  fun _ hg => (mem_supp.1 hg).1

theorem supp_mono {S T : Finset (Fin n)} (h : S ⊆ T) : supp n S ≤ supp n T := by
  change Om n ⊓ fixGroup (planeSpan n Sᶜ) ≤ Om n ⊓ fixGroup (planeSpan n Tᶜ)
  refine inf_le_inf_left _ (CFSG.LargeExtraspecial.S2.fixGroup_anti ?_)
  intro v hv
  apply mem_planeSpan.mpr
  intro k hk
  apply (mem_planeSpan.mp hv) k
  simpa only [Finset.mem_compl, not_not] using
    h (by simpa only [Finset.mem_compl, not_not] using hk)

theorem supp_inf (S T : Finset (Fin n)) : supp n S ⊓ supp n T = supp n (S ∩ T) := by
  apply le_antisymm
  · intro g hg
    refine mem_supp.mpr ⟨hg.1.1, ?_⟩
    intro v hv
    let vS : V n := fun k => if planeOf k ∈ S then 0 else v k
    let vT : V n := fun k => if planeOf k ∈ S then v k else 0
    have hS : vS ∈ planeSpan n Sᶜ := by
      apply mem_planeSpan.mpr
      intro k hk
      have hkS : planeOf k ∈ S := by
        simpa only [Finset.mem_compl, not_not] using hk
      simp [vS, hkS]
    have hT : vT ∈ planeSpan n Tᶜ := by
      apply mem_planeSpan.mpr
      intro k hk
      have hkT : planeOf k ∈ T := by
        simpa only [Finset.mem_compl, not_not] using hk
      by_cases hkS : planeOf k ∈ S
      · have hvk := (mem_planeSpan.mp hv) k (by
          simpa only [Finset.mem_compl, not_not] using Finset.mem_inter.mpr ⟨hkS, hkT⟩)
        simpa [vT, hkS] using hvk
      · simp [vT, hkS]
    have hvadd : vS + vT = v := by
      ext k
      by_cases hk : planeOf k ∈ S <;> simp [vS, vT, hk]
    calc
      g v = g (vS + vT) := congrArg g hvadd.symm
      _ = vS + vT := by rw [map_add, hg.1.2 _ hS, hg.2.2 _ hT]
      _ = v := hvadd
  · exact le_inf (supp_mono Finset.inter_subset_left) (supp_mono Finset.inter_subset_right)

theorem apply_mem_planeSpan_of_mem_supp {S : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n}
    (hg : g ∈ supp n S) {v : V n} (hv : v ∈ planeSpan n S) : g v ∈ planeSpan n S := by
  have hq : ∀ x, Q n (g x) = Q n x :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg.1.1
  have hpolar (x y : V n) :
      QuadraticMap.polar (Q n) (g x) (g y) = QuadraticMap.polar (Q n) x y := by
    unfold QuadraticMap.polar
    rw [← map_add, hq, hq, hq]
  have hsingle (k : Fin n ⊕ Fin n) (hk : planeOf k ∉ S) :
      Pi.single k (1 : ZMod 2) ∈ planeSpan n Sᶜ := by
    apply mem_planeSpan.mpr
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact False.elim (hl (Finset.mem_compl.mpr hk))
    · simp [Pi.single_apply, hlk, Ne.symm hlk]
  apply mem_planeSpan.mpr
  intro k hk
  rcases k with i | i
  · have hp := hpolar v (Pi.single (Sum.inr i) 1)
    rw [hg.2 _ (hsingle (Sum.inr i) hk)] at hp
    have hcoord : g v (Sum.inl i) = v (Sum.inl i) := by
      simpa [polar_Q, Pi.single_apply] using hp
    exact hcoord.trans ((mem_planeSpan.mp hv) _ hk)
  · have hp := hpolar v (Pi.single (Sum.inl i) 1)
    rw [hg.2 _ (hsingle (Sum.inl i) hk)] at hp
    have hcoord : g v (Sum.inr i) = v (Sum.inr i) := by
      simpa [polar_Q, Pi.single_apply] using hp
    exact hcoord.trans ((mem_planeSpan.mp hv) _ hk)

theorem commute_of_mem_supp_of_disjoint {S T : Finset (Fin n)} (hST : Disjoint S T)
    {g h : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ supp n S) (hh : h ∈ supp n T) : Commute g h := by
  have fix_other {U W : Finset (Fin n)} (hUW : Disjoint U W)
      {f : V n ≃ₗ[ZMod 2] V n} (hf : f ∈ supp n W) {x : V n}
      (hx : x ∈ planeSpan n U) : f x = x := by
    apply hf.2 x
    apply mem_planeSpan.mpr
    intro k hk
    apply (mem_planeSpan.mp hx) k
    have hkW : planeOf k ∈ W := by
      simpa only [Finset.mem_compl, not_not] using hk
    exact fun hkU => Finset.disjoint_left.mp hUW hkU hkW
  change g * h = h * g
  apply (Pi.basisFun (ZMod 2) (Fin n ⊕ Fin n)).ext'
  intro k
  rw [Pi.basisFun_apply]
  change g (h (Pi.single k 1)) = h (g (Pi.single k 1))
  have hsingle (U : Finset (Fin n)) (hk : planeOf k ∈ U) :
      Pi.single k (1 : ZMod 2) ∈ planeSpan n U := by
    apply mem_planeSpan.mpr
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact False.elim (hl hk)
    · simp [Pi.single_apply, hlk, Ne.symm hlk]
  by_cases hkS : planeOf k ∈ S
  · have heS := hsingle S hkS
    have hhE := fix_other hST hh heS
    have hhGE := fix_other hST hh (apply_mem_planeSpan_of_mem_supp hg heS)
    simp only [hhE, hhGE]
  · by_cases hkT : planeOf k ∈ T
    · have heT := hsingle T hkT
      have hgE := fix_other hST.symm hg heT
      have hgHE := fix_other hST.symm hg (apply_mem_planeSpan_of_mem_supp hh heT)
      simp only [hgE, hgHE]
    · have heS := hsingle Sᶜ (Finset.mem_compl.mpr hkS)
      have heT := hsingle Tᶜ (Finset.mem_compl.mpr hkT)
      simp only [hh.2 _ heT, hg.2 _ heS]

variable (n) in
theorem Q_single (k : Fin n ⊕ Fin n) : Q n (Pi.single k 1) = 1 := by
  rw [Q_apply, Finset.sum_eq_single (planeOf k)]
  · rcases k with i | i <;> simp [planeOf]
  · intro j _ hj
    rcases k with i | i <;> simp_all [planeOf, Pi.single_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

instance (k : Fin n ⊕ Fin n) : Invertible (Q n (Pi.single k 1)) :=
  invertibleOfNonzero (by rw [Q_single]; exact one_ne_zero)

variable (n) in
@[expose] def crefl (k : Fin n ⊕ Fin n) : V n ≃ₗ[ZMod 2] V n :=
  TauCeti.QuadraticMap.reflection (Q n) (Pi.single k 1)

variable (n) in
@[expose] def rot (i : Fin n) : V n ≃ₗ[ZMod 2] V n :=
  crefl n (Sum.inl i) * crefl n (Sum.inr i)

theorem polar_single_inl_apply (i : Fin n) (v : V n) :
    QuadraticMap.polar (Q n) (Pi.single (Sum.inl i) (1 : ZMod 2)) v = v (Sum.inr i) := by
  rw [polar_Q, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem polar_single_inr_apply (i : Fin n) (v : V n) :
    QuadraticMap.polar (Q n) (Pi.single (Sum.inr i) (1 : ZMod 2)) v = v (Sum.inl i) := by
  rw [polar_Q, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma rotation_invOf_Q_single (k : Fin n ⊕ Fin n) :
    ⅟(Q n (Pi.single k 1)) = 1 := by
  rw [invOf_eq_inv, Q_single, inv_one]

private lemma rotation_crefl_inl_apply (i : Fin n) (v : V n) :
    crefl n (Sum.inl i) v = v - v (Sum.inr i) • Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [crefl, TauCeti.QuadraticMap.reflection_apply, polar_single_inl_apply,
    rotation_invOf_Q_single]
  simp

private lemma rotation_crefl_inr_apply (i : Fin n) (v : V n) :
    crefl n (Sum.inr i) v = v - v (Sum.inl i) • Pi.single (Sum.inr i) (1 : ZMod 2) := by
  rw [crefl, TauCeti.QuadraticMap.reflection_apply, polar_single_inr_apply,
    rotation_invOf_Q_single]
  simp

private lemma rotation_crefl_inl_apply_inl (i : Fin n) (v : V n) :
    crefl n (Sum.inl i) v (Sum.inl i) = v (Sum.inl i) - v (Sum.inr i) := by
  rw [rotation_crefl_inl_apply]
  simp

private lemma rotation_crefl_inl_apply_of_ne {i : Fin n} {v : V n} {k : Fin n ⊕ Fin n}
    (hk : k ≠ Sum.inl i) : crefl n (Sum.inl i) v k = v k := by
  rw [rotation_crefl_inl_apply]
  simp [hk]

private lemma rotation_crefl_inr_apply_inr (i : Fin n) (v : V n) :
    crefl n (Sum.inr i) v (Sum.inr i) = v (Sum.inr i) - v (Sum.inl i) := by
  rw [rotation_crefl_inr_apply]
  simp

private lemma rotation_crefl_inr_apply_of_ne {i : Fin n} {v : V n} {k : Fin n ⊕ Fin n}
    (hk : k ≠ Sum.inr i) : crefl n (Sum.inr i) v k = v k := by
  rw [rotation_crefl_inr_apply]
  simp [hk]

theorem rot_apply_inl (i : Fin n) (v : V n) : rot n i v (Sum.inl i) = v (Sum.inr i) := by
  rw [rot, LinearEquiv.mul_apply, rotation_crefl_inl_apply_inl, rotation_crefl_inr_apply_of_ne (by simp),
    rotation_crefl_inr_apply_inr]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add,
    add_comm (v (Sum.inr i)) (v (Sum.inl i)), CharTwo.add_cancel_left]

theorem rot_apply_inr (i : Fin n) (v : V n) :
    rot n i v (Sum.inr i) = v (Sum.inl i) + v (Sum.inr i) := by
  rw [rot, LinearEquiv.mul_apply, rotation_crefl_inl_apply_of_ne (by simp), rotation_crefl_inr_apply_inr,
    CharTwo.sub_eq_add, add_comm]

theorem rot_apply_of_ne (i : Fin n) (v : V n) {k : Fin n ⊕ Fin n} (hk : planeOf k ≠ i) :
    rot n i v k = v k := by
  rw [rot, LinearEquiv.mul_apply]
  have h1 : k ≠ Sum.inr i := by
    intro h; exact hk (by rw [h]; rfl)
  have h2 : k ≠ Sum.inl i := by
    intro h; exact hk (by rw [h]; rfl)
  rw [rotation_crefl_inl_apply_of_ne h2, rotation_crefl_inr_apply_of_ne h1]

theorem rot_mem_supp {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) : rot n i ∈ supp n S := by
  rw [mem_supp]
  refine ⟨?_, ?_⟩
  · have h1 : crefl n (Sum.inl i) = reflect (Q n) (Pi.single (Sum.inl i) (1 : ZMod 2)) :=
      (reflect_eq_reflection (Q := Q n) (v := Pi.single (Sum.inl i) (1 : ZMod 2))).symm
    have h2 : crefl n (Sum.inr i) = reflect (Q n) (Pi.single (Sum.inr i) (1 : ZMod 2)) :=
      (reflect_eq_reflection (Q := Q n) (v := Pi.single (Sum.inr i) (1 : ZMod 2))).symm
    have hl : ∀ a ∈ [(Pi.single (Sum.inl i) (1 : ZMod 2) : V n), (Pi.single (Sum.inr i) (1 : ZMod 2) : V n)], Q n a ≠ 0 := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rw [Q_single] <;> exact one_ne_zero
    have hev : Even [(Pi.single (Sum.inl i) (1 : ZMod 2) : V n), (Pi.single (Sum.inr i) (1 : ZMod 2) : V n)].length := by simp
    have hprod := CFSG.RankThree.OrthogonalInvolutions.prod_reflect_mem_omegaGroup (Q n) (nondegenerate_Q n)
      [(Pi.single (Sum.inl i) (1 : ZMod 2) : V n), (Pi.single (Sum.inr i) (1 : ZMod 2) : V n)] hl hev
    simpa [rot, h1, h2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] using hprod
  · intro v hv
    funext k
    by_cases hk : planeOf k = i
    · have h0l : v (Sum.inl i) = 0 :=
        hv _ (by simp [Finset.mem_compl, planeOf, hi])
      have h0r : v (Sum.inr i) = 0 :=
        hv _ (by simp [Finset.mem_compl, planeOf, hi])
      rcases k with a | a
      · have ha : a = i := hk
        subst ha
        rw [rot_apply_inl, h0r, h0l]
      · have ha : a = i := hk
        subst ha
        rw [rot_apply_inr, h0l, h0r]
        simp
    · exact rot_apply_of_ne i v hk

private lemma rotation_rot_three_apply (i : Fin n) (v : V n) :
    rot n i (rot n i (rot n i v)) = v := by
  funext k
  by_cases hi : planeOf k = i
  · rcases k with a | a
    · have ha : a = i := hi
      subst a
      simp only [rot_apply_inl, rot_apply_inr]
      rw [add_comm (v (Sum.inl i)) (v (Sum.inr i)), CharTwo.add_cancel_left]
    · have ha : a = i := hi
      subst a
      simp only [rot_apply_inr, rot_apply_inl]
      rw [add_comm (v (Sum.inr i)) (v (Sum.inl i) + v (Sum.inr i)),
        CharTwo.add_cancel_left]
  · rw [rot_apply_of_ne i _ hi, rot_apply_of_ne i _ hi, rot_apply_of_ne i _ hi]

theorem rot_pow_three (i : Fin n) : rot n i ^ 3 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  simpa [pow_three, LinearEquiv.mul_apply] using rotation_rot_three_apply i v

theorem commute_rot (i j : Fin n) : Commute (rot n i) (rot n j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  · refine (commute_iff_eq _ _).mpr ?_
    ext v k
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rcases k with a | a <;> by_cases hai : a = i <;> by_cases haj : a = j
    · subst a; exact absurd haj hij
    · subst a
      rw [rot_apply_inl,
        rot_apply_of_ne j v (k := Sum.inr i) (by simpa [planeOf] using hij),
        rot_apply_of_ne j (rot n i v) (k := Sum.inl i) (by simpa [planeOf] using hij),
        rot_apply_inl]
    · subst a
      rw [rot_apply_of_ne i (rot n j v) (k := Sum.inl j) (by simpa [planeOf] using hai),
        rot_apply_inl, rot_apply_inl,
        rot_apply_of_ne i v (k := Sum.inr j) (by simpa [planeOf] using hai)]
    · have hki : planeOf (Sum.inl a) ≠ i := by simpa [planeOf] using hai
      have hkj : planeOf (Sum.inl a) ≠ j := by simpa [planeOf] using haj
      rw [rot_apply_of_ne i (rot n j v) hki, rot_apply_of_ne j v hkj,
        rot_apply_of_ne j (rot n i v) hkj, rot_apply_of_ne i v hki]
    · subst a; exact absurd haj hij
    · subst a
      rw [rot_apply_inr,
        rot_apply_of_ne j v (k := Sum.inl i) (by simpa [planeOf] using hij),
        rot_apply_of_ne j v (k := Sum.inr i) (by simpa [planeOf] using hij),
        rot_apply_of_ne j (rot n i v) (k := Sum.inr i) (by simpa [planeOf] using hij),
        rot_apply_inr]
    · subst a
      rw [rot_apply_of_ne i (rot n j v) (k := Sum.inr j) (by simpa [planeOf] using hai)]
      simp only [rot_apply_inr]
      rw [rot_apply_of_ne i v (k := Sum.inl j) (by simpa [planeOf] using hai),
        rot_apply_of_ne i v (k := Sum.inr j) (by simpa [planeOf] using hai)]
    · have hki : planeOf (Sum.inr a) ≠ i := by simpa [planeOf] using hai
      have hkj : planeOf (Sum.inr a) ≠ j := by simpa [planeOf] using haj
      rw [rot_apply_of_ne i (rot n j v) hki, rot_apply_of_ne j v hkj,
        rot_apply_of_ne j (rot n i v) hkj, rot_apply_of_ne i v hki]

variable (n) in
@[expose] def torus (S : Finset (Fin n)) : Subgroup (V n ≃ₗ[ZMod 2] V n) :=
  Subgroup.closure (rot n '' (S : Set (Fin n)))

private noncomputable def torusAux_CN (n : ℕ) : Subgroup (V n ≃ₗ[ZMod 2] V n) :=
  Subgroup.closure (Set.range (fun i : Fin n => rot n i))

private theorem torusAux_CN_comm :
    ∀ a ∈ Set.range (fun i : Fin n => rot n i),
      ∀ b ∈ Set.range (fun i : Fin n => rot n i), a * b = b * a := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact (commute_rot i j).eq

private noncomputable instance torusAux_instCommGroupCN (n : ℕ) : CommGroup (torusAux_CN n) :=
  letI hC : IsMulCommutative (torusAux_CN n) :=
    CFSG.subgroup_isMulCommutative_closure (s := Set.range (fun i : Fin n => rot n i))
      (torusAux_CN_comm (n := n))
  { (torusAux_CN n).toGroup with mul_comm := hC.is_comm.comm }

private noncomputable def torusAux_v (n : ℕ) (i : Fin n) : torusAux_CN n :=
  ⟨rot n i, Subgroup.subset_closure ⟨i, rfl⟩⟩

private theorem torusAux_v_coe (i : Fin n) : (↑(torusAux_v n i) : V n ≃ₗ[ZMod 2] V n) = rot n i := rfl

private theorem torusAux_v_pow_three (i : Fin n) : torusAux_v n i ^ 3 = 1 := by
  apply Subtype.ext
  simpa [torusAux_v] using rot_pow_three i

private noncomputable def torusAux_powHom {C : Type*} [CommGroup C] {ι : Type*} [Fintype ι]
    (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) :
    Multiplicative (ι → ZMod 3) →* C where
  toFun t := ∏ r, u r ^ (Multiplicative.toAdd t r).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu r), pow_add]

private noncomputable def torusAux_psi (n : ℕ) :
    Multiplicative (Fin n → ZMod 3) →* torusAux_CN n :=
  torusAux_powHom (torusAux_v n) (torusAux_v_pow_three)

private theorem torusAux_psi_apply (a : Fin n → ZMod 3) :
    torusAux_psi n (Multiplicative.ofAdd a) = ∏ i, torusAux_v n i ^ (a i).val := rfl

private theorem torusAux_psi_single (i : Fin n) :
    torusAux_psi n (Multiplicative.ofAdd (Pi.single i 1)) = torusAux_v n i := by
  rw [torusAux_psi_apply, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
  · intro r _ hr
    rw [Pi.single_eq_of_ne hr, ZMod.val_zero, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem torusAux_rot_apply_eq_of_supported {i j : Fin n} (hij : i ≠ j) {w : V n}
    (hw : ∀ k, planeOf k ≠ j → w k = 0) : rot n i w = w := by
  funext k
  by_cases hk : planeOf k = i
  · rcases k with l | l
    · have hli : l = i := hk
      subst hli
      rw [rot_apply_inl, hw (Sum.inr l) (by simpa [planeOf] using hij),
        hw (Sum.inl l) (by simpa [planeOf] using hij)]
    · have hli : l = i := hk
      subst hli
      rw [rot_apply_inr, hw (Sum.inl l) (by simpa [planeOf] using hij),
        hw (Sum.inr l) (by simpa [planeOf] using hij)]
      simp
  · rw [rot_apply_of_ne i w hk]

private theorem torusAux_pow_apply_eq_of_apply_eq (f : V n ≃ₗ[ZMod 2] V n) {w : V n} (h : f w = w)
    (m : ℕ) : (f ^ m) w = w := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, h]

private theorem torusAux_rot_pow_apply_of_supported {i j : Fin n} (hij : i ≠ j) {w : V n}
    (hw : ∀ k, planeOf k ≠ j → w k = 0) (m : ℕ) : (rot n i ^ m) w = w :=
  torusAux_pow_apply_eq_of_apply_eq (rot n i) (torusAux_rot_apply_eq_of_supported hij hw) m

private theorem torusAux_rot_pow_single_inl_inr (j : Fin n) (m : ℕ) (hm : m = 1 ∨ m = 2) :
    ((rot n j ^ m) (Pi.single (Sum.inl j) (1 : ZMod 2) : V n)) (Sum.inr j) = 1 := by
  rcases hm with rfl | rfl
  · rw [pow_one, rot_apply_inr]
    simp [Pi.single_apply, Sum.inr_ne_inl]
  · rw [pow_two, LinearEquiv.mul_apply, rot_apply_inr, rot_apply_inl, rot_apply_inr]
    simp [Pi.single_apply, Sum.inr_ne_inl]

private theorem torusAux_coe_prod_apply_of_fixes {s : Finset (Fin n)} {f : Fin n → torusAux_CN n} {w : V n}
    (hfix : ∀ i ∈ s, (↑(f i) : V n ≃ₗ[ZMod 2] V n) w = w) :
    (↑(∏ i ∈ s, f i) : V n ≃ₗ[ZMod 2] V n) w = w := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Subgroup.coe_mul, LinearEquiv.mul_apply]
      have h1 : (↑(∏ j ∈ s, f j) : V n ≃ₗ[ZMod 2] V n) w = w :=
        ih (fun j hj => hfix j (Finset.mem_insert_of_mem hj))
      rw [h1]
      exact hfix i (Finset.mem_insert_self i s)

private theorem torusAux_psi_ne_one {a : Fin n → ZMod 3} (ha : a ≠ 0) :
    torusAux_psi n (Multiplicative.ofAdd a) ≠ 1 := by
  intro h1
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i0, hi0⟩ := hex
  set e : V n := Pi.single (Sum.inl i0) (1 : ZMod 2) with he
  have hsupp : ∀ k, planeOf k ≠ i0 → e k = 0 := by
    intro k hk
    rw [he]
    by_cases h : k = Sum.inl i0
    · subst h
      exact absurd (by simp [planeOf]) hk
    · rw [Pi.single_apply, if_neg h]
  have hsplit : torusAux_psi n (Multiplicative.ofAdd a) =
      torusAux_v n i0 ^ (a i0).val *
        ∏ i ∈ (Finset.univ : Finset (Fin n)) \ {i0}, torusAux_v n i ^ (a i).val := by
    rw [torusAux_psi_apply, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i0)]
  have hcoord :
      ((↑(torusAux_psi n (Multiplicative.ofAdd a)) : V n ≃ₗ[ZMod 2] V n) e) (Sum.inr i0) = 1 := by
    rw [hsplit, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hrest :
        (↑(∏ i ∈ (Finset.univ : Finset (Fin n)) \ {i0}, torusAux_v n i ^ (a i).val) :
          V n ≃ₗ[ZMod 2] V n) e = e := by
      apply torusAux_coe_prod_apply_of_fixes
      intro i hi
      have hne : i ≠ i0 := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
        exact hi.2
      rw [Subgroup.coe_pow, torusAux_v_coe]
      exact torusAux_rot_pow_apply_of_supported hne hsupp (a i).val
    rw [hrest, Subgroup.coe_pow, torusAux_v_coe]
    have hm0 : (a i0).val ≠ 0 := by
      simpa [ZMod.val_eq_zero] using hi0
    have hlt : (a i0).val < 3 := ZMod.val_lt _
    have hm : (a i0).val = 1 ∨ (a i0).val = 2 := by omega
    exact torusAux_rot_pow_single_inl_inr i0 (a i0).val hm
  have hzero :
      ((↑(1 : torusAux_CN n) : V n ≃ₗ[ZMod 2] V n) e) (Sum.inr i0) = 0 := by
    rw [Subgroup.coe_one]
    change e (Sum.inr i0) = 0
    rw [he, Pi.single_apply, if_neg (Sum.inr_ne_inl)]
  rw [h1] at hcoord
  rw [hzero] at hcoord
  exact zero_ne_one hcoord

private theorem torusAux_psi_injective (n : ℕ) : Function.Injective (torusAux_psi n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  rw [MonoidHom.mem_ker] at ht
  rw [Subgroup.mem_bot]
  by_contra hne
  have h0 : Multiplicative.toAdd t ≠ 0 := by
    intro h
    apply hne
    rw [← ofAdd_toAdd t, h, ofAdd_zero]
  exact torusAux_psi_ne_one h0 (by simpa [ofAdd_toAdd] using ht)

private noncomputable def torusAux_D (S : Finset (Fin n)) : Subgroup (Multiplicative (Fin n → ZMod 3)) where
  carrier := {a | ∀ i, i ∉ S → Multiplicative.toAdd a i = 0}
  one_mem' := by
    intro i _
    simp
  mul_mem' := by
    intro a b ha hb i hi
    rw [toAdd_mul, Pi.add_apply, ha i hi, hb i hi, add_zero]
  inv_mem' := by
    intro a ha i hi
    rw [toAdd_inv, Pi.neg_apply, ha i hi]
    exact neg_zero

private theorem torusAux_mem_D_iff {S : Finset (Fin n)} {a : Multiplicative (Fin n → ZMod 3)} :
    a ∈ torusAux_D S ↔ ∀ i, i ∉ S → Multiplicative.toAdd a i = 0 := Iff.rfl

private noncomputable def torusAux_K (S : Finset (Fin n)) : Subgroup (torusAux_CN n) :=
  Subgroup.closure (torusAux_v n '' (S : Set (Fin n)))

private noncomputable def torusAux_H (S : Finset (Fin n)) : Subgroup (torusAux_CN n) :=
  (torusAux_D S).map (torusAux_psi n)

private theorem torusAux_H_le_K (S : Finset (Fin n)) : torusAux_H S ≤ torusAux_K S := by
  intro x hx
  rw [torusAux_H, Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from (ofAdd_toAdd a).symm,
    torusAux_psi_apply]
  rw [torusAux_mem_D_iff] at ha
  have hsupp : ∀ i, i ∉ S → torusAux_v n i ^ (Multiplicative.toAdd a i).val = 1 := by
    intro i hi
    rw [ha i hi, ZMod.val_zero, pow_zero]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => hsupp i hi)]
  exact Subgroup.prod_mem (torusAux_K S) (fun i hi =>
    Subgroup.pow_mem (torusAux_K S) (Subgroup.subset_closure (k := torusAux_v n '' (S : Set (Fin n)))
      ⟨i, hi, rfl⟩) _)

private theorem torusAux_K_le_H (S : Finset (Fin n)) : torusAux_K S ≤ torusAux_H S := by
  rw [torusAux_K, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [torusAux_H]
  refine Subgroup.mem_map.mpr ⟨Multiplicative.ofAdd (Pi.single i 1), ?_, torusAux_psi_single i⟩
  rw [torusAux_mem_D_iff, toAdd_ofAdd]
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk hi
  rw [Pi.single_apply, if_neg hki]

private theorem torusAux_H_eq_K (S : Finset (Fin n)) : torusAux_H S = torusAux_K S :=
  le_antisymm (torusAux_H_le_K S) (torusAux_K_le_H S)

private theorem torusAux_torus_eq_K (S : Finset (Fin n)) :
    (torusAux_K S).map (torusAux_CN n).subtype = torus n S := by
  rw [torusAux_K, MonoidHom.map_closure, Set.image_image]
  rfl

private theorem torusAux_mem_H_map_iff {S : Finset (Fin n)} {x : V n ≃ₗ[ZMod 2] V n} :
    x ∈ (torusAux_H S).map (torusAux_CN n).subtype ↔
      ∃ a : Fin n → ZMod 3, (∀ i, i ∉ S → a i = 0) ∧
        x = (↑(torusAux_psi n (Multiplicative.ofAdd a)) : V n ≃ₗ[ZMod 2] V n) := by
  rw [torusAux_H, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨Multiplicative.toAdd a, ?_, ?_⟩
    · rwa [torusAux_mem_D_iff] at ha
    · rw [← hyx, ← hay, ofAdd_toAdd a]
      rfl
  · rintro ⟨a, ha, rfl⟩
    refine ⟨torusAux_psi n (Multiplicative.ofAdd a), ?_, rfl⟩
    rw [Subgroup.mem_map]
    exact ⟨Multiplicative.ofAdd a, by simpa [torusAux_mem_D_iff, toAdd_ofAdd] using ha, rfl⟩

private theorem torusAux_torus_eq_map_H (S : Finset (Fin n)) :
    torus n S = (torusAux_H S).map (torusAux_CN n).subtype := by
  apply le_antisymm
  · rw [torus, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    refine Subgroup.mem_map.mpr ⟨torusAux_v n i, ?_, rfl⟩
    rw [torusAux_H_eq_K]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩
  · intro x hx
    rw [torusAux_mem_H_map_iff] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hmem : torusAux_psi n (Multiplicative.ofAdd a) ∈ torusAux_K S := by
      rw [torusAux_psi_apply]
      have hsupp : ∀ i, i ∉ S → torusAux_v n i ^ (a i).val = 1 := by
        intro i hi
        rw [ha i hi, ZMod.val_zero, pow_zero]
      rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => hsupp i hi)]
      exact Subgroup.prod_mem (torusAux_K S) (fun i hi =>
        Subgroup.pow_mem (torusAux_K S) (Subgroup.subset_closure (k := torusAux_v n '' (S : Set (Fin n)))
          ⟨i, hi, rfl⟩) _)
    rw [← torusAux_torus_eq_K S]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

private theorem torusAux_mem_torus_iff {S : Finset (Fin n)} {x : V n ≃ₗ[ZMod 2] V n} :
    x ∈ torus n S ↔ ∃ a : Fin n → ZMod 3, (∀ i, i ∉ S → a i = 0) ∧
      x = (↑(torusAux_psi n (Multiplicative.ofAdd a)) : V n ≃ₗ[ZMod 2] V n) := by
  rw [torusAux_torus_eq_map_H, torusAux_mem_H_map_iff]

private theorem torusAux_rot_preserves_planeSpan (i : Fin n) {S : Finset (Fin n)} {w : V n}
    (hw : w ∈ planeSpan n S) : rot n i w ∈ planeSpan n S := by
  rw [mem_planeSpan] at hw ⊢
  intro k hk
  by_cases hki : planeOf k = i
  · rcases k with l | l
    · have hli : l = i := hki
      subst hli
      rw [rot_apply_inl]
      exact hw (Sum.inr l) (by simpa [planeOf] using hk)
    · have hli : l = i := hki
      subst hli
      rw [rot_apply_inr, hw (Sum.inl l) (by simpa [planeOf] using hk),
        hw (Sum.inr l) (by simpa [planeOf] using hk)]
      simp
  · rw [rot_apply_of_ne i w hki]
    exact hw k hk

private theorem torusAux_torus_le_Om (S : Finset (Fin n)) : torus n S ≤ Om n := by
  rw [torus, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact supp_le_Om n S (rot_mem_supp hi)

theorem torus_le_supp (S : Finset (Fin n)) : torus n S ≤ supp n S := by
  rw [torus, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact rot_mem_supp hi

theorem torus_mono {S T : Finset (Fin n)} (h : S ⊆ T) : torus n S ≤ torus n T := by
  intro x hx
  rw [torusAux_mem_torus_iff] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, fun i hi => ha i (fun hS => hi (h hS)), rfl⟩

theorem torus_inf (S T : Finset (Fin n)) : torus n S ⊓ torus n T = torus n (S ∩ T) := by
  apply le_antisymm
  · rintro x ⟨hxS, hxT⟩
    change x ∈ torus n S at hxS
    change x ∈ torus n T at hxT
    rw [torusAux_mem_torus_iff] at hxS hxT ⊢
    obtain ⟨a, ha, hxa⟩ := hxS
    obtain ⟨b, hb, hxb⟩ := hxT
    have hcoe : (↑(torusAux_psi n (Multiplicative.ofAdd a)) : V n ≃ₗ[ZMod 2] V n) =
        (↑(torusAux_psi n (Multiplicative.ofAdd b)) : V n ≃ₗ[ZMod 2] V n) := by
      rw [← hxa, hxb]
    have hab : torusAux_psi n (Multiplicative.ofAdd a) = torusAux_psi n (Multiplicative.ofAdd b) :=
      Subtype.ext hcoe
    have hof : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
      torusAux_psi_injective n hab
    have hfun : a = b := by
      have := congrArg Multiplicative.toAdd hof
      simpa using this
    refine ⟨a, ?_, hxa⟩
    intro i hi
    by_cases hS : i ∈ S
    · have hT : i ∉ T := by
        intro hT
        exact hi (Finset.mem_inter.mpr ⟨hS, hT⟩)
      rw [hfun]
      exact hb i hT
    · exact ha i hS
  · exact le_inf (torus_mono Finset.inter_subset_left) (torus_mono Finset.inter_subset_right)

theorem conj_mem_supp_of_mem_torus {T : Finset (Fin n)} {t g : V n ≃ₗ[ZMod 2] V n}
    (ht : t ∈ torus n Finset.univ) (hg : g ∈ supp n T) : t * g * t⁻¹ ∈ supp n T := by
  have htorus : torus n (Finset.univ : Finset (Fin n)) = torusAux_CN n := by
    simp [torus, torusAux_CN]
  have htCN : t ∈ torusAux_CN n := by rw [← htorus]; exact ht
  have hpres : ∀ f : V n ≃ₗ[ZMod 2] V n, f ∈ torusAux_CN n →
      (∀ w ∈ planeSpan n Tᶜ, f w ∈ planeSpan n Tᶜ) ∧
        (∀ w ∈ planeSpan n Tᶜ, f⁻¹ w ∈ planeSpan n Tᶜ) := by
    intro f hf
    change f ∈ Subgroup.closure (Set.range (fun i : Fin n => rot n i)) at hf
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hf
    · rintro x ⟨i, rfl⟩
      refine ⟨fun w hw => torusAux_rot_preserves_planeSpan i hw, ?_⟩
      have h3 : rot n i * rot n i ^ 2 = 1 := by
        simpa [pow_succ'] using rot_pow_three i
      have hinv : (rot n i)⁻¹ = rot n i ^ 2 := inv_eq_of_mul_eq_one_right h3
      intro w hw
      rw [hinv, pow_two, LinearEquiv.mul_apply]
      exact torusAux_rot_preserves_planeSpan i (torusAux_rot_preserves_planeSpan i hw)
    · exact ⟨fun w hw => hw, fun w hw => hw⟩
    · rintro f g _ _ ⟨hpf, hpf'⟩ ⟨hpg, hpg'⟩
      refine ⟨fun w hw => hpf (g w) (hpg w hw), ?_⟩
      intro w hw
      rw [mul_inv_rev, LinearEquiv.mul_apply]
      exact hpg' (f⁻¹ w) (hpf' w hw)
    · rintro f _ ⟨hpf, hpf'⟩
      exact ⟨hpf', hpf⟩
  obtain ⟨hpt, hpt'⟩ := hpres t htCN
  rw [mem_supp]
  refine ⟨?_, ?_⟩
  · have htOm : t ∈ Om n := torusAux_torus_le_Om Finset.univ ht
    have hgOm : g ∈ Om n := (mem_supp.1 hg).1
    exact (Om n).mul_mem ((Om n).mul_mem htOm hgOm) ((Om n).inv_mem htOm)
  · intro w hw
    have hw' : t⁻¹ w ∈ planeSpan n Tᶜ := hpt' w hw
    have hgw : g (t⁻¹ w) = t⁻¹ w := (mem_supp.1 hg).2 (t⁻¹ w) hw'
    simp only [LinearEquiv.mul_apply, hgw]
    exact t.apply_symm_apply w

variable (n) in
@[expose] def planePerm (σ : Equiv.Perm (Fin n)) : V n ≃ₗ[ZMod 2] V n :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.sumCongr σ.symm σ.symm)

theorem planePerm_apply (σ : Equiv.Perm (Fin n)) (v : V n) (k : Fin n ⊕ Fin n) :
    planePerm n σ v k = v (Sum.map σ.symm σ.symm k) :=
  rfl

theorem planePerm_mul (σ τ : Equiv.Perm (Fin n)) :
    planePerm n (σ * τ) = planePerm n σ * planePerm n τ := by
  ext v k
  simp only [LinearEquiv.mul_apply]
  rw [planePerm_apply, planePerm_apply, planePerm_apply]
  rcases k with i | i <;> rfl

theorem planePerm_one : planePerm n 1 = 1 := by
  ext v k
  rw [planePerm_apply]
  rcases k with i | i <;> rfl

theorem planePerm_inv (σ : Equiv.Perm (Fin n)) : (planePerm n σ)⁻¹ = planePerm n σ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← planePerm_mul, mul_inv_cancel, planePerm_one]

theorem planePerm_mem_Om (σ : Equiv.Perm (Fin n)) : planePerm n σ ∈ Om n := by
  rw [Om, mem_omegaGroup]
  constructor
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [Q_apply, Q_apply]
    simp only [planePerm_apply, Sum.map_inl, Sum.map_inr]
    exact Equiv.sum_comp σ.symm (fun j => v (Sum.inl j) * v (Sum.inr j) +
      (v (Sum.inl j) * v (Sum.inl j) + v (Sum.inr j) * v (Sum.inr j)))
  · let a : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
      LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ.symm
    have hcomm : commSpace (planePerm n σ) =
        Submodule.directSum (commSpace a) (commSpace a) := by
      ext x
      rw [Submodule.mem_directSum_iff]
      constructor
      · intro hx
        obtain ⟨v, hv⟩ := mem_commSpace.mp hx
        constructor
        · rw [mem_commSpace]
          refine ⟨fun i => v (Sum.inl i), ?_⟩
          funext i
          rw [← congrFun hv (Sum.inl i)]
          simp [a, planePerm_apply, LinearEquiv.funCongrLeft_apply,
            LinearMap.funLeft_apply]
        · rw [mem_commSpace]
          refine ⟨fun i => v (Sum.inr i), ?_⟩
          funext i
          rw [← congrFun hv (Sum.inr i)]
          simp [a, planePerm_apply, LinearEquiv.funCongrLeft_apply,
            LinearMap.funLeft_apply]
      · rintro ⟨hx1, hx2⟩
        obtain ⟨p, hp⟩ := mem_commSpace.mp hx1
        obtain ⟨q, hq⟩ := mem_commSpace.mp hx2
        rw [mem_commSpace]
        refine ⟨Sum.elim p q, ?_⟩
        funext k
        rcases k with i | i
        · rw [← congrFun hp i]
          simp [a, planePerm_apply, Sum.elim, LinearEquiv.funCongrLeft_apply,
            LinearMap.funLeft_apply]
        · rw [← congrFun hq i]
          simp [a, planePerm_apply, Sum.elim, LinearEquiv.funCongrLeft_apply,
            LinearMap.funLeft_apply]
    have hfin : Module.finrank (ZMod 2) (commSpace (planePerm n σ)) =
        Module.finrank (ZMod 2) (commSpace a × commSpace a) := by
      rw [hcomm]
      exact LinearEquiv.finrank_eq
        (Submodule.directSumEquivProd (commSpace a) (commSpace a))
    rw [hfin, Module.finrank_prod]
    exact ⟨_, rfl⟩

theorem planePerm_conj_rot (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    planePerm n σ * rot n i * (planePerm n σ)⁻¹ = rot n (σ i) := by
  have hpQ : ∀ v : V n, Q n (planePerm n σ v) = Q n v := by
    intro v
    rw [Q_apply, Q_apply]
    simp only [planePerm_apply, Sum.map_inl, Sum.map_inr]
    exact Equiv.sum_comp σ.symm (fun j => v (Sum.inl j) * v (Sum.inr j) +
      (v (Sum.inl j) * v (Sum.inl j) + v (Sum.inr j) * v (Sum.inr j)))
  have hsingle (k : Fin n ⊕ Fin n) :
      planePerm n σ (Pi.single k (1 : ZMod 2)) = Pi.single (Sum.map σ σ k) 1 := by
    ext j
    rw [planePerm_apply]
    rcases k with i | i <;> rcases j with j | j <;>
      simp [Pi.single_apply, Sum.map_inl, Sum.map_inr, Equiv.symm_apply_eq]
  have hcrefl (k : Fin n ⊕ Fin n) :
      planePerm n σ * crefl n k * (planePerm n σ)⁻¹ = crefl n (Sum.map σ σ k) := by
    let e : QuadraticMap.IsometryEquiv (Q n) (Q n) :=
      { toLinearEquiv := planePerm n σ, map_app' := hpQ }
    haveI : Invertible (Q n (e (Pi.single k (1 : ZMod 2)))) := by
      change Invertible (Q n (planePerm n σ (Pi.single k (1 : ZMod 2))))
      rw [hsingle k]
      infer_instance
    have hrefl : TauCeti.QuadraticMap.reflection (Q n) (e (Pi.single k (1 : ZMod 2))) =
        crefl n (Sum.map σ σ k) := by
      apply LinearEquiv.ext
      intro x
      rw [crefl, TauCeti.QuadraticMap.reflection_apply,
        TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, invOf_eq_inv]
      change x - ((Q n (planePerm n σ (Pi.single k 1)))⁻¹ *
        QuadraticMap.polar (Q n) (planePerm n σ (Pi.single k 1)) x) •
        planePerm n σ (Pi.single k 1) = _
      rw [hsingle]
    have h := TauCeti.QuadraticMap.reflection_map (Q₁ := Q n) (Q₂ := Q n) e
      (Pi.single k (1 : ZMod 2))
    rw [hrefl] at h
    apply LinearEquiv.ext
    intro x
    exact (congrArg (fun f : V n ≃ₗ[ZMod 2] V n => f x) h).symm
  calc
    planePerm n σ * rot n i * (planePerm n σ)⁻¹
        = (planePerm n σ * crefl n (Sum.inl i) * (planePerm n σ)⁻¹) *
          (planePerm n σ * crefl n (Sum.inr i) * (planePerm n σ)⁻¹) := by
            rw [rot]
            group
    _ = crefl n (Sum.map σ σ (Sum.inl i)) * crefl n (Sum.map σ σ (Sum.inr i)) := by
            rw [hcrefl, hcrefl]
    _ = rot n (σ i) := by
            simp [rot, Sum.map_inl, Sum.map_inr]

theorem planePerm_conj_mem_supp (σ : Equiv.Perm (Fin n)) {S : Finset (Fin n)}
    {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ supp n S) :
    planePerm n σ * g * (planePerm n σ)⁻¹ ∈ supp n (S.map σ.toEmbedding) := by
  rw [mem_supp] at hg ⊢
  refine ⟨?_, ?_⟩
  · exact (Om n).mul_mem ((Om n).mul_mem (planePerm_mem_Om σ) hg.1)
      ((Om n).inv_mem (planePerm_mem_Om σ))
  · intro v hv
    rw [mem_planeSpan] at hv
    have hqv : planePerm n σ⁻¹ v ∈ planeSpan n Sᶜ := by
      rw [mem_planeSpan]
      intro l hl
      have hl' : planeOf l ∈ S := by simpa using hl
      rw [planePerm_apply]
      have hmem : planeOf (Sum.map σ σ l) ∈ S.map σ.toEmbedding := by
        rcases l with i | i <;>
          simp only [Sum.map_inl, Sum.map_inr, planeOf] at hl' ⊢
        · exact Finset.mem_map.2 ⟨i, hl', by simp⟩
        · exact Finset.mem_map.2 ⟨i, hl', by simp⟩
      have hmem' : planeOf (Sum.map σ σ l) ∉ (S.map σ.toEmbedding)ᶜ := by
        simpa using hmem
      change v (Sum.map σ σ l) = 0
      exact hv (Sum.map σ σ l) hmem'
    have hfix : g (planePerm n σ⁻¹ v) = planePerm n σ⁻¹ v := hg.2 _ hqv
    have hp_inv : (planePerm n σ)⁻¹ = planePerm n σ⁻¹ := by
      have h1 : planePerm n (1 : Equiv.Perm (Fin n)) = 1 := by
        have hsymm : (1 : Equiv.Perm (Fin n)).symm = 1 := rfl
        have hcongr : Equiv.sumCongr (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n)) = 1 := by
          simpa using (Equiv.sumCongr_refl (α := Fin n) (β := Fin n))
        rw [planePerm, hsymm, hcongr]
        rfl
      have hmul : planePerm n σ * planePerm n σ⁻¹ = 1 := by
        rw [← planePerm_mul, mul_inv_cancel, h1]
      exact inv_eq_of_mul_eq_one_right hmul
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hp_inv, hfix, ← hp_inv]
    simp

end

end CFSG.ClassicalGroups.Orthogonal.SixPlane
