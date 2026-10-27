module
public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
public import CFSG.RankThree.OrthogonalInvolutions.DicksonReflect

public section
namespace CFSG.ClassicalGroups.Orthogonal.SixPlane
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
noncomputable section
variable {n : ℕ}

private theorem toral_lead_fix_complement {S : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n}
    (hfix : ∀ k : Fin n ⊕ Fin n, planeOf k ∉ S →
      g (Pi.single k (1 : ZMod 2)) = Pi.single k 1) :
    ∀ v ∈ planeSpan n Sᶜ, g v = v := by
  intro v hv
  have hexp : (∑ k : Fin n ⊕ Fin n, v k • Pi.single k (1 : ZMod 2)) = v := by
    funext j
    simp [Pi.single_apply]
  rw [← hexp, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : planeOf k ∈ S
  · have hzero : v k = 0 := (mem_planeSpan.mp hv) k (by simpa using h)
    simp [hzero]
  · rw [map_smul, hfix k h]

private theorem lead_rot_single_inl (i : Fin n) :
    rot n i (Pi.single (Sum.inl i) (1 : ZMod 2)) = Pi.single (Sum.inr i) 1 := by
  funext k
  rcases k with j | j <;> by_cases h : j = i
  · subst j; simp [rot_apply_inl]
  · rw [rot_apply_of_ne i _ (by simpa [planeOf] using h)]
    simp [Pi.single_apply, h]
  · subst j; simp [rot_apply_inr]
  · rw [rot_apply_of_ne i _ (by simpa [planeOf] using h)]
    simp [Pi.single_apply, h]

private theorem lead_rot_single_inr (i : Fin n) :
    rot n i (Pi.single (Sum.inr i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  funext k
  rcases k with j | j <;> by_cases h : j = i
  · subst j; simp [rot_apply_inl]
  · rw [rot_apply_of_ne i _ (by simpa [planeOf] using h)]
    simp [Pi.single_apply, h]
  · subst j; simp [rot_apply_inr]
  · rw [rot_apply_of_ne i _ (by simpa [planeOf] using h)]
    simp [Pi.single_apply, h]

private theorem toral_lead_off_plane {g : V n ≃ₗ[ZMod 2] V n} {i : Fin n}
    (hc : Commute g (rot n i)) {k : Fin n ⊕ Fin n} (hk : planeOf k ≠ i) :
    g (Pi.single (Sum.inl i) (1 : ZMod 2)) k = 0 ∧
      g (Pi.single (Sum.inr i) (1 : ZMod 2)) k = 0 := by
  have h1 := congrArg (fun a : V n ≃ₗ[ZMod 2] V n =>
    a (Pi.single (Sum.inl i) (1 : ZMod 2))) hc.eq
  simp only [LinearEquiv.mul_apply, lead_rot_single_inl] at h1
  have h2 := congrArg (fun a : V n ≃ₗ[ZMod 2] V n =>
    a (Pi.single (Sum.inr i) (1 : ZMod 2))) hc.eq
  simp only [LinearEquiv.mul_apply, lead_rot_single_inr, map_add] at h2
  have h1k := congrFun h1 k
  have h2k := congrFun h2 k
  rw [rot_apply_of_ne i _ hk] at h1k
  rw [rot_apply_of_ne i _ hk] at h2k
  simp only [Pi.add_apply] at h2k
  have hz : g (Pi.single (Sum.inl i) (1 : ZMod 2)) k = 0 := by
    exact add_right_cancel (h2k.trans (zero_add _).symm)
  exact ⟨hz, h1k.trans hz⟩

private theorem toral_lead_exists_pow_rot {g : V n ≃ₗ[ZMod 2] V n} {i : Fin n}
    (hc : Commute g (rot n i)) :
    ∃ m : ℕ, m < 3 ∧
      g (Pi.single (Sum.inl i) (1 : ZMod 2)) = (rot n i ^ m) (Pi.single (Sum.inl i) 1) ∧
      g (Pi.single (Sum.inr i) (1 : ZMod 2)) = (rot n i ^ m) (Pi.single (Sum.inr i) 1) := by
  have hbits : ∀ a b : ZMod 2,
      (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by decide
  have hne : ¬ (g (Pi.single (Sum.inl i) (1 : ZMod 2)) (Sum.inl i) = 0 ∧
      g (Pi.single (Sum.inl i) (1 : ZMod 2)) (Sum.inr i) = 0) := by
    rintro ⟨ha, hb⟩
    have hz : g (Pi.single (Sum.inl i) (1 : ZMod 2)) = 0 := by
      funext k
      rcases k with j | j <;> by_cases h : j = i
      · subst j; exact ha
      · exact (toral_lead_off_plane hc (by simpa [planeOf] using h)).1
      · subst j; exact hb
      · exact (toral_lead_off_plane hc (by simpa [planeOf] using h)).1
    have he : Pi.single (Sum.inl i) (1 : ZMod 2) = (0 : V n) :=
      g.injective (hz.trans (map_zero g).symm)
    have h10 : (1 : ZMod 2) = 0 := by simpa using congrFun he (Sum.inl i)
    exact one_ne_zero h10
  have hex : ∃ m : ℕ, m < 3 ∧
      g (Pi.single (Sum.inl i) (1 : ZMod 2)) = (rot n i ^ m) (Pi.single (Sum.inl i) 1) := by
    rcases hbits (g (Pi.single (Sum.inl i) 1) (Sum.inl i))
      (g (Pi.single (Sum.inl i) 1) (Sum.inr i)) with H | H | H | H
    · exact (hne H).elim
    · refine ⟨0, by omega, ?_⟩
      funext k
      rcases k with j | j <;> by_cases h : j = i
      · subst j; simp [H.1, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inl j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inl j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
      · subst j; simp [H.2, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inr j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inr j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
    · refine ⟨1, by omega, ?_⟩
      funext k
      rcases k with j | j <;> by_cases h : j = i
      · subst j; simp [H.1, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inl j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inl j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
      · subst j; simp [H.2, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inr j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inr j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
    · refine ⟨2, by omega, ?_⟩
      funext k
      rcases k with j | j <;> by_cases h : j = i
      · subst j; simp [H.1, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inl j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inl j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
      · subst j; simp [H.2, pow_two, LinearEquiv.mul_apply, rot_apply_inl, rot_apply_inr]
      · have hgk := (toral_lead_off_plane hc (k := Sum.inr j) (by simpa [planeOf] using h)).1
        simp only [pow_two, LinearEquiv.mul_apply, pow_zero, pow_one]
        repeat rw [rot_apply_of_ne i _ (k := Sum.inr j) (by simpa [planeOf] using h)]
        simp [hgk, Pi.single_apply, h]
  obtain ⟨m, hm, he⟩ := hex
  refine ⟨m, hm, he, ?_⟩
  have h1 := congrArg (fun a : V n ≃ₗ[ZMod 2] V n =>
    a (Pi.single (Sum.inl i) (1 : ZMod 2))) hc.eq
  simp only [LinearEquiv.mul_apply, lead_rot_single_inl] at h1
  rw [h1, he]
  have hp := congrArg (fun a : V n ≃ₗ[ZMod 2] V n =>
    a (Pi.single (Sum.inl i) (1 : ZMod 2))) ((Commute.refl (rot n i)).pow_right m).eq
  simpa only [LinearEquiv.mul_apply, lead_rot_single_inl] using hp

private theorem lead_single_mem_complement {S : Finset (Fin n)} {k : Fin n ⊕ Fin n}
    (hk : planeOf k ∉ S) : Pi.single k (1 : ZMod 2) ∈ planeSpan n Sᶜ := by
  apply mem_planeSpan.mpr
  intro l hl
  by_cases h : l = k
  · subst l
    exact (hl (Finset.mem_compl.mpr hk)).elim
  · simp [Pi.single_apply, h]

theorem mem_torus_of_fix_compl_of_commute {S : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n}
    (hg : ∀ v ∈ planeSpan n Sᶜ, g v = v) (hc : ∀ i ∈ S, Commute g (rot n i)) :
    g ∈ torus n S := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty =>
      have h1 : g = 1 := LinearEquiv.ext fun v => hg v (by simp [mem_planeSpan])
      rw [h1]
      exact (torus n ∅).one_mem
  | @insert i S hi ih =>
      obtain ⟨m, hm, he1, he2⟩ := toral_lead_exists_pow_rot (hc i (Finset.mem_insert_self i S))
      let g' : V n ≃ₗ[ZMod 2] V n := (rot n i ^ m)⁻¹ * g
      have hfix : ∀ k : Fin n ⊕ Fin n, planeOf k ∉ S →
          g' (Pi.single k (1 : ZMod 2)) = Pi.single k 1 := by
        intro k hk
        apply (rot n i ^ m).injective
        have hcancel : (rot n i ^ m) (g' (Pi.single k (1 : ZMod 2))) =
            g (Pi.single k 1) := by simp [g', LinearEquiv.mul_apply]
        rw [hcancel]
        by_cases hki : planeOf k = i
        · rcases k with j | j
          · change j = i at hki
            subst j
            exact he1
          · change j = i at hki
            subst j
            exact he2
        · have hins : planeOf k ∉ insert i S := by simpa using And.intro hki hk
          have hgk := hg (Pi.single k 1) (lead_single_mem_complement hins)
          have hrmem : rot n i ^ m ∈ supp n ({i} : Finset (Fin n)) :=
            (supp n {i}).pow_mem (rot_mem_supp (Finset.mem_singleton_self i)) m
          have hrk := (mem_supp.mp hrmem).2 (Pi.single k 1)
            (lead_single_mem_complement (by simpa using hki))
          exact hgk.trans hrk.symm
      have hg' : g' ∈ torus n S := ih (toral_lead_fix_complement hfix) (by
        intro j hj
        exact ((commute_rot i j).pow_left m).inv_left.mul_left
          (hc j (Finset.mem_insert_of_mem hj)))
      have hri : rot n i ∈ torus n (insert i S) :=
        Subgroup.subset_closure ⟨i, Finset.mem_insert_self i S, rfl⟩
      have hprod := (torus n (insert i S)).mul_mem
        ((torus n (insert i S)).pow_mem hri m)
        (torus_mono (Finset.subset_insert i S) hg')
      simpa [g', mul_assoc] using hprod

theorem mem_torus_of_commute {S : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ supp n S)
    (hc : ∀ i ∈ S, Commute g (rot n i)) : g ∈ torus n S :=
  mem_torus_of_fix_compl_of_commute (mem_supp.mp hg).2 hc

private lemma invOf_Q_single (k : Fin n ⊕ Fin n) :
    ⅟(Q n (Pi.single k (1 : ZMod 2))) = 1 := by
  rw [invOf_eq_inv, Q_single, inv_one]

private lemma crefl_inl_apply (i : Fin n) (v : V n) :
    crefl n (Sum.inl i) v =
      v + v (Sum.inr i) • Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [crefl, TauCeti.QuadraticMap.reflection_apply, polar_single_inl_apply, invOf_Q_single]
  rw [ZModModule.sub_eq_add, one_mul]

private lemma crefl_inl_apply_single_inl (i : Fin n) :
    crefl n (Sum.inl i) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [crefl_inl_apply]
  simp [Pi.single_apply, Sum.inr_ne_inl]

private lemma crefl_inl_apply_single_inr (i : Fin n) :
    crefl n (Sum.inl i) (Pi.single (Sum.inr i) (1 : ZMod 2)) =
      Pi.single (Sum.inr i) (1 : ZMod 2) + Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [crefl_inl_apply]
  simp [Pi.single_apply, Sum.inr_ne_inl]

private lemma crefl_inl_apply_of_eq_zero {i : Fin n} {v : V n}
    (hv : v (Sum.inr i) = 0) : crefl n (Sum.inl i) v = v := by
  rw [crefl_inl_apply, hv, zero_smul, add_zero]

private theorem prod_crefl_mem_Om (k₁ k₂ : Fin n ⊕ Fin n) :
    crefl n k₁ * crefl n k₂ ∈ Om n := by
  have h1 : crefl n k₁ = reflect (Q n) (Pi.single k₁ (1 : ZMod 2)) :=
    (reflect_eq_reflection (Q := Q n) (v := Pi.single k₁ (1 : ZMod 2))).symm
  have h2 : crefl n k₂ = reflect (Q n) (Pi.single k₂ (1 : ZMod 2)) :=
    (reflect_eq_reflection (Q := Q n) (v := Pi.single k₂ (1 : ZMod 2))).symm
  have hl : ∀ a ∈ [(Pi.single k₁ (1 : ZMod 2) : V n),
      (Pi.single k₂ (1 : ZMod 2) : V n)], Q n a ≠ 0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rw [Q_single] <;> exact one_ne_zero
  have hev : Even [(Pi.single k₁ (1 : ZMod 2) : V n),
      (Pi.single k₂ (1 : ZMod 2) : V n)].length := by simp
  have hprod := CFSG.RankThree.OrthogonalInvolutions.prod_reflect_mem_omegaGroup
    (Q n) (nondegenerate_Q n)
    [(Pi.single k₁ (1 : ZMod 2) : V n), (Pi.single k₂ (1 : ZMod 2) : V n)] hl hev
  simpa [h1, h2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] using hprod

private theorem crefl_mul_crefl_mem_supp {S : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ S) (hj : j ∈ S) :
    crefl n (Sum.inl i) * crefl n (Sum.inl j) ∈ supp n S := by
  rw [mem_supp]
  constructor
  · exact prod_crefl_mem_Om (Sum.inl i) (Sum.inl j)
  · intro v hv
    rw [LinearEquiv.mul_apply]
    have hfix_j : crefl n (Sum.inl j) v = v := by
      apply crefl_inl_apply_of_eq_zero
      exact (mem_planeSpan.mp hv) (Sum.inr j) (by simp [planeOf, Finset.mem_compl, hj])
    have hfix_i : crefl n (Sum.inl i) v = v := by
      apply crefl_inl_apply_of_eq_zero
      exact (mem_planeSpan.mp hv) (Sum.inr i) (by simp [planeOf, Finset.mem_compl, hi])
    rw [hfix_j, hfix_i]

private theorem commute_rot_of_mem_torus {S : Finset (Fin n)}
    {t : V n ≃ₗ[ZMod 2] V n} (ht : t ∈ torus n S) (j : Fin n) :
    Commute t (rot n j) := by
  rw [torus] at ht
  refine Subgroup.closure_induction (p := fun x _ => Commute x (rot n j)) ?_ ?_ ?_ ?_ ht
  · rintro x ⟨i, _hi, rfl⟩
    exact commute_rot i j
  · exact Commute.one_left (rot n j)
  · intro x y _hx _hy hx' hy'
    exact hx'.mul_left hy'
  · intro x _hx hx'
    exact hx'.inv_left

private theorem rot_sq_apply_single_inl (i : Fin n) :
    (rot n i ^ 2) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  rw [pow_two, LinearEquiv.mul_apply, lead_rot_single_inl, lead_rot_single_inr]

private lemma crefl_mul_apply_single_inl {i j : Fin n} :
    (crefl n (Sum.inl i) * crefl n (Sum.inl j))
        (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [LinearEquiv.mul_apply]
  have hfix : crefl n (Sum.inl j) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) (1 : ZMod 2) := by
    apply crefl_inl_apply_of_eq_zero
    simp [Pi.single_apply]
  rw [hfix, crefl_inl_apply_single_inl]

private lemma crefl_mul_apply_single_inr {i j : Fin n} (hij : i ≠ j) :
    (crefl n (Sum.inl i) * crefl n (Sum.inl j))
        (Pi.single (Sum.inr i) (1 : ZMod 2)) =
      Pi.single (Sum.inr i) (1 : ZMod 2) + Pi.single (Sum.inl i) (1 : ZMod 2) := by
  rw [LinearEquiv.mul_apply]
  have hfix : crefl n (Sum.inl j) (Pi.single (Sum.inr i) (1 : ZMod 2)) =
      Pi.single (Sum.inr i) (1 : ZMod 2) := by
    apply crefl_inl_apply_of_eq_zero
    have hne : (Sum.inr i : Fin n ⊕ Fin n) ≠ (Sum.inr j : Fin n ⊕ Fin n) :=
      fun h => hij (Sum.inr.inj h)
    simp [Pi.single_apply, hne]
  rw [hfix, crefl_inl_apply_single_inr]

private theorem fix_single_inl_inr_of_mem_torus_of_commute
    {S T : Finset (Fin n)} (hT : 2 ≤ T.card) {t : V n ≃ₗ[ZMod 2] V n}
    (ht : t ∈ torus n S) (hc : ∀ g ∈ supp n T, Commute t g)
    {i : Fin n} (hi : i ∈ T) :
    t (Pi.single (Sum.inl i) (1 : ZMod 2)) = Pi.single (Sum.inl i) 1 ∧
      t (Pi.single (Sum.inr i) (1 : ZMod 2)) = Pi.single (Sum.inr i) 1 := by
  classical
  obtain ⟨j, hjT, hji⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) i
  have hij : i ≠ j := fun h => hji h.symm
  have hc_supp : crefl n (Sum.inl i) * crefl n (Sum.inl j) ∈ supp n T :=
    crefl_mul_crefl_mem_supp hi hjT
  have hct : Commute t (crefl n (Sum.inl i) * crefl n (Sum.inl j)) := hc _ hc_supp
  obtain ⟨m, hm3, hm_inl, hm_inr⟩ :=
    toral_lead_exists_pow_rot (g := t) (i := i)
      (commute_rot_of_mem_torus ht i)
  have hct_apply : ∀ x : V n,
      t ((crefl n (Sum.inl i) * crefl n (Sum.inl j)) x) =
        (crefl n (Sum.inl i) * crefl n (Sum.inl j)) (t x) := by
    intro x
    have h := congrArg (fun f : V n ≃ₗ[ZMod 2] V n => f x) hct.eq
    simpa only [LinearEquiv.mul_apply] using h
  have hmain : (rot n i ^ m) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      (crefl n (Sum.inl i) * crefl n (Sum.inl j))
        ((rot n i ^ m) (Pi.single (Sum.inl i) (1 : ZMod 2))) := by
    have h := hct_apply (Pi.single (Sum.inl i) (1 : ZMod 2))
    rw [crefl_mul_apply_single_inl, hm_inl] at h
    exact h
  have hsum : (crefl n (Sum.inl i) * crefl n (Sum.inl j))
      (Pi.single (Sum.inl i) (1 : ZMod 2) + Pi.single (Sum.inr i) (1 : ZMod 2)) =
      Pi.single (Sum.inr i) (1 : ZMod 2) := by
    rw [map_add, crefl_mul_apply_single_inl, crefl_mul_apply_single_inr hij]
    rw [add_comm (Pi.single (Sum.inr i) (1 : ZMod 2) : V n)
      (Pi.single (Sum.inl i) (1 : ZMod 2) : V n)]
    rw [← add_assoc, ZModModule.add_self, zero_add]
  have hm0 : m = 0 := by
    interval_cases m
    · rfl
    · exfalso
      have h1 : (rot n i ^ 1) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
          Pi.single (Sum.inr i) (1 : ZMod 2) := by
        rw [pow_one, lead_rot_single_inl]
      rw [h1, crefl_mul_apply_single_inr hij] at hmain
      have hcoord := congrFun hmain (Sum.inl i)
      simp [Pi.single_apply, Sum.inr_ne_inl] at hcoord
    · exfalso
      have h2 : (rot n i ^ 2) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
          Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 :=
        rot_sq_apply_single_inl i
      rw [h2, hsum] at hmain
      have hcoord := congrFun hmain (Sum.inl i)
      simp [Pi.single_apply] at hcoord
  refine ⟨?_, ?_⟩
  · rw [hm0, pow_zero] at hm_inl
    simpa using hm_inl
  · rw [hm0, pow_zero] at hm_inr
    simpa using hm_inr

theorem mem_torus_sdiff_of_commute {S T : Finset (Fin n)} (hT : 2 ≤ T.card)
    {t : V n ≃ₗ[ZMod 2] V n} (ht : t ∈ torus n S)
    (hc : ∀ g ∈ supp n T, Commute t g) :
    t ∈ torus n (S \ T) := by
  classical
  have hbasis : ∀ k : Fin n ⊕ Fin n, planeOf k ∈ T →
      t (Pi.single k (1 : ZMod 2)) = Pi.single k 1 := by
    rintro (i | i) hi
    · exact (fix_single_inl_inr_of_mem_torus_of_commute hT ht hc hi).1
    · exact (fix_single_inl_inr_of_mem_torus_of_commute hT ht hc hi).2
  have hfixT : ∀ v ∈ planeSpan n T, t v = v :=
    by
      have hfix := toral_lead_fix_complement (S := Tᶜ) (g := t) (by
        intro k hk
        exact hbasis k (by simpa using hk))
      simpa using hfix
  have hcommT : ∀ i ∈ Tᶜ, Commute t (rot n i) := fun i _ =>
    commute_rot_of_mem_torus ht i
  have htT : t ∈ torus n Tᶜ :=
    mem_torus_of_fix_compl_of_commute (S := Tᶜ) (by simpa using hfixT) hcommT
  rw [Finset.sdiff_eq_inter_compl, ← torus_inf]
  exact ⟨ht, htT⟩

private theorem three_dvd_of_rot_pow_fix {i : Fin n} {j : ℕ}
    (h : (rot n i ^ j) (Pi.single (Sum.inl i) (1 : ZMod 2)) = Pi.single (Sum.inl i) 1) :
    3 ∣ j := by
  have hj : rot n i ^ j = rot n i ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, rot_pow_three, one_pow, one_mul]
  rw [hj] at h
  have hlt : j % 3 < 3 := Nat.mod_lt j (by norm_num)
  refine Nat.dvd_of_mod_eq_zero ?_
  interval_cases hm : j % 3
  · rfl
  · exfalso
    rw [pow_one, lead_rot_single_inl] at h
    have := congrFun h (Sum.inl i)
    simp at this
  · exfalso
    rw [rot_sq_apply_single_inl] at h
    have := congrFun h (Sum.inr i)
    simp at this

theorem fix_single_of_two_of_commute_rot {g : V n ≃ₗ[ZMod 2] V n} {i : Fin n} {k : ℕ}
    (hg : g ^ (2 ^ k) = 1) (hc : Commute g (rot n i)) :
    g (Pi.single (Sum.inl i) (1 : ZMod 2)) = Pi.single (Sum.inl i) 1 ∧
      g (Pi.single (Sum.inr i) (1 : ZMod 2)) = Pi.single (Sum.inr i) 1 := by
  obtain ⟨m, hm, he1, he2⟩ := toral_lead_exists_pow_rot hc
  obtain ⟨h, hh⟩ : ∃ h : V n ≃ₗ[ZMod 2] V n, h = (rot n i ^ m)⁻¹ * g := ⟨_, rfl⟩
  have hgh : g = rot n i ^ m * h := by rw [hh, mul_inv_cancel_left]
  have hfix : h (Pi.single (Sum.inl i) (1 : ZMod 2)) = Pi.single (Sum.inl i) 1 := by
    rw [hh, LinearEquiv.mul_apply, he1, ← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hcomm : Commute (rot n i ^ m) h := by
    rw [hh]
    exact ((Commute.refl (rot n i)).pow_pow m m).inv_right.mul_right (hc.symm.pow_left m)
  have hpowfix : ∀ N : ℕ, (h ^ N) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [pow_succ, LinearEquiv.mul_apply, hfix, ih]
  have hrot : (rot n i ^ (m * 2 ^ k)) (Pi.single (Sum.inl i) (1 : ZMod 2)) =
      Pi.single (Sum.inl i) 1 := by
    have h1 : g ^ (2 ^ k) = rot n i ^ (m * 2 ^ k) * h ^ (2 ^ k) := by
      rw [hgh, hcomm.mul_pow, pow_mul]
    have h2 := congrArg (fun f : V n ≃ₗ[ZMod 2] V n => f (Pi.single (Sum.inl i) (1 : ZMod 2)))
      h1
    simp only [hg, LinearEquiv.coe_one, id_eq, LinearEquiv.mul_apply, hpowfix] at h2
    exact h2.symm
  have h3 : 3 ∣ m * 2 ^ k := three_dvd_of_rot_pow_fix hrot
  have hm0 : m = 0 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h3m : 3 ∣ m := hcop.dvd_of_dvd_mul_right h3
    omega
  subst hm0
  simpa using And.intro he1 he2

theorem mem_supp_of_two_of_commute_rot {A T : Finset (Fin n)} {g : V n ≃ₗ[ZMod 2] V n} {k : ℕ}
    (hg : g ∈ supp n A) (h2 : g ^ (2 ^ k) = 1) (hc : ∀ j ∈ A, j ∉ T → Commute g (rot n j)) :
    g ∈ supp n T := by
  rw [mem_supp] at hg ⊢
  refine ⟨hg.1, toral_lead_fix_complement fun l hl => ?_⟩
  by_cases hlA : planeOf l ∈ A
  · obtain ⟨hinl, hinr⟩ := fix_single_of_two_of_commute_rot h2 (hc _ hlA hl)
    rcases l with j | j
    · exact hinl
    · exact hinr
  · exact hg.2 _ (lead_single_mem_complement hlA)

end
end CFSG.ClassicalGroups.Orthogonal.SixPlane
