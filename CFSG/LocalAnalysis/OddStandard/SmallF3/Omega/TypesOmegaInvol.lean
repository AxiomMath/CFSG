module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_isSquare_units_zmod3_eq_one (u : (ZMod 3)ˣ) : IsSquare u ↔ u = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    rcases aux_units_zmod3 v with rfl | rfl <;> rw [hv] <;> decide
  · rintro rfl
    exact ⟨1, by simp⟩

private lemma aux_neg_one_pow_units_eq_or (n : ℕ) :
    (-1 : ℤˣ) ^ n = 1 ∨ (-1 : ℤˣ) ^ n = -1 := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h]
    · right; rw [one_mul]
    · left; decide

private lemma aux_neg_one_pow_units_eq_one_iff (n : ℕ) : (-1 : ℤˣ) ^ n = 1 ↔ Even n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.even_add_one]
    constructor
    · intro h hn
      rw [ih.mpr hn, one_mul] at h
      exact (by decide : (-1 : ℤˣ) ≠ 1) h
    · intro hn
      have hn' : (-1 : ℤˣ) ^ n = -1 := by
        rcases aux_neg_one_pow_units_eq_or n with h | h
        · exact absurd (ih.mp h) hn
        · exact h
      rw [hn']
      decide

private lemma aux_neg_one_pow_zmod3_eq_or (n : ℕ) :
    (-1 : (ZMod 3)ˣ) ^ n = 1 ∨ (-1 : (ZMod 3)ˣ) ^ n = -1 := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h]
    · right; rw [one_mul]
    · left; decide

private lemma aux_neg_one_pow_zmod3_eq_one_iff (n : ℕ) : (-1 : (ZMod 3)ˣ) ^ n = 1 ↔ Even n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.even_add_one]
    constructor
    · intro h hn
      rw [ih.mpr hn, one_mul] at h
      exact (by decide : (-1 : (ZMod 3)ˣ) ≠ 1) h
    · intro hn
      have hn' : (-1 : (ZMod 3)ˣ) ^ n = -1 := by
        rcases aux_neg_one_pow_zmod3_eq_or n with h | h
        · exact absurd (ih.mp h) hn
        · exact h
      rw [hn']
      decide

private lemma aux_nsmul_squareClass_neg_one_eq_zero_iff_even (n : ℕ) :
    n • squareClass (-1 : (ZMod 3)ˣ) = 0 ↔ Even n := by
  rw [← squareClass_pow, squareClass_eq_zero_iff, aux_isSquare_units_zmod3_eq_one]
  exact aux_neg_one_pow_zmod3_eq_one_iff n

private lemma aux_nsmul_eq_zero_or_self (n : ℕ) :
    n • squareClass (-1 : (ZMod 3)ˣ) = 0 ∨
      n • squareClass (-1 : (ZMod 3)ˣ) = squareClass (-1 : (ZMod 3)ˣ) := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    rw [succ_nsmul]
    rcases ih with h | h
    · right; rw [h, zero_add]
    · left
      rw [h]
      simpa [two_nsmul] using ZModModule.char_nsmul_eq_zero 2
        (squareClass (-1 : (ZMod 3)ˣ))

private lemma aux_choose_two_two_mul (k : ℕ) :
    (2 * k).choose 2 = k * (2 * k - 1) := by
  rw [Nat.choose_two_right]
  rw [show 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) by rw [mul_assoc]]
  exact Nat.mul_div_right (k * (2 * k - 1)) (by norm_num)

private lemma aux_odd_two_mul_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 * k - 1) := by
  refine ⟨k - 1, ?_⟩
  omega

private lemma aux_choose_two_parity {r : ℕ} (hr : Even r) :
    Even (r.choose 2) ↔ Even (r / 2) := by
  rw [Nat.even_iff, Nat.even_iff]
  conv_lhs => rw [← Nat.two_mul_div_two_of_even hr]
  rw [aux_choose_two_two_mul, ← Nat.even_iff, ← Nat.even_iff, Nat.even_mul]
  constructor
  · rintro (h | h)
    · exact h
    · rcases Nat.eq_zero_or_pos (r / 2) with h0 | hpos
      · rw [h0]; exact ⟨0, by simp⟩
      · exact absurd h (Nat.not_even_iff_odd.mpr (aux_odd_two_mul_sub_one hpos))
  · intro h; exact Or.inl h

private lemma aux_choose_two_nsmul_eq (r : ℕ) (hr : Even r) :
    r.choose 2 • squareClass (-1 : (ZMod 3)ˣ) =
      (r / 2) • squareClass (-1 : (ZMod 3)ˣ) := by
  have hpar : Even (r.choose 2) ↔ Even (r / 2) := aux_choose_two_parity hr
  have hself : ∀ {n : ℕ}, n • squareClass (-1 : (ZMod 3)ˣ) = squareClass (-1 : (ZMod 3)ˣ) →
      Odd n := fun h => Nat.not_even_iff_odd.mp fun he => by
    have h0 := (aux_nsmul_squareClass_neg_one_eq_zero_iff_even _).mpr he
    rw [h] at h0
    exact aux_squareClass_neg_one_ne_zero h0
  rcases aux_nsmul_eq_zero_or_self (r.choose 2) with h1 | h1 <;>
    rcases aux_nsmul_eq_zero_or_self (r / 2) with h2 | h2
  · rw [h1, h2]
  · exfalso
    exact (Nat.not_even_iff_odd.mpr (hself h2))
      (hpar.mp ((aux_nsmul_squareClass_neg_one_eq_zero_iff_even _).mp h1))
  · exfalso
    exact (Nat.not_even_iff_odd.mpr (hself h1))
      (hpar.mpr ((aux_nsmul_squareClass_neg_one_eq_zero_iff_even _).mp h2))
  · rw [h1, h2]

private lemma aux_discr_eq_zero_or_neg_one (x : RegularFormClass (ZMod 3)) :
    RegularFormClass.discr x = 0 ∨
      RegularFormClass.discr x = squareClass (-1 : (ZMod 3)ˣ) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [RegularFormClass.discr_mk]
    rcases aux_units_zmod3 (∏ i, w i) with h | h <;> rw [h]
    · left
      rw [squareClass_eq_zero_iff]
      exact ⟨1, by simp⟩
    · right
      rfl

private lemma aux_signOf_eq_neg_one_pow {x : RegularFormClass (ZMod 3)} (hr : Even x.rank) :
    signOf x = (-1 : ℤˣ) ^ (x.rank / 2) ↔ RegularFormClass.discr x = 0 := by
  classical
  set e := squareClass (-1 : (ZMod 3)ˣ) with he
  have hcross : x.rank.choose 2 • e = (x.rank / 2) • e := aux_choose_two_nsmul_eq x.rank hr
  have hd : RegularFormClass.discr x = 0 ∨ RegularFormClass.discr x = e :=
    aux_discr_eq_zero_or_neg_one x
  have hsignm1 : signOf x = -1 ↔ RegularFormClass.signedDiscr x ≠ 0 := by
    constructor
    · intro h1 h0
      have : signOf x = 1 := (signOf_eq_one_iff x).mpr h0
      rw [h1] at this
      exact (by decide : (-1 : ℤˣ) ≠ 1) this
    · intro h0
      rw [signOf]
      exact if_neg h0
  by_cases hev : Even (x.rank / 2)
  · rw [(aux_neg_one_pow_units_eq_one_iff _).mpr hev]
    rw [signOf_eq_one_iff, RegularFormClass.signedDiscr_eq_sign_add_discr, hcross,
      (aux_nsmul_squareClass_neg_one_eq_zero_iff_even _).mpr hev, zero_add]
  · have hself : (x.rank / 2) • e = e := by
      rcases aux_nsmul_eq_zero_or_self (x.rank / 2) with h | h
      · exact absurd ((aux_nsmul_squareClass_neg_one_eq_zero_iff_even _).mp h) hev
      · exact h
    have hpow : (-1 : ℤˣ) ^ (x.rank / 2) = -1 := by
      rcases aux_neg_one_pow_units_eq_or (x.rank / 2) with h | h
      · exact absurd ((aux_neg_one_pow_units_eq_one_iff _).mp h) hev
      · exact h
    rw [hpow, hsignm1, RegularFormClass.signedDiscr_eq_sign_add_discr, hcross, hself]
    constructor
    · intro h
      rcases hd with hd0 | hde
      · exact hd0
      · exfalso
        apply h
        rw [hde, ← two_nsmul, ZModModule.char_nsmul_eq_zero]
    · intro hd0
      rw [hd0, add_zero]
      exact aux_squareClass_neg_one_ne_zero

private lemma aux_list_prod_pair (l : List V) (f : V → (ZMod 3)ˣ) :
    (l.map (fun v => ((-1 : (ZMod 3)ˣ), squareClassHom (f v)))).prod =
      (((-1 : (ZMod 3)ˣ) ^ l.length, squareClassHom ((l.map f).prod))) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, map_one]
    rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ, map_mul]
    exact Prod.ext (mul_comm _ _) rfl

private lemma aux_prod_reflect_eq_of_span (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {l : List V} (hl0 : ∀ a ∈ l, Q a ≠ 0)
    (hpair : l.Pairwise (fun a b => polar Q a b = 0))
    (hspan : Submodule.span (ZMod 3) {x | x ∈ l} = commSp t) :
    (l.map (fun v => reflect Q v)).prod = (t : V ≃ₗ[ZMod 3] V) := by
  have hsup : fixSp t ⊔ commSp t = ⊤ := (isCompl_fixSp_commSp htt).sup_eq_top
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ fixSp t ⊔ commSp t := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hx
  rw [← huw, map_add, map_add]
  have hfixu : (l.map (reflect Q)).prod u = u :=
    prod_map_reflect_apply_of_forall_polar_eq_zero (fun a ha => by
      rw [polar_comm]
      exact polar_fixSp_commSp htt hu (by rw [← hspan]; exact Submodule.subset_span ha))
  have hnegw : (l.map (reflect Q)).prod w = -w := by
    rw [← hspan] at hw
    refine Submodule.span_induction (p := fun z _ => (l.map (reflect Q)).prod z = -z)
      ?_ ?_ ?_ ?_ hw
    · intro y hy
      exact prod_map_reflect_apply_of_mem hl0 hpair hy
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, neg_add]
    · intro c y _ hy
      rw [map_smul, hy, smul_neg]
  rw [hfixu, hnegw, mem_fixSp_iff.mp hu, (mem_commSp_iff htt).mp hw]

private lemma aux_detSpinorNorm_involution (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) :
    detSpinorNorm hQ t =
      (((-1 : (ZMod 3)ˣ) ^ invDim t,
        Multiplicative.ofAdd (RegularFormClass.discr
          (TauCeti.formClass (Q.restrict (commSp t))
            (nondegenerate_restrict_commSp hQ htt))))) := by
  obtain ⟨l, hlen, hpair, hl0, hspan, hdisc⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_orthogonal_list_restrict Q (commSp t)
      (nondegenerate_restrict_commSp hQ htt)
  have hpair' : l.Pairwise (fun a b => polar Q a b = 0) := hpair.imp fun h => h.polar_eq_zero
  let reflO : V → OGroup Q := fun v => ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
  let f : V → (ZMod 3)ˣ := fun v => if h : Q v = 0 then 1 else Units.mk0 (Q v) h
  have hprod : (l.map (fun v => reflect Q v)).prod = (t : V ≃ₗ[ZMod 3] V) :=
    aux_prod_reflect_eq_of_span hQ htt hl0 hpair' hspan
  have hprodO : t = (l.map reflO).prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    exact hprod.symm
  have hper : ∀ v ∈ l, detSpinorNorm hQ (reflO v) =
      ((-1 : (ZMod 3)ˣ), squareClassHom (f v)) := by
    intro v hv
    have hv0 : Q v ≠ 0 := hl0 v hv
    let _ : Invertible (Q v) := invertibleOfNonzero hv0
    have hrefl : reflO v = reflectionOrthogonal Q v := by
      apply Subtype.ext
      rw [coe_reflectionOrthogonal_eq_reflect]
    rw [hrefl, detSpinorNorm_reflectionOrthogonal]
    congr 1
    apply congrArg squareClassHom
    apply Units.ext
    rw [val_unitOfInvertible]
    simp [f, hv0]
  have hdet : detSpinorNorm hQ t =
      (l.map (fun v => ((-1 : (ZMod 3)ˣ), squareClassHom (f v)))).prod := by
    rw [hprodO, map_list_prod, List.map_map]
    apply congrArg List.prod
    exact List.map_congr_left (fun v hv => hper v hv)
  have hval : (((l.map f).prod : (ZMod 3)ˣ) : ZMod 3) = (l.map Q).prod := by
    change (Units.coeHom (ZMod 3)) ((l.map f).prod) = (l.map Q).prod
    rw [map_list_prod (Units.coeHom (ZMod 3)) (l.map f), List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    simp [f, hl0 v hv]
  have hdisc' := hdisc ((l.map f).prod) hval
  rw [hdet, aux_list_prod_pair]
  refine Prod.ext ?_ ?_
  · rw [hlen]
    rfl
  · rw [squareClassHom_apply, ← hdisc']

theorem involution_mem_omegaGroup_iff (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    t ∈ omegaGroup hQ ↔ Even (invDim t) ∧ invSign t = (-1) ^ (invDim t / 2) := by
  set x := TauCeti.formClass (Q.restrict (commSp t)) (nondegenerate_restrict_commSp hQ htt) with hx
  have hrank : x.rank = invDim t := by
    rw [hx, rank_formClass, invDim]
  have hsign : signOf x = quadSign (Q.restrict (commSp t)) :=
    (quadSign_eq_signOf _ (nondegenerate_restrict_commSp hQ htt)).symm
  rw [mem_omegaGroup_iff hQ, aux_detSpinorNorm_involution hQ htt]
  constructor
  · intro h
    have h1 : ((-1 : (ZMod 3)ˣ) ^ invDim t) = 1 := congrArg Prod.fst h
    have h2 : Multiplicative.ofAdd (RegularFormClass.discr x) = 1 := congrArg Prod.snd h
    have hd : RegularFormClass.discr x = 0 := by
      simpa using congrArg Multiplicative.toAdd h2
    refine ⟨(aux_neg_one_pow_zmod3_eq_one_iff (invDim t)).mp h1, ?_⟩
    rw [invSign, ← hsign, ← hrank]
    exact (aux_signOf_eq_neg_one_pow (by rw [hrank]; exact
      (aux_neg_one_pow_zmod3_eq_one_iff (invDim t)).mp h1)).mpr hd
  · rintro ⟨hev, hsign'⟩
    have hrank' : Even x.rank := by rw [hrank]; exact hev
    have hd : RegularFormClass.discr x = 0 := by
      apply (aux_signOf_eq_neg_one_pow hrank').mp
      rw [hsign, ← invSign, hsign', hrank]
    refine Prod.ext ?_ ?_
    · exact (aux_neg_one_pow_zmod3_eq_one_iff (invDim t)).mpr hev
    · rw [hd]
      rfl

theorem piOrth_mem_omegaGroup_iff (hQ : Q.Nondegenerate) :
    piOrth Q ∈ omegaGroup hQ ↔
      Even (Module.finrank (ZMod 3) V) ∧
        quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2) := by
  have hdim : invDim (piOrth Q) = Module.finrank (ZMod 3) V :=
    congrArg Prod.fst (invType_piOrth hQ)
  have hsign : invSign (piOrth Q) = quadSign Q :=
    congrArg Prod.snd (invType_piOrth hQ)
  rw [involution_mem_omegaGroup_iff hQ piOrth_mul_self, hdim, hsign]

end CFSG.OddStandard.SmallF3.Omega
