module

public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

variable {n : ℕ}

theorem perm_inv_apply_self (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by simp

theorem perm_apply_inv_self (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ (σ⁻¹ x) = x := by simp

@[expose] def vcoord (v : ↥(coreMod n)) (i : Fin n) : ZMod 2 :=
  Multiplicative.toAdd (v : PermMod n) i

theorem vcoord_mul (v w : ↥(coreMod n)) (i : Fin n) :
    vcoord (v * w) i = vcoord v i + vcoord w i := rfl

theorem vcoord_one (i : Fin n) : vcoord (1 : ↥(coreMod n)) i = 0 := rfl

theorem vcoord_inv (v : ↥(coreMod n)) (i : Fin n) : vcoord v⁻¹ i = vcoord v i := by
  show -(vcoord v i) = vcoord v i
  exact CharTwo.neg_eq _

theorem vcoord_ext {v w : ↥(coreMod n)} (h : ∀ i, vcoord v i = vcoord w i) : v = w := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  exact h i

theorem sum_vcoord (v : ↥(coreMod n)) : ∑ i, vcoord v i = 0 := v.2

@[expose] def mkEven (f : Fin n → ZMod 2) (h : ∑ i, f i = 0) : ↥(coreMod n) :=
  ⟨Multiplicative.ofAdd f, h⟩

theorem vcoord_mkEven (f : Fin n → ZMod 2) (h : ∑ i, f i = 0) (i : Fin n) :
    vcoord (mkEven f h) i = f i := rfl

theorem vcoord_coreAct (σ : Equiv.Perm (Fin n)) (v : ↥(coreMod n)) (i : Fin n) :
    vcoord (coreAct n σ v) i = vcoord v (σ⁻¹ i) := rfl

theorem coreAct_injective (h3 : 3 ≤ n) : Function.Injective (coreAct n) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have hcard : ({i, σ i} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, σ i} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  set f : Fin n → ZMod 2 := Pi.single i 1 + Pi.single k 1 with hf
  have hsum : ∑ j : Fin n, f j = 0 := by
    simp only [hf, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    exact CharTwo.add_self_eq_zero _
  have h1 := congrArg (fun x => vcoord x (σ i)) (DFunLike.congr_fun hσ (mkEven f hsum))
  simp only [vcoord_coreAct, vcoord_mkEven] at h1
  simp only [MulAut.one_apply, vcoord_mkEven] at h1
  have hik : i ≠ k := fun h => hk.1 h.symm
  have hσk : σ i ≠ k := fun h => hk.2 h.symm
  simp [hf, hi, hik, hσk] at h1

theorem mem_fixV_map_iff {A : Subgroup (Equiv.Perm (Fin n))} {v : ↥(coreMod n)} :
    v ∈ fixV (A.map (coreAct n)) ↔ ∀ a ∈ A, ∀ i, vcoord v (a i) = vcoord v i := by
  constructor
  · intro h a ha i
    have h1 : coreAct n a⁻¹ v = v := h (coreAct n a⁻¹) (Subgroup.mem_map_of_mem _ (A.inv_mem ha))
    have h2 := congrArg (fun w => vcoord w i) h1
    simpa only [vcoord_coreAct, inv_inv] using h2
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    show coreAct n a v = v
    apply vcoord_ext
    intro i
    rw [vcoord_coreAct]
    exact h a⁻¹ (A.inv_mem ha) i

abbrev OrbQ (A : Subgroup (Equiv.Perm (Fin n))) : Type :=
  MulAction.orbitRel.Quotient A (Fin n)

noncomputable instance (A : Subgroup (Equiv.Perm (Fin n))) : Fintype (OrbQ A) :=
  Fintype.ofFinite _

@[expose] def orbOf (A : Subgroup (Equiv.Perm (Fin n))) (x : Fin n) : OrbQ A := Quotient.mk'' x

theorem orbOf_eq_iff {A : Subgroup (Equiv.Perm (Fin n))} {x y : Fin n} :
    orbOf A x = orbOf A y ↔ ∃ a ∈ A, a y = x := by
  unfold orbOf
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, ha⟩, h⟩

theorem orbOf_apply {A : Subgroup (Equiv.Perm (Fin n))} {a : Equiv.Perm (Fin n)} (ha : a ∈ A)
    (x : Fin n) : orbOf A (a x) = orbOf A x :=
  orbOf_eq_iff.2 ⟨a, ha, rfl⟩

theorem orbOf_surjective (A : Subgroup (Equiv.Perm (Fin n))) : Function.Surjective (orbOf A) :=
  Quotient.mk''_surjective

@[expose] noncomputable def orbRep (A : Subgroup (Equiv.Perm (Fin n))) (q : OrbQ A) : Fin n :=
  Quotient.out q

theorem orbOf_orbRep (A : Subgroup (Equiv.Perm (Fin n))) (q : OrbQ A) :
    orbOf A (orbRep A q) = q :=
  Quotient.out_eq' q

@[expose] noncomputable def orbSize (A : Subgroup (Equiv.Perm (Fin n))) (q : OrbQ A) : ℕ :=
  Nat.card {x : Fin n // orbOf A x = q}

theorem orbSize_pos (A : Subgroup (Equiv.Perm (Fin n))) (q : OrbQ A) : 0 < orbSize A q := by
  have : Nonempty {x : Fin n // orbOf A x = q} := ⟨⟨orbRep A q, orbOf_orbRep A q⟩⟩
  exact Nat.card_pos

theorem sum_orbSize (A : Subgroup (Equiv.Perm (Fin n))) : ∑ q : OrbQ A, orbSize A q = n := by
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv (orbOf A))
  rw [Nat.card_sigma, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

theorem card_orbQ_bot : Nat.card (OrbQ (⊥ : Subgroup (Equiv.Perm (Fin n)))) = n := by
  have hb : Function.Bijective (orbOf (⊥ : Subgroup (Equiv.Perm (Fin n)))) := by
    refine ⟨fun x y h => ?_, orbOf_surjective _⟩
    obtain ⟨a, ha, rfl⟩ := orbOf_eq_iff.1 h
    rw [Subgroup.mem_bot] at ha
    subst ha
    rfl
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem vcoord_eq_of_mem_fixV {A : Subgroup (Equiv.Perm (Fin n))} {v : ↥(coreMod n)}
    (hv : v ∈ fixV (A.map (coreAct n))) {x y : Fin n} (h : orbOf A x = orbOf A y) :
    vcoord v x = vcoord v y := by
  obtain ⟨a, ha, rfl⟩ := orbOf_eq_iff.1 h
  exact mem_fixV_map_iff.1 hv a ha y

@[expose] noncomputable def descend (A : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → ZMod 2)
    (hf : ∀ x y, orbOf A x = orbOf A y → f x = f y) : OrbQ A → ZMod 2 :=
  Quotient.lift f fun x y h => hf x y (Quotient.sound h)

theorem descend_orbOf (A : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → ZMod 2)
    (hf : ∀ x y, orbOf A x = orbOf A y → f x = f y) (x : Fin n) :
    descend A f hf (orbOf A x) = f x := rfl

theorem sum_shift (hn : Odd n) (f : Fin n → ZMod 2) : ∑ x, (f x + ∑ y, f y) = 0 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.2 hn, one_mul]
  exact CharTwo.add_self_eq_zero _

theorem sum_vcoord_add (hn : Odd n) (v : ↥(coreMod n)) (e : ZMod 2) :
    ∑ x, (vcoord v x + e) = e := by
  rw [Finset.sum_add_distrib, sum_vcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.2 hn, one_mul, zero_add]

@[expose] noncomputable def fixEquiv (hn : Odd n) (A : Subgroup (Equiv.Perm (Fin n))) :
    ↥(fixV (A.map (coreAct n))) × ZMod 2 ≃ (OrbQ A → ZMod 2) where
  toFun p := descend A (fun x => vcoord p.1.1 x + p.2) fun x y h => by
    rw [vcoord_eq_of_mem_fixV p.1.2 h]
  invFun g :=
    (⟨mkEven (fun x => g (orbOf A x) + ∑ y, g (orbOf A y)) (sum_shift hn _),
      mem_fixV_map_iff.2 fun a ha i => by simp only [vcoord_mkEven, orbOf_apply ha]⟩,
      ∑ y, g (orbOf A y))
  left_inv p := by
    obtain ⟨⟨v, hv⟩, e⟩ := p
    have hsum : ∑ y, (vcoord v y + e) = e := sum_vcoord_add hn v e
    refine Prod.ext (Subtype.ext (vcoord_ext fun x => ?_)) ?_
    · simp only [vcoord_mkEven, descend_orbOf, hsum, add_assoc, CharTwo.add_self_eq_zero,
        add_zero]
    · exact hsum
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn' with
    | h x =>
      change descend A _ _ (orbOf A x) = g (orbOf A x)
      simp only [descend_orbOf, vcoord_mkEven, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem card_fixV_mul_two (hn : Odd n) (A : Subgroup (Equiv.Perm (Fin n))) :
    Nat.card (fixV (A.map (coreAct n))) * 2 = 2 ^ Nat.card (OrbQ A) := by
  have h := Nat.card_congr (fixEquiv hn A)
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_zmod] at h
  exact h

theorem card_coreMod_mul_two (hn : Odd n) : Nat.card (coreMod n) * 2 = 2 ^ n := by
  have h := card_fixV_mul_two hn (⊥ : Subgroup (Equiv.Perm (Fin n)))
  have h1 : fixV ((⊥ : Subgroup (Equiv.Perm (Fin n))).map (coreAct n)) = ⊤ :=
    eq_top_iff.2 fun v _ => mem_fixV_map_iff.2 fun a ha i => by
      rw [Subgroup.mem_bot.1 ha]
      rfl
  rw [card_orbQ_bot, h1, Subgroup.card_top] at h
  exact h

end CFSG.CGT.PushingUpLit.BHS
