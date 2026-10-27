module

public import CFSG.Quasithin.H13.L32NMatNGen

public section

namespace CFSG.KC.H12C

open CFSG.Quasithin.H13.MatNCert

variable {n : ℕ}

theorem mulN_assoc (A B C : List ℕ) : mulN (mulN A B) C = mulN A (mulN B C) := by
  simp only [mulN, List.map_map]
  congr 1
  funext v
  exact mvN_mulN A B v

theorem mulN_oneN {A : List ℕ} (hA : ValidN n A) : mulN (oneN n) A = A := by
  refine decN_injOn (validN_mulN validN_oneN hA) hA ?_
  rw [decN_mulN (validN_oneN (n := n)).1 hA.1, decN_oneN, Matrix.one_mul]

theorem colsN_inv_of {u : GL (Fin n) (ZMod 2)} {A B : List ℕ}
    (hu : colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) = A) (hB : ValidN n B)
    (hAB : mulN A B = oneN n) :
    colsN ((u⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = B := by
  have hA : ValidN n A := hu ▸ validN_colsN _
  have hu' : (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n A := by rw [← hu, decN_colsN]
  have h1 : (u : Matrix (Fin n) (Fin n) (ZMod 2)) * decN n B = 1 := by
    rw [hu', ← decN_mulN hA.1 hB.1, hAB, decN_oneN]
  have h2 : ((u⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n B := by
    calc ((u⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
        = ((u⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
            ((u : Matrix (Fin n) (Fin n) (ZMod 2)) * decN n B) := by rw [h1, Matrix.mul_one]
      _ = decN n B := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h2, colsN_decN hB]

theorem colsN_conj_of {u v x : GL (Fin n) (ZMod 2)} {r r' : List ℕ × List ℕ}
    (hu : colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) = r.1)
    (hv : colsN (v : Matrix (Fin n) (Fin n) (ZMod 2)) = r'.1) (hr' : ValidN n r'.2)
    (hinv : mulN r'.1 r'.2 = oneN n) :
    colsN ((v⁻¹ * (x * u) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      mulN r'.2 (mulN (colsN (x : Matrix (Fin n) (Fin n) (ZMod 2))) r.1) := by
  rw [Units.val_mul, Units.val_mul, colsN_mul, colsN_mul, colsN_inv_of hv hr' hinv, hu]

theorem mvN_mem_of_mapsTo {gens : List (List ℕ)} {A : List ℕ}
    (hA : ∀ g ∈ gens, ∀ a ∈ A, mvN g a ∈ A) (hlt : ∀ a ∈ A, a < 2 ^ n)
    {t : GL (Fin n) (ZMod 2)} (ht : t ∈ genSubN n gens) {a : ℕ} (ha : a ∈ A) :
    mvN (colsN (t : Matrix (Fin n) (Fin n) (ZMod 2))) a ∈ A := by
  let P : GL (Fin n) (ZMod 2) → Prop := fun x => ∀ a ∈ A, ∃ b ∈ A,
    (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (vecN n a) = vecN n b
  have hstep : ∀ x : GL (Fin n) (ZMod 2), colsN (x : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens →
      ∀ y, P y → P (x * y) := by
    intro x hx y hy a ha
    obtain ⟨b, hb, hyb⟩ := hy a ha
    refine ⟨_, hA _ hx b hb, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyb, mulVec_vecN]
  have hpow : ∀ x : GL (Fin n) (ZMod 2), colsN (x : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens →
      ∀ m : ℕ, ∀ y, P y → P (x ^ m * y) := by
    intro x hx m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep x hx _ (ih y hy)
  have hP : P t := by
    refine Subgroup.closure_induction_left (p := fun x _ => P x) ?_ ?_ ?_ ht
    · intro a ha
      exact ⟨a, ha, by rw [Units.val_one, Matrix.one_mulVec]⟩
    · intro x hx y _ hy
      exact hstep x hx _ hy
    · intro x hx y _ hy
      have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
      have hinv' : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
      rw [hinv']
      exact hpow x hx _ _ hy
  obtain ⟨b, hb, htb⟩ := hP a ha
  rw [mulVec_vecN] at htb
  rwa [vecN_inj (mvN_lt (validN_colsN _).2 a) (hlt b hb) htb]

theorem cosets_genSubN {gens : List (List ℕ)} (T : Subgroup (GL (Fin n) (ZMod 2)))
    (L : List (List ℕ))
    (hTL : ∀ u, u ∈ T ↔ colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L)
    (hTH : T ≤ genSubN n gens) (reps : List (List ℕ × List ℕ))
    (hrep : ∀ r ∈ reps, ∃ u ∈ genSubN n gens, colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) = r.1)
    (hval : ∀ r ∈ reps, ValidN n r.2) (hinv : ∀ r ∈ reps, mulN r.1 r.2 = oneN n)
    (hnd : (reps.map Prod.fst).Nodup) (h1 : ∃ r ∈ reps, r.1 ∈ L)
    (hcl : ∀ g ∈ gens, ∀ r ∈ reps, ∃ r' ∈ reps, mulN r'.2 (mulN g r.1) ∈ L)
    (hdis : ∀ r ∈ reps, ∀ r' ∈ reps, mulN r'.2 r.1 ∈ L → r.1 = r'.1) :
    (∀ u ∈ genSubN n gens, ∃ r ∈ reps, ∃ t ∈ T,
      colsN (t : Matrix (Fin n) (Fin n) (ZMod 2)) =
        mulN r.2 (colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)))) ∧
      Nat.card (genSubN n gens) = reps.length * Nat.card T := by
  let P : GL (Fin n) (ZMod 2) → Prop := fun x => ∃ r ∈ reps, ∃ u : GL (Fin n) (ZMod 2),
    colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) = r.1 ∧ u⁻¹ * x ∈ T
  have hstep : ∀ x : GL (Fin n) (ZMod 2), colsN (x : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens →
      ∀ y, P y → P (x * y) := by
    rintro x hx y ⟨r, hr, u, hu, huy⟩
    obtain ⟨r', hr', hL⟩ := hcl _ hx r hr
    obtain ⟨v, -, hv⟩ := hrep r' hr'
    refine ⟨r', hr', v, hv, ?_⟩
    have hc : v⁻¹ * (x * u) ∈ T := by
      rw [hTL, colsN_conj_of hu hv (hval r' hr') (hinv r' hr')]
      exact hL
    have : v⁻¹ * (x * y) = (v⁻¹ * (x * u)) * (u⁻¹ * y) := by group
    rw [this]
    exact T.mul_mem hc huy
  have hpow : ∀ x : GL (Fin n) (ZMod 2), colsN (x : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens →
      ∀ m : ℕ, ∀ y, P y → P (x ^ m * y) := by
    intro x hx m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep x hx _ (ih y hy)
  have hcov : ∀ x ∈ genSubN n gens, P x := by
    intro x hx
    refine Subgroup.closure_induction_left (p := fun x _ => P x) ?_ ?_ ?_ hx
    · obtain ⟨r, hr, hrL⟩ := h1
      obtain ⟨u, -, hu⟩ := hrep r hr
      refine ⟨r, hr, u, hu, ?_⟩
      rw [mul_one]
      exact T.inv_mem ((hTL u).mpr (hu ▸ hrL))
    · intro x hx y _ hy
      exact hstep x hx y hy
    · intro x hx y _ hy
      have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
      have hinv' : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
      rw [hinv']
      exact hpow x hx _ y hy
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, u, hu, hux⟩ := hcov x hx
    refine ⟨r, hr, _, hux, ?_⟩
    rw [Units.val_mul, colsN_mul, colsN_inv_of hu (hval r hr) (hinv r hr)]
  ·
    let R : Type := {u : GL (Fin n) (ZMod 2) //
      colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ reps.map Prod.fst}
    have hmemR : ∀ u : R, ∃ r ∈ reps, colsN ((u : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = r.1 := by
      intro u
      obtain ⟨r, hr, he⟩ := List.mem_map.mp u.2
      exact ⟨r, hr, he.symm⟩
    have hRH : ∀ u : R, (u : GL (Fin n) (ZMod 2)) ∈ genSubN n gens := by
      intro u
      obtain ⟨r, hr, he⟩ := hmemR u
      obtain ⟨v, hv, hv'⟩ := hrep r hr
      have : (u : GL (Fin n) (ZMod 2)) = v := eq_of_colsN_eq (he.trans hv'.symm)
      exact this ▸ hv
    let f : R × T → genSubN n gens := fun p =>
      ⟨(p.1 : GL (Fin n) (ZMod 2)) * p.2, mul_mem (hRH p.1) (hTH p.2.2)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun p q h => ?_, fun ⟨x, hx⟩ => ?_⟩
      · have h1 : (p.1 : GL (Fin n) (ZMod 2)) * p.2 = (q.1 : GL (Fin n) (ZMod 2)) * q.2 :=
          congrArg Subtype.val h
        obtain ⟨r, hr, hpr⟩ := hmemR p.1
        obtain ⟨r', hr', hqr⟩ := hmemR q.1
        have hT' : (q.1 : GL (Fin n) (ZMod 2))⁻¹ * (1 * (p.1 : GL (Fin n) (ZMod 2))) ∈ T := by
          have : (q.1 : GL (Fin n) (ZMod 2))⁻¹ * (1 * (p.1 : GL (Fin n) (ZMod 2))) =
              (q.2 : GL (Fin n) (ZMod 2)) * (p.2 : GL (Fin n) (ZMod 2))⁻¹ := by
            rw [one_mul, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
          rw [this]
          exact T.mul_mem q.2.2 (T.inv_mem p.2.2)
        rw [hTL, colsN_conj_of hpr hqr (hval r' hr') (hinv r' hr'), Units.val_one, colsN_one,
          mulN_oneN (n := n) (hpr ▸ validN_colsN _)] at hT'
        have he : (p.1 : GL (Fin n) (ZMod 2)) = q.1 :=
          eq_of_colsN_eq (hpr.trans ((hdis r hr r' hr' hT').trans hqr.symm))
        have hpq : p.1 = q.1 := Subtype.ext he
        rw [he] at h1
        exact Prod.ext hpq (Subtype.ext (mul_left_cancel h1))
      · obtain ⟨r, hr, u, hu, hux⟩ := hcov x hx
        refine ⟨(⟨u, List.mem_map.mpr ⟨r, hr, hu.symm⟩⟩, ⟨_, hux⟩), ?_⟩
        apply Subtype.ext
        change u * (u⁻¹ * x) = x
        group
    have hR : Nat.card R = reps.length := by
      let e : R → {c // c ∈ reps.map Prod.fst} := fun u =>
        ⟨colsN ((u : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)), u.2⟩
      have he : Function.Bijective e := by
        refine ⟨fun u v h => Subtype.ext (eq_of_colsN_eq (congrArg Subtype.val h)),
          fun ⟨c, hc⟩ => ?_⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
        obtain ⟨v, -, hv⟩ := hrep r hr
        exact ⟨⟨v, hv ▸ hc⟩, Subtype.ext hv⟩
      rw [Nat.card_eq_of_bijective e he,
        Nat.card_congr (Equiv.subtypeEquivRight fun x =>
          (List.mem_toFinset (l := reps.map Prod.fst) (a := x)).symm),
        Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd,
        List.length_map]
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, hR]

end CFSG.KC.H12C

end
