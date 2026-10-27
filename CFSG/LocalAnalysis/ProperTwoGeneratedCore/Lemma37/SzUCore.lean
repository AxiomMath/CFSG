module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUCount

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

structure BenderRootData (R : Type*) [Group R] (q n : ℕ) : Prop where
  card_sq_one : Nat.card {x : R // x ^ 2 = 1} = q
  card_sq : ∀ r : R, r ≠ 1 → r ^ 2 = 1 → Nat.card {x : R // x ^ 2 = r} = n
  comm : ∀ x : R, x ^ 2 = 1 → ∀ y : R, x * y = y * x

@[expose] def BenderCenterSqOne (R : Type*) [Group R] : Prop :=
  ∀ x : R, (∀ y : R, x * y = y * x) → x ^ 2 = 1

theorem card_sq_eq_card_sq_of_mulEquiv {A B : Type*} [Group A] [Group B] (θ : A ≃* B) (a : A) :
    Nat.card {x : A // x ^ 2 = a} = Nat.card {y : B // y ^ 2 = θ a} :=
  Nat.card_congr
    { toFun := fun x => ⟨θ x, by rw [← map_pow, x.2]⟩
      invFun := fun y => ⟨θ.symm y, by rw [← map_pow, y.2, MulEquiv.symm_apply_apply]⟩
      left_inv := fun x => Subtype.ext (θ.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (θ.apply_symm_apply y) }

theorem BenderRootData.congr {A B : Type*} [Group A] [Group B] {q n : ℕ}
    (h : BenderRootData A q n) (θ : A ≃* B) : BenderRootData B q n where
  card_sq_one := by rw [← map_one θ, ← card_sq_eq_card_sq_of_mulEquiv, h.card_sq_one]
  card_sq r hr1 hr2 := by
    rw [← θ.apply_symm_apply r, ← card_sq_eq_card_sq_of_mulEquiv]
    refine h.card_sq _ (fun h1 => hr1 ?_) ?_
    · rw [← θ.apply_symm_apply r, h1, map_one]
    · rw [← map_pow, hr2, map_one]
  comm x hx y := by
    have h1 := h.comm (θ.symm x) (by rw [← map_pow, hx, map_one]) (θ.symm y)
    simpa using congrArg θ h1

theorem BenderCenterSqOne.congr {A B : Type*} [Group A] [Group B] (h : BenderCenterSqOne A)
    (θ : A ≃* B) : BenderCenterSqOne B := by
  intro x hx
  have h1 := h (θ.symm x) fun y => by
    apply θ.injective
    simpa using hx (θ y)
  simpa using congrArg θ h1

variable {X : Type*} [Group X]

theorem card_mem_sq_eq_card_subtype_sq (R : Subgroup X) {r : X} (hr : r ∈ R) :
    Nat.card {x : X // x ∈ R ∧ x ^ 2 = r} = Nat.card {x : R // x ^ 2 = ⟨r, hr⟩} :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by simpa using x.2.2)⟩
      invFun := fun y => ⟨y.1, y.1.2, by simpa using congrArg Subtype.val y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

variable [Finite X]

theorem false_of_bender_root_counts {P R T Z : Subgroup X} {z : X} (hRP : R ≤ P) (hTP : T ≤ P)
    (hcomm : ∀ x ∈ R, ∀ k ∈ T, x * k = k * x) (hdisj : ∀ g ∈ R, g ∈ T → g = 1)
    (hgen : ∀ w ∈ P, ∃ x ∈ R, ∃ k ∈ T, x * k = w) (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hTinv : ∀ k ∈ T, k ^ 2 = 1 → k = 1 ∨ k = z) (hT2 : IsPGroup 2 T)
    {q n : ℕ} (hq : Even q) (hn : 0 < n) (hroot : BenderRootData R q n)
    (hcase : n ≠ q ∨ BenderCenterSqOne R) (hZ : ∀ v, v ∈ Z ↔ v ∈ P ∧ ∀ y ∈ P, v * y = y * v)
    (A : Set X) (hA : Odd (Nat.card A)) (hzA : z ∈ A)
    (hAinv : ∀ w ∈ A, w ∈ P ∧ w ^ 2 = 1 ∧ w ≠ 1)
    (hAP : ∀ w ∈ A, Nat.card {v : X // v ∈ P ∧ v ^ 2 = w} =
      Nat.card {v : X // v ∈ P ∧ v ^ 2 = z})
    (hAZ : ∀ w ∈ A, Nat.card {v : X // v ∈ Z ∧ v ^ 2 = w} =
      Nat.card {v : X // v ∈ Z ∧ v ^ 2 = z})
    (hfus : (∀ r ∈ R, r ^ 2 = 1 → r ≠ 1 → r ∈ A) ∨ (∀ r ∈ R, r ^ 2 = 1 → r ≠ 1 → r * z ∈ A)) :
    False := by
  set I : Set X := {x | x ∈ R ∧ x ^ 2 = 1 ∧ x ≠ 1} with hIdef
  set Iz : Set X := (· * z) '' I with hIzdef
  have hzR : z ∉ R := fun h => hz1 (hdisj z h hzT)
  have hzI : z ∉ I := fun h => hzR h.1
  have hzIz : z ∉ Iz := by
    rintro ⟨x, hx, hxz⟩
    exact hx.2.2 (mul_eq_right.mp hxz)
  have hR1 : Nat.card {x : X // x ∈ R ∧ x ^ 2 = 1} = q := by
    rw [card_mem_sq_eq_card_subtype_sq R R.one_mem]
    exact hroot.card_sq_one
  have hcardI : Nat.card I + 1 = q := by
    have hset : {x : X | x ∈ R ∧ x ^ 2 = 1} = insert 1 I := by
      ext x
      by_cases hx : x = 1
      · subst hx
        simp [R.one_mem]
      · simp [hIdef, hx]
    have h := hR1
    change Nat.card ({x : X | x ∈ R ∧ x ^ 2 = 1} : Set X) = q at h
    rwa [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (fun h => h.2.2 rfl),
      ← Nat.card_coe_set_eq] at h
  have hcardIz : Nat.card Iz = Nat.card I := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hIzdef,
      Set.ncard_image_of_injective _ (mul_left_injective z)]
  have hsub : ∀ w ∈ A, w = z ∨ w ∈ I ∨ w ∈ Iz := by
    intro w hw
    obtain ⟨hwP, hw2, hw1⟩ := hAinv w hw
    rcases involution_cases_of_internal_prod hcomm hdisj hgen hTinv hwP hw2 hw1 with
      h | h | ⟨x, hx, hxw⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, hx, hxw⟩)
  obtain ⟨r₀, hr₀⟩ : I.Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Nat.card_pos_iff.trans (and_iff_left (Set.toFinite I))]
    obtain ⟨k, hk⟩ := hq
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0] at hcardI
      omega
    omega
  have hpar : (∃ r ∈ I, r ∈ A) ∧ ∃ r ∈ I, r * z ∈ A := by
    rcases hfus with hall | hall
    · have hIA : I ⊆ A := fun r hr => hall r hr.1 hr.2.1 hr.2.2
      obtain ⟨c, ⟨r, hr, rfl⟩, hcA⟩ :=
        exists_mem_of_odd_card_of_parity hA (hcardI ▸ hq) hzI hsub hzA hIA
      exact ⟨⟨r₀, hr₀, hIA hr₀⟩, r, hr, hcA⟩
    · have hIzA : Iz ⊆ A := by
        rintro _ ⟨r, hr, rfl⟩
        exact hall r hr.1 hr.2.1 hr.2.2
      obtain ⟨r, hr, hrA⟩ := exists_mem_of_odd_card_of_parity hA (hcardIz ▸ hcardI ▸ hq) hzIz
        (fun w hw => (hsub w hw).imp_right Or.symm) hzA hIzA
      exact ⟨⟨r, hr, hrA⟩, r₀, hr₀, hIzA ⟨r₀, hr₀, rfl⟩⟩
  obtain ⟨⟨r₁, hr₁, hr₁A⟩, r₂, hr₂, hr₂A⟩ := hpar
  have hRr : ∀ r ∈ I, Nat.card {x : X // x ∈ R ∧ x ^ 2 = r} = n := by
    intro r hr
    rw [card_mem_sq_eq_card_subtype_sq R hr.1]
    exact hroot.card_sq _ (fun h => hr.2.2 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hr.2.1))
  have hT1 : Nat.card {k : X // k ∈ T ∧ k ^ 2 = 1} = 2 := by
    refine Nat.card_eq_two_iff.mpr ⟨⟨1, T.one_mem, one_pow 2⟩, ⟨z, hzT, hz2⟩,
      fun h => hz1 (congrArg Subtype.val h).symm, Set.eq_univ_of_forall fun k => ?_⟩
    rcases hTinv k.1 k.2.1 k.2.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  set nT := Nat.card {k : X // k ∈ T ∧ k ^ 2 = z} with hnT
  have hPz : Nat.card {v : X // v ∈ P ∧ v ^ 2 = z} = q * nT := by
    have h := card_sq_mul_eq_of_internal_prod hRP hTP hcomm hdisj hgen R.one_mem hzT
    rwa [one_mul, hR1] at h
  have hPr₁ : Nat.card {v : X // v ∈ P ∧ v ^ 2 = r₁} = n * 2 := by
    have h := card_sq_mul_eq_of_internal_prod hRP hTP hcomm hdisj hgen hr₁.1 T.one_mem
    rwa [mul_one, hRr r₁ hr₁, hT1] at h
  have hPr₂ : Nat.card {v : X // v ∈ P ∧ v ^ 2 = r₂ * z} = n * nT := by
    have h := card_sq_mul_eq_of_internal_prod hRP hTP hcomm hdisj hgen hr₂.1 hzT
    rwa [hRr r₂ hr₂] at h
  have h1 := hAP r₁ hr₁A
  have h2 := hAP _ hr₂A
  rw [hPr₁, hPz] at h1
  rw [hPr₂, hPz] at h2
  have hnT2 : nT = 2 := Nat.eq_of_mul_eq_mul_left hn (h2.trans h1.symm)
  have hnq : n = q := by
    rw [hnT2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  rcases hcase with hne | hcenter
  · exact hne hnq
  obtain ⟨k, hkT, hk2, hkc⟩ := exists_central_sq_eq_of_card_sq_eq_two hT2 hz1 hz2 hTinv
    (hnT ▸ hnT2)
  have hkZ : k ∈ Z := by
    refine (hZ k).mpr ⟨hTP hkT, fun y hy => ?_⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := hgen y hy
    calc k * (x * t) = k * x * t := by group
      _ = x * k * t := by rw [← hcomm x hx k hkT]
      _ = x * (k * t) := by group
      _ = x * (t * k) := by rw [← hkc t ht]
      _ = x * t * k := by group
  have hZz : 0 < Nat.card {v : X // v ∈ Z ∧ v ^ 2 = z} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨k, hkZ, hk2⟩⟩, inferInstance⟩
  have hZr : Nat.card {v : X // v ∈ Z ∧ v ^ 2 = r₁} = 0 := by
    suffices h : IsEmpty {v : X // v ∈ Z ∧ v ^ 2 = r₁} from Nat.card_of_isEmpty
    refine ⟨fun v => ?_⟩
    obtain ⟨hvP, hvc⟩ := (hZ v.1).mp v.2.1
    obtain ⟨x, hx, t, ht, hxt⟩ := hgen v.1 hvP
    have hxc : ∀ y ∈ R, x * y = y * x := by
      intro y hy
      have h := hvc y (hRP hy)
      rw [← hxt, mul_assoc, ← hcomm y hy t ht, ← mul_assoc, ← mul_assoc] at h
      exact mul_right_cancel h
    have hx2 : x ^ 2 = 1 := by
      have h := hcenter ⟨x, hx⟩ fun y => Subtype.ext (hxc y y.2)
      simpa using congrArg Subtype.val h
    have hv2 := v.2.2
    rw [← hxt, Commute.mul_pow (hcomm x hx t ht) 2, hx2, one_mul] at hv2
    exact hr₁.2.2 (hdisj r₁ hr₁.1 (hv2 ▸ T.pow_mem ht 2))
  have h3 := hAZ r₁ hr₁A
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37
