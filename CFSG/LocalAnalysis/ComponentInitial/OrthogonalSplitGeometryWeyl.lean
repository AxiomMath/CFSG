module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {r : ℕ}

section Sign

@[expose] def IsSign (s : ℤ) : Prop := s = 1 ∨ s = -1

theorem isSign_one : IsSign 1 := Or.inl rfl

theorem isSign_neg_one : IsSign (-1) := Or.inr rfl

theorem IsSign.neg {s : ℤ} (hs : IsSign s) : IsSign (-s) := by
  rcases hs with rfl | rfl
  · exact isSign_neg_one
  · exact isSign_one

theorem IsSign.mul {s t : ℤ} (hs : IsSign s) (ht : IsSign t) : IsSign (s * t) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [IsSign]

theorem isSign_unit (u : ℤˣ) : IsSign u := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h]
  · exact isSign_one
  · exact isSign_neg_one

theorem eps_eval_self (i : Fin r) : eps r i i = 1 := by
  simp [eps_apply]

theorem eps_eval_ne {i j : Fin r} (h : j ≠ i) : eps r i j = 0 := by
  simp [eps_apply, h]

theorem sign_vec_apply (s t : ℤ) (a b j : Fin r) :
    (s • eps r a + t • eps r b) j = (if j = a then s else 0) + if j = b then t else 0 := by
  simp [eps_apply]

end Sign

section Forms

theorem mem_roots_iff_sign {α : Fin r → ℤ} :
    α ∈ roots r ↔ ∃ a b : Fin r, a ≠ b ∧ ∃ s t : ℤ, IsSign s ∧ IsSign t ∧
      α = s • eps r a + t • eps r b := by
  constructor
  · rintro ⟨i, j, hij, h | h | h | h⟩ <;> refine ⟨i, j, hij.ne, ?_⟩
    · exact ⟨1, -1, isSign_one, isSign_neg_one, by rw [h]; simp [sub_eq_add_neg]⟩
    · exact ⟨-1, 1, isSign_neg_one, isSign_one, by rw [h]; simp⟩
    · exact ⟨1, 1, isSign_one, isSign_one, by rw [h]; simp⟩
    · exact ⟨-1, -1, isSign_neg_one, isSign_neg_one, by rw [h]; simp [sub_eq_add_neg]⟩
  · rintro ⟨a, b, hab, s, t, hs, ht, rfl⟩
    rcases lt_or_gt_of_ne hab with h | h
    · refine ⟨a, b, h, ?_⟩
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [sub_eq_add_neg]
    · refine ⟨b, a, h, ?_⟩
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [sub_eq_add_neg, add_comm]

theorem mem_posRoots_iff_sign {α : Fin r → ℤ} :
    α ∈ posRoots r ↔ ∃ a b : Fin r, a < b ∧ ∃ t : ℤ, IsSign t ∧ α = eps r a + t • eps r b := by
  constructor
  · rintro ⟨i, j, hij, h | h⟩ <;> refine ⟨i, j, hij, ?_⟩
    · exact ⟨-1, isSign_neg_one, by rw [h]; simp [sub_eq_add_neg]⟩
    · exact ⟨1, isSign_one, by rw [h]; simp⟩
  · rintro ⟨a, b, hab, t, ht, rfl⟩
    refine ⟨a, b, hab, ?_⟩
    rcases ht with rfl | rfl
    · right
      simp
    · left
      simp [sub_eq_add_neg]

theorem sign_vec_mem_posRoots_iff {a b : Fin r} (hab : a ≠ b) {s t : ℤ} (hs : IsSign s)
    (ht : IsSign t) :
    s • eps r a + t • eps r b ∈ posRoots r ↔ (a < b ∧ s = 1) ∨ (b < a ∧ t = 1) := by
  rw [mem_posRoots_iff_sign]
  constructor
  · rintro ⟨c, d, hcd, u, hu, h⟩
    have hval : ∀ j, (if j = a then s else 0) + (if j = b then t else 0) =
        (if j = c then 1 else 0) + if j = d then u else 0 := fun j => by
      have := congrFun h j
      simpa [eps_apply] using this
    have hcd' : c ≠ d := hcd.ne
    have hc := hval c
    have hd := hval d
    rw [ite_eq_left rfl, ite_eq_right hcd'] at hc
    rw [ite_eq_right hcd'.symm, ite_eq_left rfl] at hd
    have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> norm_num
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
    by_cases hca : c = a
    · subst hca
      rw [ite_eq_left rfl, ite_eq_right hab] at hc
      have hdb : d = b := by
        by_contra hdb
        rw [ite_eq_right hcd'.symm, ite_eq_right hdb, add_zero] at hd
        exact hu0 (by linarith)
      subst hdb
      exact Or.inl ⟨hcd, by linarith⟩
    · have hcb : c = b := by
        by_contra hcb
        rw [ite_eq_right hca, ite_eq_right hcb, add_zero] at hc
        exact zero_ne_one hc
      subst hcb
      rw [ite_eq_right hca, ite_eq_left rfl, zero_add, add_zero] at hc
      have hda : d = a := by
        by_contra hda
        rw [ite_eq_right hda, ite_eq_right hcd'.symm, zero_add] at hd
        exact hu0 (by linarith)
      subst hda
      exact Or.inr ⟨hcd, hc⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨a, b, h, t, ht, by simp⟩
    · exact ⟨b, a, h, s, hs, by rw [add_comm]; simp⟩

theorem sign_vec_mem_roots {a b : Fin r} (hab : a ≠ b) {s t : ℤ} (hs : IsSign s)
    (ht : IsSign t) : s • eps r a + t • eps r b ∈ roots r :=
  mem_roots_iff_sign.mpr ⟨a, b, hab, s, t, hs, ht, rfl⟩

theorem mem_posRoots_or_neg_mem_posRoots {α : Fin r → ℤ} (hα : α ∈ roots r) :
    (α ∈ posRoots r ∨ -α ∈ posRoots r) ∧ ¬(α ∈ posRoots r ∧ -α ∈ posRoots r) := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  have hneg : -(s • eps r a + t • eps r b) = (-s) • eps r a + (-t) • eps r b := by
    rw [neg_add, neg_smul, neg_smul]
  rw [hneg, sign_vec_mem_posRoots_iff hab hs ht, sign_vec_mem_posRoots_iff hab hs.neg ht.neg]
  rcases lt_or_gt_of_ne hab with h | h <;>
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp [h, not_lt.mpr h.le]

theorem neg_mem_roots {α : Fin r → ℤ} (hα : α ∈ roots r) : -α ∈ roots r := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  have hneg : -(s • eps r a + t • eps r b) = (-s) • eps r a + (-t) • eps r b := by
    rw [neg_add, neg_smul, neg_smul]
  rw [hneg]
  exact sign_vec_mem_roots hab hs.neg ht.neg

end Forms

section Action

theorem signedPermAut_sign_vec (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) (s t : ℤ)
    (a b : Fin r) :
    signedPermAut r σ δ (s • eps r a + t • eps r b) =
      (s * δ a) • eps r (σ a) + (t * δ b) • eps r (σ b) := by
  rw [map_add, map_smul, map_smul, signedPermAut_eps, signedPermAut_eps, smul_smul, smul_smul]

theorem apply_mem_roots {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroup r)
    {α : Fin r → ℤ} (hα : α ∈ roots r) : w α ∈ roots r := by
  obtain ⟨σ, δ, -, rfl⟩ := hw
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  rw [signedPermAut_sign_vec]
  exact sign_vec_mem_roots (σ.injective.ne hab) (hs.mul (isSign_unit _)) (ht.mul (isSign_unit _))

theorem posRoots_finite : (posRoots r).Finite := by
  refine (Set.finite_range fun p : Fin r × Fin r × Bool =>
    eps r p.1 + (if p.2.2 then 1 else -1 : ℤ) • eps r p.2.1).subset ?_
  intro α hα
  obtain ⟨a, b, -, t, ht, rfl⟩ := mem_posRoots_iff_sign.mp hα
  rcases ht with rfl | rfl
  · exact ⟨(a, b, true), by simp⟩
  · exact ⟨(a, b, false), by simp⟩

theorem ne_zero_of_mem_roots {α : Fin r → ℤ} (hα : α ∈ roots r) : α ≠ 0 := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  intro h
  have h1 : s = 0 := by simpa [eps_apply, hab] using congrFun h a
  rcases hs with rfl | rfl <;> norm_num at h1

end Action

section Simple

theorem simpleRoot_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleRoot r i = (1 : ℤ) • eps r i + (-1 : ℤ) • eps r ⟨i.val + 1, h⟩ := by
  rw [simpleRoot, dite_eq_left h]
  simp [sub_eq_add_neg]

theorem simpleRoot_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    simpleRoot r i = (1 : ℤ) • eps r ⟨r - 2, by omega⟩ + (1 : ℤ) • eps r i := by
  rw [simpleRoot, dite_eq_right h]
  simp

theorem simpleRoot_mem_posRoots (hr : 2 ≤ r) (i : Fin r) : simpleRoot r i ∈ posRoots r := by
  by_cases h : i.val + 1 < r
  · rw [simpleRoot_of_lt h, sign_vec_mem_posRoots_iff (by simp [Fin.ext_iff]) isSign_one
      isSign_neg_one]
    exact Or.inl ⟨by simp [Fin.lt_def], rfl⟩
  · rw [simpleRoot_of_not_lt h, sign_vec_mem_posRoots_iff
      (by simp [Fin.ext_iff]; omega) isSign_one isSign_one]
    exact Or.inl ⟨by simp [Fin.lt_def]; omega, rfl⟩

variable (r) in
@[expose] def lastSigns (i : Fin r) : Fin r → ℤˣ :=
  fun j => if j = i ∨ j.val + 2 = r then -1 else 1

variable (r) in
@[expose] def simpleRefl (i : Fin r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) :=
  if h : i.val + 1 < r then signedPermAut r (Equiv.swap i ⟨i.val + 1, h⟩) 1
  else signedPermAut r (Equiv.swap ⟨r - 2, by omega⟩ i) (lastSigns r i)

theorem simpleRefl_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleRefl r i = signedPermAut r (Equiv.swap i ⟨i.val + 1, h⟩) 1 := by
  rw [simpleRefl, dite_eq_left h]

theorem simpleRefl_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    simpleRefl r i = signedPermAut r (Equiv.swap ⟨r - 2, by omega⟩ i) (lastSigns r i) := by
  rw [simpleRefl, dite_eq_right h]

theorem prod_lastSigns (hr : 2 ≤ r) {i : Fin r} (h : ¬i.val + 1 < r) :
    ∏ j, lastSigns r i j = 1 := by
  have hpi : (⟨r - 2, by omega⟩ : Fin r) ≠ i := by simp [Fin.ext_iff]; omega
  have hsplit : ∀ j, lastSigns r i j = (if j = i then -1 else 1) *
      (if j = ⟨r - 2, by omega⟩ then -1 else 1) := by
    intro j
    simp only [lastSigns, Fin.ext_iff]
    split_ifs <;> simp_all
    all_goals omega
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  simp

theorem simpleRefl_mem (hr : 2 ≤ r) (i : Fin r) : simpleRefl r i ∈ weylGroup r := by
  by_cases h : i.val + 1 < r
  · exact ⟨_, 1, by simp, simpleRefl_of_lt h⟩
  · exact ⟨_, _, prod_lastSigns hr h, simpleRefl_of_not_lt h⟩

end Simple


section SimpleAction

theorem simpleRefl_simpleRoot (hr : 2 ≤ r) (i : Fin r) :
    simpleRefl r i (simpleRoot r i) = -simpleRoot r i := by
  by_cases h : i.val + 1 < r
  · rw [simpleRefl_of_lt h, simpleRoot_of_lt h, signedPermAut_sign_vec, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    simp only [Pi.one_apply, Units.val_one, mul_one, one_smul, neg_smul, neg_add]
    abel
  · have hpi : (⟨r - 2, by omega⟩ : Fin r) ≠ i := by simp [Fin.ext_iff]; omega
    rw [simpleRefl_of_not_lt h, simpleRoot_of_not_lt h, signedPermAut_sign_vec,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hr2 : r - 2 + 2 = r := by omega
    have h1 : ((lastSigns r i ⟨r - 2, by omega⟩ : ℤˣ) : ℤ) = -1 := by
      simp [lastSigns, hr2]
    have h2 : ((lastSigns r i i : ℤˣ) : ℤ) = -1 := by
      simp [lastSigns]
    rw [h1, h2]
    simp only [one_mul, neg_smul, one_smul, neg_add]
    abel

theorem simpleRefl_mem_posRoots (hr : 2 ≤ r) {i : Fin r} {β : Fin r → ℤ} (hβ : β ∈ posRoots r)
    (hne : β ≠ simpleRoot r i) : simpleRefl r i β ∈ posRoots r := by
  obtain ⟨a, b, hab, t, ht, rfl⟩ := mem_posRoots_iff_sign.mp hβ
  have hab' : a ≠ b := hab.ne
  rw [show eps r a + t • eps r b = (1 : ℤ) • eps r a + t • eps r b by rw [one_smul]]
  by_cases h : i.val + 1 < r
  · rw [simpleRefl_of_lt h, signedPermAut_sign_vec]
    simp only [Pi.one_apply, Units.val_one, mul_one]
    set j : Fin r := ⟨i.val + 1, h⟩ with hj
    rw [sign_vec_mem_posRoots_iff ((Equiv.swap i j).injective.ne hab') isSign_one ht]
    by_cases hij : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hij
      right
      refine ⟨by rw [Equiv.swap_apply_left, Equiv.swap_apply_right]; exact hab, ?_⟩
      rcases ht with rfl | rfl
      · rfl
      · exact absurd (by rw [simpleRoot_of_lt h, one_smul]) hne
    · left
      refine ⟨?_, rfl⟩
      rw [Fin.lt_def] at hab ⊢
      simp only [Equiv.swap_apply_def]
      split_ifs <;> simp_all [Fin.ext_iff, j] <;> omega
  · rw [simpleRefl_of_not_lt h, signedPermAut_sign_vec]
    have hi : i.val = r - 1 := by omega
    obtain ⟨p, hpv⟩ : ∃ p : Fin r, p.val = r - 2 := ⟨⟨r - 2, by omega⟩, rfl⟩
    have hp : (⟨r - 2, by omega⟩ : Fin r) = p := Fin.ext hpv.symm
    rw [hp]
    have hpi : p ≠ i := by rw [Ne, Fin.ext_iff]; omega
    have hδ : ∀ c : Fin r, ((lastSigns r i c : ℤˣ) : ℤ) =
        if c.val + 2 = r ∨ c.val + 1 = r then -1 else 1 := by
      intro c
      simp only [lastSigns, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [hδ, hδ]
    by_cases ha : a.val + 2 < r
    ·
      have hσa : Equiv.swap p i a = a := Equiv.swap_apply_of_ne_of_ne
        (by rw [Ne, Fin.ext_iff]; omega) (by rw [Ne, Fin.ext_iff]; omega)
      rw [hσa, ite_eq_right (by omega), mul_one]
      rw [sign_vec_mem_posRoots_iff (by rw [← hσa]; exact (Equiv.swap p i).injective.ne hab')
        isSign_one (ht.mul (by split_ifs <;> simp [IsSign]))]
      left
      refine ⟨?_, rfl⟩
      rw [Fin.lt_def] at hab ⊢
      simp only [Equiv.swap_apply_def]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    ·
      have ha' : a = p := by rw [Fin.ext_iff]; rw [Fin.lt_def] at hab; omega
      have hb' : b = i := by rw [Fin.ext_iff]; rw [Fin.lt_def] at hab; omega
      have ht' : t = -1 := by
        rcases ht with rfl | rfl
        · exfalso
          apply hne
          rw [simpleRoot_of_not_lt h, hp, ha', hb', one_smul, one_smul]
        · rfl
      rw [ht', ha', hb', Equiv.swap_apply_left, Equiv.swap_apply_right,
        ite_eq_left (Or.inl (by omega)), ite_eq_left (Or.inr (by omega))]
      rw [sign_vec_mem_posRoots_iff hpi.symm (isSign_one.mul isSign_neg_one)
        (isSign_neg_one.mul isSign_neg_one)]
      right
      exact ⟨by rw [Fin.lt_def]; omega, by norm_num⟩

theorem simpleRefl_mul_self (hr : 2 ≤ r) (i : Fin r) : simpleRefl r i * simpleRefl r i = 1 := by
  by_cases h : i.val + 1 < r
  · rw [simpleRefl_of_lt h, signedPermAut_mul, Equiv.swap_mul_self]
    simp only [Pi.one_apply, mul_one]
    exact signedPermAut_one
  · rw [simpleRefl_of_not_lt h, signedPermAut_mul, Equiv.swap_mul_self]
    have : (fun j => lastSigns r i j * lastSigns r i (Equiv.swap ⟨r - 2, by omega⟩ i j)) = 1 := by
      funext j
      simp only [lastSigns, Pi.one_apply, Equiv.swap_apply_def, Fin.ext_iff]
      split_ifs <;> simp_all
    rw [this]
    exact signedPermAut_one

end SimpleAction


section Transitive

theorem exists_perm_apply_zero_one {a b : Fin r} (hab : a ≠ b) (i₀ i₁ : Fin r) (h01 : i₀ ≠ i₁) :
    ∃ σ : Equiv.Perm (Fin r), σ i₀ = a ∧ σ i₁ = b := by
  set τ := Equiv.swap i₀ a with hτ
  have hτa : a ≠ τ i₁ := by
    intro h
    have : τ a = i₀ := Equiv.swap_apply_right i₀ a
    rw [h, Equiv.swap_apply_self] at this
    exact h01 this.symm
  refine ⟨Equiv.swap (τ i₁) b * τ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hτ, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hτa hab
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem exists_weyl_apply_base (hr : 3 ≤ r) {β : Fin r → ℤ} (hβ : β ∈ roots r) :
    ∃ w ∈ weylGroup r, w ((1 : ℤ) • eps r ⟨0, by omega⟩ + (-1 : ℤ) • eps r ⟨1, by omega⟩) = β := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hβ
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  set i₂ : Fin r := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_apply_zero_one hab i₀ i₁ h01
  obtain ⟨u, hu⟩ : ∃ u : ℤˣ, (u : ℤ) = s := by
    rcases hs with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤˣ, (v : ℤ) = -t := by
    rcases ht with rfl | rfl
    · exact ⟨-1, rfl⟩
    · exact ⟨1, rfl⟩
  set δ : Fin r → ℤˣ := fun j =>
    (if j = i₀ then u else 1) * (if j = i₁ then v else 1) * (if j = i₂ then u * v else 1) with hδ
  have hprod : ∏ j, δ j = 1 := by
    rw [hδ, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [show u * v * (u * v) = (u * v) * (u * v) by group, Int.units_mul_self]
  refine ⟨signedPermAut r σ δ, ⟨σ, δ, hprod, rfl⟩, ?_⟩
  rw [signedPermAut_sign_vec, hσ0, hσ1]
  have hδ0 : ((δ i₀ : ℤˣ) : ℤ) = s := by
    simp [hδ, h01, h02, hu]
  have hδ1 : ((δ i₁ : ℤˣ) : ℤ) = -t := by
    simp [hδ, h01.symm, h12, hv]
  rw [hδ0, hδ1, one_mul, show (-1 : ℤ) * -t = t by ring]

theorem exists_weyl_apply_eq (hr : 3 ≤ r) {α β : Fin r → ℤ} (hα : α ∈ roots r)
    (hβ : β ∈ roots r) : ∃ w ∈ weylGroup r, w α = β := by
  obtain ⟨w₁, hw₁, h₁⟩ := exists_weyl_apply_base hr hα
  obtain ⟨w₂, hw₂, h₂⟩ := exists_weyl_apply_base hr hβ
  refine ⟨w₂ * w₁⁻¹, mul_mem hw₂ (inv_mem hw₁), ?_⟩
  rw [LinearEquiv.mul_apply, ← h₁, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, h₂]

end Transitive

section Combination

theorem eps_sub_eps_mem_closure {i j : Fin r} (hij : i < j) :
    eps r i - eps r j ∈ AddSubmonoid.closure (Set.range (simpleRoot r)) := by
  obtain ⟨n, hn⟩ : ∃ n, j.val = i.val + n + 1 :=
    ⟨j.val - i.val - 1, by rw [Fin.lt_def] at hij; omega⟩
  induction n generalizing j with
  | zero =>
    have h : i.val + 1 < r := by have := j.isLt; omega
    have hj : j = ⟨i.val + 1, h⟩ := Fin.ext (by simp [hn])
    refine AddSubmonoid.subset_closure ⟨i, ?_⟩
    rw [simpleRoot_of_lt h, hj]
    simp [sub_eq_add_neg]
  | succ n ih =>
    set k : Fin r := ⟨i.val + n + 1, by have := j.isLt; omega⟩
    have hik : i < k := by rw [Fin.lt_def]; simp [k]
    have hkj : k.val + 1 < r := by have := j.isLt; simp [k]; omega
    have hj : j = ⟨k.val + 1, hkj⟩ := Fin.ext (by simp [k, hn]; omega)
    have h1 := ih hik (by simp [k])
    have h2 : eps r k - eps r j ∈ AddSubmonoid.closure (Set.range (simpleRoot r)) := by
      refine AddSubmonoid.subset_closure ⟨k, ?_⟩
      rw [simpleRoot_of_lt hkj, hj]
      simp [sub_eq_add_neg]
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

theorem eps_add_eps_mem_closure (hr : 2 ≤ r) {i j : Fin r} (hij : i < j) :
    eps r i + eps r j ∈ AddSubmonoid.closure (Set.range (simpleRoot r)) := by
  set q : Fin r := ⟨r - 1, by omega⟩
  set p : Fin r := ⟨r - 2, by omega⟩
  have hlast : eps r p + eps r q ∈ AddSubmonoid.closure (Set.range (simpleRoot r)) := by
    refine AddSubmonoid.subset_closure ⟨q, ?_⟩
    rw [simpleRoot_of_not_lt (by simp [q]; omega)]
    simp [p]
  have hq : ∀ i : Fin r, i < q → eps r i + eps r q ∈
      AddSubmonoid.closure (Set.range (simpleRoot r)) := by
    intro i hi
    by_cases hip : i = p
    · rw [hip]
      exact hlast
    · have hip' : i < p := by
        rw [Fin.lt_def] at hi ⊢
        simp [p, q, Fin.ext_iff] at hi hip ⊢
        omega
      have := add_mem (eps_sub_eps_mem_closure hip') hlast
      rwa [show eps r i - eps r p + (eps r p + eps r q) = eps r i + eps r q by abel] at this
  by_cases hjq : j = q
  · rw [hjq]
    exact hq i (hjq ▸ hij)
  · have hjq' : j < q := by
      rw [Fin.lt_def]
      have := j.isLt
      simp [q, Fin.ext_iff] at hjq ⊢
      omega
    have hiq : i < q := hij.trans hjq'
    have := add_mem (eps_sub_eps_mem_closure hiq) (hq j hjq')
    rwa [show eps r i - eps r q + (eps r j + eps r q) = eps r i + eps r j by abel] at this

theorem exists_nonneg_comb (hr : 2 ≤ r) {β : Fin r → ℤ} (hβ : β ∈ posRoots r) :
    ∃ c : Fin r → ℕ, β = ∑ i, c i • simpleRoot r i := by
  rw [← AddSubmonoid.mem_closure_range_iff_of_fintype]
  obtain ⟨i, j, hij, h | h⟩ := hβ <;> rw [h]
  · exact eps_sub_eps_mem_closure hij
  · exact eps_add_eps_mem_closure hr hij

end Combination


section Descent

variable (r) in
@[expose] def rootHeight : (Fin r → ℤ) →+ ℤ where
  toFun x := ∑ j, ((r : ℤ) - j) * x j
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

theorem rootHeight_apply (x : Fin r → ℤ) : rootHeight r x = ∑ j, ((r : ℤ) - j) * x j :=
  rfl

theorem rootHeight_eps (a : Fin r) : rootHeight r (eps r a) = r - a := by
  rw [rootHeight_apply]
  simp [eps_apply]

theorem rootHeight_sign_vec (s t : ℤ) (a b : Fin r) :
    rootHeight r (s • eps r a + t • eps r b) = s * (r - a) + t * (r - b) := by
  rw [map_add, map_zsmul, map_zsmul, rootHeight_eps, rootHeight_eps, smul_eq_mul, smul_eq_mul]

theorem mem_posRoots_iff_rootHeight_pos {α : Fin r → ℤ} (hα : α ∈ roots r) :
    α ∈ posRoots r ↔ 0 < rootHeight r α := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  rw [sign_vec_mem_posRoots_iff hab hs ht, rootHeight_sign_vec]
  have ha := a.isLt
  have hb := b.isLt
  have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
  rw [Fin.lt_def, Fin.lt_def]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp <;> omega

theorem rootHeight_pos_of_mem_posRoots {β : Fin r → ℤ} (hβ : β ∈ posRoots r) :
    0 < rootHeight r β :=
  (mem_posRoots_iff_rootHeight_pos (posRoots_subset_roots hβ)).mp hβ

theorem eq_one_of_forall_posRoots (hr : 2 ≤ r) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroup r) (h : ∀ β ∈ posRoots r, w β ∈ posRoots r) : w = 1 := by
  obtain ⟨σ, δ, hδ, rfl⟩ := hw
  have key : ∀ a b : Fin r, a < b → σ a < σ b ∧ (δ a : ℤ) = 1 := by
    intro a b hab
    have h1 := h ((1 : ℤ) • eps r a + (1 : ℤ) • eps r b)
      (by rw [sign_vec_mem_posRoots_iff hab.ne isSign_one isSign_one]; exact Or.inl ⟨hab, rfl⟩)
    have h2 := h ((1 : ℤ) • eps r a + (-1 : ℤ) • eps r b)
      (by rw [sign_vec_mem_posRoots_iff hab.ne isSign_one isSign_neg_one]
          exact Or.inl ⟨hab, rfl⟩)
    rw [signedPermAut_sign_vec, sign_vec_mem_posRoots_iff (σ.injective.ne hab.ne)
      (isSign_one.mul (isSign_unit _)) (isSign_one.mul (isSign_unit _))] at h1
    rw [signedPermAut_sign_vec, sign_vec_mem_posRoots_iff (σ.injective.ne hab.ne)
      (isSign_one.mul (isSign_unit _)) (isSign_neg_one.mul (isSign_unit _))] at h2
    rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
    · exact ⟨h1a, by linarith⟩
    · rcases h2 with ⟨h2a, -⟩ | ⟨-, h2b⟩
      · exact absurd h2a (not_lt.mpr h1a.le)
      · exfalso
        linarith
  have hmono : StrictMono σ := fun a b hab => (key a b hab).1
  have hσ : σ = 1 := Equiv.ext fun a => hmono.apply_eq
  set q : Fin r := ⟨r - 1, by omega⟩ with hq
  have hδ' : ∀ a, a ≠ q → δ a = 1 := by
    intro a ha
    have hlt : a < q := by
      rw [Fin.lt_def]
      have := a.isLt
      rw [Ne, Fin.ext_iff] at ha
      simp only [hq] at ha ⊢
      omega
    exact Units.ext (key a q hlt).2
  have hδq : δ q = 1 := by
    rw [Fintype.prod_eq_single q fun a ha => hδ' a ha] at hδ
    exact hδ
  have hδ1 : δ = 1 := funext fun a => by
    by_cases ha : a = q
    · rw [ha, hδq]
      rfl
    · exact hδ' a ha
  rw [hσ, hδ1, signedPermAut_one]

theorem exists_simpleRoot_neg (hr : 3 ≤ r) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroup r) (hne : w ≠ 1) : ∃ i, -(w⁻¹ (simpleRoot r i)) ∈ posRoots r := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hpos : ∀ i, w⁻¹ (simpleRoot r i) ∈ posRoots r := fun i =>
    ((mem_posRoots_or_neg_mem_posRoots (apply_mem_roots (inv_mem hw)
      (posRoots_subset_roots (simpleRoot_mem_posRoots (by omega) i)))).1).resolve_right (hcon i)
  have hall : ∀ β ∈ posRoots r, w⁻¹ β ∈ posRoots r := by
    intro β hβ
    obtain ⟨c, hc⟩ := exists_nonneg_comb (by omega) hβ
    have hroot := apply_mem_roots (inv_mem hw) (posRoots_subset_roots hβ)
    rw [mem_posRoots_iff_rootHeight_pos hroot, hc, map_sum, map_sum]
    simp only [map_nsmul]
    have hne0 : ∃ i, c i ≠ 0 := by
      by_contra h0
      simp only [not_exists, not_not] at h0
      apply ne_zero_of_mem_roots (posRoots_subset_roots hβ)
      rw [hc]
      simp [h0]
    obtain ⟨i, hi⟩ := hne0
    have hterm : 0 < c i • rootHeight r (w⁻¹ (simpleRoot r i)) :=
      nsmul_pos (rootHeight_pos_of_mem_posRoots (hpos i)) hi
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (fun j _ => nsmul_nonneg (rootHeight_pos_of_mem_posRoots (hpos j)).le _)
      (Finset.mem_univ i))
  exact hne (inv_eq_one.mp (eq_one_of_forall_posRoots (by omega) (inv_mem hw) hall))

variable (r) in
@[expose] def inversionSet (w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : Set (Fin r → ℤ) :=
  {β | β ∈ posRoots r ∧ -(w β) ∈ posRoots r}

variable (r) in
@[expose] noncomputable def weylLength (w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : ℕ :=
  (inversionSet r w).ncard

theorem inversionSet_simpleRefl_mul (hr : 2 ≤ r) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroup r) {i : Fin r} (hi : -(w⁻¹ (simpleRoot r i)) ∈ posRoots r) :
    inversionSet r (simpleRefl r i * w) = inversionSet r w \ {-(w⁻¹ (simpleRoot r i))} ∧
      -(w⁻¹ (simpleRoot r i)) ∈ inversionSet r w := by
  have hαpos := simpleRoot_mem_posRoots hr i
  have hwβ₀ : w (-(w⁻¹ (simpleRoot r i))) = -simpleRoot r i := by
    rw [map_neg, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hexcl : ∀ γ ∈ roots r, ¬(γ ∈ posRoots r ∧ -γ ∈ posRoots r) := fun γ hγ =>
    (mem_posRoots_or_neg_mem_posRoots hγ).2
  have hnegα : -simpleRoot r i ∉ posRoots r := fun h =>
    hexcl _ (posRoots_subset_roots hαpos) ⟨hαpos, h⟩
  have hsneg : simpleRefl r i (-simpleRoot r i) = simpleRoot r i := by
    rw [map_neg, simpleRefl_simpleRoot hr i, neg_neg]
  have hinv : ∀ β, w⁻¹ (w β) = β := fun β => by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  refine ⟨Set.ext fun β => ?_, hi, by rw [hwβ₀, neg_neg]; exact hαpos⟩
  simp only [inversionSet, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨hβ, hs⟩
    have hγ : w β ∈ roots r := apply_mem_roots hw (posRoots_subset_roots hβ)
    have hβ₀ : β ≠ -(w⁻¹ (simpleRoot r i)) := by
      rintro rfl
      rw [hwβ₀, hsneg] at hs
      exact hnegα hs
    refine ⟨⟨hβ, ?_⟩, hβ₀⟩
    rcases (mem_posRoots_or_neg_mem_posRoots hγ).1 with hpos | hneg
    · exfalso
      by_cases heq : w β = simpleRoot r i
      · have hβeq : β = w⁻¹ (simpleRoot r i) := by rw [← heq, hinv]
        rw [hβeq] at hβ
        exact hexcl _ (apply_mem_roots (inv_mem hw) (posRoots_subset_roots hαpos)) ⟨hβ, hi⟩
      · have := simpleRefl_mem_posRoots hr hpos heq
        exact hexcl _ (posRoots_subset_roots this) ⟨this, hs⟩
    · exact hneg
  · rintro ⟨⟨hβ, hγ⟩, hne⟩
    refine ⟨hβ, ?_⟩
    have hne' : -(w β) ≠ simpleRoot r i := by
      intro h
      apply hne
      rw [← hinv β, show w β = -simpleRoot r i by rw [← h, neg_neg], map_neg]
    have := simpleRefl_mem_posRoots hr hγ hne'
    rwa [map_neg] at this

theorem weylLength_simpleRefl_mul (hr : 2 ≤ r) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroup r) {i : Fin r} (hi : -(w⁻¹ (simpleRoot r i)) ∈ posRoots r) :
    weylLength r (simpleRefl r i * w) = weylLength r w - 1 := by
  obtain ⟨hset, hmem⟩ := inversionSet_simpleRefl_mul hr hw hi
  rw [weylLength, hset, Set.ncard_sdiff_singleton_of_mem hmem, ← weylLength]

theorem weylLength_pos (hr : 2 ≤ r) {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroup r) {i : Fin r} (hi : -(w⁻¹ (simpleRoot r i)) ∈ posRoots r) :
    0 < weylLength r w := by
  have hfin : (inversionSet r w).Finite := posRoots_finite.subset fun β hβ => hβ.1
  exact (Set.ncard_pos hfin).mpr ⟨_, (inversionSet_simpleRefl_mul hr hw hi).2⟩

theorem closure_simpleRefl (hr : 3 ≤ r) :
    Subgroup.closure (Set.range (simpleRefl r)) = weylGroup r := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun w hw => ?_
  · rintro _ ⟨i, rfl⟩
    exact simpleRefl_mem (by omega) i
  · have key : ∀ n, ∀ w ∈ weylGroup r, weylLength r w = n →
        w ∈ Subgroup.closure (Set.range (simpleRefl r)) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro w hw hn
        by_cases h1 : w = 1
        · rw [h1]
          exact one_mem _
        · obtain ⟨i, hi⟩ := exists_simpleRoot_neg hr hw h1
          have hpos := weylLength_pos (by omega) hw hi
          have hlen := weylLength_simpleRefl_mul (by omega) hw hi
          have hmem := ih (n - 1) (by omega) _ (mul_mem (simpleRefl_mem (by omega) i) hw)
            (by rw [hlen, hn])
          have hw' : w = simpleRefl r i * (simpleRefl r i * w) := by
            rw [← mul_assoc, simpleRefl_mul_self (by omega), one_mul]
          rw [hw']
          exact mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hmem
    exact key _ w hw rfl

theorem bijOn_simpleRefl (hr : 2 ≤ r) (i : Fin r) :
    Set.BijOn (simpleRefl r i) (posRoots r \ {simpleRoot r i}) (posRoots r \ {simpleRoot r i}) := by
  have hαpos := simpleRoot_mem_posRoots hr i
  have hinvol : ∀ x, simpleRefl r i (simpleRefl r i x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, simpleRefl_mul_self hr]
    rfl
  have hmaps : Set.MapsTo (simpleRefl r i) (posRoots r \ {simpleRoot r i})
      (posRoots r \ {simpleRoot r i}) := by
    rintro β ⟨hβ, hne⟩
    refine ⟨simpleRefl_mem_posRoots hr hβ hne, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h
    have : β = -simpleRoot r i := by rw [← hinvol β, h, simpleRefl_simpleRoot hr]
    rw [this] at hβ
    exact (mem_posRoots_or_neg_mem_posRoots (posRoots_subset_roots hαpos)).2 ⟨hαpos, hβ⟩
  refine ⟨hmaps, (simpleRefl r i).injective.injOn, fun γ hγ => ⟨simpleRefl r i γ, hmaps hγ,
    hinvol γ⟩⟩

end Descent


theorem orthogonal_geometry_split_D_signed_descent {r : ℕ} (hr : 3 ≤ r) :
    (∀ i, simpleRefl r i ∈ weylGroup r) ∧
      Subgroup.closure (Set.range (simpleRefl r)) = weylGroup r ∧
      (∀ α ∈ roots r, ∀ β ∈ roots r, ∃ w ∈ weylGroup r, w α = β) ∧
      (∀ i, simpleRefl r i (simpleRoot r i) = -simpleRoot r i ∧
        Set.BijOn (simpleRefl r i) (posRoots r \ {simpleRoot r i})
          (posRoots r \ {simpleRoot r i})) ∧
      (∀ β ∈ posRoots r, ∃ c : Fin r → ℕ, β = ∑ i, c i • simpleRoot r i) ∧
      (∀ w ∈ weylGroup r, w ≠ 1 → ∃ i, -(w⁻¹ (simpleRoot r i)) ∈ posRoots r) ∧
      (∀ w ∈ weylGroup r, ∀ i, -(w⁻¹ (simpleRoot r i)) ∈ posRoots r →
        weylLength r (simpleRefl r i * w) = weylLength r w - 1) :=
  ⟨simpleRefl_mem (by omega), closure_simpleRefl hr,
    fun _ hα _ hβ => exists_weyl_apply_eq hr hα hβ,
    fun i => ⟨simpleRefl_simpleRoot (by omega) i, bijOn_simpleRefl (by omega) i⟩,
    fun _ hβ => exists_nonneg_comb (by omega) hβ,
    fun _ hw hne => exists_simpleRoot_neg hr hw hne,
    fun _ hw _ hi => weylLength_simpleRefl_mul (by omega) hw hi⟩


end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
