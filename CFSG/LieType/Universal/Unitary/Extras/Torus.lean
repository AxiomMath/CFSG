module

public import CFSG.LieType.Universal.Unitary.Extras.Unipotent

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (σ) in
@[expose] noncomputable def tFun (k : Fin (n / 2)) (c : F) : Fin n → F :=
  if h : k.val + 1 < n / 2 then shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, h⟩) c
  else if Even n then longTorusFun (lowIdx k) c else heisTorusFun σ (lowIdx k) c

variable (hσ : ∀ c, σ (σ c) = c)

omit [Field F] in
theorem ite_mul_ite_eq {M : Type*} [Monoid M] (p : Prop) [Decidable p] (a b x y : M) :
    (if p then a else x) * (if p then b else y) = if p then a * b else x * y := by
  split_ifs <;> rfl

theorem tFun_one (k : Fin (n / 2)) : tFun σ k 1 = 1 := by
  funext s
  unfold tFun
  split_ifs
  · simp only [shortTorusFun]
    split_ifs <;> simp
  · simp only [longTorusFun]
    split_ifs <;> simp
  · simp only [heisTorusFun]
    split_ifs <;> simp

theorem tFun_mul (k : Fin (n / 2)) {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    tFun σ k (c * d) = tFun σ k c * tFun σ k d := by
  funext s
  simp only [Pi.mul_apply]
  unfold tFun
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  split_ifs
  · simp only [shortTorusFun]
    split_ifs <;> (try simp only [map_mul]) <;> ring
  · simp only [longTorusFun]
    split_ifs <;> ring
  · simp only [heisTorusFun]
    split_ifs <;> (try simp only [map_mul]) <;> ring

theorem tFun_inv (k : Fin (n / 2)) (c : F) :
    tFun σ k c⁻¹ = fun s => (tFun σ k c s)⁻¹ := by
  funext s
  unfold tFun
  split_ifs
  · simp only [shortTorusFun]
    split_ifs <;> simp only [map_inv₀, inv_one]
  · simp only [longTorusFun]
    split_ifs <;> ring
  · simp only [heisTorusFun]
    split_ifs <;> (try simp only [map_inv₀]) <;> ring

theorem tFun_ne_zero (k : Fin (n / 2)) {c : F} (hc : c ≠ 0) (s : Fin n) : tFun σ k c s ≠ 0 := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  unfold tFun
  split_ifs
  · simp only [shortTorusFun]
    split_ifs <;> simp [hc, hσc]
  · simp only [longTorusFun]
    split_ifs <;> simp [hc]
  · simp only [heisTorusFun]
    split_ifs <;> simp [hc, hσc]

theorem diagonal_inv_eq {g : SU σ n} {t : Fin n → F} (ht0 : ∀ s, t s ≠ 0)
    (hg : mat σ n g = diagonal t) : mat σ n g⁻¹ = diagonal fun s => (t s)⁻¹ := by
  have h1 : mat σ n g * diagonal (fun s => (t s)⁻¹) = 1 := by
    rw [hg, diagonal_mul_diagonal]
    convert diagonal_one (n := Fin n) (α := F) using 2
    funext s
    exact mul_inv_cancel₀ (ht0 s)
  have h3 : mat σ n g⁻¹ * mat σ n g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc mat σ n g⁻¹ = mat σ n g⁻¹ * (mat σ n g * diagonal fun s => (t s)⁻¹) := by
        rw [h1, Matrix.mul_one]
    _ = diagonal fun s => (t s)⁻¹ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem exists_tFun_of_mem_levelTorus {k : Fin (n / 2)} {x : SU σ n}
    (hx : x ∈ levelTorus σ k) : ∃ c : Fˣ, mat σ n x = diagonal (tFun σ k (c : F)) := by
  have key : ∀ S : Set (SU σ n), (∀ g ∈ S, ∃ c : Fˣ, mat σ n g = diagonal (tFun σ k (c : F))) →
      ∀ y ∈ Subgroup.closure S, ∃ c : Fˣ, mat σ n y = diagonal (tFun σ k (c : F)) := by
    intro S hS y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hS y hy
    | one => exact ⟨1, by rw [map_one, Units.val_one, tFun_one]; exact diagonal_one.symm⟩
    | mul y z _ _ hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨d, hd⟩ := hz
      exact ⟨c * d, by
        rw [map_mul, hc, hd, diagonal_mul_diagonal, Units.val_mul,
          tFun_mul k c.ne_zero d.ne_zero]
        rfl⟩
    | inv y _ hy =>
      obtain ⟨c, hc⟩ := hy
      refine ⟨c⁻¹, ?_⟩
      rw [diagonal_inv_eq (tFun_ne_zero k c.ne_zero) hc, Units.val_inv_eq_inv_val,
        tFun_inv k (c : F)]
  revert hx
  unfold levelTorus
  split_ifs with h1 h2
  · intro hx
    refine key _ (fun g hg => ?_) x hx
    obtain ⟨c, hc⟩ := hg
    refine ⟨c, ?_⟩
    rw [mat_apply, hc]
    unfold tFun
    rw [dite_eq_left h1]
  · intro hx
    refine key _ (fun g hg => ?_) x hx
    obtain ⟨c, -, hc⟩ := hg
    refine ⟨c, ?_⟩
    rw [mat_apply, hc]
    unfold tFun
    rw [dite_eq_right h1, ite_eq_left h2]
  · intro hx
    refine key _ (fun g hg => ?_) x hx
    obtain ⟨c, hc⟩ := hg
    refine ⟨c, ?_⟩
    rw [mat_apply, hc]
    unfold tFun
    rw [dite_eq_right h1, ite_eq_right h2]

theorem exists_diagonal_of_mem_levelTorus {k : Fin (n / 2)} {x : SU σ n}
    (hx : x ∈ levelTorus σ k) : ∃ t : Fin n → F, mat σ n x = diagonal t := by
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hx
  exact ⟨_, hc⟩

theorem torus_commute (i j : Fin (n / 2)) (h : SU σ n) (hh : h ∈ levelTorus σ i) (h' : SU σ n)
    (hh' : h' ∈ levelTorus σ j) : Commute h h' := by
  obtain ⟨t, ht⟩ := exists_diagonal_of_mem_levelTorus hh
  obtain ⟨t', ht'⟩ := exists_diagonal_of_mem_levelTorus hh'
  apply mat_injective
  rw [map_mul, map_mul, ht, ht', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext s
  exact mul_comm _ _

@[expose] noncomputable def prefixProd (k : Fin (n / 2)) (t : Fin n → F) : F :=
  ∏ a ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ k.val), t a

theorem prefixProd_mul (k : Fin (n / 2)) (t t' : Fin n → F) :
    prefixProd k (t * t') = prefixProd k t * prefixProd k t' := by
  simp only [prefixProd, Pi.mul_apply, Finset.prod_mul_distrib]

theorem shortTorusFun_left (a b : Fin n) (c : F) : shortTorusFun σ a b c a = c := by
  simp [shortTorusFun]

theorem shortTorusFun_right {a b : Fin n} (hab : a ≠ b) (c : F) :
    shortTorusFun σ a b c b = c⁻¹ := by
  simp [shortTorusFun, Ne.symm hab]

theorem shortTorusFun_of_ne {a b s : Fin n} (h1 : s ≠ a) (h2 : s ≠ b) (h3 : s ≠ Fin.rev a)
    (h4 : s ≠ Fin.rev b) (c : F) : shortTorusFun σ a b c s = 1 := by
  simp [shortTorusFun, h1, h2, h3, h4]

theorem longTorusFun_self (b : Fin n) (c : F) : longTorusFun b c b = c := by
  simp [longTorusFun]

theorem longTorusFun_of_ne {b s : Fin n} (h1 : s ≠ b) (h2 : s ≠ Fin.rev b) (c : F) :
    longTorusFun b c s = 1 := by
  simp [longTorusFun, h1, h2]

theorem heisTorusFun_self (b : Fin n) (c : F) : heisTorusFun σ b c b = c := by
  simp [heisTorusFun]

theorem heisTorusFun_of_ne {b s : Fin n} (h1 : s ≠ b) (h2 : s ≠ Fin.rev b)
    (h3 : Fin.rev s ≠ s) (c : F) : heisTorusFun σ b c s = 1 := by
  simp [heisTorusFun, h1, h2, h3]

theorem tFun_lowIdx_of_last {j : Fin (n / 2)} (h1 : ¬j.val + 1 < n / 2) (c : F) :
    tFun σ j c (lowIdx j) = c := by
  unfold tFun
  rw [dite_eq_right h1]
  split_ifs
  · exact longTorusFun_self _ _
  · exact heisTorusFun_self _ _

theorem tFun_of_last {j : Fin (n / 2)} (h1 : ¬j.val + 1 < n / 2) {s : Fin n}
    (h2 : s ≠ lowIdx j) (h3 : s ≠ Fin.rev (lowIdx j)) (h4 : Fin.rev s ≠ s) (c : F) :
    tFun σ j c s = 1 := by
  unfold tFun
  rw [dite_eq_right h1]
  split_ifs
  · exact longTorusFun_of_ne h2 h3 c
  · exact heisTorusFun_of_ne h2 h3 h4 c

theorem prefixProd_tFun (j k : Fin (n / 2)) {c : F} (hc : c ≠ 0) :
    prefixProd k (tFun σ j c) = if j = k then c else 1 := by
  have hj := j.isLt
  have hk := k.isLt
  unfold prefixProd
  rw [Finset.prod_filter]
  have hlow : ∀ (b : Fin n) (l : Fin (n / 2)), b.val ≤ k.val → b ≠ Fin.rev (lowIdx l) := by
    intro b l hb h
    have h' := congrArg Fin.val h
    have := l.isLt
    simp only [Fin.val_rev, val_lowIdx] at h'
    omega
  have hlow' : ∀ b : Fin n, b.val ≤ k.val → Fin.rev b ≠ b := by
    intro b hb h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  by_cases h1 : j.val + 1 < n / 2
  · have htf : tFun σ j c = shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, h1⟩) c := by
      unfold tFun
      rw [dite_eq_left h1]
    rw [htf, Finset.prod_eq_mul (lowIdx j) (lowIdx ⟨j.val + 1, h1⟩) (lowIdx_ne_succ h1)]
    · rw [shortTorusFun_left, shortTorusFun_right (lowIdx_ne_succ h1)]
      have e1 : (lowIdx (n := n) j).val = j.val := rfl
      have e2 : (lowIdx (n := n) ⟨j.val + 1, h1⟩).val = j.val + 1 := rfl
      by_cases hjk : j = k
      · have hjk' : j.val = k.val := congrArg Fin.val hjk
        rw [ite_eq_left hjk]
        split_ifs with h3 h4
        · exfalso
          omega
        · rw [mul_one]
        · exfalso
          omega
        · exfalso
          omega
      · have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        rw [ite_eq_right hjk]
        split_ifs with h3 h4
        · exact mul_inv_cancel₀ hc
        · exfalso
          omega
        · exfalso
          omega
        · rw [mul_one]
    · intro b _ hb
      split_ifs with hbk
      · exact shortTorusFun_of_ne hb.1 hb.2 (hlow b j hbk) (hlow b _ hbk) c
      · rfl
    · simp
    · simp
  · rw [Finset.prod_eq_single (lowIdx j)]
    · rw [tFun_lowIdx_of_last h1]
      have e1 : (lowIdx (n := n) j).val = j.val := rfl
      by_cases hjk : j = k
      · have hjk' : j.val = k.val := congrArg Fin.val hjk
        rw [ite_eq_left hjk]
        split_ifs with h3
        · rfl
        · exfalso
          omega
      · have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        rw [ite_eq_right hjk]
        split_ifs with h3
        · exfalso
          omega
        · rfl
    · intro b _ hb
      split_ifs with hbk
      · exact tFun_of_last h1 hb (hlow b j hbk) (hlow' b hbk) c
      · rfl
    · simp

theorem torus_iSupIndep : iSupIndep (levelTorus σ : Fin (n / 2) → Subgroup (SU σ n)) := by
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hxk
  have hP : ∃ t : Fin n → F, mat σ n x = diagonal t ∧ prefixProd k t = 1 := by
    rw [iSup_subtype'] at hx
    refine Subgroup.iSup_induction _ hx (C := fun x => ∃ t : Fin n → F,
      mat σ n x = diagonal t ∧ prefixProd k t = 1) (fun j y hy => ?_)
      ⟨1, by rw [map_one]; exact diagonal_one.symm, by simp [prefixProd]⟩ ?_
    · obtain ⟨d, hd⟩ := exists_tFun_of_mem_levelTorus hy
      exact ⟨_, hd, by rw [prefixProd_tFun _ _ d.ne_zero, ite_eq_right j.2]⟩
    · rintro y z ⟨t, ht, ht1⟩ ⟨t', ht', ht1'⟩
      exact ⟨t * t', by rw [map_mul, ht, ht', diagonal_mul_diagonal]; rfl,
        by rw [prefixProd_mul, ht1, ht1', mul_one]⟩
  obtain ⟨t, ht, ht1⟩ := hP
  have htt : tFun σ k (c : F) = t := diagonal_injective (hc.symm.trans ht)
  rw [← htt, prefixProd_tFun _ _ c.ne_zero, ite_eq_left rfl] at ht1
  apply mat_injective
  rw [hc, ht1, tFun_one, map_one]
  exact diagonal_one

theorem torus_inf_posPart :
    (⨆ i, levelTorus σ i) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ 0 < ht γ},
        rootGroup σ hσ n γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  have hdiag : ∃ t : Fin n → F, mat σ n x = diagonal t := by
    refine Subgroup.iSup_induction _ hxt (C := fun x => ∃ t : Fin n → F, mat σ n x = diagonal t)
      (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
      ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ ?_
    rintro y z ⟨t, ht⟩ ⟨t', ht'⟩
    exact ⟨t * t', by rw [map_mul, ht, ht', diagonal_mul_diagonal]; rfl⟩
  obtain ⟨t, ht⟩ := hdiag
  have hpos := idBelow_of_mem_iSup hσ 1 _ (fun γ hγ => by have := hγ.2; omega) hxp
  apply mat_injective
  rw [map_one]
  ext a b
  by_cases hab : a = b
  · subst hab
    exact hpos a a (by simp)
  · rw [ht, diagonal_apply_ne _ hab, one_apply_ne hab]

end CFSG.LieType.Universal.Unitary.SUExtras
