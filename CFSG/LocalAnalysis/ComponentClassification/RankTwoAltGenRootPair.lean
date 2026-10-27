module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRootK

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

section Pair

variable {m : ℕ}

@[expose] def pairEmb {N : ℕ} (h : 2 * m ≤ N) : Fin m × Fin 2 ↪ Fin N where
  toFun kb := ⟨2 * kb.1 + kb.2, by have := kb.1.2; have := kb.2.2; omega⟩
  inj' := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h'
    have h2 : 2 * (k : ℕ) + b = 2 * k' + b' := by simpa using congrArg Fin.val h'
    have := b.2
    have := b'.2
    have hk : (k : ℕ) = k' := by omega
    have hb : (b : ℕ) = b' := by omega
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext hk, Fin.ext hb⟩

@[expose] def diagHom : Perm (Fin m) →* Perm (Fin m × Fin 2) where
  toFun σ := Equiv.prodCongr σ (Equiv.refl _)
  map_one' := by
    ext ⟨k, b⟩ <;> rfl
  map_mul' σ τ := by
    ext ⟨k, b⟩ <;> rfl

theorem diagHom_apply (σ : Perm (Fin m)) (k : Fin m) (b : Fin 2) :
    diagHom σ (k, b) = (σ k, b) :=
  rfl

@[expose] def zPair (m : ℕ) : Perm (Fin m × Fin 2) := Equiv.prodCongr (Equiv.refl _) (swap 0 1)

theorem zPair_apply (k : Fin m) (b : Fin 2) : zPair m (k, b) = (k, swap 0 1 b) :=
  rfl

@[expose] def tauPair (k : Fin m) : Perm (Fin m × Fin 2) := swap (k, 0) (k, 1)

theorem sign_diagHom (σ : Perm (Fin m)) : sign (diagHom σ) = 1 := by
  show sign (Equiv.prodCongr σ (Equiv.refl (Fin 2))) = 1
  rw [prodCongr_refl_right, sign_prodCongrLeft, Fin.prod_univ_two, Int.units_mul_self]

theorem sign_zPair (hm : Even m) : sign (zPair m) = 1 := by
  show sign (Equiv.prodCongr (Equiv.refl (Fin m)) (swap (0 : Fin 2) 1)) = 1
  rw [prodCongr_refl_left, sign_prodCongrRight, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, sign_swap (by decide), hm.neg_one_pow]

theorem sign_tauPair_mul (a b : Fin m) : sign (tauPair a * tauPair b) = 1 := by
  rw [Perm.sign_mul, tauPair, tauPair, sign_swap (by simp), sign_swap (by simp)]
  rfl

theorem diagHom_mul_zPair (σ : Perm (Fin m)) : diagHom σ * zPair m = zPair m * diagHom σ := by
  ext ⟨k, b⟩ <;> rfl

theorem tauPair_mul_zPair (k : Fin m) : tauPair k * zPair m = zPair m * tauPair k := by
  have h := swap_apply_apply (zPair m) (k, 0) (k, 1)
  rw [zPair_apply, zPair_apply, swap_apply_left, swap_apply_right, swap_comm] at h
  show swap (k, 0) (k, 1) * zPair m = zPair m * swap (k, 0) (k, 1)
  calc swap (k, 0) (k, 1) * zPair m = zPair m * swap (k, 0) (k, 1) * (zPair m)⁻¹ * zPair m := by
        rw [← h]
    _ = zPair m * swap (k, 0) (k, 1) := by group

theorem diagHom_conj_tauPair (σ : Perm (Fin m)) (k : Fin m) :
    diagHom σ * tauPair k * (diagHom σ)⁻¹ = tauPair (σ k) := by
  rw [tauPair, tauPair, ← swap_apply_apply, diagHom_apply, diagHom_apply]

theorem tauPair_mul_self (k : Fin m) : tauPair k * tauPair k = 1 :=
  swap_mul_self _ _

theorem tauPair_commute {a b : Fin m} (hab : a ≠ b) :
    tauPair a * tauPair b = tauPair b * tauPair a :=
  (Perm.Disjoint.commute (disjoint_swap_swap (by simp [hab]))).eq

theorem tauPair_apply (j k : Fin m) (b : Fin 2) :
    tauPair j (k, b) = if k = j then (k, swap 0 1 b) else (k, b) := by
  by_cases hkj : k = j
  · subst hkj
    simp only [ite_true, tauPair]
    fin_cases b <;> simp
  · simp only [hkj, ite_false, tauPair]
    rw [swap_apply_of_ne_of_ne] <;> simp [hkj]

@[expose] def zUpTo (m r : ℕ) : Perm (Fin m × Fin 2) where
  toFun kb := if (kb.1 : ℕ) < r then (kb.1, swap 0 1 kb.2) else kb
  invFun kb := if (kb.1 : ℕ) < r then (kb.1, swap 0 1 kb.2) else kb
  left_inv kb := by
    by_cases h : (kb.1 : ℕ) < r <;> simp [h]
  right_inv kb := by
    by_cases h : (kb.1 : ℕ) < r <;> simp [h]

theorem zUpTo_apply (r : ℕ) (k : Fin m) (b : Fin 2) :
    zUpTo m r (k, b) = if (k : ℕ) < r then (k, swap 0 1 b) else (k, b) :=
  rfl

theorem zUpTo_zero : zUpTo m 0 = 1 := by
  ext ⟨k, b⟩ <;> simp [zUpTo_apply]

theorem zUpTo_self : zUpTo m m = zPair m := by
  ext ⟨k, b⟩ <;> simp [zUpTo_apply, zPair_apply, k.2]

theorem zUpTo_add_two {r : ℕ} (hr : r + 2 ≤ m) :
    zUpTo m (r + 2) = zUpTo m r * (tauPair ⟨r, by omega⟩ * tauPair ⟨r + 1, by omega⟩) := by
  refine Equiv.ext fun ⟨k, b⟩ => ?_
  rw [Perm.mul_apply, Perm.mul_apply, tauPair_apply ⟨r + 1, by omega⟩ k b]
  by_cases h1 : (k : ℕ) = r + 1
  · have hk : k = ⟨r + 1, by omega⟩ := Fin.ext h1
    simp [hk, tauPair_apply, zUpTo_apply]
  · have hk1 : k ≠ ⟨r + 1, by omega⟩ := fun h => h1 (congrArg Fin.val h)
    simp only [hk1, ite_false]
    rw [tauPair_apply ⟨r, by omega⟩ k b]
    by_cases h2 : (k : ℕ) = r
    · have hk : k = ⟨r, by omega⟩ := Fin.ext h2
      simp [hk, zUpTo_apply]
    · have hk2 : k ≠ ⟨r, by omega⟩ := fun h => h2 (congrArg Fin.val h)
      simp only [hk2, ite_false, zUpTo_apply]
      by_cases h3 : (k : ℕ) < r
      · simp [h3, show (k : ℕ) < r + 2 by omega]
      · simp [h3, show ¬ (k : ℕ) < r + 2 by omega]

end Pair

section Closure

variable {m : ℕ}

@[expose] noncomputable def diagAlt :
    alternatingGroup (Fin m) →* alternatingGroup (Fin m × Fin 2) :=
  (diagHom.comp (alternatingGroup (Fin m)).subtype).codRestrict _ fun σ => by
    rw [mem_alternatingGroup]
    exact sign_diagHom _

theorem coe_diagAlt (σ : alternatingGroup (Fin m)) :
    ((diagAlt σ : alternatingGroup (Fin m × Fin 2)) : Perm (Fin m × Fin 2)) = diagHom σ :=
  rfl

theorem diagAlt_injective : Function.Injective (diagAlt (m := m)) := by
  intro σ τ h
  have h1 := congrArg (fun x : alternatingGroup (Fin m × Fin 2) => (x : Perm (Fin m × Fin 2))) h
  simp only [coe_diagAlt] at h1
  apply Subtype.ext
  refine Equiv.ext fun k => ?_
  have h2 := congrArg (fun π : Perm (Fin m × Fin 2) => (π (k, 0)).1) h1
  simpa [diagHom_apply] using h2

@[expose] noncomputable def betaAlt (hm : 2 ≤ m) : alternatingGroup (Fin m × Fin 2) :=
  ⟨tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩, by
    rw [mem_alternatingGroup]
    exact sign_tauPair_mul _ _⟩

@[expose] noncomputable def zAlt (hm : Even m) : alternatingGroup (Fin m × Fin 2) :=
  ⟨zPair m, by
    rw [mem_alternatingGroup]
    exact sign_zPair hm⟩

theorem zAlt_mem_sup (hm4 : 4 ≤ m) (hm : Even m) :
    zAlt hm ∈ diagAlt.range ⊔ diagAlt.range.map (MulAut.conj (betaAlt (by omega))).toMonoidHom := by
  set M : Subgroup (alternatingGroup (Fin m × Fin 2)) := (diagAlt (m := m)).range ⊔
    (diagAlt (m := m)).range.map (MulAut.conj (betaAlt (by omega))).toMonoidHom with hM
  set M' : Subgroup (Perm (Fin m × Fin 2)) := M.map (alternatingGroup (Fin m × Fin 2)).subtype
  have hD : ∀ σ : alternatingGroup (Fin m), diagHom (σ : Perm (Fin m)) ∈ M' := fun σ =>
    Subgroup.mem_map.mpr ⟨diagAlt σ, mem_sup_left (MonoidHom.mem_range.mpr ⟨σ, rfl⟩), rfl⟩
  have hDβ : ∀ σ : alternatingGroup (Fin m),
      tauPair (⟨0, by omega⟩ : Fin m) * tauPair ⟨1, by omega⟩ * diagHom (σ : Perm (Fin m)) *
        (tauPair (⟨0, by omega⟩ : Fin m) * tauPair ⟨1, by omega⟩)⁻¹ ∈ M' := by
    intro σ
    refine Subgroup.mem_map.mpr ⟨betaAlt (by omega) * diagAlt σ * (betaAlt (by omega))⁻¹,
      mem_sup_right ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨diagAlt σ, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, rfl⟩
  have h12 : tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩ ∈ M' := by
    let σ : alternatingGroup (Fin m) := ⟨swap ⟨1, by omega⟩ ⟨2, by omega⟩ *
      swap ⟨2, by omega⟩ ⟨3, by omega⟩, by
        rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Fin.ne_of_val_ne (by norm_num)),
          sign_swap (Fin.ne_of_val_ne (by norm_num))]
        rfl⟩
    have hσ0 : (σ : Perm (Fin m)) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      simp [σ, swap_apply_of_ne_of_ne]
    have hσ1 : (σ : Perm (Fin m)) ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
      simp [σ, swap_apply_of_ne_of_ne]
    have h1 := mul_mem (hDβ σ) (inv_mem (hD σ))
    have h2 : tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ * diagHom (σ : Perm (Fin m)) *
        (tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩)⁻¹ * (diagHom (σ : Perm (Fin m)))⁻¹ =
        tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩ := by
      have e0 := diagHom_conj_tauPair (σ : Perm (Fin m)) ⟨0, by omega⟩
      have e1 := diagHom_conj_tauPair (σ : Perm (Fin m)) ⟨1, by omega⟩
      rw [hσ0] at e0
      rw [hσ1] at e1
      have hinv : (tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ : Perm (Fin m × Fin 2))⁻¹ =
          tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ := by
        rw [mul_inv_rev, tauPair, tauPair, swap_inv, swap_inv,
          ← tauPair, ← tauPair, tauPair_commute (by simp [Fin.ext_iff])]
      have hc : tauPair (⟨0, by omega⟩ : Fin m) * tauPair ⟨1, by omega⟩ =
          tauPair ⟨1, by omega⟩ * tauPair ⟨0, by omega⟩ := tauPair_commute (by simp [Fin.ext_iff])
      calc tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ * diagHom (σ : Perm (Fin m)) *
            (tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩)⁻¹ * (diagHom (σ : Perm (Fin m)))⁻¹ =
          tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ *
            ((diagHom (σ : Perm (Fin m)) * tauPair ⟨0, by omega⟩ *
              (diagHom (σ : Perm (Fin m)))⁻¹) * (diagHom (σ : Perm (Fin m)) *
                tauPair ⟨1, by omega⟩ * (diagHom (σ : Perm (Fin m)))⁻¹)) := by
            rw [hinv]
            group
        _ = tauPair ⟨1, by omega⟩ * (tauPair ⟨0, by omega⟩ * tauPair ⟨0, by omega⟩) *
            tauPair ⟨2, by omega⟩ := by
            rw [e0, e1, hc]
            group
        _ = tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩ := by
            rw [tauPair_mul_self, mul_one]
    rw [← h2]
    exact h1
  have hpair : ∀ k : ℕ, (hk : 2 * k + 1 < m) →
      tauPair ⟨2 * k, by omega⟩ * tauPair ⟨2 * k + 1, hk⟩ ∈ M' := by
    intro k hk
    obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : alternatingGroup (Fin m),
        (σ : Perm (Fin m)) ⟨1, by omega⟩ = ⟨2 * k, by omega⟩ ∧
          (σ : Perm (Fin m)) ⟨2, by omega⟩ = ⟨2 * k + 1, hk⟩ := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk2
      · refine ⟨⟨swap ⟨2, by omega⟩ ⟨0, by omega⟩ * swap ⟨2, by omega⟩ ⟨1, by omega⟩, by
          rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Fin.ne_of_val_ne (by norm_num)),
          sign_swap (Fin.ne_of_val_ne (by norm_num))]
          rfl⟩, ?_, ?_⟩ <;> simp [swap_apply_of_ne_of_ne]
      · refine ⟨⟨swap ⟨1, by omega⟩ ⟨3, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩, by
          rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Fin.ne_of_val_ne (by norm_num)),
          sign_swap (Fin.ne_of_val_ne (by norm_num))]
          rfl⟩, ?_, ?_⟩ <;> simp [swap_apply_of_ne_of_ne]
      · have n12 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
        have n1a : (⟨1, by omega⟩ : Fin m) ≠ ⟨2 * k, by omega⟩ :=
          Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 * k by omega)
        have n1b : (⟨1, by omega⟩ : Fin m) ≠ ⟨2 * k + 1, hk⟩ :=
          Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 * k + 1 by omega)
        have n2b : (⟨2, by omega⟩ : Fin m) ≠ ⟨2 * k + 1, hk⟩ :=
          Fin.ne_of_val_ne (show (2 : ℕ) ≠ 2 * k + 1 by omega)
        have nab : (⟨2 * k + 1, hk⟩ : Fin m) ≠ ⟨2 * k, by omega⟩ :=
          Fin.ne_of_val_ne (show 2 * k + 1 ≠ 2 * k by omega)
        refine ⟨⟨swap ⟨1, by omega⟩ ⟨2 * k, by omega⟩ * swap ⟨2, by omega⟩ ⟨2 * k + 1, hk⟩, by
          rw [mem_alternatingGroup, Perm.sign_mul, sign_swap n1a, sign_swap n2b]
          rfl⟩, ?_, ?_⟩
        · show swap (⟨1, by omega⟩ : Fin m) ⟨2 * k, by omega⟩
            (swap (⟨2, by omega⟩ : Fin m) ⟨2 * k + 1, hk⟩ ⟨1, by omega⟩) = ⟨2 * k, by omega⟩
          rw [swap_apply_of_ne_of_ne n12 n1b, swap_apply_left]
        · show swap (⟨1, by omega⟩ : Fin m) ⟨2 * k, by omega⟩
            (swap (⟨2, by omega⟩ : Fin m) ⟨2 * k + 1, hk⟩ ⟨2, by omega⟩) = ⟨2 * k + 1, hk⟩
          rw [swap_apply_left, swap_apply_of_ne_of_ne n1b.symm nab]
    have h1 : diagHom (σ : Perm (Fin m)) * (tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩) *
        (diagHom (σ : Perm (Fin m)))⁻¹ ∈ M' :=
      mul_mem (mul_mem (hD σ) h12) (inv_mem (hD σ))
    have h2 : diagHom (σ : Perm (Fin m)) * (tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩) *
        (diagHom (σ : Perm (Fin m)))⁻¹ = tauPair ⟨2 * k, by omega⟩ * tauPair ⟨2 * k + 1, hk⟩ := by
      have e1 := diagHom_conj_tauPair (σ : Perm (Fin m)) ⟨1, by omega⟩
      have e2 := diagHom_conj_tauPair (σ : Perm (Fin m)) ⟨2, by omega⟩
      rw [hσ1] at e1
      rw [hσ2] at e2
      calc diagHom (σ : Perm (Fin m)) * (tauPair ⟨1, by omega⟩ * tauPair ⟨2, by omega⟩) *
            (diagHom (σ : Perm (Fin m)))⁻¹ =
          (diagHom (σ : Perm (Fin m)) * tauPair ⟨1, by omega⟩ * (diagHom (σ : Perm (Fin m)))⁻¹) *
            (diagHom (σ : Perm (Fin m)) * tauPair ⟨2, by omega⟩ *
              (diagHom (σ : Perm (Fin m)))⁻¹) := by group
        _ = _ := by rw [e1, e2]
    rw [← h2]
    exact h1
  have hup : ∀ k : ℕ, 2 * k ≤ m → zUpTo m (2 * k) ∈ M' := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.mul_zero, zUpTo_zero]; exact one_mem _
    | succ k ih =>
      intro hk
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, zUpTo_add_two (by omega)]
      exact mul_mem (ih (by omega)) (hpair k (by omega))
  obtain ⟨k, hk⟩ := hm
  have hz := hup k (by omega)
  rw [show 2 * k = m by omega, zUpTo_self] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have : y = zAlt ⟨k, hk⟩ := Subtype.ext hyz
  rw [← this]
  exact hy

theorem zAlt_mul_self (hm : Even m) : zAlt hm * zAlt hm = 1 := by
  apply Subtype.ext
  refine Equiv.ext fun ⟨k, b⟩ => ?_
  show zPair m (zPair m (k, b)) = (k, b)
  rw [zPair_apply, zPair_apply, swap_apply_self]

theorem zAlt_ne_one (hm : Even m) (hm0 : 0 < m) : zAlt hm ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : alternatingGroup (Fin m × Fin 2) =>
    ((x : Perm (Fin m × Fin 2)) (⟨0, hm0⟩, 0)).2) h
  simp only [zAlt] at h1
  rw [zPair_apply, swap_apply_left] at h1
  simp at h1

theorem diagAlt_mul_zAlt (hm : Even m) (σ : alternatingGroup (Fin m)) :
    diagAlt σ * zAlt hm = zAlt hm * diagAlt σ :=
  Subtype.ext (diagHom_mul_zPair (σ : Perm (Fin m)))

theorem betaAlt_mul_zAlt (hm2 : 2 ≤ m) (hm : Even m) :
    betaAlt hm2 * zAlt hm = zAlt hm * betaAlt hm2 := by
  apply Subtype.ext
  show tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩ * zPair m =
    zPair m * (tauPair ⟨0, by omega⟩ * tauPair ⟨1, by omega⟩)
  rw [mul_assoc, tauPair_mul_zPair, ← mul_assoc, tauPair_mul_zPair, mul_assoc]

theorem even_five_dvd_card_alternatingGroup (hm : 5 ≤ m) :
    Even (Nat.card (alternatingGroup (Fin m))) ∧ 5 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hm
  rw [hc, show Nat.factorial 5 = 2 * 60 by rfl, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨⟨30 * c, by ring⟩, ⟨12 * c, by ring⟩⟩

end Closure

section PairAlt

variable {m N : ℕ}

@[expose] noncomputable def pairAlt (h : 2 * m ≤ N) :
    alternatingGroup (Fin m × Fin 2) →* alternatingGroup (Fin N) :=
  ((viaEmbeddingHom (pairEmb h)).comp (alternatingGroup (Fin m × Fin 2)).subtype).codRestrict _
    fun x => by
      rw [MonoidHom.comp_apply, mem_alternatingGroup, sign_viaEmbeddingHom]
      exact x.2

theorem coe_pairAlt (h : 2 * m ≤ N) (x : alternatingGroup (Fin m × Fin 2)) :
    ((pairAlt h x : alternatingGroup (Fin N)) : Perm (Fin N)) =
      viaEmbeddingHom (pairEmb h) (x : Perm (Fin m × Fin 2)) :=
  rfl

theorem pairAlt_injective (h : 2 * m ≤ N) : Function.Injective (pairAlt h) := by
  intro x y hxy
  have h1 := congrArg (fun z : alternatingGroup (Fin N) => (z : Perm (Fin N))) hxy
  simp only [coe_pairAlt] at h1
  exact Subtype.ext (viaEmbeddingHom_injective _ h1)

end PairAlt

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

theorem false_of_conj_mem_of_six_le (h7 : 7 ≤ n) {m : ℕ} (hm6 : 6 ≤ m) (hm : Even m)
    (h2m : 2 * m ≤ n + 4) {x : G}
    (hx : x * Φ (pairAlt h2m (zAlt hm)) * x⁻¹ ∈ centralizer (A : Set G)) : False := by
  set Θ := Φ.comp (pairAlt h2m) with hΘdef
  have hΘ : Function.Injective Θ := s.injective.comp (pairAlt_injective h2m)
  set β := betaAlt (m := m) (by omega) with hβ
  set u := Θ (zAlt hm) with hu
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, zAlt_mul_self, map_one]
  have hu1 : u ≠ 1 := fun h1 => zAlt_ne_one hm (by omega) (hΘ (h1.trans (map_one Θ).symm))
  set S₁ := (Θ.comp diagAlt).range with hS₁
  set S₂ := S₁.map (MulAut.conj (Θ β)).toMonoidHom with hS₂
  have hcomm : ∀ y : alternatingGroup (Fin m × Fin 2), y * zAlt hm = zAlt hm * y →
      Θ y ∈ centralizer ({u} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff, hu, ← map_mul, ← map_mul, hy]
  have hS₁u : S₁ ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨σ, rfl⟩
    exact hcomm _ (diagAlt_mul_zAlt hm σ)
  have hS₂u : S₂ ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    have h1 : (MulAut.conj (Θ β)).toMonoidHom ((Θ.comp diagAlt) σ) = Θ (β * diagAlt σ * β⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, map_mul,
        map_inv]
    rw [h1]
    refine hcomm _ ?_
    have hb : Commute β (zAlt hm) := betaAlt_mul_zAlt (m := m) (by omega) hm
    have hd : Commute (diagAlt σ) (zAlt hm) := diagAlt_mul_zAlt hm σ
    exact ((hb.mul_left hd).mul_left hb.inv_left).eq
  have hinj₁ : Function.Injective (Θ.comp diagAlt) := hΘ.comp diagAlt_injective
  have e₁ : alternatingGroup (Fin m) ≃* S₁ := MonoidHom.ofInjective hinj₁
  have e₂ : S₁ ≃* S₂ := S₁.equivMapOfInjective _ (MulAut.conj (Θ β)).injective
  have hsimple : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hs₁ : IsSimpleGroup S₁ := MulEquiv.isSimpleGroup e₁.symm
  have hs₂ : IsSimpleGroup S₂ := MulEquiv.isSimpleGroup (e₁.trans e₂).symm
  obtain ⟨hev, h5⟩ := even_five_dvd_card_alternatingGroup (m := m) (by omega)
  have hc₁ : Nat.card S₁ = Nat.card (alternatingGroup (Fin m)) := (Nat.card_congr e₁.toEquiv).symm
  have hc₂ : Nat.card S₂ = Nat.card (alternatingGroup (Fin m)) :=
    (Nat.card_congr (e₁.trans e₂).toEquiv).symm
  have hA₁ := s.conj_le_of_simple h7 hu1 hu2 hx hS₁u hs₁ (hc₁ ▸ hev) (hc₁ ▸ h5)
  have hA₂ := s.conj_le_of_simple h7 hu1 hu2 hx hS₂u hs₂ (hc₂ ▸ hev) (hc₂ ▸ h5)
  have hz := Subgroup.mem_map_of_mem Θ (zAlt_mem_sup (by omega) hm)
  rw [Subgroup.map_sup] at hz
  have hle : (diagAlt.range.map Θ ⊔ (diagAlt.range.map (MulAut.conj
      (betaAlt (m := m) (by omega))).toMonoidHom).map Θ) ≤ S₁ ⊔ S₂ := by
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, rfl⟩
    · rintro _ ⟨_, ⟨_, ⟨σ, rfl⟩, rfl⟩, rfl⟩
      refine ⟨(Θ.comp diagAlt) σ, ⟨σ, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, map_mul,
        map_inv]
      rfl
  have hu' : u ∈ S₁ ⊔ S₂ := hle hz
  have hxu : x * u * x⁻¹ ∈ A := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hu'
    rw [Subgroup.map_sup] at h1
    exact sup_le hA₁ hA₂ h1
  have h1 : x * u * x⁻¹ ∈ A ⊓ centralizer (A : Set G) := ⟨hxu, hx⟩
  rw [s.inf_centralizer_eq_bot, mem_bot] at h1
  apply hu1
  calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
