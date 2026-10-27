module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRootPair

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

section Model

@[expose] def flipB (b : Fin 4 → Bool) : Perm (Fin 4 × Fin 2) where
  toFun kc := (kc.1, if b kc.1 then swap 0 1 kc.2 else kc.2)
  invFun kc := (kc.1, if b kc.1 then swap 0 1 kc.2 else kc.2)
  left_inv kc := by
    rcases kc with ⟨k, c⟩
    by_cases h : b k <;> simp [h]
  right_inv kc := by
    rcases kc with ⟨k, c⟩
    by_cases h : b k <;> simp [h]

theorem flipB_apply (b : Fin 4 → Bool) (k : Fin 4) (c : Fin 2) :
    flipB b (k, c) = (k, if b k then swap 0 1 c else c) :=
  rfl

@[expose] def cz (τ : Perm (Fin 4)) (b : Fin 4 → Bool) : Perm (Fin 4 × Fin 2) :=
  diagHom τ * flipB b

theorem cz_apply (τ : Perm (Fin 4)) (b : Fin 4 → Bool) (k : Fin 4) (c : Fin 2) :
    cz τ b (k, c) = (τ k, if b k then swap 0 1 c else c) :=
  rfl

@[expose] def evenB (b : Fin 4 → Bool) : Bool :=
  !(xor (xor (b 0) (b 1)) (xor (b 2) (b 3)))

theorem cz_one (b : Fin 4 → Bool) : cz 1 b = flipB b := by
  rw [cz, map_one, one_mul]

theorem cz_mul_cz (τ τ' : Perm (Fin 4)) (b b' : Fin 4 → Bool) :
    cz τ b * cz τ' b' = cz (τ * τ') (fun k => xor (b' k) (b (τ' k))) := by
  ext ⟨k, c⟩
  · rfl
  · simp only [Perm.mul_apply, cz_apply]
    cases b' k <;> cases b (τ' k) <;> simp

theorem cz_mul_flipB (τ : Perm (Fin 4)) (b c : Fin 4 → Bool) :
    cz τ b * flipB c = cz τ (fun k => xor (c k) (b k)) := by
  rw [← cz_one, cz_mul_cz, mul_one]
  rfl

theorem cz_injective {τ τ' : Perm (Fin 4)} {b b' : Fin 4 → Bool} (h : cz τ b = cz τ' b') :
    τ = τ' := by
  ext k
  have h1 := congrArg (fun g : Perm (Fin 4 × Fin 2) => (g (k, 0)).1) h
  simpa only [cz_apply] using congrArg Fin.val h1

theorem exists_eq_cz {g : Perm (Fin 4 × Fin 2)} (hg : g * zPair 4 = zPair 4 * g) :
    ∃ τ b, g = cz τ b := by
  have hg1 : ∀ k, g (k, 1) = ((g (k, 0)).1, swap 0 1 (g (k, 0)).2) := by
    intro k
    have h := congrArg (· (k, 0)) hg
    simp only [Perm.mul_apply, zPair_apply] at h
    rw [show (swap (0 : Fin 2) 1) 0 = 1 from swap_apply_left _ _] at h
    rw [h]
    rfl
  set f : Fin 4 → Fin 4 := fun k => (g (k, 0)).1 with hf
  have hfin2 : ∀ u v : Fin 2, u = v ∨ v = swap 0 1 u := by decide
  have hfi : Function.Injective f := by
    intro k k' hkk
    rcases hfin2 (g (k, 0)).2 (g (k', 0)).2 with hc | hc
    · have : g (k, 0) = g (k', 0) := Prod.ext hkk hc
      exact congrArg Prod.fst (g.injective this)
    · have : g (k', 0) = g (k, 1) := by
        rw [hg1 k]
        exact Prod.ext hkk.symm hc
      have h2 := g.injective this
      simp at h2
  let τ : Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  refine ⟨τ, fun k => decide ((g (k, 0)).2 = 1), ?_⟩
  ext ⟨k, c⟩
  · rw [cz_apply]
    fin_cases c
    · rfl
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hg1]
      rfl
  · rw [cz_apply]
    have hv : (g (k, 0)).2 = 0 ∨ (g (k, 0)).2 = 1 := by
      rcases (g (k, 0)).2 with ⟨v, hv⟩
      interval_cases v <;> simp
    fin_cases c
    · rcases hv with hv | hv <;> simp [hv]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hg1]
      rcases hv with hv | hv <;> simp [hv]

end Model

section Checks

theorem cz_eq_cz_iff {τ τ' : Perm (Fin 4)} {b b' : Fin 4 → Bool} :
    cz τ b = cz τ' b' ↔ τ = τ' ∧ b = b' := by
  refine ⟨fun h => ⟨cz_injective h, funext fun k => ?_⟩, fun h => by rw [h.1, h.2]⟩
  have h1 := congrArg (fun g : Perm (Fin 4 × Fin 2) => (g (k, 0)).2) h
  simp only [cz_apply] at h1
  cases hb : b k <;> cases hb' : b' k <;> simp_all

theorem one_eq_cz : (1 : Perm (Fin 4 × Fin 2)) = cz 1 (fun _ => false) := by
  ext ⟨k, c⟩ <;> rfl

theorem zPair_eq_cz : zPair 4 = cz 1 (fun _ => true) := by
  ext ⟨k, c⟩ <;> rfl

theorem sign_flipB : ∀ c : Fin 4 → Bool, sign (flipB c) = 1 ↔ evenB c = true := by
  decide

theorem sign_cz (τ : Perm (Fin 4)) (b : Fin 4 → Bool) : sign (cz τ b) = sign (flipB b) := by
  rw [cz, Perm.sign_mul, sign_diagHom, one_mul]

theorem xor_comp_of_even : ∀ τ : Perm (Fin 4), τ * τ = 1 → (∀ i, τ i ≠ i) →
    ∀ d : Fin 4 → Bool, evenB d = true →
      (∀ k, xor (d k) (d (τ k)) = false) ∨ (∀ k, xor (d k) (d (τ k)) = true) := by
  decide

theorem exists_even_xor_invariant : ∀ τ : Perm (Fin 4), τ * τ = 1 → τ ≠ 1 → (∃ i, τ i = i) →
    ∀ b : Fin 4 → Bool, ∃ c : Fin 4 → Bool, evenB c = true ∧
      ∀ k, xor (c k) (b k) = xor (c (τ k)) (b (τ k)) := by
  decide

theorem cz_sq (τ : Perm (Fin 4)) (b : Fin 4 → Bool) :
    cz τ b * cz τ b = cz (τ * τ) (fun k => xor (b k) (b (τ k))) :=
  cz_mul_cz τ τ b b

theorem cz_one_mem_of_const {e : Fin 4 → Bool}
    (h : (∀ k, e k = false) ∨ (∀ k, e k = true)) :
    cz 1 e = 1 ∨ cz 1 e = zPair 4 := by
  rcases h with h | h
  · left
    rw [one_eq_cz, cz_eq_cz_iff]
    exact ⟨rfl, funext h⟩
  · right
    rw [zPair_eq_cz, cz_eq_cz_iff]
    exact ⟨rfl, funext h⟩

theorem exists_flipB_sq_of_fixed {τ : Perm (Fin 4)} (b : Fin 4 → Bool) (h2 : τ * τ = 1)
    (h1 : τ ≠ 1) (hfix : ∃ i, τ i = i) : ∃ c : Fin 4 → Bool, evenB c = true ∧
      cz τ b * flipB c * (cz τ b * flipB c) = 1 := by
  obtain ⟨c, hc, hinv⟩ := exists_even_xor_invariant τ h2 h1 hfix b
  refine ⟨c, hc, ?_⟩
  rw [cz_mul_flipB, cz_sq, h2, one_eq_cz, cz_eq_cz_iff]
  refine ⟨rfl, funext fun k => ?_⟩
  rw [hinv k]
  simp

theorem cz_sq_mem_of_even {τ : Perm (Fin 4)} {b : Fin 4 → Bool} (h2 : τ * τ = 1)
    (hfpf : ∀ i, τ i ≠ i) (hb : evenB b = true) :
    cz τ b * cz τ b = 1 ∨ cz τ b * cz τ b = zPair 4 := by
  rw [cz_sq, h2]
  exact cz_one_mem_of_const (xor_comp_of_even τ h2 hfpf b hb)

theorem fpf_mul_fpf : ∀ τ τ' : Perm (Fin 4), τ * τ = 1 → (∀ i, τ i ≠ i) → τ' * τ' = 1 →
    (∀ i, τ' i ≠ i) → τ ≠ τ' → τ * τ' * (τ * τ') = 1 ∧ ∀ i, (τ * τ') i ≠ i := by
  decide

theorem fpf_sq_of_pow_four : ∀ τ : Perm (Fin 4), τ ^ 4 = 1 → τ * τ ≠ 1 →
    τ * τ * (τ * τ) = 1 ∧ ∀ i, (τ * τ) i ≠ i := by
  decide

theorem pow_four_or_pow_three : ∀ τ : Perm (Fin 4), τ ^ 4 = 1 ∨ τ ^ 3 = 1 := by
  decide

end Checks

section Lift

variable {N : ℕ} (h8 : 2 * 4 ≤ N)

@[expose] noncomputable def pi0 : Perm (Fin N) := viaEmbeddingHom (pairEmb h8) (zPair 4)

@[expose] def unpair (x : Fin N) : Fin 4 × Fin 2 :=
  (⟨(x : ℕ) / 2 % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨(x : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩)

variable {h8}

theorem val_pairEmb (kc : Fin 4 × Fin 2) :
    ((pairEmb h8 kc : Fin N) : ℕ) = 2 * (kc.1 : ℕ) + kc.2 :=
  rfl

theorem pairEmb_lt (kc : Fin 4 × Fin 2) : ((pairEmb h8 kc : Fin N) : ℕ) < 8 := by
  rw [val_pairEmb]
  have := kc.1.2
  have := kc.2.2
  omega

theorem unpair_pairEmb (kc : Fin 4 × Fin 2) : unpair (pairEmb h8 kc) = kc := by
  rcases kc with ⟨⟨k, hk⟩, ⟨c, hc⟩⟩
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [unpair, val_pairEmb] <;> omega

theorem pairEmb_unpair {x : Fin N} (hx : (x : ℕ) < 8) : pairEmb h8 (unpair x) = x := by
  apply Fin.ext
  rw [val_pairEmb]
  simp only [unpair]
  omega

theorem mem_range_pairEmb {x : Fin N} : x ∈ Set.range (pairEmb h8) ↔ (x : ℕ) < 8 :=
  ⟨by rintro ⟨kc, rfl⟩; exact pairEmb_lt kc, fun hx => ⟨unpair x, pairEmb_unpair hx⟩⟩

theorem pi0_pairEmb (kc : Fin 4 × Fin 2) : pi0 h8 (pairEmb h8 kc) = pairEmb h8 (zPair 4 kc) :=
  viaEmbeddingHom_apply_image _ _ _

theorem pi0_of_le {x : Fin N} (hx : 8 ≤ (x : ℕ)) : pi0 h8 x = x :=
  viaEmbeddingHom_apply_of_notMem _ _ (by rw [mem_range_pairEmb]; omega)

theorem zPair_mul_self : zPair 4 * zPair 4 = 1 := by
  ext ⟨k, c⟩
  · rfl
  · simp [zPair_apply]

theorem pi0_mul_self : pi0 h8 * pi0 h8 = 1 := by
  rw [pi0, ← map_mul, zPair_mul_self, map_one]

theorem pi0_pi0 (x : Fin N) : pi0 h8 (pi0 h8 x) = x := by
  rw [← Perm.mul_apply, pi0_mul_self, Perm.one_apply]

theorem zPair_ne : ∀ kc : Fin 4 × Fin 2, zPair 4 kc ≠ kc := by decide

theorem pi0_ne_iff (x : Fin N) : pi0 h8 x ≠ x ↔ (x : ℕ) < 8 := by
  constructor
  · intro h
    by_contra hx
    exact h (pi0_of_le (by omega))
  · intro hx h
    rw [← pairEmb_unpair (h8 := h8) hx, pi0_pairEmb] at h
    exact zPair_ne _ ((pairEmb h8).injective h)

theorem pi0_mem_centralizer : pi0 h8 ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))) :=
  mem_centralizer_singleton_iff.mpr rfl

theorem lt_eight_iff_of_mem {σ : Perm (Fin N)}
    (hσ : σ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) (x : Fin N) :
    ((σ x : Fin N) : ℕ) < 8 ↔ (x : ℕ) < 8 := by
  have hc : σ (pi0 h8 x) = pi0 h8 (σ x) := by
    rw [← Perm.mul_apply, mem_centralizer_singleton_iff.mp hσ, Perm.mul_apply]
  rw [← pi0_ne_iff (h8 := h8), ← pi0_ne_iff (h8 := h8), ← hc]
  exact σ.injective.ne_iff

@[expose] noncomputable def rho8Perm (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    Perm (Fin 4 × Fin 2) where
  toFun kc := unpair ((σ : Perm (Fin N)) (pairEmb h8 kc))
  invFun kc := unpair ((σ : Perm (Fin N))⁻¹ (pairEmb h8 kc))
  left_inv kc := by
    have hlt := (lt_eight_iff_of_mem σ.2 (pairEmb h8 kc)).mpr (pairEmb_lt kc)
    change unpair ((σ : Perm (Fin N))⁻¹ (pairEmb h8 (unpair _))) = kc
    rw [pairEmb_unpair hlt, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply, unpair_pairEmb]
  right_inv kc := by
    have hlt := (lt_eight_iff_of_mem (inv_mem σ.2) (pairEmb h8 kc)).mpr (pairEmb_lt kc)
    change unpair ((σ : Perm (Fin N)) (pairEmb h8 (unpair _))) = kc
    rw [pairEmb_unpair hlt, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply, unpair_pairEmb]

theorem rho8Perm_apply (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) (kc : Fin 4 × Fin 2) :
    rho8Perm σ kc = unpair ((σ : Perm (Fin N)) (pairEmb h8 kc)) :=
  rfl

@[expose] noncomputable def rho8 :
    centralizer ({pi0 h8} : Set (Perm (Fin N))) →* Perm (Fin 4 × Fin 2) where
  toFun := rho8Perm
  map_one' := Equiv.ext fun kc => unpair_pairEmb (h8 := h8) kc
  map_mul' σ τ := by
    refine Equiv.ext fun kc => ?_
    have hlt := (lt_eight_iff_of_mem τ.2 (pairEmb h8 kc)).mpr (pairEmb_lt kc)
    rw [Perm.mul_apply, rho8Perm_apply, rho8Perm_apply, rho8Perm_apply, pairEmb_unpair hlt]
    rfl

theorem rho8_apply (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) (kc : Fin 4 × Fin 2) :
    rho8 σ kc = unpair ((σ : Perm (Fin N)) (pairEmb h8 kc)) :=
  rfl

theorem pairEmb_rho8 (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) (kc : Fin 4 × Fin 2) :
    pairEmb h8 (rho8 σ kc) = (σ : Perm (Fin N)) (pairEmb h8 kc) := by
  rw [rho8_apply]
  exact pairEmb_unpair ((lt_eight_iff_of_mem σ.2 (pairEmb h8 kc)).mpr (pairEmb_lt kc))

theorem rho8_pi0 : rho8 ⟨pi0 h8, pi0_mem_centralizer⟩ = zPair 4 := by
  refine Equiv.ext fun kc => ?_
  rw [rho8_apply]
  exact (congrArg unpair (pi0_pairEmb kc)).trans (unpair_pairEmb _)

theorem rho8_comm (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    rho8 σ * zPair 4 = zPair 4 * rho8 σ := by
  rw [← rho8_pi0 (h8 := h8), ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp σ.2)

@[expose] noncomputable def blk (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) : Perm (Fin 4) :=
  Classical.choose (exists_eq_cz (rho8_comm σ))

theorem exists_rho8_eq (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    ∃ b, rho8 σ = cz (blk σ) b :=
  Classical.choose_spec (exists_eq_cz (rho8_comm σ))

theorem blk_eq {σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))} {τ : Perm (Fin 4)}
    {b : Fin 4 → Bool} (h : rho8 σ = cz τ b) : blk σ = τ := by
  obtain ⟨b', hb'⟩ := exists_rho8_eq σ
  exact (cz_injective (hb'.symm.trans h))

theorem blk_mul (σ τ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    blk (σ * τ) = blk σ * blk τ := by
  obtain ⟨b, hb⟩ := exists_rho8_eq σ
  obtain ⟨b', hb'⟩ := exists_rho8_eq τ
  exact blk_eq (by rw [map_mul, hb, hb', cz_mul_cz])

theorem blk_one : blk (1 : centralizer ({pi0 h8} : Set (Perm (Fin N)))) = 1 :=
  blk_eq (b := fun _ => false) (by rw [map_one, one_eq_cz])

theorem blk_pow (σ : centralizer ({pi0 h8} : Set (Perm (Fin N)))) (m : ℕ) :
    blk (σ ^ m) = blk σ ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, blk_one]
  | succ m ih => rw [pow_succ, pow_succ, blk_mul, ih]

@[expose] def Y8 (h8 : 2 * 4 ≤ N) : Subgroup (Perm (Fin N)) where
  carrier := {σ | sign σ = 1 ∧ ∀ x, σ x = x ∨ σ x = pi0 h8 x}
  mul_mem' := by
    rintro σ τ ⟨hσs, hσ⟩ ⟨hτs, hτ⟩
    refine ⟨by rw [Perm.sign_mul, hσs, hτs, one_mul], fun x => ?_⟩
    rw [Perm.mul_apply]
    rcases hτ x with h | h <;> rw [h]
    · exact hσ x
    · rcases hσ (pi0 h8 x) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [h', pi0_pi0])
  one_mem' := ⟨sign_one, fun _ => Or.inl rfl⟩
  inv_mem' := by
    rintro σ ⟨hσs, hσ⟩
    have hss : ∀ x, σ (σ x) = x := by
      intro x
      rcases hσ x with h | h
      · rw [h, h]
      · rw [h]
        rcases hσ (pi0 h8 x) with h' | h'
        · have hx : pi0 h8 x = x := σ.injective (h'.trans h.symm)
          rw [h', hx]
        · rw [h', pi0_pi0]
    refine ⟨by rw [sign_inv, hσs], fun x => ?_⟩
    have hinv : σ⁻¹ x = σ x := by rw [Perm.inv_eq_iff_eq, hss]
    rw [hinv]
    exact hσ x

theorem pi0_mem_Y8 : pi0 h8 ∈ Y8 h8 :=
  ⟨by rw [pi0, sign_viaEmbeddingHom, sign_zPair ⟨2, rfl⟩], fun _ => Or.inr rfl⟩

theorem Y8_le_centralizer : Y8 h8 ≤ centralizer ({pi0 h8} : Set (Perm (Fin N))) := by
  rintro σ ⟨-, hσ⟩
  rw [mem_centralizer_singleton_iff]
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : pi0 h8 x = x
  · have h1 : σ x = x := by rcases hσ x with h | h <;> [exact h; exact h.trans hx]
    rw [hx, h1, hx]
  · rcases hσ x with h | h
    · rcases hσ (pi0 h8 x) with h' | h'
      · rw [h', h]
      · exact absurd (σ.injective (h'.trans (pi0_pi0 x) |>.trans h.symm)) hx
    · rcases hσ (pi0 h8 x) with h' | h'
      · exact absurd (σ.injective (h'.trans h.symm)) hx
      · rw [h', pi0_pi0, h, pi0_pi0]

theorem apply_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) {x : Fin N} (hx : 8 ≤ (x : ℕ)) :
    σ x = x := by
  rcases hσ.2 x with h | h
  · exact h
  · rw [h, pi0_of_le hx]

theorem mul_self_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) : σ * σ = 1 := by
  have h := inv_mem hσ
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hσ.2 x with h1 | h1
  · rw [h1, h1]
  · rw [h1]
    rcases hσ.2 (pi0 h8 x) with h2 | h2
    · rw [h2]
      exact σ.injective (h2.trans h1.symm)
    · rw [h2, pi0_pi0]

theorem eq_of_rho8_eq {σ τ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) (hτ : τ ∈ Y8 h8)
    (h : rho8 ⟨σ, Y8_le_centralizer hσ⟩ = rho8 ⟨τ, Y8_le_centralizer hτ⟩) : σ = τ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : (x : ℕ) < 8
  · rw [← pairEmb_unpair (h8 := h8) hx]
    have h1 := pairEmb_rho8 ⟨σ, Y8_le_centralizer hσ⟩ (unpair x)
    have h2 := pairEmb_rho8 ⟨τ, Y8_le_centralizer hτ⟩ (unpair x)
    rw [h] at h1
    exact h1.symm.trans h2
  · rw [apply_of_mem_Y8 hσ (by omega), apply_of_mem_Y8 hτ (by omega)]

theorem exists_rho8_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) :
    ∃ c, evenB c = true ∧ rho8 ⟨σ, Y8_le_centralizer hσ⟩ = flipB c := by
  obtain ⟨b, hb⟩ := exists_rho8_eq ⟨σ, Y8_le_centralizer hσ⟩
  have hblk : blk ⟨σ, Y8_le_centralizer hσ⟩ = 1 := by
    ext k
    have h1 := congrArg (fun g : Perm (Fin 4 × Fin 2) => (g (k, 0)).1) hb
    simp only [cz_apply] at h1
    rw [← h1, rho8_apply]
    rcases hσ.2 (pairEmb h8 (k, 0)) with h | h
    · rw [h, unpair_pairEmb]
      rfl
    · rw [h, pi0_pairEmb, unpair_pairEmb]
      rfl
  rw [hblk, cz_one] at hb
  refine ⟨b, ?_, hb⟩
  have hext : σ = viaEmbeddingHom (pairEmb h8) (flipB b) := by
    refine Equiv.ext fun x => ?_
    by_cases hx : (x : ℕ) < 8
    · rw [← pairEmb_unpair (h8 := h8) hx, viaEmbeddingHom_apply_image, ← hb,
        pairEmb_rho8]
    · rw [apply_of_mem_Y8 hσ (by omega), viaEmbeddingHom_apply_of_notMem]
      rw [mem_range_pairEmb]
      exact hx
  rw [← sign_flipB, ← sign_viaEmbeddingHom (pairEmb h8), ← hext]
  exact hσ.1

theorem lift_mem_Y8 {c : Fin 4 → Bool} (hc : evenB c = true) :
    viaEmbeddingHom (pairEmb h8) (flipB c) ∈ Y8 h8 := by
  refine ⟨by rw [sign_viaEmbeddingHom, sign_flipB]; exact hc, fun x => ?_⟩
  by_cases hx : (x : ℕ) < 8
  · rw [← pairEmb_unpair (h8 := h8) hx, viaEmbeddingHom_apply_image, pi0_pairEmb]
    rcases unpair x with ⟨k, d⟩
    rw [flipB_apply]
    by_cases hk : c k
    · right
      simp [hk, zPair_apply]
    · left
      simp [hk]
  · left
    exact viaEmbeddingHom_apply_of_notMem _ _ (by rw [mem_range_pairEmb]; exact hx)

theorem rho8_lift {c : Fin 4 → Bool} (hc : evenB c = true) :
    rho8 ⟨_, Y8_le_centralizer (lift_mem_Y8 (h8 := h8) hc)⟩ = flipB c := by
  refine Equiv.ext fun kc => ?_
  rw [rho8_apply]
  exact (congrArg unpair (viaEmbeddingHom_apply_image _ _ _)).trans (unpair_pairEmb _)

end Lift

section Y8Facts

variable {N : ℕ} {h8 : 2 * 4 ≤ N}

theorem flipB_injective {c c' : Fin 4 → Bool} (h : flipB c = flipB c') : c = c' := by
  rw [← cz_one, ← cz_one, cz_eq_cz_iff] at h
  exact h.2

theorem conj_mem_Y8 {β σ : Perm (Fin N)} (hβ : β * pi0 h8 = pi0 h8 * β) (hσ : σ ∈ Y8 h8) :
    β * σ * β⁻¹ ∈ Y8 h8 := by
  refine ⟨by rw [Perm.sign_mul, Perm.sign_mul, sign_inv, hσ.1, mul_one, Int.units_mul_self],
    fun x => ?_⟩
  have hβ' : β (pi0 h8 (β⁻¹ x)) = pi0 h8 x := by
    rw [← Perm.mul_apply, hβ, Perm.mul_apply, perm_apply_inv]
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases hσ.2 (β⁻¹ x) with h | h
  · left
    rw [h, perm_apply_inv]
  · right
    rw [h, hβ']

theorem diagHom_conj_flipB (τ : Perm (Fin 4)) (c : Fin 4 → Bool) :
    diagHom τ * flipB c * (diagHom τ)⁻¹ = flipB (fun k => c (τ⁻¹ k)) := by
  rw [← map_inv]
  refine Equiv.ext fun kd => ?_
  rcases kd with ⟨k, d⟩
  rw [Perm.mul_apply, Perm.mul_apply, diagHom_apply, flipB_apply, diagHom_apply, flipB_apply,
    perm_apply_inv]

theorem exists_perm_comp : ∀ c c' : Fin 4 → Bool, evenB c = true → evenB c' = true →
    c ≠ (fun _ => false) → c ≠ (fun _ => true) → c' ≠ (fun _ => false) →
    c' ≠ (fun _ => true) → ∃ τ : Perm (Fin 4), ∀ k, c k = c' (τ k) := by
  decide

theorem eq_lift_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) {c : Fin 4 → Bool}
    (hc : evenB c = true) (h : rho8 ⟨σ, Y8_le_centralizer hσ⟩ = flipB c) :
    σ = viaEmbeddingHom (pairEmb h8) (flipB c) :=
  eq_of_rho8_eq hσ (lift_mem_Y8 hc) (by rw [h, rho8_lift hc])

theorem flipB_ne_one_of_ne {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) {c : Fin 4 → Bool}
    (hc : evenB c = true) (h : rho8 ⟨σ, Y8_le_centralizer hσ⟩ = flipB c) (h1 : σ ≠ 1) :
    c ≠ (fun _ => false) := by
  rintro rfl
  apply h1
  rw [eq_lift_of_mem_Y8 hσ hc h, ← cz_one, ← one_eq_cz, map_one]

theorem flipB_ne_zPair_of_ne {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) {c : Fin 4 → Bool}
    (hc : evenB c = true) (h : rho8 ⟨σ, Y8_le_centralizer hσ⟩ = flipB c) (h2 : σ ≠ pi0 h8) :
    c ≠ (fun _ => true) := by
  rintro rfl
  apply h2
  rw [eq_lift_of_mem_Y8 hσ hc h, ← cz_one, ← zPair_eq_cz]
  rfl

theorem exists_conj_eq_of_mem_Y8 {σ σ' : Perm (Fin N)} (hσ : σ ∈ Y8 h8) (hσ' : σ' ∈ Y8 h8)
    (h1 : σ ≠ 1) (h2 : σ ≠ pi0 h8) (h1' : σ' ≠ 1) (h2' : σ' ≠ pi0 h8) :
    ∃ β : Perm (Fin N), sign β = 1 ∧ β * pi0 h8 = pi0 h8 * β ∧ β * σ * β⁻¹ = σ' := by
  obtain ⟨c, hc, hrc⟩ := exists_rho8_of_mem_Y8 hσ
  obtain ⟨c', hc', hrc'⟩ := exists_rho8_of_mem_Y8 hσ'
  obtain ⟨τ, hτ⟩ := exists_perm_comp c c' hc hc' (flipB_ne_one_of_ne hσ hc hrc h1)
    (flipB_ne_zPair_of_ne hσ hc hrc h2) (flipB_ne_one_of_ne hσ' hc' hrc' h1')
    (flipB_ne_zPair_of_ne hσ' hc' hrc' h2')
  refine ⟨viaEmbeddingHom (pairEmb h8) (diagHom τ), by rw [sign_viaEmbeddingHom, sign_diagHom],
    by rw [pi0, ← map_mul, ← map_mul, diagHom_mul_zPair], ?_⟩
  rw [eq_lift_of_mem_Y8 hσ hc hrc, eq_lift_of_mem_Y8 hσ' hc' hrc', ← map_inv, ← map_mul,
    ← map_mul, diagHom_conj_flipB]
  congr 2
  funext k
  rw [hτ, perm_apply_inv]

theorem card_evenB : Fintype.card {c : Fin 4 → Bool // evenB c = true} = 8 := by
  decide

@[expose] noncomputable def Y8Equiv : ↥(Y8 h8) ≃ {c : Fin 4 → Bool // evenB c = true} where
  toFun y := ⟨Classical.choose (exists_rho8_of_mem_Y8 y.2),
    (Classical.choose_spec (exists_rho8_of_mem_Y8 y.2)).1⟩
  invFun c := ⟨_, lift_mem_Y8 c.2⟩
  left_inv y := Subtype.ext (eq_lift_of_mem_Y8 y.2
    (Classical.choose_spec (exists_rho8_of_mem_Y8 y.2)).1
    (Classical.choose_spec (exists_rho8_of_mem_Y8 y.2)).2).symm
  right_inv c := by
    apply Subtype.ext
    have h := (Classical.choose_spec (exists_rho8_of_mem_Y8 (lift_mem_Y8 (h8 := h8) c.2))).2
    exact (flipB_injective ((rho8_lift c.2).symm.trans h)).symm

theorem card_Y8 : Nat.card (Y8 h8) = 8 := by
  rw [Nat.card_congr Y8Equiv, Nat.card_eq_fintype_card, card_evenB]

@[expose] def V8 (h8 : 2 * 4 ≤ N) : Subgroup (Perm (Fin N)) :=
  Y8 h8 ⊓ MulAction.stabilizer (Perm (Fin N)) (pairEmb h8 (3, 0))

theorem mem_V8_iff {σ : Perm (Fin N)} :
    σ ∈ V8 h8 ↔ σ ∈ Y8 h8 ∧ σ (pairEmb h8 (3, 0)) = pairEmb h8 (3, 0) := by
  rw [V8, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem pi0_notMem_V8 : pi0 h8 ∉ V8 h8 := by
  intro h'
  have h := (mem_V8_iff.mp h').2
  rw [pi0_pairEmb] at h
  exact zPair_ne _ ((pairEmb h8).injective h)

theorem card_evenB_three :
    Fintype.card {c : Fin 4 → Bool // evenB c = true ∧ c 3 = false} = 4 := by
  decide

theorem mem_V8_iff_lift {c : Fin 4 → Bool} (hc : evenB c = true) :
    viaEmbeddingHom (pairEmb h8) (flipB c) ∈ V8 h8 ↔ c 3 = false := by
  rw [mem_V8_iff]
  refine ⟨fun h => ?_, fun h => ⟨lift_mem_Y8 hc, ?_⟩⟩
  · have h' := h.2
    rw [viaEmbeddingHom_apply_image, flipB_apply] at h'
    have h'' := congrArg Prod.snd ((pairEmb h8).injective h')
    by_contra hc3
    rw [Bool.not_eq_false] at hc3
    simp [hc3] at h''
  · rw [viaEmbeddingHom_apply_image, flipB_apply, h]
    rfl

@[expose] noncomputable def V8Equiv :
    ↥(V8 h8) ≃ {c : Fin 4 → Bool // evenB c = true ∧ c 3 = false} where
  toFun y := ⟨Classical.choose (exists_rho8_of_mem_Y8 (mem_V8_iff.mp y.2).1),
    (Classical.choose_spec (exists_rho8_of_mem_Y8 (mem_V8_iff.mp y.2).1)).1, by
      have h := (Classical.choose_spec (exists_rho8_of_mem_Y8 (mem_V8_iff.mp y.2).1))
      have hy := eq_lift_of_mem_Y8 (mem_V8_iff.mp y.2).1 h.1 h.2
      have hmem := y.2
      rw [hy] at hmem
      exact (mem_V8_iff_lift h.1).mp hmem⟩
  invFun c := ⟨_, (mem_V8_iff_lift c.2.1).mpr c.2.2⟩
  left_inv y := Subtype.ext (eq_lift_of_mem_Y8 (mem_V8_iff.mp y.2).1
    (Classical.choose_spec (exists_rho8_of_mem_Y8 (mem_V8_iff.mp y.2).1)).1
    (Classical.choose_spec (exists_rho8_of_mem_Y8 (mem_V8_iff.mp y.2).1)).2).symm
  right_inv c := by
    apply Subtype.ext
    have h := (Classical.choose_spec
      (exists_rho8_of_mem_Y8 (lift_mem_Y8 (h8 := h8) c.2.1))).2
    exact (flipB_injective ((rho8_lift c.2.1).symm.trans h)).symm

theorem card_V8 : Nat.card (V8 h8) = 4 := by
  rw [Nat.card_congr V8Equiv, Nat.card_eq_fintype_card, card_evenB_three]

end Y8Facts

section Structure

variable {N : ℕ} {h8 : 2 * 4 ≤ N}

theorem rho8_mul' {σ τ : Perm (Fin N)} (hσ : σ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (hτ : τ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (h : σ * τ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    rho8 ⟨σ * τ, h⟩ = rho8 ⟨σ, hσ⟩ * rho8 ⟨τ, hτ⟩ := by
  rw [← map_mul]
  rfl

theorem rho8_pow' {σ : Perm (Fin N)} (hσ : σ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (m : ℕ) (h : σ ^ m ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    rho8 ⟨σ ^ m, h⟩ = rho8 ⟨σ, hσ⟩ ^ m := by
  rw [← map_pow]
  rfl

theorem rho8_one' (h : (1 : Perm (Fin N)) ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    rho8 ⟨1, h⟩ = 1 :=
  map_one _

theorem blk_mul' {σ τ : Perm (Fin N)} (hσ : σ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (hτ : τ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (h : σ * τ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    blk ⟨σ * τ, h⟩ = blk ⟨σ, hσ⟩ * blk ⟨τ, hτ⟩ :=
  blk_mul ⟨σ, hσ⟩ ⟨τ, hτ⟩

theorem blk_pow' {σ : Perm (Fin N)} (hσ : σ ∈ centralizer ({pi0 h8} : Set (Perm (Fin N))))
    (m : ℕ) (h : σ ^ m ∈ centralizer ({pi0 h8} : Set (Perm (Fin N)))) :
    blk ⟨σ ^ m, h⟩ = blk ⟨σ, hσ⟩ ^ m := by
  rw [← blk_pow]
  rfl

theorem blk_eq_one_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) :
    blk ⟨σ, Y8_le_centralizer hσ⟩ = 1 := by
  obtain ⟨c, -, hc⟩ := exists_rho8_of_mem_Y8 hσ
  exact blk_eq (b := c) (by rw [hc, cz_one])

theorem exists_pow_involution {P : Subgroup (Perm (Fin N))} (hP2 : IsPGroup 2 P)
    {t : Perm (Fin N)} (ht : t ∈ P) (h1 : t ≠ 1) : ∃ m : ℕ, t ^ m * t ^ m = 1 ∧ t ^ m ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨t, ht⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact h1 hk
  refine ⟨2 ^ (k - 1), ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0),
      ← hk, pow_orderOf_eq_one]
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

structure OmegaHyp (h8 : 2 * 4 ≤ N) (P : Subgroup (Perm (Fin N))) : Prop where
  two : IsPGroup 2 P
  le_centralizer : P ≤ centralizer ({pi0 h8} : Set (Perm (Fin N)))
  Y8_le : Y8 h8 ≤ P
  omega : ∀ σ ∈ P, σ * σ = 1 ∨ σ * σ = pi0 h8 → σ ∈ Y8 h8

namespace OmegaHyp

variable {P : Subgroup (Perm (Fin N))} (hP : OmegaHyp h8 P)
include hP

theorem mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ P) (hb : blk ⟨σ, hP.le_centralizer hσ⟩ = 1) :
    σ ∈ Y8 h8 := by
  obtain ⟨b, hrb⟩ := exists_rho8_eq ⟨σ, hP.le_centralizer hσ⟩
  rw [hb, cz_one] at hrb
  have hσσ := mul_mem hσ hσ
  have hsq : rho8 ⟨σ * σ, hP.le_centralizer hσσ⟩ = 1 := by
    rw [rho8_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ), hrb, ← cz_one, cz_sq,
      one_eq_cz, cz_eq_cz_iff]
    exact ⟨one_mul 1, funext fun k => by simp⟩
  by_cases h1 : σ * σ = 1
  · exact hP.omega σ hσ (Or.inl h1)
  · obtain ⟨m, hm2, hm1⟩ := exists_pow_involution hP.two hσσ h1
    have htP : (σ * σ) ^ m ∈ P := pow_mem hσσ m
    have htY := hP.omega _ htP (Or.inl hm2)
    refine absurd (eq_of_rho8_eq htY (one_mem _) ?_) hm1
    rw [rho8_pow' (hP.le_centralizer hσσ), hsq, one_pow, rho8_one']

theorem false_of_fixed {σ : Perm (Fin N)} (hσ : σ ∈ P)
    (h2 : blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1)
    (h1 : blk ⟨σ, hP.le_centralizer hσ⟩ ≠ 1)
    (hfix : ∃ i, blk ⟨σ, hP.le_centralizer hσ⟩ i = i) : False := by
  set τ := blk ⟨σ, hP.le_centralizer hσ⟩ with hτ
  obtain ⟨b, hrb⟩ := exists_rho8_eq ⟨σ, hP.le_centralizer hσ⟩
  obtain ⟨c, hc, hsq⟩ := exists_flipB_sq_of_fixed b h2 h1 hfix
  have hyY := lift_mem_Y8 (h8 := h8) hc
  have htP : σ * viaEmbeddingHom (pairEmb h8) (flipB c) ∈ P := mul_mem hσ (hP.Y8_le hyY)
  set t := σ * viaEmbeddingHom (pairEmb h8) (flipB c) with ht
  have hrt : rho8 ⟨t, hP.le_centralizer htP⟩ = cz τ b * flipB c := by
    rw [rho8_mul' (hP.le_centralizer hσ) (Y8_le_centralizer hyY), hrb, rho8_lift hc]
  have httP := mul_mem htP htP
  have hrtt : rho8 ⟨t * t, hP.le_centralizer httP⟩ = 1 := by
    rw [rho8_mul' (hP.le_centralizer htP) (hP.le_centralizer htP), hrt, hsq]
  have hbtt : blk ⟨t * t, hP.le_centralizer httP⟩ = 1 :=
    blk_eq (b := fun _ => false) (by rw [hrtt, one_eq_cz])
  have httY := hP.mem_Y8 httP hbtt
  have htt1 : t * t = 1 := eq_of_rho8_eq httY (one_mem _) (by rw [hrtt, rho8_one'])
  have htY := hP.omega t htP (Or.inl htt1)
  have hb1 := blk_eq_one_of_mem_Y8 htY
  have hbτ : blk ⟨t, Y8_le_centralizer htY⟩ = τ :=
    blk_eq (b := fun k => xor (c k) (b k)) (by rw [hrt, cz_mul_flipB])
  exact h1 (hbτ.symm.trans hb1)

theorem evenB_eq_false {σ : Perm (Fin N)} (hσ : σ ∈ P)
    (h2 : blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1)
    (hfpf : ∀ i, blk ⟨σ, hP.le_centralizer hσ⟩ i ≠ i) {b : Fin 4 → Bool}
    (hb : rho8 ⟨σ, hP.le_centralizer hσ⟩ = cz (blk ⟨σ, hP.le_centralizer hσ⟩) b) :
    evenB b = false := by
  set τ := blk ⟨σ, hP.le_centralizer hσ⟩ with hτ
  by_contra hev
  rw [Bool.not_eq_false] at hev
  have hσσ := mul_mem hσ hσ
  have hrσσ : rho8 ⟨σ * σ, hP.le_centralizer hσσ⟩ = cz τ b * cz τ b := by
    rw [rho8_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ), hb]
  have hbσσ : blk ⟨σ * σ, hP.le_centralizer hσσ⟩ = 1 := by
    rw [blk_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ), ← hτ, h2]
  have hσσY := hP.mem_Y8 hσσ hbσσ
  have hmem : σ * σ = 1 ∨ σ * σ = pi0 h8 := by
    rcases cz_sq_mem_of_even h2 hfpf hev with h | h
    · exact Or.inl (eq_of_rho8_eq hσσY (one_mem _) (by rw [hrσσ, h, rho8_one']))
    · exact Or.inr (eq_of_rho8_eq hσσY pi0_mem_Y8 (by rw [hrσσ, h, ← rho8_pi0]))
  have hσY := hP.omega σ hσ hmem
  have hb1 := blk_eq_one_of_mem_Y8 hσY
  have hτ1 : τ ≠ 1 := fun h => hfpf 0 (by rw [h]; rfl)
  exact hτ1 hb1

theorem sign_rho8 {σ : Perm (Fin N)} (hσ : σ ∈ P)
    (h2 : blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1)
    (hfpf : ∀ i, blk ⟨σ, hP.le_centralizer hσ⟩ i ≠ i) :
    sign (rho8 ⟨σ, hP.le_centralizer hσ⟩) = -1 := by
  obtain ⟨b, hb⟩ := exists_rho8_eq ⟨σ, hP.le_centralizer hσ⟩
  have h := hP.evenB_eq_false hσ h2 hfpf hb
  rw [hb, sign_cz]
  rcases Int.units_eq_one_or (sign (flipB b)) with h' | h'
  · rw [sign_flipB, h] at h'
    exact absurd h' (by decide)
  · exact h'

theorem blk_mul_self {σ : Perm (Fin N)} (hσ : σ ∈ P) :
    blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1 := by
  set τ := blk ⟨σ, hP.le_centralizer hσ⟩ with hτ
  by_contra hne
  obtain ⟨j, hj⟩ := hP.two ⟨σ, hσ⟩
  have hσj : σ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hτj : τ ^ 2 ^ j = 1 := by
    rw [hτ, ← blk_pow' (hP.le_centralizer hσ) _ (by rw [hσj]; exact one_mem _)]
    simp only [hσj]
    exact blk_one
  have hτ4 : τ ^ 4 = 1 := by
    rcases pow_four_or_pow_three τ with h | h
    · exact h
    · have hg := pow_gcd_eq_one.mpr ⟨h, hτj⟩
      have : Nat.gcd 3 (2 ^ j) = 1 :=
        Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
      rw [this, pow_one] at hg
      rw [hg, one_pow]
  obtain ⟨hττ2, hττf⟩ := fpf_sq_of_pow_four τ hτ4 hne
  have hσσ := mul_mem hσ hσ
  have hbσσ : blk ⟨σ * σ, hP.le_centralizer hσσ⟩ = τ * τ :=
    blk_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ) _
  have h := hP.sign_rho8 hσσ (by rw [hbσσ]; exact hττ2) (by rw [hbσσ]; exact hττf)
  rw [rho8_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ), Perm.sign_mul,
    Int.units_mul_self] at h
  exact absurd h (by decide)

theorem blk_cases {σ : Perm (Fin N)} (hσ : σ ∈ P) :
    σ ∈ Y8 h8 ∨ (blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1 ∧
      ∀ i, blk ⟨σ, hP.le_centralizer hσ⟩ i ≠ i) := by
  by_cases h1 : blk ⟨σ, hP.le_centralizer hσ⟩ = 1
  · exact Or.inl (hP.mem_Y8 hσ h1)
  · right
    refine ⟨hP.blk_mul_self hσ, fun i hi => ?_⟩
    exact hP.false_of_fixed hσ (hP.blk_mul_self hσ) h1 ⟨i, hi⟩

theorem blk_eq_blk {σ σ' : Perm (Fin N)} (hσ : σ ∈ P) (hσ' : σ' ∈ P)
    (h2 : blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ, hP.le_centralizer hσ⟩ = 1)
    (hfpf : ∀ i, blk ⟨σ, hP.le_centralizer hσ⟩ i ≠ i)
    (h2' : blk ⟨σ', hP.le_centralizer hσ'⟩ * blk ⟨σ', hP.le_centralizer hσ'⟩ = 1)
    (hfpf' : ∀ i, blk ⟨σ', hP.le_centralizer hσ'⟩ i ≠ i) :
    blk ⟨σ, hP.le_centralizer hσ⟩ = blk ⟨σ', hP.le_centralizer hσ'⟩ := by
  by_contra hne
  obtain ⟨h2'', hfpf''⟩ := fpf_mul_fpf _ _ h2 hfpf h2' hfpf' hne
  have hσσ' := mul_mem hσ hσ'
  have hb : blk ⟨σ * σ', hP.le_centralizer hσσ'⟩ =
      blk ⟨σ, hP.le_centralizer hσ⟩ * blk ⟨σ', hP.le_centralizer hσ'⟩ :=
    blk_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ') _
  have h := hP.sign_rho8 hσσ' (by rw [hb]; exact h2'') (by rw [hb]; exact hfpf'')
  rw [rho8_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ'), Perm.sign_mul,
    hP.sign_rho8 hσ h2 hfpf, hP.sign_rho8 hσ' h2' hfpf'] at h
  exact absurd h (by decide)

theorem mul_mem_Y8 {σ σ' : Perm (Fin N)} (hσ : σ ∈ P) (hσ' : σ' ∈ P) (hσY : σ ∉ Y8 h8)
    (hσ'Y : σ' ∉ Y8 h8) : σ * σ' ∈ Y8 h8 := by
  rcases hP.blk_cases hσ with hY | ⟨h2, hfpf⟩
  · exact absurd hY hσY
  rcases hP.blk_cases hσ' with hY' | ⟨h2', hfpf'⟩
  · exact absurd hY' hσ'Y
  have heq := hP.blk_eq_blk hσ hσ' h2 hfpf h2' hfpf'
  refine hP.mem_Y8 (mul_mem hσ hσ') ?_
  rw [blk_mul' (hP.le_centralizer hσ) (hP.le_centralizer hσ'), ← heq, h2]

end OmegaHyp

end Structure

end CFSG.ComponentClassification.RankTwoAlt
