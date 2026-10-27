module

public import CFSG.LieType.SeitzGeneration.ThreeIndep

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

section Block

variable {F : Type*} [Field F] {e r n : ℕ}

@[expose] noncomputable def blockMat (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    (Fin 3 → Matrix (Fin e) (Fin e) F) →* Matrix (Fin n) (Fin n) F where
  toFun X := reindex σ σ (fromBlocks (blockDiagonal X) 0 0 1)
  map_one' := by
    rw [blockDiagonal_one, fromBlocks_one, reindex_apply, submatrix_one_equiv]
  map_mul' X Y := by
    have hXY : blockDiagonal (X * Y) = blockDiagonal X * blockDiagonal Y := blockDiagonal_mul X Y
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv _ _ _ σ.symm,
      fromBlocks_multiply, hXY]
    simp

theorem blockMat_apply (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n)
    (X : Fin 3 → Matrix (Fin e) (Fin e) F) :
    blockMat σ X = reindex σ σ (fromBlocks (blockDiagonal X) 0 0 1) := rfl

theorem det_blockMat (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n)
    (X : Fin 3 → Matrix (Fin e) (Fin e) F) : (blockMat σ X).det = ∏ t, (X t).det := by
  rw [blockMat_apply, det_reindex_self, det_fromBlocks_zero₂₁, det_blockDiagonal, det_one,
    mul_one]

theorem blockMat_injective (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blockMat (F := F) σ) := by
  intro X Y h
  rw [blockMat_apply, blockMat_apply] at h
  have h1 := (reindex σ σ).injective h
  obtain ⟨h2, -⟩ := fromBlocks_inj.1 h1
  exact blockDiagonal_injective h2

@[expose] noncomputable def blockSL (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    (Fin 3 → SpecialLinearGroup (Fin e) F) →* SpecialLinearGroup (Fin n) F where
  toFun h := ⟨blockMat σ (fun t => (h t : Matrix (Fin e) (Fin e) F)), by
    rw [det_blockMat]
    simp⟩
  map_one' := by
    apply Subtype.ext
    change blockMat σ (fun t => (((1 : Fin 3 → SpecialLinearGroup (Fin e) F) t :
      SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) = 1
    have : (fun t => (((1 : Fin 3 → SpecialLinearGroup (Fin e) F) t :
        SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) = 1 := by
      funext t
      simp
    rw [this, map_one]
  map_mul' h k := by
    apply Subtype.ext
    change blockMat σ (fun t => (((h * k) t : SpecialLinearGroup (Fin e) F) :
      Matrix (Fin e) (Fin e) F)) = blockMat σ (fun t => (h t : Matrix (Fin e) (Fin e) F)) *
        blockMat σ (fun t => (k t : Matrix (Fin e) (Fin e) F))
    have : (fun t => (((h * k) t : SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) =
        (fun t => (h t : Matrix (Fin e) (Fin e) F)) *
          fun t => (k t : Matrix (Fin e) (Fin e) F) := by
      funext t
      simp
    rw [this, map_mul]

theorem blockSL_injective (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blockSL (F := F) σ) := by
  intro h k hhk
  have h1 := blockMat_injective σ (congrArg Subtype.val hhk)
  funext t
  exact Subtype.ext (congrFun h1 t)

end Block

section Order

variable {F : Type} [Field F] [Finite F]

theorem exists_sl_orderOf_eq {e : ℕ} (he : 1 ≤ e) {p : ℕ} (hp : p.Prime)
    (hpe : p ∣ Nat.card F ^ e - 1) (hp1 : ¬ p ∣ Nat.card F - 1) :
    ∃ g : SpecialLinearGroup (Fin e) F, orderOf g = p := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hGL : p ∣ Nat.card (GL (Fin e) F) := by
    rw [Matrix.card_GL_field]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨0, he⟩ : Fin e)))
    rw [← Nat.card_eq_fintype_card]
    simpa using hpe
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hGL
  have hdet : GeneralLinearGroup.det g = 1 := by
    have h1 : (GeneralLinearGroup.det g) ^ p = 1 := by
      rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
    have h2 : orderOf (GeneralLinearGroup.det g) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (GeneralLinearGroup.det g) ∣ Nat.card F - 1 := by
      have := orderOf_dvd_natCard (GeneralLinearGroup.det g)
      rwa [Nat.card_units] at this
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h3) hp1
  let g' : SpecialLinearGroup (Fin e) F := ⟨(g : Matrix (Fin e) (Fin e) F), by
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have htoGL : SpecialLinearGroup.toGL g' = g := Units.ext rfl
  refine ⟨g', ?_⟩
  have h1 := orderOf_injective SpecialLinearGroup.toGL toGL_injective' g'
  rw [htoGL, hg] at h1
  exact h1.symm

theorem hasThreeIndep_psl_blocks {e r n : ℕ} (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n)
    (he : 1 ≤ e) {p : ℕ} (hp : p.Prime) (hpe : p ∣ Nat.card F ^ e - 1)
    (hp1 : ¬ p ∣ Nat.card F - 1) :
    HasThreeIndep (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_sl_orderOf_eq he hp hpe hp1
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → SpecialLinearGroup (Fin n) F,
      x = fun t => blockSL σ (Pi.mulSingle t g) := ⟨_, rfl⟩
  have hxt : ∀ t, x t = blockSL σ (Pi.mulSingle t g) := fun t => by rw [hx]
  have hcomm : ∀ s t : Fin 3, Commute (x s) (x t) := fun s t => by
    rw [hxt, hxt]
    exact (Pi.mulSingle_apply_commute (fun _ : Fin 3 => g) s t).map (blockSL σ)
  have hpow : ∀ t, x t ^ p = 1 := fun t => by
    rw [hxt, ← map_pow, ← Pi.mulSingle_pow, hgp, Pi.mulSingle_one, map_one]
  have hprod : ∀ i j k : ℤ, x 0 ^ i * x 1 ^ j * x 2 ^ k =
      blockSL σ (Pi.mulSingle 0 (g ^ i) * Pi.mulSingle 1 (g ^ j) * Pi.mulSingle 2 (g ^ k)) := by
    intro i j k
    rw [hxt, hxt, hxt, map_mul, map_mul, ← map_zpow, ← map_zpow, ← map_zpow,
      ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow]
  refine HasThreeIndep.of_hom (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))
    (hcomm 0 1) (hcomm 0 2) (hcomm 1 2) (hpow 0) (hpow 1) (hpow 2) fun i j k h => ?_
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  set y := x 0 ^ i * x 1 ^ j * x 2 ^ k with hy
  have hyp : y ^ p = 1 := by
    have c1 : Commute (x 0 ^ i) (x 1 ^ j) := ((hcomm 0 1).zpow_left i).zpow_right j
    have c2 : Commute (x 0 ^ i * x 1 ^ j) (x 2 ^ k) :=
      (((hcomm 0 2).zpow_left i).zpow_right k).mul_left (((hcomm 1 2).zpow_left j).zpow_right k)
    have key : ∀ (t : Fin 3) (m : ℤ), (x t ^ m) ^ p = 1 := fun t m => by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hpow,
        _root_.one_zpow]
    rw [hy, c2.mul_pow, c1.mul_pow, key, key, key, one_mul, one_mul]
  have hn : 0 < n := Fin.pos (σ (Sum.inl (⟨0, by omega⟩, 0)))
  have hy1 : y = 1 := by
    obtain ⟨c, -, hcy⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
    have hcp : c ^ p = 1 := by
      have h1 : ((y ^ p : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
        rw [hyp]
        rfl
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hcy, ← map_pow] at h1
      have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
      rwa [scalar_apply, diagonal_apply_eq, one_apply_eq] at h2
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, zero_pow hp.ne_zero] at hcp
      exact zero_ne_one hcp
    have hcq : c ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one c hc0
    have hcop : Nat.Coprime p (Fintype.card F - 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hp1
    have hc1 : c = 1 := by
      have := pow_gcd_eq_one.2 ⟨hcp, hcq⟩
      rwa [hcop, pow_one] at this
    apply Subtype.ext
    rw [← hcy, hc1, map_one]
    rfl
  rw [hy, hprod] at hy1
  have h2 := blockSL_injective σ (hy1.trans (map_one _).symm)
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  have e2 := congrFun h2 2
  simp only [Pi.mul_apply, Pi.one_apply] at e0 e1 e2
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 2), mul_one, mul_one] at e0
  rw [Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 0), Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 2), one_mul, mul_one] at e1
  rw [Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), Pi.mulSingle_eq_same, one_mul,
    one_mul] at e2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hg]; exact orderOf_dvd_iff_zpow_eq_one.2 e0
  · rw [← hg]; exact orderOf_dvd_iff_zpow_eq_one.2 e1
  · rw [← hg]; exact orderOf_dvd_iff_zpow_eq_one.2 e2

end Order

end CFSG.LieType.SeitzGeneration
