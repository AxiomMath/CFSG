module

public import CFSG.LieType.SeitzGeneration.ThreeIndepBlock

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open

section Numerics

private theorem neg_pow_eq_one_iff_sub {R : Type*} [CommRing R] (x : R) (N : ℕ) :
    (-x) ^ N = 1 ↔ x ^ N - (-1) ^ N = 0 := by
  have hs : ((-1 : R) ^ N) * ((-1 : R) ^ N) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have h1 : (-x) ^ N = (-1) ^ N * x ^ N := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [h1, sub_eq_zero]
  constructor
  · intro h
    linear_combination ((-1 : R) ^ N) * h - (x ^ N) * hs
  · intro h
    rw [h]
    exact hs

private theorem neg_pow_eq_one_iff_dvd_sub (p N ℓ f : ℕ) [Fact p.Prime] :
    (-((ℓ : ZMod p) ^ f)) ^ N = 1 ↔ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ N - (-1) ^ N := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact neg_pow_eq_one_iff_sub _ N

end Numerics

section Order

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_orderOf_eq_prime_unitarySU {e p : ℕ} (hU : UnitaryFieldData ℓ f K) (he : 2 ≤ e)
    [Fact p.Prime] (hpe : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ e - (-1) ^ e) :
    ∃ g : unitarySU ℓ f K e, orderOf g = p := by
  have hfin := hU.finite
  have hsymm : (gramForm hU (1 : Matrix (Fin e) (Fin e) K)).IsSymm :=
    gramForm_isSymm hU (by simp [Matrix.map_one])
  have hsep : (gramForm hU (1 : Matrix (Fin e) (Fin e) K)).SeparatingLeft :=
    gramForm_separatingLeft hU (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order hU hsymm hsep
    (Module.finrank_fin_fun K) (by omega)).2.1
  have hcard : Nat.card (unitarySU ℓ f K e) =
      Nat.card (sesqSpecialUnitaryGroup (gramForm hU (1 : Matrix (Fin e) (Fin e) K))) := by
    rw [unitarySU_eq_gramSU hU, card_gramSU]
  have hdvd : p ∣ Nat.card (unitarySU ℓ f K e) := by
    rw [hcard]
    refine Int.natCast_dvd_natCast.1 ?_
    rw [hSU]
    exact (hpe.trans (Finset.dvd_prod_of_mem (fun i => (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i))
      (Finset.mem_Icc.2 ⟨he, le_rfl⟩))).mul_left _
  exact exists_prime_orderOf_dvd_card' p hdvd

end Order

section Block

variable {ℓ f e r n : ℕ} {K : Type} [Field K]

theorem blockMat_barTranspose_mul (hU : UnitaryFieldData ℓ f K)
    (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) (X : Fin 3 → Matrix (Fin e) (Fin e) K)
    (hX : ∀ t, ((X t).map hU.bar)ᵀ * X t = 1) :
    ((blockMat σ X).map hU.bar)ᵀ * blockMat σ X = 1 := by
  have h1 : ((blockMat σ X).map hU.bar)ᵀ = blockMat σ (fun t => ((X t).map hU.bar)ᵀ) := by
    rw [blockMat_apply, blockMat_apply, reindex_apply, reindex_apply]
    change ((fromBlocks (blockDiagonal X) 0 0 1).map hU.bar)ᵀ.submatrix σ.symm σ.symm = _
    congr 1
    rw [fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero _),
      blockDiagonal_transpose]
    simp
  rw [h1, ← map_mul]
  have h2 : (fun t => ((X t).map hU.bar)ᵀ) * X = 1 := by
    funext t
    exact hX t
  rw [h2, map_one]

@[expose] noncomputable def unitaryBlockGL (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    (Fin 3 → GL (Fin e) K) →* GL (Fin n) K :=
  (Units.map (blockMat (F := K) σ)).comp
    (MulEquiv.piUnits (M := fun _ : Fin 3 => Matrix (Fin e) (Fin e) K)).symm.toMonoidHom

theorem coe_unitaryBlockGL (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) (h : Fin 3 → GL (Fin e) K) :
    ((unitaryBlockGL σ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMat σ (fun t => (h t : Matrix (Fin e) (Fin e) K)) := rfl

theorem unitaryBlockGL_injective (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    Function.Injective (unitaryBlockGL (K := K) σ) := by
  intro h k hhk
  have h1 := blockMat_injective σ
    (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hhk)
  funext t
  exact Units.ext (congrFun h1 t)

theorem unitaryBlockGL_mem (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n)
    (h : Fin 3 → GL (Fin e) K) (hh : ∀ t, h t ∈ unitarySU ℓ f K e) :
    unitaryBlockGL σ h ∈ unitarySU ℓ f K n := by
  rw [mem_unitarySU_iff hU]
  have h' := fun t => (mem_unitarySU_iff hU).1 (hh t)
  refine ⟨?_, ?_⟩
  · rw [coe_unitaryBlockGL, det_blockMat]
    exact Finset.prod_eq_one fun t _ => (h' t).1
  · rw [coe_unitaryBlockGL]
    exact blockMat_barTranspose_mul hU σ _ fun t => (h' t).2

@[expose] noncomputable def blockUnitarySU (hU : UnitaryFieldData ℓ f K)
    (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) :
    (Fin 3 → unitarySU ℓ f K e) →* unitarySU ℓ f K n :=
  ((unitaryBlockGL σ).comp (MonoidHom.compLeft (unitarySU ℓ f K e).subtype (Fin 3))).codRestrict
    (unitarySU ℓ f K n) fun h => unitaryBlockGL_mem hU σ _ fun t => (h t).2

theorem blockUnitarySU_injective (hU : UnitaryFieldData ℓ f K)
    (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) : Function.Injective (blockUnitarySU hU σ) := by
  intro h k hhk
  have h1 := unitaryBlockGL_injective σ (congrArg Subtype.val hhk)
  funext t
  exact Subtype.ext (congrFun h1 t)

end Block

section Independence

theorem hasThreeIndep_of_blockHom {G H Q : Type*} [Group G] [Group H] [Group Q] {p : ℕ}
    (φ : (Fin 3 → G) →* H) (hφ : Function.Injective φ) (π : H →* Q) {g : G}
    (hg : orderOf g = p) (hker : ∀ y : H, π y = 1 → y ^ p = 1 → y = 1) :
    HasThreeIndep Q p := by
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → H, x = fun t => φ (Pi.mulSingle t g) := ⟨_, rfl⟩
  have hxt : ∀ t, x t = φ (Pi.mulSingle t g) := fun t => by rw [hx]
  have hcomm : ∀ s t : Fin 3, Commute (x s) (x t) := fun s t => by
    rw [hxt, hxt]
    exact (Pi.mulSingle_apply_commute (fun _ : Fin 3 => g) s t).map φ
  have hpow : ∀ t, x t ^ p = 1 := fun t => by
    rw [hxt, ← map_pow, ← Pi.mulSingle_pow, hgp, Pi.mulSingle_one, map_one]
  have hprod : ∀ i j k : ℤ, x 0 ^ i * x 1 ^ j * x 2 ^ k =
      φ (Pi.mulSingle 0 (g ^ i) * Pi.mulSingle 1 (g ^ j) * Pi.mulSingle 2 (g ^ k)) := by
    intro i j k
    rw [hxt, hxt, hxt, map_mul, map_mul, ← map_zpow, ← map_zpow, ← map_zpow,
      ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow]
  refine HasThreeIndep.of_hom π (hcomm 0 1) (hcomm 0 2) (hcomm 1 2) (hpow 0) (hpow 1) (hpow 2)
    fun i j k h => ?_
  set y := x 0 ^ i * x 1 ^ j * x 2 ^ k with hy
  have hyp : y ^ p = 1 := by
    have c1 : Commute (x 0 ^ i) (x 1 ^ j) := ((hcomm 0 1).zpow_left i).zpow_right j
    have c2 : Commute (x 0 ^ i * x 1 ^ j) (x 2 ^ k) :=
      (((hcomm 0 2).zpow_left i).zpow_right k).mul_left (((hcomm 1 2).zpow_left j).zpow_right k)
    have key : ∀ (t : Fin 3) (m : ℤ), (x t ^ m) ^ p = 1 := fun t m => by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hpow,
        _root_.one_zpow]
    rw [hy, c2.mul_pow, c1.mul_pow, key, key, key, one_mul, one_mul]
  have hy1 : y = 1 := hker y h hyp
  rw [hy, hprod] at hy1
  have h2 := hφ (hy1.trans (map_one _).symm)
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

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem eq_one_of_mem_scalars_of_pow_eq_one (hU : UnitaryFieldData ℓ f K) (hn : 1 ≤ n)
    (hp : p.Prime) (hp1 : ¬ p ∣ ℓ ^ f + 1) {y : unitarySU ℓ f K n}
    (hy : y ∈ (StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)) (hyp : y ^ p = 1) :
    y = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hy
  have hsc : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (ℓ ^ f) K := hc ▸ y.2
  have hc1 : c ^ (ℓ ^ f + 1) = 1 :=
    (((CFSG.LinearGroups.unitary_scalar_kernel hU.prime hU.card_eq_sq hn).2.1 c).1 hsc).2
  have hcp : c ^ p = 1 := by
    have h1 : (y : GL (Fin n) K) ^ p = 1 := by
      have := congrArg Subtype.val hyp
      simpa using this
    rw [← hc, ← map_pow] at h1
    have h2 := congrArg
      (fun g : GL (Fin n) K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_pow_eq_pow_val, Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hcop : Nat.Coprime p (ℓ ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hp1
  have hc1' : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hc1⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [← hc, hc1', map_one]
  rfl

end Independence

theorem hasThreeIndep_psu_blocks {ℓ f e r n p : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × Fin 3) ⊕ Fin r ≃ Fin n) (he : 1 ≤ e)
    (hp : p.Prime) (hpe : (-((ℓ : ZMod p) ^ f)) ^ e = 1) (hp1 : ¬ p ∣ ℓ ^ f + 1) :
    HasThreeIndep (StatedProj (StatedSU n (ℓ ^ f) K)) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpe' := (neg_pow_eq_one_iff_dvd_sub p e ℓ f).1 hpe
  have he2 : 2 ≤ e := by
    by_contra hlt
    obtain rfl : e = 1 := by omega
    apply hp1
    have h1 : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1 := by simpa using hpe'
    exact_mod_cast h1
  obtain ⟨g, hg⟩ := exists_orderOf_eq_prime_unitarySU hU he2 hpe'
  have hn : 1 ≤ n := Fin.pos (σ (Sum.inl (⟨0, by omega⟩, 0)))
  exact hasThreeIndep_of_blockHom (blockUnitarySU hU σ) (blockUnitarySU_injective hU σ)
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n))) hg
    fun y hy hyp =>
      eq_one_of_mem_scalars_of_pow_eq_one hU hn hp hp1 ((QuotientGroup.eq_one_iff _).1 hy) hyp

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
