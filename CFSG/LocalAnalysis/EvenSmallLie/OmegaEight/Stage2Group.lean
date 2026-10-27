module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Fix
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix

variable {G : Type*} [Group G]

abbrev NW (W : Subgroup G) : Subgroup G := Subgroup.normalizer (W : Set G)

variable (W : Subgroup G) (φ : W ≃* Multiplicative (Fin 12 → ZMod 2))

@[expose] def conjW (g : NW W) : W →* W where
  toFun w := ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.1 g.2 w).1 w.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjW_apply (g : NW W) (w : W) : ((conjW W g w : W) : G) = g * w * g⁻¹ := rfl

@[expose] def matOfAdd (f : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2)) : Mat12 :=
  Matrix.of fun i j => f (Pi.single j 1) i

theorem matOfAdd_mulVec (f : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2)) (v : Fin 12 → ZMod 2) :
    matOfAdd f *ᵥ v = f v := by
  ext i
  have hv : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
  conv_rhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  simp only [mulVec, dotProduct, matOfAdd, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ c : ZMod 2, f (Pi.single j c) i = f (Pi.single j 1) i * c := by
    intro c
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · rw [Pi.single_zero, map_zero, mul_zero]
      rfl
    · rw [mul_one]
  rw [key (v j)]

theorem matOfAdd_apply (f : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2)) (i j : Fin 12) :
    matOfAdd f i j = f (Pi.single j 1) i := rfl

theorem matOfAdd_comp (f g : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2)) :
    matOfAdd (f.comp g) = matOfAdd f * matOfAdd g := by
  ext i j
  have h := congrFun (matOfAdd_mulVec f (g (Pi.single j 1))) i
  rw [matOfAdd_apply, AddMonoidHom.comp_apply, ← h, ← matOfAdd_mulVec g, mulVec_mulVec,
    mulVec_single_one]
  rfl

theorem matOfAdd_id : matOfAdd (AddMonoidHom.id _) = 1 := by
  ext i j
  rw [matOfAdd_apply, AddMonoidHom.id_apply, Matrix.one_apply, Pi.single_apply]

@[expose] def conjAdd (g : NW W) : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2) where
  toFun v := Multiplicative.toAdd (φ (conjW W g (φ.symm (Multiplicative.ofAdd v))))
  map_zero' := by simp only [ofAdd_zero, map_one, toAdd_one]
  map_add' a b := by simp only [ofAdd_add, map_mul, toAdd_mul]

theorem conjAdd_apply (g : NW W) (v : Fin 12 → ZMod 2) :
    conjAdd W φ g v = Multiplicative.toAdd (φ (conjW W g (φ.symm (Multiplicative.ofAdd v)))) :=
  rfl

theorem conjAdd_mul (g h : NW W) :
    conjAdd W φ (g * h) = (conjAdd W φ g).comp (conjAdd W φ h) := by
  refine AddMonoidHom.ext fun v => ?_
  simp only [conjAdd_apply, AddMonoidHom.comp_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  congr 2
  ext
  simp only [conjW_apply, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_assoc]

theorem conjAdd_one : conjAdd W φ 1 = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun v => ?_
  simp only [conjAdd_apply, AddMonoidHom.id_apply]
  have : conjW W 1 (φ.symm (Multiplicative.ofAdd v)) = φ.symm (Multiplicative.ofAdd v) := by
    ext
    simp [conjW_apply]
  rw [this, MulEquiv.apply_symm_apply, toAdd_ofAdd]

@[expose] def rhoMat (g : NW W) : Mat12 := matOfAdd (conjAdd W φ g)

theorem rhoMat_mul (g h : NW W) : rhoMat W φ (g * h) = rhoMat W φ g * rhoMat W φ h := by
  rw [rhoMat, conjAdd_mul, matOfAdd_comp]
  rfl

theorem rhoMat_one : rhoMat W φ 1 = 1 := by
  rw [rhoMat, conjAdd_one, matOfAdd_id]

@[expose] def rho : NW W →* GL12 where
  toFun g := ⟨rhoMat W φ g, rhoMat W φ g⁻¹, by rw [← rhoMat_mul, mul_inv_cancel, rhoMat_one],
    by rw [← rhoMat_mul, inv_mul_cancel, rhoMat_one]⟩
  map_one' := Units.ext (rhoMat_one W φ)
  map_mul' g h := Units.ext (rhoMat_mul W φ g h)

theorem rho_mulVec (g : NW W) (v : Fin 12 → ZMod 2) :
    (rho W φ g : Mat12) *ᵥ v = conjAdd W φ g v :=
  matOfAdd_mulVec _ _

@[expose] noncomputable def rhoG (g : G) : GL12 := by
  classical exact if h : g ∈ NW W then rho W φ ⟨g, h⟩ else 1

variable {W φ}

theorem rhoG_of_mem {g : G} (hg : g ∈ NW W) : rhoG W φ g = rho W φ ⟨g, hg⟩ := by
  simp [rhoG, hg]

theorem rhoG_mul {g h : G} (hg : g ∈ NW W) (hh : h ∈ NW W) :
    rhoG W φ (g * h) = rhoG W φ g * rhoG W φ h := by
  rw [rhoG_of_mem (mul_mem hg hh), rhoG_of_mem hg, rhoG_of_mem hh, ← map_mul]
  rfl

theorem rhoG_one : rhoG W φ 1 = 1 := by
  rw [rhoG_of_mem (one_mem _)]
  exact map_one _

theorem rhoG_inv {g : G} (hg : g ∈ NW W) : rhoG W φ g⁻¹ = (rhoG W φ g)⁻¹ := by
  rw [rhoG_of_mem (inv_mem hg), rhoG_of_mem hg, ← map_inv]
  rfl

theorem rhoG_pow {g : G} (hg : g ∈ NW W) (n : ℕ) : rhoG W φ (g ^ n) = rhoG W φ g ^ n := by
  rw [rhoG_of_mem (pow_mem hg n), rhoG_of_mem hg, ← map_pow]
  rfl

theorem rhoG_mulVec {g : G} (hg : g ∈ NW W) (w : W) :
    (rhoG W φ g : Mat12) *ᵥ Multiplicative.toAdd (φ w) =
      Multiplicative.toAdd (φ ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg w).1 w.2⟩) := by
  rw [rhoG_of_mem hg, rho_mulVec, conjAdd_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rfl

theorem W_le_NW : W ≤ NW W := Subgroup.le_normalizer

theorem W_comm (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) (a b : W) : a * b = b * a :=
  φ.injective (by rw [map_mul, map_mul, mul_comm])

theorem W_sq (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) (a : W) : a * a = 1 := by
  apply φ.injective
  rw [map_mul, map_one]
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  apply Multiplicative.toAdd.injective
  ext i
  exact h _

theorem W_mem_sq (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) {w : G} (hw : w ∈ W) :
    w * w = 1 := by
  have := W_sq φ ⟨w, hw⟩
  simpa using congrArg Subtype.val this

theorem eq_one_of_mulVec_eq (M : Mat12) (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at e
  rw [Matrix.one_apply]
  rw [show M i j = M.col j i from rfl, e, Pi.single_apply]

theorem rhoG_eq_one_iff {g : G} (hg : g ∈ NW W) :
    rhoG W φ g = 1 ↔ ∀ w ∈ W, g * w * g⁻¹ = w := by
  constructor
  · intro h w hw
    have e := rhoG_mulVec (φ := φ) hg ⟨w, hw⟩
    rw [h, Units.val_one, one_mulVec] at e
    have e' := φ.injective (Multiplicative.toAdd.injective e)
    exact (congrArg Subtype.val e').symm
  · intro h
    apply Units.ext
    apply eq_one_of_mulVec_eq
    intro v
    have hv := rhoG_mulVec (φ := φ) hg (φ.symm (Multiplicative.ofAdd v))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hv
    rw [hv]
    have e : (⟨g * ↑(φ.symm (Multiplicative.ofAdd v)) * g⁻¹,
        (Subgroup.mem_normalizer_iff.1 hg _).1 (φ.symm _).2⟩ : W) =
        φ.symm (Multiplicative.ofAdd v) := Subtype.ext (h _ (φ.symm _).2)
    rw [e, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem rhoG_W {w : G} (hw : w ∈ W) : rhoG W φ w = 1 := by
  rw [rhoG_eq_one_iff (W_le_NW hw)]
  intro w' hw'
  have := W_comm φ ⟨w, hw⟩ ⟨w', hw'⟩
  have e : w * w' = w' * w := congrArg Subtype.val this
  rw [e, mul_inv_cancel_right]

theorem mem_fixM_rhoG_iff {g : G} (hg : g ∈ NW W) (w : W) :
    Multiplicative.toAdd (φ w) ∈ fixM (rhoG W φ g : Mat12) ↔ g * w * g⁻¹ = w := by
  show (rhoG W φ g : Mat12) *ᵥ _ = _ ↔ _
  rw [rhoG_mulVec hg]
  constructor
  · intro e
    exact congrArg Subtype.val (φ.injective (Multiplicative.toAdd.injective e))
  · intro e
    congr 2
    exact Subtype.ext e

theorem card_fixM_rhoG {g : G} (hg : g ∈ NW W) :
    Nat.card (fixM (rhoG W φ g : Mat12)) = Nat.card {w : W // g * w * g⁻¹ = w} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨φ.symm (Multiplicative.ofAdd v.1), ?_⟩
      invFun := fun w => ⟨Multiplicative.toAdd (φ w.1), (mem_fixM_rhoG_iff hg w.1).2 w.2⟩
      left_inv := fun v => ?_
      right_inv := fun w => ?_ }
  · have := (mem_fixM_rhoG_iff (φ := φ) hg (φ.symm (Multiplicative.ofAdd v.1))).1
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
    exact this v.2
  · ext1
    simp
  · ext1
    simp

theorem card_fixM_le_of_conj {t : G}
    (hm2 : ∀ E : Subgroup G, E ≤ Subgroup.centralizer {t} → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 2 ^ 7)
    {u x : G} (hu : u = x * t * x⁻¹) (hun : u ∈ NW W) :
    Nat.card (fixM (rhoG W φ u : Mat12)) ≤ 2 ^ 7 := by
  rw [card_fixM_rhoG hun]
  set E : Subgroup G := ((W ⊓ Subgroup.centralizer {u}).map (MulAut.conj x⁻¹).toMonoidHom)
  have hE : E ≤ Subgroup.centralizer {t} := by
    rintro _ ⟨e, ⟨heW, heu⟩, rfl⟩
    have heu : e ∈ Subgroup.centralizer {u} := heu
    rw [Subgroup.mem_centralizer_singleton_iff] at heu ⊢
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    rw [hu] at heu
    calc x⁻¹ * e * x * t = x⁻¹ * (e * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * t * x⁻¹) * e) * x := by rw [heu]
      _ = t * (x⁻¹ * e * x) := by group
  have hsq : ∀ y ∈ E, y * y = 1 := by
    rintro _ ⟨e, ⟨heW, -⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    calc x⁻¹ * e * x * (x⁻¹ * e * x) = x⁻¹ * (e * e) * x := by group
      _ = 1 := by rw [W_mem_sq φ heW]; group
  have hcard : Nat.card E = Nat.card {w : W // u * w * u⁻¹ = w} := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    refine Nat.card_congr
      { toFun := fun e => ⟨⟨e.1, e.2.1⟩, ?_⟩
        invFun := fun w => ⟨w.1.1, w.1.2, ?_⟩
        left_inv := fun e => rfl
        right_inv := fun w => rfl }
    · have h2 : e.1 ∈ Subgroup.centralizer {u} := e.2.2
      rw [Subgroup.mem_centralizer_singleton_iff] at h2
      show u * e.1 * u⁻¹ = e.1
      rw [← h2, mul_inv_cancel_right]
    · show w.1.1 ∈ Subgroup.centralizer {u}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := w.2
      calc w.1.1 * u = u * w.1.1 * u⁻¹ * u := by rw [h2]
        _ = u * w.1.1 := by group
  rw [← hcard]
  exact hm2 E hE hsq

end CFSG.EvenSmallLie.OmegaEight.Stage2
