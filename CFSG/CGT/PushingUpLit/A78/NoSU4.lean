module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.CGT.PushingUpLit.A78

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.Open

theorem antidiag_four {F : Type} [Field F] : (antidiag 4 : Matrix (Fin 4) (Fin 4) F) =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, Fin.rev]

section Matrices

variable {F : Type} [Field F]

@[expose] def sieg (a b c d : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, a, b; 0, 1, c, d; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def lowJ : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; 1, 0, 0, 1]

theorem sieg_mul (a b c d a' b' c' d' : F) :
    sieg a b c d * sieg a' b' c' d' = sieg (a + a') (b + b') (c + c') (d + d') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sieg, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem sieg_zero : (sieg 0 0 0 0 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sieg]

variable [CharP F 2]

theorem sieg_mul_self (a b c d : F) : sieg a b c d * sieg a b c d = 1 := by
  rw [sieg_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, sieg_zero]

theorem lowJ_mul_self : (lowJ : Matrix (Fin 4) (Fin 4) F) * lowJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

theorem det_eq_one_of_mul_self {M : Matrix (Fin 4) (Fin 4) F} (h : M * M = 1) : M.det = 1 := by
  have h2 : M.det ^ 2 = 1 := by
    rw [sq, ← Matrix.det_mul, h, Matrix.det_one]
  have h3 : (M.det - 1) ^ 2 = 0 := by
    rw [sub_sq, h2]
    have : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (1 - M.det) * this
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  exact sub_eq_zero.mp this

@[expose] def siegGL (a b c d : F) : GL (Fin 4) F :=
  ⟨sieg a b c d, sieg a b c d, sieg_mul_self a b c d, sieg_mul_self a b c d⟩

@[expose] def lowGL : GL (Fin 4) F := ⟨lowJ, lowJ, lowJ_mul_self, lowJ_mul_self⟩

end Matrices

section Unitary

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem siegGL_mem_SU (hσ : ∀ x, σ (σ x) = x) {a b c : F} (hb : σ b = b) (hc : σ c = c) :
    siegGL a b c (σ a) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_eq_one_of_mul_self (sieg_mul_self _ _ _ _), ?_⟩
  change conjTr σ (sieg a b c (σ a)) * antidiag 4 * sieg a b c (σ a) = antidiag 4
  rw [antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, sieg, Matrix.mul_apply, Fin.sum_univ_four, hb, hc, hσ,
      CharTwo.add_self_eq_zero]

theorem lowGL_mem_SU : (lowGL : GL (Fin 4) F) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_eq_one_of_mul_self lowJ_mul_self, ?_⟩
  change conjTr σ lowJ * antidiag 4 * lowJ = antidiag 4
  rw [antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, lowJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

end Unitary

section Radical

variable {F : Type} [Field F] [Finite F] [CharP F 2] (f : ℕ)

abbrev SiegParam (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) : Type :=
  F × (fixedSubfield F 2 f).toAddSubgroup × (fixedSubfield F 2 f).toAddSubgroup

variable {f}

noncomputable def siegSU (hF : Nat.card F = (2 ^ f) ^ 2) (x : SiegParam F f) :
    ↥(SU (unitaryInvolution F 2 f) 4) :=
  ⟨siegGL x.1 (x.2.1 : F) (x.2.2 : F) (unitaryInvolution F 2 f x.1),
    siegGL_mem_SU (unitaryInvolution_involutive hF) (mem_fixedSubfield.mp x.2.1.2)
      (mem_fixedSubfield.mp x.2.2.2)⟩

theorem siegSU_add (hF : Nat.card F = (2 ^ f) ^ 2) (x y : SiegParam F f) :
    siegSU hF (x + y) = siegSU hF x * siegSU hF y := by
  apply Subtype.ext
  apply Units.ext
  change sieg _ _ _ _ = sieg _ _ _ _ * sieg _ _ _ _
  rw [sieg_mul]
  simp [map_add]

theorem siegSU_injective (hF : Nat.card F = (2 ^ f) ^ 2) : Function.Injective (siegSU hF) := by
  intro x y h
  have h1 := congrArg (fun g : ↥(SU (unitaryInvolution F 2 f) 4) =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  have e02 := congrFun (congrFun h1 0) 2
  have e03 := congrFun (congrFun h1 0) 3
  have e12 := congrFun (congrFun h1 1) 2
  simp only [siegSU, siegGL, sieg] at e02 e03 e12
  simp at e02 e03 e12
  exact Prod.ext e02 (Prod.ext e03 e12)

theorem eq_zero_of_central (hF : Nat.card F = (2 ^ f) ^ 2) {x : SiegParam F f}
    (hz : siegSU hF x ∈ Subgroup.center ↥(SU (unitaryInvolution F 2 f) 4)) : x = 0 := by
  have h := Subgroup.mem_center_iff.mp hz
    ⟨lowGL, lowGL_mem_SU⟩
  have h1 := congrArg (fun g : ↥(SU (unitaryInvolution F 2 f) 4) =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e11 := congrFun (congrFun h1 1) 1
  simp only [siegSU, siegGL, sieg, lowGL, lowJ] at e00 e01 e11
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e11
  exact Prod.ext e01.symm (Prod.ext e00 e11)

end Radical

section Assembly

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

noncomputable def siegHom (hF : Nat.card F = (2 ^ f) ^ 2) :
    Multiplicative (SiegParam F f) →* ↥(SU (unitaryInvolution F 2 f) 4) :=
  MonoidHom.mk' (fun x => siegSU hF (Multiplicative.toAdd x))
    (fun x y => siegSU_add hF (Multiplicative.toAdd x) (Multiplicative.toAdd y))

theorem siegHom_injective (hF : Nat.card F = (2 ^ f) ^ 2) : Function.Injective (siegHom hF) :=
  fun _ _ h => Multiplicative.toAdd.injective (siegSU_injective hF h)

theorem card_siegParam (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (Multiplicative (SiegParam F f)) = 2 ^ (4 * f) := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (SiegParam F f) ≃ SiegParam F f),
    Nat.card_prod, Nat.card_prod]
  have h1 : Nat.card (fixedSubfield F 2 f).toAddSubgroup = 2 ^ f := card_fixedSubfield hF
  rw [h1, hF, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem siegParam_add_self (p : SiegParam F f) : p + p = 0 :=
  Prod.ext (CharTwo.add_self_eq_zero _) (Prod.ext (Subtype.ext (CharTwo.add_self_eq_zero _))
    (Subtype.ext (CharTwo.add_self_eq_zero _)))

theorem su4_exists_elemAbelian_of_card (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ E : Subgroup ↥(SU (unitaryInvolution F 2 f) 4),
      IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (4 * f) ∧ E ⊓ Subgroup.center _ = ⊥ := by
  refine ⟨(siegHom hF).range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · rcases a with ⟨_, u, rfl⟩
    rcases b with ⟨_, v, rfl⟩
    apply Subtype.ext
    change siegHom hF u * siegHom hF v = siegHom hF v * siegHom hF u
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      simp [pow_two, siegParam_add_self]
    rw [this, map_one]
  · rw [← card_siegParam hF]
    exact (Nat.card_congr (MonoidHom.ofInjective (siegHom_injective hF)).toEquiv).symm
  · rw [eq_bot_iff]
    rintro z ⟨⟨u, rfl⟩, hz⟩
    have h0 := eq_zero_of_central hF hz
    have : u = 1 := Multiplicative.toAdd.injective h0
    rw [this, map_one]
    exact Subgroup.one_mem _

end Assembly

section Final

theorem su4_exists_elemAbelian {f : ℕ} (hf : 1 ≤ f) :
    ∃ E : Subgroup (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4),
      IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (4 * f) ∧ E ⊓ Subgroup.center _ = ⊥ :=
  su4_exists_elemAbelian_of_card (F := GaloisField 2 (2 * f)) (f := f)
    (by rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm])

theorem su4_exists_elemAbelian_image {G : Type*} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (Φ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * 2)) →* G)
    (hk : Φ.ker = Subgroup.center _) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (4 * f) := by
  obtain ⟨E, ⟨hcomm, hexp⟩, hcard, hcenter⟩ := su4_exists_elemAbelian hf
  have hinj : Function.Injective (Φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4)) ∈ Φ.ker := hx
    rw [hk] at hx1
    have : (x : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4)) ∈ E ⊓
        Subgroup.center _ := ⟨x.2, hx1⟩
    rw [hcenter] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hrange : (Φ.comp E.subtype).range = E.map Φ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨E.map Φ, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rcases a with ⟨_, u, hu, rfl⟩
    rcases b with ⟨_, v, hv, rfl⟩
    apply Subtype.ext
    change Φ u * Φ v = Φ v * Φ u
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩))
  · obtain ⟨u, hu, rfl⟩ := hx
    rw [← map_pow]
    exact (congrArg Φ (hexp u hu)).trans (map_one Φ)
  · rw [← hcard, ← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem su4_exists_big_abelian {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (Φ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * 2)) →* G)
    (_hs : Function.Surjective Φ) (hk : Φ.ker = Subgroup.center _) :
    ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, Commute x y) ∧ (∀ x ∈ E, x * x = 1) ∧
      2 ^ (3 * f) < Nat.card E := by
  obtain ⟨E, ⟨hcomm, hexp⟩, hcard⟩ := su4_exists_elemAbelian_image hf Φ hk
  refine ⟨E, fun x hx y hy => ?_, fun x hx => by simpa [pow_two] using hexp x hx, ?_⟩
  · exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  · rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end Final

end CFSG.CGT.PushingUpLit.A78
