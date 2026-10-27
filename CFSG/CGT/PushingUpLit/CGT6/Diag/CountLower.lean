module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

namespace Diag.Count

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open CFSG.SL2MinimalFaithful

section Card

theorem card_sup_mul_card_inf {G : Type*} [CommGroup G] (A B : Subgroup G) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.relIndex_sup_right A B
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3]
  ring

theorem exists_fixed_of_hom {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    [Nontrivial W] {Q : Type} [Group Q] (hQ : IsPGroup 2 Q) (ρ : Q →* MulAut W) :
    ∃ w : W, w ≠ 1 ∧ ∀ q : Q, ρ q w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction Q W := MulAction.compHom W ρ
  have hmod := hQ.card_modEq_card_fixedPoints W
  have hWp : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := W)).mp hWp
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card W = 1 := by simpa using hk
    have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial W)
    have h3 : 1 < Nat.card W := by simpa [Nat.card_eq_fintype_card] using h2
    omega
  have h2W : 2 ∣ Nat.card W := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hdvd : 2 ∣ Nat.card (MulAction.fixedPoints Q W) :=
    (Nat.ModEq.dvd_iff hmod (dvd_refl 2)).mp h2W
  let x0 : MulAction.fixedPoints Q W := ⟨1, fun q => by show ρ q 1 = 1; exact map_one _⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q W) := by
    have : Nonempty (MulAction.fixedPoints Q W) := ⟨x0⟩
    exact Nat.card_pos
  have hgt : 1 < Nat.card (MulAction.fixedPoints Q W) := by
    obtain ⟨m, hm⟩ := hdvd
    omega
  have : Nontrivial (MulAction.fixedPoints Q W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨x, hx⟩ := exists_ne x0
  refine ⟨x.1, fun h => hx (Subtype.ext h), fun q => ?_⟩
  exact x.2 q

end Card

section Sylow

variable {n : ℕ}

theorem slAct_mul (a b : Matrix.SpecialLinearGroup (Fin 2) (Fq n))
    (m : Multiplicative (Fin 2 → Fq n)) : slAct n (a * b) m = slAct n a (slAct n b m) := by
  simp only [slAct, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem slAct_one (m : Multiplicative (Fin 2 → Fq n)) : slAct n 1 m = m := by
  simp [slAct]

theorem slAct_mul_mul (s : Matrix.SpecialLinearGroup (Fin 2) (Fq n))
    (a b : Multiplicative (Fin 2 → Fq n)) : slAct n s (a * b) = slAct n s a * slAct n s b := by
  simp only [slAct, toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem slAct_inv (s : Matrix.SpecialLinearGroup (Fin 2) (Fq n))
    (a : Multiplicative (Fin 2 → Fq n)) : slAct n s a⁻¹ = (slAct n s a)⁻¹ := by
  simp only [slAct, toAdd_inv, Matrix.mulVec_neg, ofAdd_neg]

theorem sylow_comm (hn : 1 ≤ n) (S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Fq n)))
    (hS₀ : Nat.card ↥S₀ = 2 ^ n) :
    ∃ ε : Fq n → Multiplicative (Fin 2 → Fq n), Function.Injective ε ∧
      ∀ x, ∃ s ∈ S₀, ∃ m, slAct n s m * m⁻¹ = ε x := by
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hF (hS₀.trans hF.symm)
  refine ⟨fun x => slAct n g (Multiplicative.ofAdd ![x, 0]), ?_, fun x => ?_⟩
  · intro x y hxy
    have h1 : slAct n g⁻¹ (slAct n g (Multiplicative.ofAdd ![x, 0])) =
        slAct n g⁻¹ (slAct n g (Multiplicative.ofAdd ![y, 0])) := by
      simp only at hxy
      rw [hxy]
    rw [← slAct_mul, ← slAct_mul, inv_mul_cancel, slAct_one, slAct_one] at h1
    have h2 := congrArg (fun m => (Multiplicative.toAdd m) 0) h1
    simpa using h2
  · refine ⟨g * unipotent x * g⁻¹, hg x, slAct n g (Multiplicative.ofAdd ![0, 1]), ?_⟩
    have h1 : slAct n (g * unipotent x * g⁻¹) (slAct n g (Multiplicative.ofAdd ![0, 1])) =
        slAct n g (slAct n (unipotent x) (Multiplicative.ofAdd ![0, 1])) := by
      rw [slAct_mul, slAct_mul, ← slAct_mul g⁻¹ g, inv_mul_cancel, slAct_one]
    have h2 : slAct n (unipotent x) (Multiplicative.ofAdd ![0, 1]) =
        Multiplicative.ofAdd ![x, 1] := by
      simp only [slAct, toAdd_ofAdd, coe_unipotent]
      congr 1
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h1, h2, ← slAct_inv, ← slAct_mul_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp

end Sylow

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

theorem card_inf_ge {n : ℕ} (hn : 1 ≤ n) {K : Subgroup (MulAut V)}
    (θ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) {W U : Subgroup V}
    (hKW : ∀ x ∈ K, ∀ p ∈ W, x p ∈ W) (β : ↥W →* Multiplicative (Fin 2 → Fq n))
    (hβs : Function.Surjective β)
    (hβe : ∀ (x : ↥K) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ = slAct n (θ x) (β p))
    (S : Subgroup ↥K) (hS : Nat.card ↥S = 2 ^ n)
    (hcomm : ∀ u ∈ S, ∀ w ∈ W, (u : MulAut V) w * w⁻¹ ∈ U) :
    2 ^ n ≤ Nat.card ↥(W ⊓ U) := by
  have hcard : Nat.card ↥(S.map θ.toMonoidHom) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective θ.injective, hS]
  obtain ⟨ε, hεi, hε⟩ := sylow_comm hn _ hcard
  have key : ∀ x : Fq n, ∃ w : ↥W, β w = ε x ∧ (w : V) ∈ U := by
    intro x
    obtain ⟨s, hs, m, hm⟩ := hε x
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨w', rfl⟩ := hβs m
    have hp : (u : MulAut V) (w' : V) ∈ W := hKW _ u.2 _ w'.2
    refine ⟨⟨(u : MulAut V) (w' : V), hp⟩ * w'⁻¹, ?_, hcomm u hu w' w'.2⟩
    rw [map_mul, map_inv, hβe u w' hp, ← hm]
    rfl
  choose Φ hΦ using key
  let Ψ : Fq n → ↥(W ⊓ U) := fun x => ⟨(Φ x : V), (Φ x).2, (hΦ x).2⟩
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have h0 : ((Ψ x : ↥(W ⊓ U)) : V) = ((Ψ y : ↥(W ⊓ U)) : V) := congrArg Subtype.val hxy
    have h1 : Φ x = Φ y := Subtype.ext h0
    apply hεi
    rw [← (hΦ x).1, ← (hΦ y).1, h1]
  have h2 := Nat.card_le_card_of_injective Ψ hΨ
  rwa [GaloisField.card 2 n (by omega)] at h2

end Transfer

end Diag.Count

end CFSG.CGT.PushingUpLit.CGT6
