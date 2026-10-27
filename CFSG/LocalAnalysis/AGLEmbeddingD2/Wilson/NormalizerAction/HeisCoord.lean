module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q]

theorem exists_coordEquiv (x y : Q) (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤)
    (hcomm : commutator Q ≤ Subgroup.center Q)
    (hcard : Nat.card (Q ⧸ Subgroup.center Q) = p ^ 2) (hexp : ∀ g : Q, g ^ p = 1) :
    ∃ e : Q ⧸ Subgroup.center Q ≃* Multiplicative (Fin 2 → ZMod p),
      e (QuotientGroup.mk x) = Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod p) ∧
      e (QuotientGroup.mk y) = Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod p) := by
  set B := Q ⧸ Subgroup.center Q with hB
  have : IsMulCommutative B := Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hcomm
  let _ : CommGroup B := { (inferInstance : Group B) with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  have hpB : ∀ b : B, b ^ p = 1 := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_pow, hexp, QuotientGroup.mk_one]
  have hz : ∀ a : B, ((zmultiplesHom (Additive B)) (Additive.ofMul a)) (p : ℤ) = 0 := by
    intro a
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hpB]; rfl
  let lift1 : B → (ZMod p →+ Additive B) := fun a =>
    ZMod.lift p ⟨zmultiplesHom (Additive B) (Additive.ofMul a), hz a⟩
  have lift1_one : ∀ a : B, lift1 a 1 = Additive.ofMul a := by
    intro a
    have := ZMod.lift_coe p ⟨zmultiplesHom (Additive B) (Additive.ofMul a), hz a⟩ 1
    simpa using this
  let F : (Fin 2 → ZMod p) →+ Additive B :=
    (lift1 (QuotientGroup.mk x)).comp (Pi.evalAddMonoidHom (fun _ : Fin 2 => ZMod p) 0) +
    (lift1 (QuotientGroup.mk y)).comp (Pi.evalAddMonoidHom (fun _ : Fin 2 => ZMod p) 1)
  let φ : Multiplicative (Fin 2 → ZMod p) →* B := AddMonoidHom.toMultiplicativeLeft F
  have hφ : ∀ v : Fin 2 → ZMod p, φ (Multiplicative.ofAdd v) =
      Additive.toMul (lift1 (QuotientGroup.mk x) (v 0) + lift1 (QuotientGroup.mk y) (v 1)) :=
    fun v => rfl
  have hφx : φ (Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod p)) = QuotientGroup.mk x := by
    rw [hφ]; simp [lift1_one]
  have hφy : φ (Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod p)) = QuotientGroup.mk y := by
    rw [hφ]; simp [lift1_one]
  have hsurj : Function.Surjective φ := by
    have hB : (⊤ : Subgroup B) = Subgroup.closure {(QuotientGroup.mk x : B), QuotientGroup.mk y} := by
      have h1 : (Subgroup.closure ({x, y} : Set Q)).map (QuotientGroup.mk' (Subgroup.center Q)) =
          Subgroup.closure ((QuotientGroup.mk' (Subgroup.center Q)) '' {x, y}) :=
        MonoidHom.map_closure _ _
      rw [hgen, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)] at h1
      rw [h1, Set.image_pair]; rfl
    rw [← MonoidHom.range_eq_top, eq_top_iff, hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hφx⟩
    · exact ⟨_, hφy⟩
  have hbij : Function.Bijective φ := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have hfin : Finite (Multiplicative (Fin 2 → ZMod p)) :=
      Finite.of_equiv (Fin 2 → ZMod p) (Multiplicative.ofAdd : (Fin 2 → ZMod p) ≃ _)
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod p) ≃ _),
      Nat.card_pi]
    simp [ZMod.card]
  refine ⟨(MulEquiv.ofBijective φ hbij).symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]; exact hφx.symm
  · rw [MulEquiv.symm_apply_eq]; exact hφy.symm

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
