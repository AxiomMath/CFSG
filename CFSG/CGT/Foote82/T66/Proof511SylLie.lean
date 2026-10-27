module

public import CFSG.Blueprint.Catalog
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ord
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Model

public section

namespace CFSG.CGT.Foote82.Proof511

namespace SylLie

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

private def sqOneP (v : Multiplicative V4) (r : R0) : Prop :=
  (⟨v, r⟩ * ⟨v, r⟩ : M128).left = 1 ∧ (⟨v, r⟩ * ⟨v, r⟩ : M128).right = 1

private instance (v : Multiplicative V4) (r : R0) : Decidable (sqOneP v r) := by
  unfold sqOneP; infer_instance

private theorem card_sqOneP : Nat.card {p : Multiplicative V4 × R0 // sqOneP p.1 p.2} = 36 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_sqOne_M128 : Nat.card {x : M128 // x ^ 2 = 1} = 36 := by
  rw [← card_sqOneP]
  exact Nat.card_congr (Equiv.subtypeEquiv SemidirectProduct.equivProd (fun x => by
    rw [pow_two, SemidirectProduct.ext_iff]; rfl))

theorem card_sqOne_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card {x : A // x ^ 2 = 1} = Nat.card {x : B // x ^ 2 = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show x ^ 2 = 1 ↔ e x ^ 2 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])

theorem card_sqOne_of_M128 {Y : Type*} [Group Y] [Finite Y] (S : Sylow 2 Y)
    (e : M128 ≃* ↥(S : Subgroup Y)) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← card_sqOne_congr (e.trans (S.equiv P)), card_sqOne_M128]

end SylLie

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81 CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5

theorem sqOne_card_PSU4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 = 3) (h : CFSG.Blueprint.LieModel Y .PSU 4 p f) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psu_unpack h
  haveI : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  haveI : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
  obtain ⟨Φ, hΦ⟩ := exists_M128_embedding_uni hF hp2 (by omega)
  have e' : Y ≃* PG (ModelData.uni hF) := e
  obtain ⟨S, ⟨eM⟩⟩ := exists_sylow_M128_of_embedding (e'.symm.toMonoidHom.comp Φ)
    (e'.symm.injective.comp hΦ) (v2_card_model_psu hp h8 h)
  exact SylLie.card_sqOne_of_M128 S eM P

end CFSG.CGT.Foote82.Proof511
