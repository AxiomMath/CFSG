module

public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped MatrixGroups Matrix

theorem exists_cube_root_of_even {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : Even n)
    (hF : Fintype.card F = 2 ^ n) : ∃ ω : Fˣ, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
    have := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp hn)
    simpa using this
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨ω, fun h => by rw [h, orderOf_one] at hω; omega, hω ▸ pow_orderOf_eq_one ω⟩

theorem evenExclusion
    {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n)
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L E : Subgroup (MulAut V)) (hirr : X1.IsIrrOn L) (hperf : Group.IsPerfect ↥L)
    (hc : Subgroup.center ↥L = ⊥)
    (hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE1 : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) (hEq : IsQuadratic E) :
    Nat.card E * Nat.card (fixV E) < Nat.card V := by
  classical
  by_contra hnot
  push Not at hnot
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hc, Subgroup.card_bot]; exact odd_one
  obtain ⟨F, iF, iFin, φ, hFcard, hcov⟩ :=
    exists_cover_of_model hperf hodd (by omega : 1 ≤ n) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  have hntV : Nontrivial V := hirr.1
  have hntW : Nontrivial W := by
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have hker := B42SL3.repOf_ker θ hcov
  have hirrρ := B42SL3.repOf_irreducible θ hirr.2 hcov.surjective
  have hEel' : CFSG.IsElementaryAbelian 2 ↥(E.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ E).1 hEel
  have hE1' : E.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective E (binPsi θ).injective]
    exact hE1
  have hoff : Nat.card W ≤ Nat.card ↥(E.map (binPsi θ).toMonoidHom) *
      Nat.card {u : W // ∀ a ∈ E.map (binPsi θ).toMonoidHom, a u = u} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective,
      ← natCard_eq θ]
    exact hnot
  obtain ⟨ψ, hψ, E', hE'⟩ := B42SL3.natural_of_offender (B42SL3.repOf θ φ) hker
    (E.map (binPsi θ).toMonoidHom)
    (B42SL3.intertwines_map θ hcov.surjective hEN) hn2 hF hirrρ hE1'
    (B42SL3.quad_map θ hEq) hoff
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root_of_even hn hF
  let s : SL(3, F) := ⟨Matrix.scalar (Fin 3) (ω : F), by
    have h3 : (ω : F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hω3]; exact Units.val_one
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simpa [Finset.prod_const] using h3⟩
  have hs : s ∈ scalars 3 F := ⟨ω, hω3, rfl⟩
  have hφs : φ s = 1 := by
    have : φ s ∈ (scalars 3 F).map φ := Subgroup.mem_map_of_mem φ hs
    rw [hcov.map_scalars, hc] at this
    exact Subgroup.mem_bot.1 this
  have hρs : ∀ u, B42SL3.repOf θ φ s u = u := by
    intro u
    rw [B42SL3.repOf_apply, hφs]
    simp
  have hψs : ψ s = 1 := by
    have hall : ∀ x : Fin 3 → F, ((ψ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
      intro x
      obtain ⟨u, rfl⟩ := E'.surjective x
      rw [← hE', hρs]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    have := congrFun (hall (Pi.single j 1)) i
    simp [Matrix.mulVec_single] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply]
  have hs1 : s = 1 := by
    have := hψ s
    rw [hψs, map_one] at this
    exact this.symm
  have hmat : ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    rw [hs1]; simp
  have hω : (ω : F) = 1 := by
    simpa [s] using hmat
  exact hω1 (Units.ext hω)

end CFSG.LocalAnalysis.RankThreeUC.S15
