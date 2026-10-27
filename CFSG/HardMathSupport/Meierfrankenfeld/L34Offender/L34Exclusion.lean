module

public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3D
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Interfaces

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.L34Offender

open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped MatrixGroups Matrix

section Group

variable {K : Type} [Group K]

theorem card_eq_of_isLinThreeFour (h : IsLinThreeFour K) : Nat.card K = 20160 := by
  obtain ⟨e⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk

theorem isSimpleGroup_of_isLinThreeFour (h : IsLinThreeFour K) : IsSimpleGroup K := by
  obtain ⟨e⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have : IsSimpleGroup (projectiveSL 3 (GaloisField 2 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.isSimpleGroup_projectiveSL_four hk
  exact e.isSimpleGroup

theorem center_eq_bot_of_isLinThreeFour (h : IsLinThreeFour K) : Subgroup.center K = ⊥ := by
  have := isSimpleGroup_of_isLinThreeFour h
  have hfin : Finite K := by
    have : Nat.card K ≠ 0 := by rw [card_eq_of_isLinThreeFour h]; norm_num
    exact Nat.finite_of_card_ne_zero this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hb | ht
  · exact hb
  · exfalso
    let : CommGroup K := { ‹Group K› with
      mul_comm := fun a b => (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top a) b).symm }
    have hp := IsSimpleGroup.prime_card (α := K)
    rw [card_eq_of_isLinThreeFour h] at hp
    exact absurd hp (by norm_num)

theorem isPerfect_of_isLinThreeFour (h : IsLinThreeFour K) : Group.IsPerfect K := by
  have := isSimpleGroup_of_isLinThreeFour h
  have hc := center_eq_bot_of_isLinThreeFour h
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with hb | ht
  · exfalso
    have h1 : (⊤ : Subgroup K) ≤ Subgroup.center K :=
      (Subgroup.commutator_top_right_eq_bot_iff_le_center).1 hb
    rw [hc] at h1
    have : Nat.card K = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have ha := Subgroup.mem_bot.1 (h1 (Subgroup.mem_top a))
      have hb' := Subgroup.mem_bot.1 (h1 (Subgroup.mem_top b))
      rw [ha, hb']
    rw [card_eq_of_isLinThreeFour h] at this
    omega
  · exact ht

theorem statedModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (ε : G ≃* G')
    (h : StatedClassicalModel G' .PSL 3 2 2) : StatedClassicalModel G .PSL 3 2 2 :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ε.symm h

theorem statedModel_of_isLinThreeFour (h : IsLinThreeFour K) :
    StatedClassicalModel K .PSL 3 2 2 := by
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at hqp hqe
  subst hqp hqe
  exact CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e

end Group

theorem statedModel_quotient_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2 := by
  have hc := center_eq_bot_of_isLinThreeFour h
  let ε : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact statedModel_of_mulEquiv ε (statedModel_of_isLinThreeFour h)

theorem exists_cube_root {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ 2) :
    ∃ ω : Fˣ, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have hcard : Fintype.card Fˣ = 3 := by
    rw [Fintype.card_units, hF]; norm_num
  have h1 : 1 < Fintype.card Fˣ := by omega
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card h1 (1 : Fˣ)
  refine ⟨ω, hω, ?_⟩
  rw [← hcard]
  exact pow_card_eq_one

theorem l34Exclusion
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L E : Subgroup (MulAut V)) (hirr : X1.IsIrrOn L) (hL : IsLinThreeFour ↥L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE1 : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) (hEq : IsQuadratic E) :
    Nat.card E * Nat.card (fixV E) < Nat.card V := by
  classical
  by_contra hnot
  push Not at hnot
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have hc : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isLinThreeFour hL
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hc, Subgroup.card_bot]; exact odd_one
  have hperf : Group.IsPerfect ↥L := isPerfect_of_isLinThreeFour hL
  have hmodel := statedModel_quotient_of_isLinThreeFour hL
  obtain ⟨F, iF, iFin, φ, hFcard, hcov⟩ :=
    exists_cover_of_model hperf hodd (by norm_num : 1 ≤ 2) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hFcard
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
    (B42SL3.intertwines_map θ hcov.surjective hEN) (by norm_num) hF hirrρ hE1'
    (B42SL3.quad_map θ hEq) hoff
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root hF
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

theorem l34ExclusionProp :
    CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.L34ExclusionProp :=
  fun V _ _ hV L E hirr hL hEN hE1 hEel hEq => l34Exclusion V hV L E hirr hL hEN hE1 hEel hEq

end CFSG.HardMathSupport.Meierfrankenfeld.L34Offender
