module

public import CFSG.GF2Type.SmithTypeE.L6.IdGram
public import CFSG.LargeExtraspecial.S14SMKDeltaBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.LMod
open CFSG.LargeExtraspecial.S14.SMK (commute_of_mem_Kz_Dl)

variable {G : Type} [Group G] [Finite G] (S : Setting G) {g : G}

omit [Finite G] in
theorem not_exists_conj_mul_z (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    ¬ ∃ y ∈ S.QG, y * (g * S.z * g⁻¹) * y⁻¹ = g * S.z * g⁻¹ * S.z := by
  rintro ⟨y, -, hy⟩
  apply hxz
  rw [← hy]
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans (isConj_iff.mpr ⟨y, rfl⟩)

theorem fixQt_eq_of_not_isConj (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.fixQt (g * S.z * g⁻¹) = S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) := by
  by_contra h
  exact not_exists_conj_mul_z S hxz (S.lemma_3_2_1 hxM h)

theorem Dl_le_commutator (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.QG ⊓ S.Qa g ≤ ⁅zpowers (g * S.z * g⁻¹), S.QG⁆ := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  rw [(S.commutator_eq_centralizer_centralizer hxM hxQ hx2
    (fixQt_eq_of_not_isConj S hxM hxz)).1]
  intro d hd
  exact ⟨hd.1, mem_centralizer_iff.mpr fun u hu => commute_of_mem_Kz_Dl S hxQ hu hd⟩

theorem clSub_Dl_le_commQt (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.clSub (S.QG ⊓ S.Qa g) ≤ S.commQt (g * S.z * g⁻¹) := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  intro v hv
  obtain ⟨d, hd, -, rfl⟩ := S.mem_clSub_iff.mp hv
  have h := Dl_le_commutator S hxM hxQ hxz hd
  rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2] at h
  exact h.2

theorem exists_commute_rhoM_eq_of_not_isConj (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) (m : S.M)
    (hm : rhoM S m * rhoM S ⟨_, hxM⟩ = rhoM S ⟨_, hxM⟩ * rhoM S m) :
    ∃ m' : S.M, Commute (m' : G) (g * S.z * g⁻¹) ∧ rhoM S m' = rhoM S m := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hfix := fixQt_eq_of_not_isConj S hxM hxz
  have hhM : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem m.2 hxM) (S.M.inv_mem m.2)) (S.M.inv_mem hxM)
  have hhQ : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ ∈ S.QG := by
    have e : (⟨_, hhM⟩ : S.M) = m * ⟨_, hxM⟩ * m⁻¹ * (⟨_, hxM⟩ : S.M)⁻¹ := Subtype.ext rfl
    have hm' : S.ρ m * S.ρ ⟨_, hxM⟩ = S.ρ ⟨_, hxM⟩ * S.ρ m := congrArg Subtype.val hm
    have h1 : S.ρ ⟨_, hhM⟩ = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hm']
      group
    exact (S.ρ_eq_one_iff _).mp h1
  have hgh : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ =
      (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ * (g * S.z * g⁻¹) := by group
  rcases S.lemma_3_2_2 hxM hx2 hfix m.2 hhQ hgh with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · have hyM : y⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hy)
    refine ⟨⟨y⁻¹, hyM⟩ * m, ?_, ?_⟩
    · show y⁻¹ * (m : G) * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * (y⁻¹ * m)
      calc y⁻¹ * (m : G) * (g * S.z * g⁻¹) =
          y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * m := by group
        _ = y⁻¹ * (y * (g * S.z * g⁻¹) * y⁻¹) * m := by rw [hgh, hyx]
        _ = (g * S.z * g⁻¹) * (y⁻¹ * m) := by group
    · have h1 : rhoM S ⟨y⁻¹, hyM⟩ = 1 :=
        Subtype.ext ((S.ρ_eq_one_iff _).mpr (S.QG.inv_mem hy))
      rw [map_mul, h1, one_mul]
  · exfalso
    apply hxz
    have e : g * S.z * g⁻¹ * S.z =
        y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * y := by
      rw [hgh, ← hyx]
      group
    rw [e]
    have h1 : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have h2 : IsConj (g * S.z * g⁻¹) ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) :=
      isConj_iff.mpr ⟨(m : G), rfl⟩
    have h3 : IsConj ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹)
        (y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * y) :=
      isConj_iff.mpr ⟨y⁻¹, by rw [inv_inv]⟩
    exact h1.trans (h2.trans h3)

omit [Finite G] in
theorem conj_mem_Dl {m : G} (hmM : m ∈ S.M) (hmx : Commute m (g * S.z * g⁻¹)) {d : G}
    (hd : d ∈ S.QG ⊓ S.Qa g) : m * d * m⁻¹ ∈ S.QG ⊓ S.Qa g := by
  have hmT : m ∈ (S.conjBy g).M := mem_centralizer_singleton_iff.mpr hmx.eq
  exact ⟨S.conj_mem_QG hmM hd.1, (S.conjBy g).conj_mem_QG hmT hd.2⟩

theorem exists_fixed_ne_zero_of_le {P : Subgroup S.O} (hP : IsPGroup 2 P)
    {W : Submodule (ZMod 2) S.Qt} (hW0 : W ≠ ⊥)
    (hW : ∀ p ∈ P, ∀ w ∈ W, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  classical
  let act : MulAction P W :=
    { smul := fun p w => ⟨((p : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, hW p p.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun p q w => Subtype.ext rfl }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card W := by
    rw [S.card_submodule]
    have : finrank (ZMod 2) W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    exact dvd_pow_self 2 this
  have h0 : (0 : W) ∈ MulAction.fixedPoints P W := fun p => Subtype.ext (map_zero _)
  obtain ⟨w, hw, hw0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h.symm), fun p hp => ?_⟩
  have := hw ⟨p, hp⟩
  exact congrArg Subtype.val this

end CFSG.GF2Type.SmithTypeE.L6
