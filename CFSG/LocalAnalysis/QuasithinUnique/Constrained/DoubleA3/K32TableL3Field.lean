module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBoundGen

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne

section Field

variable {F : Type} [Field F]

theorem k32_exists_card_two_pow [CharP F 2] [Finite F] : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem k32_l3_ker_odd [CharP F 2] [Finite F] : ¬ 2 ∣ Nat.card (LinearFlag.proj 3 F).ker := by
  rw [LinearFlag.ker_proj]
  intro h2
  obtain ⟨f, hf, hq⟩ := k32_exists_card_two_pow (F := F)
  have h1 := (h2.trans (card_scalars_dvd (K := F) (n := 3) (by norm_num)))
  rw [hq] at h1
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h4 : 2 ∣ 1 := (Nat.dvd_sub_iff_right hpos h3).mp h1
  omega

theorem k32_l3_two_lift_fixed {σ : F ≃+* F} {u : Matrix.SpecialLinearGroup (Fin 3) F} {k : ℕ}
    (hu : u ^ 2 ^ k = 1)
    (h : LinearFlag.proj 3 F (Matrix.SpecialLinearGroup.map σ.toRingHom u) = LinearFlag.proj 3 F u) :
    Matrix.SpecialLinearGroup.map σ.toRingHom u = u := by
  set su := Matrix.SpecialLinearGroup.map σ.toRingHom u with hsu
  have hz := LinearFlag.proj_eq_proj_iff.mp h
  set z := su⁻¹ * u with hzdef
  have hzcenter : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [← LinearFlag.scalars_eq_center]
    exact hz
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨c, hc, hmat⟩ := LinearFlag.mem_scalars.mp hz
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hmat, Matrix.SpecialLinearGroup.coe_one,
      ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  have hsuk : su ^ 2 ^ k = 1 := by
    rw [hsu, ← map_pow, hu, map_one]
  have hcomm : Commute su z := by
    exact Subgroup.mem_center_iff.mp hzcenter su
  have hz2 : z ^ 2 ^ k = 1 := by
    have h1 : u = su * z := by rw [hzdef]; group
    have h2 : u ^ 2 ^ k = su ^ 2 ^ k * z ^ 2 ^ k := by
      conv_lhs => rw [h1]
      exact hcomm.mul_pow _
    rw [hu, hsuk, one_mul] at h2
    exact h2.symm
  have hz1 : z = 1 := by
    have hd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz2
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have := Nat.dvd_gcd hd3 hd2
    rw [hcop, Nat.dvd_one] at this
    exact orderOf_eq_one_iff.mp this
  rw [hzdef, inv_mul_eq_one] at hz1
  exact hz1

end Field

section Bound

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem k32_l3_field_bound {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {W : Subgroup (projectiveSL 3 F)} (hW : IsPGroup 2 ↥W)
    (hfix : ∀ w ∈ W, LinearFlag.fieldAut 3 F σ w = w) : Nat.card W ≤ Nat.card F := by
  obtain ⟨V, hV2, hVmap, hVcard⟩ := k32_lift_two_group (LinearFlag.proj 3 F)
    (LinearFlag.proj_surjective 3 F) k32_l3_ker_odd hW
  obtain ⟨f, hf1, hf⟩ := k32_exists_card_two_pow (F := F)
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf1 hf hσ
  set k : Subfield F := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ with hk
  have : Finite k := Subtype.finite
  have : CharP k 2 := inferInstance
  have hrange : W ≤ (linearSubfieldInclusion 3 k).range := by
    intro w hw
    rw [← hVmap] at hw
    obtain ⟨u, huV, rfl⟩ := hw
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨u, huV⟩
    have hu : u ^ 2 ^ j = 1 := by
      have := hj
      rw [Subgroup.orderOf_mk] at this
      rw [← this]
      exact pow_orderOf_eq_one u
    have hfw : LinearFlag.fieldAut 3 F σ (LinearFlag.proj 3 F u) = LinearFlag.proj 3 F u :=
      hfix _ (hVmap ▸ Subgroup.mem_map_of_mem _ huV)
    rw [LinearFlag.fieldAut_proj] at hfw
    have hsu := k32_l3_two_lift_fixed hu hfw
    refine mem_range_linearSubfieldInclusion.mpr ⟨u, fun i j => ?_, rfl⟩
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F) i j) hsu
    simp only [Matrix.SpecialLinearGroup.map_apply_coe] at this
    exact RingHom.mem_eqLocusField.mpr this
  set j := linearSubfieldInclusion 3 k with hjdef
  have hjinj : Function.Injective j := linearSubfieldInclusion_injective (by norm_num) k
  set W₁ : Subgroup (projectiveSL 3 k) := W.comap j with hW₁
  have hmap : W₁.map j = W := by
    rw [hW₁, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hrange
  have hcard₁ : Nat.card W₁ = Nat.card W := by
    have h1 := Subgroup.card_map_of_injective (K := W₁) hjinj
    rw [hmap] at h1
    exact h1.symm
  have hW₁2 : IsPGroup 2 ↥W₁ := by
    refine hW.of_injective ((j.comp W₁.subtype).codRestrict W fun a => ?_) ?_
    · exact a.2
    · intro a b hab
      exact Subtype.ext (hjinj (congrArg Subtype.val hab))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨S', hS'⟩ := hW₁2.exists_le_sylow
  have hcardS : Nat.card (S' : Subgroup (projectiveSL 3 k)) = Nat.card k ^ 3 := by
    have h1 := S'.card_eq_multiplicity
    have h2 := S.card_eq_multiplicity
    have h3 : Nat.card (S : Subgroup (projectiveSL 3 k)) = Nat.card k ^ 3 := by
      rw [hS, card_projUnitriangular]
    rw [← h3, h2]
    exact h1
  have hle : Nat.card W₁ ≤ Nat.card k ^ 3 := by
    rw [← hcardS]
    exact Subgroup.card_le_of_le hS'
  rw [← hcard₁]
  refine hle.trans ?_
  rw [hkcard, ← pow_mul, hf]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Bound

end CFSG.QuasithinUnique.DoubleA3
