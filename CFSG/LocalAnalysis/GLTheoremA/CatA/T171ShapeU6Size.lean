module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6SizeField
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassPg
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5FieldBound
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.StandardType.Line63.H5

theorem u6SizeModel_holds : U6SizeModel := by
  intro n K _ _ h hpq Ab hAb hmem hfield
  classical
  obtain ⟨a₀, ha₀, M₀, hM₀gu, l, hM₀3, hl, ha₀eq⟩ := hfield
  let H : Subgroup (GL (Fin 6) K) := unitarySU 2 n K 6
  have hH : H = LargeEvenSUGroup (Fin 6) K (2 ^ n) := rfl
  let N : Subgroup (GL (Fin 6) K) := Subgroup.normalizer (H : Set (GL (Fin 6) K))
  let ρ : N →* MulAut (LargeEvenProj H) := TableB.projConj H
  let MB : Subgroup N := Ab.comap ρ
  have hM₀N : M₀ ∈ N := by
    change M₀ ∈ Subgroup.normalizer (H : Set (GL (Fin 6) K))
    rw [hH]
    exact TableBUE.gu_subset_normalizer h hM₀gu
  let y₀ : N := ⟨M₀, hM₀N⟩
  have hρy₀ : ρ y₀ = a₀ := by
    rw [ha₀eq]
  have hM₀MB : y₀ ∈ MB := by
    change ρ y₀ ∈ Ab
    rw [hρy₀]
    exact ha₀
  let z₀ : MB := ⟨y₀, hM₀MB⟩
  have hS : LargeEvenGUSet (Fin 6) K (2 ^ n) ⊆ (N : Set (GL (Fin 6) K)) := by
    intro M hM
    change M ∈ Subgroup.normalizer (H : Set (GL (Fin 6) K))
    rw [hH]
    exact TableBUE.gu_subset_normalizer h hM
  have hABrange : Ab ≤ ρ.range := by
    intro a ha
    obtain ⟨M, hM, hMeq⟩ := TableB.exists_eq_projConj (H := H) hS (hmem a ha)
    exact ⟨⟨M, hS hM⟩, hMeq.symm⟩
  have hMBrange : MB.map ρ = Ab := by
    change (Ab.comap ρ).map ρ = Ab
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hABrange
  let ρMB : MB →* MulAut (LargeEvenProj H) := ρ.comp MB.subtype
  have hrange : ρMB.range = Ab := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hMBrange]
  let ScalN : Subgroup N := (LargeEvenScalars (Fin 6) K).subgroupOf N
  have hScalNcard : Nat.card ScalN = Nat.card Kˣ := by
    have h1 : Nat.card ScalN = Nat.card (LargeEvenScalars (Fin 6) K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (fun z hz => TableB.scalar_mem_normalizer H hz)).toEquiv
    have h2 : Nat.card (LargeEvenScalars (Fin 6) K) = Nat.card Kˣ := by
      rw [largeEvenScalars_def]
      exact (Nat.card_congr
        (MonoidHom.ofInjective (scalar_six_injective (K := K))).toEquiv).symm
    rw [h1, h2]
  have hScalNleMB : ScalN ≤ MB := by
    intro z hz
    change ρ z ∈ Ab
    have hz' : (z : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := hz
    rw [show ρ z = 1 from TableB.projConj_of_scalar H hz']
    exact Ab.one_mem
  let ScalMB : Subgroup MB := ScalN.subgroupOf MB
  have hScalMBcard : Nat.card ScalMB = Nat.card Kˣ := by
    have h1 : Nat.card ScalMB = Nat.card ScalN :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hScalNleMB).toEquiv
    rw [h1, hScalNcard]
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have h := congrArg Prod.fst he
    simp only at h
    omega
  have hker : ρMB.ker = ScalMB := by
    change ρMB.ker = ScalN.subgroupOf MB
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      have h1 : ρ (y : N) = 1 := MonoidHom.mem_ker.mp hy
      have h1' : TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) (y : N) = 1 := h1
      exact TableBUE.mem_scalars_of_projConj_eq_one (d := 6) h hK (by norm_num) hdq
        Nat.prime_three hpq h1'
    · intro hy
      rw [MonoidHom.mem_ker]
      rw [Subgroup.mem_subgroupOf] at hy
      have hz : (y : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := hy
      exact TableB.projConj_of_scalar H hz
  have hkerCard : Nat.card ρMB.ker = Nat.card Kˣ := by
    rw [hker]
    exact hScalMBcard
  have hcardMB : Nat.card MB = Nat.card Kˣ * Nat.card Ab := by
    have h := Subgroup.card_ker_mul_card_range ρMB
    rw [hrange, hkerCard] at h
    exact h.symm

  have hcommScalar (y : MB) : ∃ ζ : Kˣ,
      ((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) ζ := by
    have hker1 : ρMB (y * z₀ * y⁻¹ * z₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change ρ (y : N) * ρ (z₀ : N) * (ρ (y : N))⁻¹ * (ρ (z₀ : N))⁻¹ = 1
      have hyA : ρ (y : N) ∈ Ab := y.2
      have hy₀A : ρ (z₀ : N) ∈ Ab := z₀.2
      have hcm : ρ (y : N) * ρ (z₀ : N) = ρ (z₀ : N) * ρ (y : N) :=
        CFSG.StandardType.TableB.IsElemAbelian.comm hAb hyA hy₀A
      rw [hcm]
      group
    have hmem : y * z₀ * y⁻¹ * z₀⁻¹ ∈ ρMB.ker := MonoidHom.mem_ker.mpr hker1
    rw [hker] at hmem
    have hmem' : (((y * z₀ * y⁻¹ * z₀⁻¹ : MB) : N) : GL (Fin 6) K) ∈
        LargeEvenScalars (Fin 6) K := hmem
    obtain ⟨ζ, hζ⟩ := hmem'
    exact ⟨ζ, by simpa [z₀] using hζ.symm⟩
  let twistFun : MB → Kˣ := fun y => (hcommScalar y).choose
  have twist_spec (y : MB) :
      ((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) :=
    (hcommScalar y).choose_spec
  have hconj (y : MB) :
      ((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) * M₀ := by
    have h := twist_spec y
    calc ((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹
        = (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹) * M₀ :=
          by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) * M₀ := by rw [h]
  have twist_mul (y z : MB) : twistFun (y * z) = twistFun y * twistFun z := by
    apply scalar_six_injective
    have h1 := twist_spec (y * z)
    have h2 : (((y * z : MB) : N) : GL (Fin 6) K) * M₀ *
        (((y * z : MB) : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y * twistFun z) := by
      have hY := hconj y
      have hZ := hconj z
      have hYZ : (((y * z : MB) : N) : GL (Fin 6) K) =
          ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) := rfl
      rw [hYZ]
      calc ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) * M₀ *
            (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K))⁻¹ * M₀⁻¹
          = ((y : N) : GL (Fin 6) K) *
              (((z : N) : GL (Fin 6) K) * M₀ * ((z : N) : GL (Fin 6) K)⁻¹) *
                ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ := by group
        _ = ((y : N) : GL (Fin 6) K) *
              (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun z) * M₀) *
                ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ := by rw [hZ]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun z) *
              (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹) * M₀⁻¹ := by
          rw [← mul_assoc ((y : N) : GL (Fin 6) K)
            (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun z)) M₀,
            (commute_scalar (twistFun z) ((y : N) : GL (Fin 6) K)).eq]
          group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun z) *
              (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) * M₀) * M₀⁻¹ := by
          rw [hY]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y * twistFun z) := by
          rw [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun z))
            (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y)) M₀,
            ← map_mul, mul_comm]
          group
    rw [← h1, h2]
  let twist : MB →* Kˣ := MonoidHom.mk' twistFun twist_mul
  have hker_comm (y : MB) (hy : twist y = 1) :
      ((y : N) : GL (Fin 6) K) * M₀ = M₀ * ((y : N) : GL (Fin 6) K) := by
    have h := hconj y
    rw [show twistFun y = 1 from hy, map_one, one_mul] at h
    calc ((y : N) : GL (Fin 6) K) * M₀
        = (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹) *
            ((y : N) : GL (Fin 6) K) := by group
      _ = M₀ * ((y : N) : GL (Fin 6) K) := by rw [h]
  have hcomm_ker (y : MB)
      (hy : ((y : N) : GL (Fin 6) K) * M₀ = M₀ * ((y : N) : GL (Fin 6) K)) :
      twist y = 1 := by
    change twistFun y = 1
    apply scalar_six_injective
    have hspec := twist_spec y
    rw [← hspec]
    have h1 : ((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹ * M₀⁻¹ = 1 := by
      rw [hy]
      group
    rw [h1, map_one]
  have twist_pow_three (y : MB) : twist y ^ 3 = 1 := by
    have h := hconj y
    have h3 : (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹) ^ 3 =
        (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) * M₀) ^ 3 := by rw [h]
    have hL : (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹) ^ 3 =
        M₀ ^ 3 := by
      calc (((y : N) : GL (Fin 6) K) * M₀ * ((y : N) : GL (Fin 6) K)⁻¹) ^ 3
          = ((y : N) : GL (Fin 6) K) * M₀ ^ 3 * ((y : N) : GL (Fin 6) K)⁻¹ := by
              rw [conj_pow]
        _ = M₀ ^ 3 := by
            rw [hM₀3, (commute_scalar l ((y : N) : GL (Fin 6) K)).eq]
            group
    have hR : (Matrix.GeneralLinearGroup.scalar (Fin 6) (twistFun y) * M₀) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) ((twistFun y) ^ 3) * M₀ ^ 3 := by
      have hh := (commute_scalar (twistFun y) M₀).symm.mul_pow 3
      simpa only [map_pow] using hh
    rw [hL, hR, hM₀3] at h3
    have h4 : Matrix.GeneralLinearGroup.scalar (Fin 6) ((twistFun y) ^ 3) = 1 := by
      apply mul_right_cancel (b := Matrix.GeneralLinearGroup.scalar (Fin 6) l)
      rw [one_mul]
      exact h3.symm
    have h5 : (twistFun y) ^ 3 = 1 := by
      apply scalar_six_injective
      rw [h4, map_one]
    change twistFun y ^ 3 = 1
    exact h5
  let S : Subgroup MB := twist.ker
  let Sgl : Subgroup (GL (Fin 6) K) := S.map (N.subtype.comp MB.subtype)
  have hSglcard : Nat.card Sgl = Nat.card S := by
    rw [show Sgl = S.map (N.subtype.comp MB.subtype) from rfl]
    exact Subgroup.card_map_of_injective (f := N.subtype.comp MB.subtype) (by
      intro a b h
      exact Subtype.ext (Subtype.ext h))
  have hMB_pow_three (y : MB) : ∃ k : Kˣ, (((y : N) : GL (Fin 6) K)) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) k := by
    have h1 : ρMB (y ^ 3) = 1 := by
      rw [map_pow]
      change (ρ (y : N)) ^ 3 = 1
      rw [hAb.2 (ρ (y : N)) y.2]
    have hmem : y ^ 3 ∈ ρMB.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    have hmem' : (((y ^ 3 : MB) : N) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := hmem
    obtain ⟨k, hk⟩ := hmem'
    exact ⟨k, by simpa using hk.symm⟩
  have hcommutatorScalar (y z : MB) : ∃ ζ : Kˣ,
      ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
        ((y : N) : GL (Fin 6) K)⁻¹ * ((z : N) : GL (Fin 6) K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) ζ := by
    have hker1 : ρMB (y * z * y⁻¹ * z⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change ρ (y : N) * ρ (z : N) * (ρ (y : N))⁻¹ * (ρ (z : N))⁻¹ = 1
      have hyA : ρ (y : N) ∈ Ab := y.2
      have hzA : ρ (z : N) ∈ Ab := z.2
      have hcm : ρ (y : N) * ρ (z : N) = ρ (z : N) * ρ (y : N) :=
        CFSG.StandardType.TableB.IsElemAbelian.comm hAb hyA hzA
      rw [hcm]
      group
    have hmem : y * z * y⁻¹ * z⁻¹ ∈ ρMB.ker := MonoidHom.mem_ker.mpr hker1
    rw [hker] at hmem
    have hmem' : (((y * z * y⁻¹ * z⁻¹ : MB) : N) : GL (Fin 6) K) ∈
        LargeEvenScalars (Fin 6) K := hmem
    obtain ⟨ζ, hζ⟩ := hmem'
    exact ⟨ζ, by simpa using hζ.symm⟩
  have hMSgl : M₀ ∈ Sgl := by
    have hz₀S : z₀ ∈ S := hcomm_ker z₀ (by rfl)
    rw [show Sgl = S.map (N.subtype.comp MB.subtype) from rfl]
    exact ⟨z₀, hz₀S, rfl⟩
  have hcommSgl : ∀ A ∈ Sgl, ∀ B ∈ Sgl, A * B = B * A := by
    intro A hA B hB
    rw [show Sgl = S.map (N.subtype.comp MB.subtype) from rfl] at hA hB
    obtain ⟨y, hyS, rfl⟩ := hA
    obtain ⟨z, hzS, rfl⟩ := hB
    have hy1 : twist y = 1 := hyS
    have hz1 : twist z = 1 := hzS
    have hYM := hker_comm y hy1
    have hZM := hker_comm z hz1
    obtain ⟨ζ, hζ⟩ := hcommutatorScalar y z
    obtain ⟨k, hk⟩ := hMB_pow_three z
    have hζ3 : ζ ^ 3 = 1 := by
      have hYZ : ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
          ((y : N) : GL (Fin 6) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ *
            ((z : N) : GL (Fin 6) K) := by
        calc ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
              ((y : N) : GL (Fin 6) K)⁻¹
            = (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
                ((y : N) : GL (Fin 6) K)⁻¹ * ((z : N) : GL (Fin 6) K)⁻¹) *
                  ((z : N) : GL (Fin 6) K) := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ *
                ((z : N) : GL (Fin 6) K) := by rw [hζ]
      have hcube : (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
          ((y : N) : GL (Fin 6) K)⁻¹) ^ 3 =
          (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * ((z : N) : GL (Fin 6) K)) ^ 3 := by
        rw [hYZ]
      have hL : (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
          ((y : N) : GL (Fin 6) K)⁻¹) ^ 3 = ((z : N) : GL (Fin 6) K) ^ 3 := by
        calc (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
              ((y : N) : GL (Fin 6) K)⁻¹) ^ 3
            = ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) ^ 3 *
                ((y : N) : GL (Fin 6) K)⁻¹ := by rw [conj_pow]
          _ = ((y : N) : GL (Fin 6) K) *
                Matrix.GeneralLinearGroup.scalar (Fin 6) k * ((y : N) : GL (Fin 6) K)⁻¹ := by
              rw [hk]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 6) k := by
              rw [(commute_scalar k ((y : N) : GL (Fin 6) K)).eq]
              group
          _ = ((z : N) : GL (Fin 6) K) ^ 3 := by rw [hk]
      have hR : (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ *
          ((z : N) : GL (Fin 6) K)) ^ 3 =
          Matrix.GeneralLinearGroup.scalar (Fin 6) (ζ ^ 3) *
            ((z : N) : GL (Fin 6) K) ^ 3 := by
        have hh := (commute_scalar ζ ((z : N) : GL (Fin 6) K)).symm.mul_pow 3
        simpa only [map_pow] using hh
      rw [hL, hR, hk] at hcube
      have h4 : Matrix.GeneralLinearGroup.scalar (Fin 6) (ζ ^ 3) = 1 := by
        apply mul_right_cancel (b := Matrix.GeneralLinearGroup.scalar (Fin 6) k)
        rw [one_mul]
        exact hcube.symm
      exact scalar_six_injective (by rw [h4, map_one])
    have hζ1 := commutator_eq_one_of_fieldType hM₀3 hl hYM hZM hζ hζ3
    rw [hζ1, map_one] at hζ
    calc ((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K)
        = (((y : N) : GL (Fin 6) K) * ((z : N) : GL (Fin 6) K) *
            ((y : N) : GL (Fin 6) K)⁻¹ * ((z : N) : GL (Fin 6) K)⁻¹) *
              (((z : N) : GL (Fin 6) K) * ((y : N) : GL (Fin 6) K)) := by group
      _ = ((z : N) : GL (Fin 6) K) * ((y : N) : GL (Fin 6) K) := by rw [hζ, one_mul]
  have hpowSgl : ∀ Y ∈ Sgl, ∃ k : Kˣ,
      Y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) k := by
    intro Y hY
    rw [show Sgl = S.map (N.subtype.comp MB.subtype) from rfl] at hY
    obtain ⟨y, -, rfl⟩ := hY
    exact hMB_pow_three y
  have hω : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    obtain ⟨h3, -⟩ := card_units_dvd_odd h hpq
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, fun h1 => ?_⟩
    rw [h1, orderOf_one] at hω
    omega
  have hScalMB_le_S : ScalMB ≤ S := by
    intro z hz
    change twist z = 1
    apply hcomm_ker
    have hz' : (((z : MB) : N) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := hz
    obtain ⟨c, hc⟩ := hz'
    have hc' : Commute (((z : MB) : N) : GL (Fin 6) K) M₀ := by
      rw [← hc]
      exact (commute_scalar c M₀).symm
    exact hc'.eq
  have hscalSgl : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Sgl := by
    intro c
    have hzN : (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) ∈ N :=
      TableB.scalar_mem_normalizer H (by
        rw [largeEvenScalars_def]
        exact ⟨c, rfl⟩)
    have hzScal : (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hzN⟩ : N) ∈ ScalN := by
      change (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) ∈
        LargeEvenScalars (Fin 6) K
      rw [largeEvenScalars_def]
      exact ⟨c, rfl⟩
    have hzMB : (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hzN⟩ : N) ∈ MB :=
      hScalNleMB hzScal
    let z : MB := ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hzN⟩, hzMB⟩
    have hzS : z ∈ S := hScalMB_le_S (by
      change (((z : MB) : N) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K
      exact hzScal)
    rw [show Sgl = S.map (N.subtype.comp MB.subtype) from rfl]
    exact ⟨z, hzS, rfl⟩
  have hSgl9 : Nat.card Sgl ≤ 9 * Nat.card Kˣ :=
    card_le_nine_of_fieldType hω hM₀3 hl hMSgl hcommSgl hscalSgl hpowSgl
  have hrange_le : twist.range ≤ rootsOfUnity 3 K := by
    rintro _ ⟨y, rfl⟩
    rw [mem_rootsOfUnity]
    exact twist_pow_three y
  have hrange_card : Nat.card twist.range ≤ 3 := by
    have h1 := Subgroup.card_le_of_le hrange_le
    have h2 : Nat.card (rootsOfUnity 3 K) = (Nat.card K - 1).gcd 3 :=
      CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd 3
    rw [h2] at h1
    exact h1.trans (Nat.gcd_le_right _ (by norm_num))
  have hcardTwist : Nat.card MB = Nat.card S * Nat.card twist.range := by
    have h := Subgroup.card_ker_mul_card_range twist
    change Nat.card S * Nat.card twist.range = Nat.card MB at h
    exact h.symm
  have hKpos : 0 < Nat.card Kˣ := Nat.card_pos
  have hmain : Nat.card Ab * Nat.card Kˣ ≤ 27 * Nat.card Kˣ := by
    calc Nat.card Ab * Nat.card Kˣ = Nat.card Kˣ * Nat.card Ab := mul_comm _ _
      _ = Nat.card MB := hcardMB.symm
      _ = Nat.card S * Nat.card twist.range := hcardTwist
      _ ≤ Nat.card Sgl * 3 := by
          rw [hSglcard]
          exact Nat.mul_le_mul_left _ hrange_card
      _ ≤ (9 * Nat.card Kˣ) * 3 := Nat.mul_le_mul_right _ hSgl9
      _ = 27 * Nat.card Kˣ := by ring
  have hAb27 : Nat.card Ab ≤ 27 := Nat.le_of_mul_le_mul_right hmain hKpos
  simpa [show (3 : ℕ) ^ 3 = 27 by norm_num] using hAb27

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
