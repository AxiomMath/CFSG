module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniA
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniDat
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniSpec

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni
  (exists_isPrimitiveRoot_three)

theorem SG.uniN_core {F : Type} [Field F] {n d : ℕ} (h : UnitaryFieldData 2 n F)
    (h3 : 3 ∣ 2 ^ n - 1) (hd : 6 ≤ d)
    {X : Subgroup (MulAut (primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)))}
    (hX : IsElemAbelian 3 X)
    (hXD : X ≤ primeFormD h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))
    {α : MulAut (primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))} (hα : α ∈ X) :
    ∃ A : Subgroup (primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)),
      IsSimpleGroup ↥A ∧ (∃ a b : ↥A, a * b ≠ b * a) ∧ 3 ∣ Nat.card ↥A ∧ A ≤ fixSubgroup α ∧
      ∃ Y : Subgroup (MulAut (primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))),
        Y.relIndex X ≤ 3 ∧ ∀ ε ∈ Y, A ≤ fixSubgroup ε := by
  haveI := h.finite
  obtain ⟨m, hm⟩ := h3
  have h2n : 2 ^ n = 3 * m + 1 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  let φ := primeFormConjHom h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  have hnp : ∀ z ∈ φ.rangeRestrict.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    rw [MonoidHom.ker_rangeRestrict] at hz
    obtain ⟨c, hc1, hzc⟩ :=
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h (by omega)
        (fun hh => absurd hh.1 (by omega)) z).1 hz
    have hz3' : (z : GL (Fin d) F) ^ 3 = 1 := by simpa using congrArg Subtype.val hz3
    have hc3 : (c : F) ^ 3 = 1 := by
      have h1 : GeneralLinearGroup.scalar (Fin d) (c ^ 3) = 1 := by
        rw [map_pow, ← hzc]
        exact hz3'
      have := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) ⟨0, by omega⟩
        ⟨0, by omega⟩) h1
      simpa only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Units.val_pow_eq_pow_val, Units.val_one,
        Matrix.one_apply_eq] using this
    have hcn : (c : F) * (c : F) ^ 2 ^ n = 1 := by
      rwa [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hc1
    have hc2 : (c : F) ^ 2 = 1 := by
      have e : (c : F) * (c : F) ^ 2 ^ n = (c : F) ^ 2 * ((c : F) ^ 3) ^ m := by
        rw [h2n]
        ring
      rw [hc3, one_pow, mul_one] at e
      exact e.symm.trans hcn
    have hc : c = 1 := Units.ext (by rw [Units.val_one]; linear_combination hc3 - (c : F) * hc2)
    rw [hc, map_one] at hzc
    exact Subtype.ext hzc
  obtain ⟨Ã, hmap, hinj, hAe, -⟩ := CFSG.StandardType.TableBUE.exists_lift_of_noTorsion
    φ.rangeRestrict φ.rangeRestrict_surjective Nat.prime_three hnp (hX.subgroupOf φ.range)
  have hαr : α ∈ φ.range := hXD hα
  have hα' : (⟨α, hαr⟩ : φ.range) ∈ Ã.map φ.rangeRestrict := by
    rw [hmap]
    exact hα
  obtain ⟨g₀, hg₀Ã, hg₀⟩ := hα'
  let ρ : ↥Ã →* Matrix (Fin d) (Fin d) F :=
    (Units.coeHom (Matrix (Fin d) (Fin d) F)).comp ((Subgroup.subtype _).comp Ã.subtype)
  have hρ : ∀ g : ↥Ã, conjTr h.barEquiv (ρ g) * ρ g = 1 := fun g => by
    have h0 := (mem_primeFormUnitary (h := h)).1 g.1.2
    simp only [Units.val_one, Matrix.mul_one] at h0
    exact h0
  have hu : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, h.card, pow_mul]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 n
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_three hu
  have hσω : h.barEquiv ω = ω := by
    rw [UnitaryFieldData.barEquiv_apply, UnitaryFieldData.bar_apply, h2n, pow_succ, pow_mul,
      hω.pow_eq_one, one_pow, one_mul]
  obtain ⟨x, y, z, hxx, hyy, hxy, hz, hzx, hzy, K, hK, hg₀K, hKact⟩ :=
    SG.exists_sl2_data h.isUnitaryInvolution_barEquiv hω hσω hd
      (fun g g' => Subtype.ext (hAe.comm g.2 g'.2)) (fun g => Subtype.ext (hAe.2 g.1 g.2)) ρ hρ
      ⟨g₀, hg₀Ã⟩
  obtain ⟨A, hAs, hAn, hA3, hAfix⟩ := SG.exists_sl2_primeFormP h x y hxx hyy hxy hz hzx hzy
  have hfix : ∀ k ∈ K, A ≤ fixSubgroup (φ k.1) := fun k hk => by
    obtain ⟨a, hx, hy⟩ := hKact k hk
    exact hAfix k.1 a hx hy
  have hψinj : Function.Injective (φ.comp Ã.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g.1 g.2 (Subtype.ext hg))
  have hψX : (⊤ : Subgroup ↥Ã).map (φ.comp Ã.subtype) = X := by
    ext e
    constructor
    · rintro ⟨g, -, rfl⟩
      have : φ.rangeRestrict g.1 ∈ X.subgroupOf φ.range := by
        rw [← hmap]
        exact ⟨g.1, g.2, rfl⟩
      exact this
    · intro he
      have he' : (⟨e, hXD he⟩ : φ.range) ∈ Ã.map φ.rangeRestrict := by
        rw [hmap]
        exact he
      obtain ⟨g, hgÃ, hg⟩ := he'
      exact ⟨⟨g, hgÃ⟩, trivial, congrArg Subtype.val hg⟩
  refine ⟨A, hAs, hAn, hA3, ?_, K.map (φ.comp Ã.subtype), ?_, ?_⟩
  · have := hfix _ hg₀K
    rwa [show φ g₀ = α from congrArg Subtype.val hg₀] at this
  · rw [← hψX, Subgroup.relIndex_map_map_of_injective _ _ hψinj, Subgroup.relIndex_top_right]
    exact hK
  · rintro _ ⟨k, hk, rfl⟩
    exact hfix k hk

end CFSG.LocalAnalysis.GLTheoremA.S265

end
