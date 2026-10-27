module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32CaseA
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Foote5.HallD8

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76X
  CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem mem_of_sq_eq_one_of_psu3 {M : Type} [Group M] [Finite M]
    (e₂ : M ⧸ Assembly.oddCore M ≃* Open.PSU3 2 2) (P : Sylow 2 M) {D : Subgroup M}
    (hDP : D ≤ P) (hD4 : Nat.card D = 4) (hD2 : ∀ x ∈ D, x * x = 1) {x : M}
    (hxP : x ∈ (P : Subgroup M)) (hx2 : x * x = 1) : x ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Assembly.oddCore M
  have hOodd : Odd (Nat.card O) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  set ρ := QuotientGroup.mk' O with hρ
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective O
  have hinj : ∀ a ∈ (P : Subgroup M), ∀ b ∈ (P : Subgroup M), ρ a = ρ b → a = b := by
    intro a ha b hb hab
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
    have hP : IsPGroup 2 (P : Subgroup M) := P.isPGroup'
    obtain ⟨k, hk⟩ := hP ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩
    have h1 : orderOf (a⁻¹ * b) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf (a⁻¹ * b) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hab
    have h3 : orderOf (a⁻¹ * b) = 1 := by
      have h4 := Nat.dvd_gcd h1 h2
      have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
      rwa [hcop.gcd_eq_one, Nat.dvd_one] at h4
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h3
    exact h3
  set Pt := P.mapSurjective hsurj with hPt
  have hPtc : (Pt : Subgroup (M ⧸ O)) = (P : Subgroup M).map ρ := Sylow.coe_mapSurjective hsurj P
  have hB := fusionBenderBorel_of_mulEquiv_psu3 (le_refl 2) e₂
  set Z := sylowCenter (Pt : Subgroup (M ⧸ O)) with hZ
  have hZc : Nat.card Z = 4 := by
    rw [hZ, ← Hall32.card_center_eq_card_sylowCenter, (hB Pt).2.2.2.1]
    norm_num
  have hcen : ∀ w ∈ (Pt : Subgroup (M ⧸ O)), w ^ 2 = 1 → w ∈ Z := fun w hw hw2 =>
    mem_inf.mpr ⟨hw, mem_centralizer_of_fusionBenderBorel hB (by norm_num) Pt hw hw2⟩
  have hDZ : D.map ρ ≤ Z := by
    rintro _ ⟨d, hd, rfl⟩
    refine hcen _ ?_ ?_
    · rw [hPtc]
      exact mem_map_of_mem _ (hDP hd)
    · rw [← map_pow, sq, hD2 d hd, map_one]
  have hDc : Nat.card (D.map ρ) = 4 := by
    rw [← hD4]
    have hinjD : Function.Injective (ρ.comp D.subtype) := fun a b hab =>
      Subtype.ext (hinj _ (hDP a.2) _ (hDP b.2) hab)
    rw [show D.map ρ = (ρ.comp D.subtype).range by
      rw [MonoidHom.range_comp, range_subtype]]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjD).toEquiv).symm
  have heq : D.map ρ = Z := eq_of_le_of_card_ge hDZ (by rw [hZc, hDc])
  have hxZ : ρ x ∈ Z := hcen _ (by rw [hPtc]; exact mem_map_of_mem _ hxP)
    (by rw [← map_pow, sq, hx2, map_one])
  rw [← heq] at hxZ
  obtain ⟨d, hd, hdx⟩ := hxZ
  rw [← hinj d (hDP hd) x hxP hdx]
  exact hd

end CFSG.ComponentClassification.Foote5.HallD8
