module

public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralQuotients

theorem r_mul_s_sq (n : ℕ) : (r n * s n) ^ 2 = Semidihedral.z n := by
  have hs : (s n)⁻¹ = s n := inv_eq_of_mul_eq_one_right (by rw [← sq, s_sq])
  have hconj : s n * r n * s n = r n ^ (2 ^ (n - 2) - 1) := by
    simpa only [hs] using s_conj_r n
  have h1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
  calc (r n * s n) ^ 2 = r n * (s n * r n * s n) := by rw [sq]; group
    _ = r n ^ (2 ^ (n - 2) - 1 + 1) := by rw [hconj, pow_succ']
    _ = Semidihedral.z n := by rw [Nat.sub_add_cancel h1]; rfl

theorem semidihedral_perfect_no_central_involution {X : Type} [Group X] [Finite X]
    (hX : Group.IsPerfect X) (S : Sylow 2 X) {n : ℕ} (hn : 4 ≤ n)
    (hS : Nonempty ((S : Subgroup X) ≃* SemidihedralGroup n))
    {z : X} (hz : z ∈ Subgroup.center X) (hz2 : orderOf z = 2) : False := by
  obtain ⟨e⟩ := hS
  set f : SemidihedralGroup n ≃* S := e.symm with hf
  set π := QuotientGroup.mk' (ambientZ z hz) with hπ
  have hn1 : 2 ≤ n - 1 := by omega
  have hD : Nonempty (DihedralGroup (2 ^ (n - 1 - 1)) ≃*
      (quotientSylow S z hz : Subgroup (X ⧸ ambientZ z hz))) := by
    have h : n - 1 - 1 = n - 2 := by omega
    rw [h]
    exact ⟨ambientDihedralEquiv S n hn f z hz hz2⟩
  have := hX
  obtain ⟨-, -, -, -, hconj⟩ :=
    CFSG.Semidihedral.Principal.dihedral_derived_involutions_conjugate _ hn1 hD
  have hall := hconj Group.IsPerfect.commutator_eq_top
  set b : X := (f (s n) : X) with hb
  set c : X := (f (r n * s n) : X) with hc
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hb2 : orderOf (π b) = 2 := ambient_quotient_reflection_order S n hn f z hz hz2
  have hbb : b ^ 2 = 1 := by
    rw [hb, ← Subgroup.coe_pow, ← map_pow, s_sq, map_one, Subgroup.coe_one]
  have hcz : c ^ 2 = z := by
    rw [hc, ← Subgroup.coe_pow, ← map_pow, r_mul_s_sq, supplied_z_eq_involution S n hn f z hz hz2]
    rfl
  have hc2 : orderOf (π c) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hcz]
      exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
    · intro h1
      have hmem : c ∈ ambientZ z hz := (QuotientGroup.eq_one_iff c).mp h1
      rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
      · rw [h, one_pow] at hcz
        exact hz1 hcz.symm
      · rw [h, ← hz2, pow_orderOf_eq_one] at hcz
        exact hz1 hcz.symm
  obtain ⟨w, hw⟩ := isConj_iff.mp (hall (π b) (π c) hb2 hc2)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (ambientZ z hz) w
  set k := (g * b * g⁻¹)⁻¹ * c with hkdef
  have hk : k ∈ ambientZ z hz := by
    rw [hkdef, ← QuotientGroup.eq]
    simpa only [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      using hw
  have hkc : k ∈ Subgroup.center X := Subgroup.zpowers_le.mpr hz hk
  have hk2 : k ^ 2 = 1 := by
    rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hz2 hk with h | h
    · rw [h, one_pow]
    · rw [h, ← hz2, pow_orderOf_eq_one]
  have hck : c = g * b * g⁻¹ * k := by rw [hkdef]; group
  have hcomm : Commute (g * b * g⁻¹) k := Subgroup.mem_center_iff.mp hkc (g * b * g⁻¹)
  have hc1 : c ^ 2 = 1 := by
    rw [hck, hcomm.mul_pow, conj_pow, hbb, hk2]
    group
  exact hz1 (hcz.symm.trans hc1)

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
