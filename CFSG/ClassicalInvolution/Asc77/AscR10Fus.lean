module

public import CFSG.ClassicalInvolution.Asc77.AscR10Lz
public import CFSG.ClassicalInvolution.Asc77.AscR10Aft2
public import CFSG.ClassicalInvolution.Asc77.AscR10Viol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



theorem Std20.r_fusion_S [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1))
    {s : G} (hs2 : s * s = 1) (hsb : s * b = b * s) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hsz : ∃ g : G, s = g * z * g⁻¹) :
    ∃ c : G, c * b = b * c ∧ s = c * z * c⁻¹ := by
  obtain ⟨e₀, hfe, h5, hzA, htA, hmem, hlt, hIH, J_b, hv⟩ :=
    d.r_aViol c7 c9 h8 h9 hb hk hu huo hact
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hsb
  have hΛ := d.x_hypOmegaMod_conjFamily hzA hmem
  have htw := d.r_nbr_twin h5 hzA hmem
  let T : Set ↥C := {y | ∃ g : G, (y : G) = g * z * g⁻¹}
  have hT : ∀ y ∈ T, ∀ e : ↥C, e * y * e⁻¹ ∈ T := by
    rintro y ⟨g, hg⟩ e
    exact ⟨(e : G) * g, by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]; group⟩
  have hZ : ∀ y ∈ T, y * y = 1 → ∀ Q : Subgroup ↥C, Q ≤ perfectCoreIn K b → IsPGroup 2 Q →
      (∃ x ∈ Q, ∃ y' ∈ Q, x * y' ≠ y' * x) →
      (∀ q ∈ Q, y⁻¹ * (q * y * q⁻¹) ∈ classicalInvolutionOddCore ↥C) →
      ∃ o ∈ classicalInvolutionOddCore ↥C, y = o * ⟨z, hzA⟩ * o⁻¹ :=
    fun y hy hy2 Q hQK hQ2 hQnc hfix => d.r_conj_of_centralizes hzA hy2 hy hQ2 hQK hQnc hfix
  have hsK : conjSub (⟨s, hsC⟩ : ↥C) (perfectCoreIn K b) = perfectCoreIn K b := by
    apply Subgroup.map_injective C.subtype_injective
    have hmap1 : (perfectCoreIn K b).map C.subtype = perfectResidualOf (K ⊓ C) := by
      have := map_conjSub_perfectCore (K := K) (a := b) 1
      rw [conjSub_one, Subgroup.coe_one, conjSub_one] at this
      exact this
    rw [map_conjSub_perfectCore, hmap1]
    exact conjSub_eq_of_mem_normalizer (x_le_normalizer_perfectCore hsN hsC)
  obtain ⟨c, hc⟩ := R10.aft_fusion (Y := ↥C) d.branch.odd h5 hIH hlt hΛ htw hv T hT hZ
    (by obtain ⟨g, hg⟩ := hsz; exact ⟨g, hg⟩) (Subtype.ext hs2) hsK
  exact ⟨(c : G), Subgroup.mem_centralizer_singleton_iff.mp c.2, congrArg Subtype.val hc⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
