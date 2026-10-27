module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeCongr
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.A5Cycle
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Lift

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_partner {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (x ρ : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1) (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x))
    (hxQ : (x : G) ∉ Qz z) (hρ5 : orderOf ρ = 5) (hρx : ρ * x = x * ρ)
    (hρQ : ∀ q ∈ Qz z, q * (ρ : G) = (ρ : G) * q → q = 1 ∨ q = z)
    (hρsh : IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z)))) :
    ∃ y : ↥(Gx z), (y : G) ^ 2 = 1 ∧ IsShapeTwoTwoTimesA5 ↥(CbarCent z y) ∧
      (y : G) * x = x * y ∧ (y : G) * ρ = ρ * y ∧ (x : G) * y ∉ Qz z := by
  have hx2K : x ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2
  have hbar2 : barOf z x ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hx2K]
    rfl
  have hbar1 : barOf z x ≠ 1 := fun h1 => hxQ ((barOf_eq_one_iff x).mp h1)
  have hbarcomm : barOf z x * barOf z ρ = barOf z ρ * barOf z x := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hρx]
  obtain ⟨sbar, hsρbar, _, hne, hrel2⟩ := gzNo_exists_cycle hρsh hbarcomm hbar2 hbar1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective sbar
  have hQ : Nat.card ↥(CFSG.pCore 2 ↥(Gx z)) = 2 ^ 9 := by
    have hh := (isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z).plus.2.1
    norm_num at hh ⊢
    exact hh
  have hgcomm : (g : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) * (ρ : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z))
      = (ρ : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) * (g : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) := by
    rw [hg]
    exact hsρbar
  obtain ⟨s, hsbarQ, hsρ⟩ := gzNo_exists_lift (CFSG.pCore 2 ↥(Gx z)) hQ hρ5 g hgcomm
  have hsbar : barOf z s = sbar := hsbarQ.trans hg
  have hz2 : z ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, h.orderOf_z]
  have hζ2 : GxSelf z ^ 2 = 1 := by
    apply Subtype.ext
    change (GxSelf z : G) ^ 2 = 1
    exact hz2
  have hζ : ∀ q ∈ CFSG.pCore 2 ↥(Gx z), q * ρ = ρ * q → q = 1 ∨ q = GxSelf z := by
    intro q hq hqc
    have hqQ : (q : G) ∈ Qz z := by
      show (q : G) ∈ (CFSG.pCore 2 ↥(Gx z)).map (Gx z).subtype
      exact Subgroup.mem_map_of_mem (Gx z).subtype hq
    have hqcG : (q : G) * (ρ : G) = (ρ : G) * (q : G) := by
      have := congrArg Subtype.val hqc
      simpa using this
    rcases hρQ (q : G) hqQ hqcG with h1 | hz
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext hz)
  have hζc : ∀ g : ↥(Gx z), g * GxSelf z = GxSelf z * g := by
    intro g
    apply Subtype.ext
    change (g : G) * z = z * (g : G)
    exact ((mem_Gx).mp g.2).symm
  have hrel : ((s * (s * x * s⁻¹) * s⁻¹ : ↥(Gx z)) : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z))
      = ((x * (s * x * s⁻¹) : ↥(Gx z)) : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) := by
    have hL : ((s * (s * x * s⁻¹) * s⁻¹ : ↥(Gx z)) : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z))
        = sbar * (sbar * barOf z x * sbar⁻¹) * sbar⁻¹ := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsbar]
    have hR : ((x * (s * x * s⁻¹) : ↥(Gx z)) : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z))
        = barOf z x * (sbar * barOf z x * sbar⁻¹) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsbar]
    rw [hL, hR, hrel2]
  let y : ↥(Gx z) := s * x * s⁻¹
  have hy_def : y = s * x * s⁻¹ := rfl
  have hy2K : y ^ 2 = 1 := by
    rw [hy_def]
    have h1 : (s * x * s⁻¹) ^ 2 = s * x ^ 2 * s⁻¹ := by rw [conj_pow]
    rw [h1, hx2K]
    simp
  have hy2G : (y : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hy2K
    simpa using this
  have hybar : barOf z y = sbar * barOf z x * sbar⁻¹ := by
    rw [hy_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsbar]
  have hshape : IsShapeTwoTwoTimesA5 ↥(CbarCent z y) := by
    obtain ⟨e⟩ := gzNo_nonempty_centralizer_conj sbar (barOf z x)
    have hcy : CbarCent z y
        = Subgroup.centralizer ({sbar * barOf z x * sbar⁻¹} : Set (Gbar z)) := by
      dsimp only [CbarCent]
      rw [hybar]
    rw [hcy]
    exact IsShapeTwoTwoTimesA5.of_mulEquiv e hsh
  have hxyK : x * y = y * x := by
    rw [hy_def]
    exact gzNo_commute_of_cycle (CFSG.pCore 2 ↥(Gx z)) hζ hζc hζ2 hx2K hρx.symm hsρ hrel
  have hxyG : (y : G) * x = x * y := by
    have := congrArg Subtype.val hxyK
    simpa using this.symm
  have hyρK : y * ρ = ρ * y := by
    rw [hy_def]
    have hsρc : Commute s ρ := hsρ
    have hxρc : Commute x ρ := hρx.symm
    have h1 : Commute (s * x) ρ := hsρc.mul_left hxρc
    have h2 : Commute s⁻¹ ρ := hsρc.inv_left
    exact h1.mul_left h2
  have hyρG : (y : G) * ρ = ρ * y := by
    have := congrArg Subtype.val hyρK
    simpa using this
  have hxybar : barOf z (x * y) = barOf z x * barOf z y := by
    simp only [QuotientGroup.mk_mul]
  have hxybar_ne : barOf z (x * y) ≠ 1 := by
    rw [hxybar, hybar]
    intro h1
    apply hne
    have h2 : sbar * barOf z x * sbar⁻¹ = (barOf z x)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hxinv : (barOf z x)⁻¹ = barOf z x := by
      rw [inv_eq_iff_mul_eq_one]
      simpa [pow_two] using hbar2
    rwa [hxinv] at h2
  have hxyQ : (x : G) * y ∉ Qz z := by
    intro hmem
    exact hxybar_ne ((barOf_eq_one_iff (x * y)).mpr (by simpa using hmem))
  exact ⟨y, hy2G, hshape, hxyG, hyρG, hxyQ⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
