module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaK
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator

theorem even_card_pSimple {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hK : GLAPComponent p X K) : Even (Nat.card (PSimple p K)) := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp hK
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.even_card_of_simple_of_not_comm hsimple hna

theorem chevAut_ne_one_of_fgOn {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {J : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (J : Set G))
    (hev : Even (Nat.card (PSimple p J))) (h : FGOn p x J) :
    chevAut p J ⟨x, hxN⟩ ≠ 1 := by
  intro h1
  have hIA : MI.indAut p J x hxN = 1 := by
    rw [OutCyc.indAut_eq_inv_chevAut, h1, inv_one]
  have h' : FieldOn p x J ∨ GFOn p x J := h
  rcases h' with hF | hG
  ·
    obtain ⟨-, lab, hlab, R, hR, I, F, θ, hsimple, hnonab, hP⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists hF.2
    have hP' : (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ∃ f ∈ F, ∃ u ∈ I,
        orderOf f = p ∧ GLAInduces θ (indRel p J x) (u * f * u⁻¹) := hP
    obtain ⟨-, f, hf, u, hu, hord, hind⟩ := hP'
    have heq : MulAut.congr θ (MI.indAut p J x hxN) = u * f * u⁻¹ :=
      ((MI.induces_indRel_iff hxN θ).1 hind).symm
    rw [hIA, map_one] at heq
    have hf1 : f = 1 := by
      calc f = u⁻¹ * (u * f * u⁻¹) * u := by group
        _ = u⁻¹ * 1 * u := by rw [heq]
        _ = 1 := by group
    have hp2' : 2 ≤ p := hp.two_le
    rw [hf1, orderOf_one] at hord
    omega
  ·
    obtain ⟨-, -, hcent⟩ := hG
    have hodd := FP.odd_card_center_pQuot hp hp2 J
    have hcard : centCard2 p J x = card2 p J := by
      rw [FP.centCard2_eq_twoPart_fixNum hxN hodd, hIA, FQ.fixNum_one,
        FP.card2_eq_twoPart_card_pSimple hp hp2 J]
    have hpow : card2 p J ^ p = card2 p J := by
      simpa only [hcard] using hcent
    have hc1 : card2 p J = 1 := by
      by_contra hne
      have hgt : 1 < card2 p J := by
        have hpos : 0 < card2 p J := by
          unfold card2 twoPart
          positivity
        omega
      exact hp.one_lt.ne' ((Nat.pow_eq_self_iff hgt).mp hpow)
    have htwo : twoPart (Nat.card (PSimple p J)) = 1 := by
      rw [← FP.card2_eq_twoPart_card_pSimple hp hp2 J, hc1]
    have h2le : 2 ^ 1 ≤ twoPart (Nat.card (PSimple p J)) :=
      i133_pow_two_le_twoPart (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
        (by simpa using even_iff_two_dvd.mp hev)
    rw [htwo] at h2le
    norm_num at h2le

end CFSG.LocalAnalysis.GLTheoremA

end
