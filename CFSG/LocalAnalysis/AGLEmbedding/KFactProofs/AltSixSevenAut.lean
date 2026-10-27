module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
import CFSG.GH74.KGroups.A6
import CFSG.GH74.KGroups.A7
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbedding

namespace AltSixSevenAut

open scoped commutatorElement

theorem not_pow_three_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n = 1440 ∨ n = 5040) :
    ¬ p ^ 3 ∣ n := by
  intro h
  have hle := Nat.le_of_dvd (by omega) h
  have hp17 : p ≤ 17 := by
    by_contra hc
    have h18 : 18 ≤ p := by omega
    have := Nat.pow_le_pow_left h18 3
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem relIndex_inf_centralizer_le {X : Type} [Group X] {L U : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hU : IsPGroup p U) {Q : Type} [Group Q]
    (ψ : ↥U →* MulAut Q) (hker : ∀ u : ↥U, ψ u = 1 → (u : X) ∈ Subgroup.centralizer (L : Set X))
    {n : ℕ} (hn : n = 1440 ∨ n = 5040) (hcard : Nat.card (MulAut Q) = n) :
    (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut Q) := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ∣ Nat.card ψ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le fun u hu => ⟨u.2, hker u hu⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := ψ.range)).1
    (hU.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
  have hk' : p ^ k ∣ n := hcard ▸ hk ▸ Subgroup.card_subgroup_dvd_card ψ.range
  have hk2 : k ≤ 2 := by
    by_contra h
    exact not_pow_three_dvd hp hp2 hn ((pow_dvd_pow p (not_le.1 h)).trans hk')
  rw [hk] at hdvd
  exact (Nat.le_of_dvd (pow_pos hp.pos k) hdvd).trans (Nat.pow_le_pow_right hp.pos hk2)

def quotientCenterAut (G : Type*) [Group G] : MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by ext ⟨x⟩; rfl
  map_mul' φ ψ := by ext ⟨x⟩; rfl

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g : G, ⁅z, g⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz g).symm
  have h2 : ∀ g : G, ⁅g, w⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hw g)
  simp [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj, h1, h2]

theorem mem_centralizer_of_quotientCenterAut_eq_one {X : Type} [Group X] {L : Subgroup X}
    (hL : commutator ↥L = ⊤) {u : X} (hu : u ∈ Subgroup.normalizer (L : Set X))
    (h : quotientCenterAut ↥L (L.normalizerMonoidHom ⟨u, hu⟩) = 1) :
    u ∈ Subgroup.centralizer (L : Set X) := by
  set c := L.normalizerMonoidHom ⟨u, hu⟩ with hc
  have h1 : ∀ l : ↥L, l⁻¹ * c l ∈ Subgroup.center ↥L := fun l =>
    QuotientGroup.eq.1 (DFunLike.congr_fun h (l : ↥L ⧸ Subgroup.center ↥L)).symm
  have h2 : ∀ l₁ l₂ : ↥L, c ⁅l₁, l₂⁆ = ⁅l₁, l₂⁆ := by
    intro l₁ l₂
    obtain ⟨z₁, hz₁, e₁⟩ : ∃ z ∈ Subgroup.center ↥L, c l₁ = l₁ * z :=
      ⟨_, h1 l₁, (mul_inv_cancel_left _ _).symm⟩
    obtain ⟨z₂, hz₂, e₂⟩ : ∃ z ∈ Subgroup.center ↥L, c l₂ = l₂ * z :=
      ⟨_, h1 l₂, (mul_inv_cancel_left _ _).symm⟩
    rw [map_commutatorElement, e₁, e₂]
    exact commutatorElement_mul_central hz₁ hz₂
  have h3 : ∀ l : ↥L, c l = l := by
    have hle : commutator ↥L ≤ MonoidHom.eqLocus (c : ↥L →* ↥L) (MonoidHom.id ↥L) :=
      Subgroup.commutator_le.2 fun a _ b _ => h2 a b
    exact fun l => hle (hL ▸ Subgroup.mem_top l)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h4 : u * l * u⁻¹ = l := congrArg Subtype.val (h3 ⟨l, hl⟩)
  calc l * u = (u * l * u⁻¹) * u := by rw [h4]
    _ = u * l := by group

end AltSixSevenAut

theorem kFactAltSixSevenAut :
    KFactAltSixSevenAut := by
  intro X _ _ L U p hL hLtype hp hp2 hUN hU
  obtain ⟨-, -, hperf, -⟩ := hL
  rcases hLtype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
    refine AltSixSevenAut.relIndex_inf_centralizer_le hp hp2 hU
      ((AltSixSevenAut.quotientCenterAut ↥L).comp
        (L.normalizerMonoidHom.comp (Subgroup.inclusion hUN))) ?_ (Or.inl rfl)
      (CFSG.GH74.KGroups.A6.card_mulAut e')
    exact fun u hu => AltSixSevenAut.mem_centralizer_of_quotientCenterAut_eq_one hperf
      (hUN u.2) hu
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A7.equiv_of_alt e
    refine AltSixSevenAut.relIndex_inf_centralizer_le hp hp2 hU
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hUN)) ?_ (Or.inr rfl)
      (CFSG.GH74.KGroups.A7.card_mulAut e')
    intro u hu
    have hmem : Subgroup.inclusion hUN u ∈ L.normalizerMonoidHom.ker := hu
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact hmem

end CFSG.AGLEmbedding
