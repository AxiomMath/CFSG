module

public import CFSG.Goldschmidt75.Sig3W
public import CFSG.Goldschmidt75.Sec27
public import CFSG.Goldschmidt75.Equivariance

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

theorem conjSub_zpowers (g b : G) : conjSub g (zpowers b) = zpowers (g⁻¹ * b * g) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  congr 1
  simp

theorem NSet_conjSub [Finite G] (g : G) {B X : Subgroup G} (hX : X ∈ NSet B) :
    conjSub g X ∈ NSet (conjSub g B) := by
  obtain ⟨hXN, hXodd, hXC⟩ := hX
  refine ⟨?_, ?_, fun t ht ht2 => ?_⟩
  · rw [normalizer_conjSub]
    exact conjSub_mono hXN
  · unfold conjSub
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  · rw [mem_conjSub] at ht
    have h2 : orderOf (g * t * g⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ht2
    have h1 := conjSub_mono (g := g) (hXC _ ht h2)
    have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rwa [conjSub_inf, conjSub_centralizer_singleton, e, oddCent, conjSub_oddCoreOf,
      conjSub_centralizer_singleton, e] at h1

variable [Finite G]

theorem exists_central_involution_of_isPGroup {S : Subgroup G} (hS : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) : ∃ z ∈ S, orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS1
  have hZ : Nontrivial (center S) := hS.center_nontrivial
  have hZp : IsPGroup 2 (center S) := hS.to_subgroup _
  obtain ⟨k, hk, hcard⟩ := hZp.nontrivial_iff_card.mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  refine ⟨((z : S) : G), (z : S).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  · exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨s, hs⟩)

theorem exists_isKleinFour_mem {S : Subgroup G} (hS : IsPGroup 2 S)
    (hm : ∃ V ≤ S, IsKleinFour V) {b : G} (hb : b ∈ S) (hb2 : orderOf b = 2) :
    ∃ V ≤ S, IsKleinFour V ∧ b ∈ V := by
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  have hS1 : S ≠ ⊥ := fun h => hb1 (by rw [h] at hb; exact mem_bot.mp hb)
  obtain ⟨z, hzS, hz2, hzc⟩ := exists_central_involution_of_isPGroup hS hS1
  by_cases hbz : b = z
  · obtain ⟨U, hUS, hU⟩ := hm
    obtain ⟨u, huU, hu1, hub⟩ := exists_mem_ne_of_isKleinFour hU b
    refine ⟨zpowers b ⊔ zpowers u, sup_le (zpowers_le.mpr hb) (zpowers_le.mpr (hUS huU)),
      isKleinFour_sup hb2 (orderOf_eq_two_of_isKleinFour hU huU hu1) (Ne.symm hub) ?_,
      mem_sup_left (mem_zpowers b)⟩
    rw [hbz]
    exact (hzc u (hUS huU)).symm
  · exact ⟨zpowers b ⊔ zpowers z, sup_le (zpowers_le.mpr hb) (zpowers_le.mpr hzS),
      isKleinFour_sup hb2 hz2 hbz (hzc b hb), mem_sup_left (mem_zpowers b)⟩

variable {S₁ S₂ : Subgroup G}

theorem wE_eq_of_mem_left {V₁ V₁' V₂ : Subgroup G} (hp : FourPair S₁ S₂ V₁ V₂)
    (hp' : FourPair S₁ S₂ V₁' V₂) (hsep : CoreSep S₁ S₂) {b : G} (hb : b ∈ V₁) (hb' : b ∈ V₁')
    (hb1 : b ≠ 1) : wE V₁ V₂ = wE V₁' V₂ := by
  obtain ⟨b₂, hb₂, hb₂1, -⟩ := exists_mem_ne_of_isKleinFour hp.four_right 1
  have hB : zpowers b ⊔ zpowers b₂ ≤ V₁ ⊔ V₂ :=
    sup_le_sup (zpowers_le.mpr hb) (zpowers_le.mpr hb₂)
  have hB' : zpowers b ⊔ zpowers b₂ ≤ V₁' ⊔ V₂ :=
    sup_le_sup (zpowers_le.mpr hb') (zpowers_le.mpr hb₂)
  exact le_antisymm (le_wE_of_mem_NSet hp' hsep hb' hb1 hb₂ hb₂1 (wE_mem_NSet hp hsep hB))
    (le_wE_of_mem_NSet hp hsep hb hb1 hb₂ hb₂1 (wE_mem_NSet hp' hsep hB'))

theorem wE_eq_of_mem_right {V₁ V₂ V₂' : Subgroup G} (hp : FourPair S₁ S₂ V₁ V₂)
    (hp' : FourPair S₁ S₂ V₁ V₂') (hsep : CoreSep S₁ S₂) {b : G} (hb : b ∈ V₂) (hb' : b ∈ V₂')
    (hb1 : b ≠ 1) : wE V₁ V₂ = wE V₁ V₂' := by
  rw [← wE_comm V₁ V₂, ← wE_comm V₁ V₂']
  exact wE_eq_of_mem_left hp.symm hp'.symm (coreSep_symm hsep) hb hb' hb1

theorem oddCent_le_thetaOne {V : Subgroup G} {t : G} (hV : IsPGroup 2 V) (htV : t ∈ V)
    (hVt : V ≤ centralizer ({t} : Set G)) : oddCent t ≤ thetaOne V t :=
  (le_commutator_sup_inf hV (hVt.trans (centralizer_le_normalizer_oddCent t))
    (Balance.odd_card_oddCoreOf _)).trans
    (sup_le_sup_left (le_inf (oddCent_inf_le_oddCentSub htV) inf_le_left) _)

theorem commutator_oddCent_le_theta {V₁ V₂ : Subgroup G} (hp : FourPair S₁ S₂ V₁ V₂) {t₁ t₂ : G}
    (ht₁ : t₁ ∈ V₁) (ht₂ : t₂ ∈ V₂) : ⁅oddCent t₁, zpowers t₂⁆ ≤ theta V₁ V₂ t₁ := by
  have hE := hp.le_centralizer_of_mem (mem_sup_left ht₁)
  refine le_inf ?_ ((commutator_mono le_rfl (zpowers_le.mpr ht₂)).trans le_sup_left)
  exact (commutator_oddCent_le ((zpowers_le.mpr (mem_sup_right ht₂)).trans hE)).trans
    (oddCent_le_thetaOne hp.isPGroup_left ht₁ (le_sup_left.trans hE))

end CFSG.Goldschmidt75
