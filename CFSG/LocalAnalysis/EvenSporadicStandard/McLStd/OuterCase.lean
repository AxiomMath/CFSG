module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.InnerCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterCommute
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.SwapHom2
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.McL

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mclOuterSetup
    (h : StdHyp G L) (hL : IsSporadic L .McL) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) : OuterSetup G L t where
  t_sq := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  t_ne := fun h1 => by rw [h1, orderOf_one] at ht2; exact absurd ht2 (by decide)
  t_comm := fun l hl => (mem_centralizer_iff.1 ht l hl).symm
  norm := fun m hm =>
    h.centralizer_le_normalizer ht ht2 (mem_centralizer_singleton_iff.2 hm)
  idx := h.relIndex_dvd_two_mcl hL ht ht2
  centerless := fun z hz hc => by
    have hzc : (⟨z, hz⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [center_eq_bot_of_isSporadic_mcl hL, mem_bot] at hzc
    exact congrArg Subtype.val hzc
  card_L := card_eq_of_isSporadic_mcl hL
  one_class := by
    intro x hx y hy hx2 hy2 hx1 hy1
    obtain ⟨e₀⟩ := hL
    have e : L ≃* NativeSporadic.McL := e₀
    have hord : ∀ w : L, w * w = 1 → w ≠ 1 → orderOf (e w) = 2 := by
      intro w hw2 hw1
      have hsq : (e w) ^ 2 = 1 := by rw [pow_two, ← map_mul, hw2, map_one]
      have hne : e w ≠ 1 := fun h' => hw1 (e.injective (by rw [h', map_one]))
      exact orderOf_eq_prime hsq hne
    let x' : L := ⟨x, hx⟩
    let y' : L := ⟨y, hy⟩
    have hx'2 : x' * x' = 1 := Subtype.ext (by simpa using hx2)
    have hy'2 : y' * y' = 1 := Subtype.ext (by simpa using hy2)
    have hx'1 : x' ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
    have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
    obtain ⟨c, hc⟩ := isConj_iff.1
      (isConj_of_involutions_mcl (hord x' hx'2 hx'1) (hord y' hy'2 hy'1))
    refine ⟨((e.symm c : L) : G), (e.symm c : L).2, ?_⟩
    have hxy : y' = e.symm c * x' * (e.symm c)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← hc]
    simpa using congrArg Subtype.val hxy
  perfect := by
    intro l hl hl2 hl1
    let l' : L := ⟨l, hl⟩
    have hl'2 : orderOf l' = 2 := by
      have : l' * l' = 1 := Subtype.ext (by simpa using hl2)
      exact orderOf_eq_prime (by rw [pow_two]; exact this) fun h1 => hl1 (congrArg Subtype.val h1)
    have hdc := isDoubleCoverOfAlt_inf hl (isDoubleCoverOfAlt_mcl hL hl'2)
    refine ⟨centralizer ({l} : Set G) ⊓ L, inf_le_left,
      ⟨mem_centralizer_singleton_iff.2 rfl, hl⟩, ?_⟩
    exact Subgroup.isPerfect_iff.1 hdc.1.1
  fix_card := by
    intro v hvt hv2 hvN
    have hvM : v ∈ normalizer (L : Set G) :=
      h.centralizer_le_normalizer ht ht2 (mem_centralizer_singleton_iff.2 hvt)
    have e : L ≃* NativeSporadic.McL :=
      (show Nonempty (↥L ≃* NativeSporadic.McL) from hL).some
    let α : MulAut L := L.normalizerMonoidHom ⟨v, hvM⟩
    have hαx : ∀ x : L, ((α x : L) : G) = v * x * v⁻¹ := fun x => rfl
    have hα2 : α * α = 1 := by
      have : (⟨v, hvM⟩ : normalizer (L : Set G)) * ⟨v, hvM⟩ = 1 := Subtype.ext hv2
      calc α * α = L.normalizerMonoidHom ((⟨v, hvM⟩ : normalizer (L : Set G)) * ⟨v, hvM⟩) :=
            (map_mul _ _ _).symm
        _ = 1 := by rw [this, map_one]
    have hα : α ∉ inner L := by
      rintro ⟨l, hl⟩
      have hl' : L.normalizerMonoidHom ⟨v, hvM⟩ = MulAut.conj l := hl.symm
      have hconj := (normalizerMonoidHom_eq_conj_iff hvM l).1 hl'
      have hvs : v ∈ L ⊔ centralizer (L : Set G) :=
        mem_sup_centralizer_iff.2 ⟨l, l.2, hconj⟩
      have : v ∈ centralizer ({t} : Set G) ⊓ (L ⊔ centralizer (L : Set G)) :=
        ⟨mem_centralizer_singleton_iff.2 hvt, hvs⟩
      rw [h.centralizer_inf_sup_centralizer_eq (h.card_sylow_eq_two_mcl hL) ht ht2] at this
      exact hvN this
    have hcard := card_fixSub_outer_mcl e α hα2 hα
    rw [← hcard]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
          rw [mem_fixSub]
          apply Subtype.ext
          rw [hαx]
          have hx := x.2.2
          calc v * x.1 * v⁻¹ = x.1 * v * v⁻¹ := by rw [← hx]
            _ = x.1 := by group⟩
        invFun := fun x => ⟨x.1.1, x.1.2, by
          have h1 := mem_fixSub.1 x.2
          have h2 := congrArg Subtype.val h1
          rw [hαx] at h2
          calc x.1.1 * v = v * x.1.1 * v⁻¹ * v := by rw [h2]
            _ = v * x.1.1 := by group⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }

theorem noSwappedPair_mcl :
    NoSwappedPair .McL := by
  intro G _ _ L h hL t u ht ht2 hu hu2 hsw
  have := h.simple
  have S := mclOuterSetup h hL ht ht2
  have htu : t ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u hu).symm
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu2; exact absurd hu2 (by decide)
  have hu'2 : orderOf (⟨u, hu⟩ : L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hdcB := isDoubleCoverOfAlt_inf hu (isDoubleCoverOfAlt_mcl hL hu'2)
  have hZ : ∀ l ∈ L, l * u = u * l →
      (∀ b ∈ centralizer ({u} : Set G) ⊓ L, l * b = b * l) → l = 1 ∨ l = u := by
    intro l hl hlu hlB
    have hlB' : l ∈ centralizer ({u} : Set G) ⊓ L := ⟨mem_centralizer_singleton_iff.2 hlu, hl⟩
    have huB' : u ∈ centralizer ({u} : Set G) ⊓ L :=
      ⟨mem_centralizer_singleton_iff.2 rfl, hu⟩
    have hlc : (⟨l, hlB'⟩ : ↥(centralizer ({u} : Set G) ⊓ L)) ∈
        center ↥(centralizer ({u} : Set G) ⊓ L) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hlB g.1 g.2).symm
    have huc : (⟨u, huB'⟩ : ↥(centralizer ({u} : Set G) ⊓ L)) ∈
        center ↥(centralizer ({u} : Set G) ⊓ L) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2.1)
    have hu1' : (⟨u, huB'⟩ : ↥(centralizer ({u} : Set G) ⊓ L)) ≠ 1 := fun h1 =>
      hu1 (congrArg Subtype.val h1)
    rcases eq_one_or_eq_of_isDoubleCoverOfAlt hdcB huc hu1' hlc with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  have hD := commute_of_relIndex_dvd_two ht hu hZ S.idx
  have hcore : Open.componentClassificationOddCore ↥(centralizer ({u} : Set G)) = ⊥ :=
    h.oddCore u hu2
  obtain ⟨φ, hφ⟩ := exists_hom_of_swappedPair_corefree ht2 htu hcore hD hsw
  exact false_of_hom_nonzero h.nonabelian S hu hu2' hu1 htu φ hφ

theorem mcl_not_standard_of_container
    (hS : Solomon2AnInput) (hct : ContainerIsDoubleCover .McL)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .McL :=
  mcl_not_standard hS (stdHasIntrinsicAn_mcl_of_residuals noSwappedPair_mcl hct) h

end CFSG.EvenSporadicStandard.McLStd
