module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem card_mulAut_le
    {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsHSCover H E) : Nat.card (MulAut E) ≤ 88704000 := by
  haveI : Finite H := h.finite
  haveI : Group.IsPerfect E := h.perfect
  rw [← TwoHS.card_mulAut_of_isSporadic_hs h.quotient]
  exact Nat.card_le_card_of_injective _
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective E)

private theorem card_centralizer_le_two {H : Type} [Group H]
    {E : Subgroup H} (h : TwoHS.IsHSCover H E) :
    Nat.card (centralizer (E : Set H)) ≤ 2 := by
  haveI : Finite H := h.finite
  rw [← h.card_center]
  refine Nat.card_le_card_of_injective
    (fun x : centralizer (E : Set H) => (⟨⟨x, h.centralizer_le x.2⟩, ?_⟩ : center E)) ?_
  · rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.1 x.2 y y.2)
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z : center E => ((z : E) : H)) hxy)

private theorem card_eq_of_isHSCover {H : Type} [Group H]
    {E : Subgroup H} (h : TwoHS.IsHSCover H E) : Nat.card E = 88704000 := by
  obtain ⟨e⟩ := h.quotient
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
  have hHS : Nat.card (Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  rw [Nat.card_congr e.toEquiv, hHS, h.card_center] at h4
  omega

theorem index_range_conj_le_two
    {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) :
    (MulAut.conj : H →* MulAut H).range.index ≤ 2 := by
  haveI : Finite H := h.toIsHSCover.finite
  have hEeq : E = _root_.commutator H := by
    apply le_antisymm
    · have hperf : ⁅E, E⁆ = E := (Subgroup.isPerfect_iff (H := E)).mp h.toIsHSCover.perfect
      calc E = ⁅E, E⁆ := hperf.symm
        _ ≤ _root_.commutator H := Subgroup.commutator_mono le_top le_top
    · haveI : E.Normal := h.toIsHSCover.normal
      have hcard : Nat.card (H ⧸ E) = 2 := by
        rw [← Subgroup.index_eq_card]
        exact h.index_eq_two
      haveI : IsCyclic (H ⧸ E) := isCyclic_of_prime_card (p := 2) hcard
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  haveI : E.Characteristic := hEeq.symm ▸ inferInstance
  let res : MulAut H →* MulAut E := MulAut.characteristic E
  have hker : Nat.card res.ker ≤ 2 := by
    obtain ⟨v, hv, _hv2⟩ := h.exists_outer_involution
    have hfix : ∀ β : res.ker, ∀ y : H, y ∈ E → (β : MulAut H) y = y := by
      intro β y hy
      have hβ : res (β : MulAut H) = 1 := MonoidHom.mem_ker.mp β.2
      have h1 : (MulAut.characteristic E) (β : MulAut H) ⟨y, hy⟩ = ⟨y, hy⟩ := by
        change res (β : MulAut H) ⟨y, hy⟩ = ⟨y, hy⟩
        rw [hβ, MulAut.one_apply]
      have h2 := congrArg (fun z : E => (z : H)) h1
      simpa [MulAut.characteristic_apply_apply_coe] using h2
    refine le_trans ?_ (card_centralizer_le_two h.toIsHSCover)
    refine Nat.card_le_card_of_injective
      (fun β : res.ker => (⟨v⁻¹ * ((β : MulAut H) v), ?_⟩ : centralizer (E : Set H))) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hconj : v * e * v⁻¹ ∈ E := Subgroup.Normal.conj_mem h.toIsHSCover.normal e he v
      have hβv : (β : MulAut H) (v * e * v⁻¹) = v * e * v⁻¹ := hfix β _ hconj
      have hβe : (β : MulAut H) e = e := hfix β e he
      have h3 : (β : MulAut H) v * e * ((β : MulAut H) v)⁻¹ = v * e * v⁻¹ := by
        rw [← hβv, map_mul, map_mul, map_inv, hβe]
      have h5 : (β : MulAut H) v * e = v * e * v⁻¹ * (β : MulAut H) v := by
        rw [← h3]; group
      have h4 : (v⁻¹ * (β : MulAut H) v) * e = e * (v⁻¹ * (β : MulAut H) v) := by
        calc (v⁻¹ * (β : MulAut H) v) * e = v⁻¹ * ((β : MulAut H) v * e) := by group
          _ = v⁻¹ * (v * e * v⁻¹ * (β : MulAut H) v) := by rw [h5]
          _ = e * (v⁻¹ * (β : MulAut H) v) := by group
      exact h4.symm
    · intro β γ hβγ
      have hv_eq : (β : MulAut H) v = (γ : MulAut H) v :=
        mul_left_cancel (congrArg (fun z : centralizer (E : Set H) => (z : H)) hβγ)
      apply Subtype.ext
      ext x
      by_cases hx : x ∈ E
      · rw [hfix β x hx, hfix γ x hx]
      · have hxv : x * v⁻¹ ∈ E :=
          TwoHS.mul_inv_mem_of_index_eq_two h.index_eq_two hx hv
        have keyβ : (β : MulAut H) x = (x * v⁻¹) * (β : MulAut H) v := by
          calc (β : MulAut H) x = (β : MulAut H) ((x * v⁻¹) * v) := by
                rw [show x * v⁻¹ * v = x from by group]
            _ = (β : MulAut H) (x * v⁻¹) * (β : MulAut H) v := map_mul _ _ _
            _ = (x * v⁻¹) * (β : MulAut H) v := by rw [hfix β (x * v⁻¹) hxv]
        have keyγ : (γ : MulAut H) x = (x * v⁻¹) * (γ : MulAut H) v := by
          calc (γ : MulAut H) x = (γ : MulAut H) ((x * v⁻¹) * v) := by
                rw [show x * v⁻¹ * v = x from by group]
            _ = (γ : MulAut H) (x * v⁻¹) * (γ : MulAut H) v := map_mul _ _ _
            _ = (x * v⁻¹) * (γ : MulAut H) v := by rw [hfix γ (x * v⁻¹) hxv]
        rw [keyβ, keyγ, hv_eq]
  have hAutH : Nat.card (MulAut H) ≤ 2 * 88704000 := by
    have hcount := Subgroup.card_ker_mul_card_range res
    have hrange : Nat.card res.range ≤ Nat.card (MulAut E) :=
      Nat.card_le_card_of_injective (fun x : res.range => (x : MulAut E))
        (fun _ _ hxy => Subtype.ext hxy)
    calc Nat.card (MulAut H) = Nat.card res.ker * Nat.card res.range := hcount.symm
      _ ≤ 2 * Nat.card (MulAut E) := Nat.mul_le_mul hker hrange
      _ ≤ 2 * 88704000 := Nat.mul_le_mul_left 2 (card_mulAut_le h.toIsHSCover)
  have hH : Nat.card H = 177408000 := by
    have h5 := Subgroup.card_mul_index E
    rw [card_eq_of_isHSCover h.toIsHSCover, h.index_eq_two] at h5
    omega
  let R : Subgroup (MulAut H) := (MulAut.conj : H →* MulAut H).range
  change R.index ≤ 2
  have hRcard : 88704000 ≤ Nat.card R := by
    have hker_conj : (MulAut.conj : H →* MulAut H).ker = center H := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro hg x
        have hx : g * x * g⁻¹ = x := by
          have := congrArg (fun α : MulAut H => α x) hg
          simpa [MulAut.conj_apply, MulAut.one_apply] using this
        calc x * g = (g * x * g⁻¹) * g := by rw [hx]
          _ = g * x := by group
      · intro hg
        ext x
        rw [MulAut.conj_apply, MulAut.one_apply]
        calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hg x]
          _ = x := by group
    have hcount := Subgroup.card_ker_mul_card_range (MulAut.conj : H →* MulAut H)
    rw [hker_conj, hH] at hcount
    have hcenter_le : Nat.card (center H) ≤ 2 := by
      have hle : center H ≤ centralizer (E : Set H) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro e _
        exact Subgroup.mem_center_iff.mp hz e
      exact le_trans
        (Nat.card_le_card_of_injective
          (fun z : center H => (⟨(z : H), hle z.2⟩ : centralizer (E : Set H)))
          (fun a b hab =>
            Subtype.ext (congrArg (fun z : centralizer (E : Set H) => (z : H)) hab)))
        (card_centralizer_le_two h.toIsHSCover)
    have h1 : Nat.card (center H) * Nat.card R ≤ 2 * Nat.card R :=
      Nat.mul_le_mul_right _ hcenter_le
    rw [hcount] at h1
    omega
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hfinal := Subgroup.card_mul_index R
  have hle : Nat.card R * R.index ≤ Nat.card R * 2 := by
    rw [hfinal]
    calc Nat.card (MulAut H) ≤ 2 * 88704000 := hAutH
      _ ≤ 2 * Nat.card R := Nat.mul_le_mul_left 2 hRcard
      _ = Nat.card R * 2 := by ring
  exact Nat.le_of_mul_le_mul_left hle hRpos

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
