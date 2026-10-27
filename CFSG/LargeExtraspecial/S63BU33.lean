module

public import CFSG.LargeExtraspecial.S63BU33Lem
public import CFSG.GH74.KGroups.U33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

@[expose] def U33CentInput : Prop :=
  ∀ (Y : Type) [Group Y], Blueprint.LieModel Y .PSU 3 3 1 →
    ∀ (s : Y), orderOf s = 2 → ∀ N : Subgroup Y, N ≤ centralizer ({s} : Set Y) →
      (∀ c ∈ centralizer ({s} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N → s ∈ N →
        2 ^ 4 ≤ Nat.card N →
          (∀ t ∈ centralizer ({s} : Set Y), t * t = 1 → t ∈ N) ∧
          ∃ q ∈ N, q * q = s ∧ (∀ c ∈ centralizer ({s} : Set Y), q * c = c * q) ∧
            ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n ∈ zpowers q

theorem card_outer_le_two_of_psu33 {Y : Type} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (h : Blueprint.LieModel Y .PSU 3 3 1) : Nat.card (OuterAutomorphisms.Outer Y) ≤ 2 := by
  obtain ⟨e⟩ := GH74.KGroups.U33.equiv_of_lieModel h
  have hA := GH74.KGroups.U33.card_mulAut e
  have hY : Nat.card Y = 6048 := by
    rw [Nat.card_congr e.toEquiv, GH74.KGroups.card_group _ GH74.KGroups.U33.QP_ok,
      GH74.KGroups.U33.QP_valid.2]
  have hI : Nat.card (OuterAutomorphisms.inner Y) = 6048 := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_map, card_map_of_injective hinj, card_top, hY]
  have h1 := card_eq_card_quotient_mul_card_subgroup (OuterAutomorphisms.inner Y)
  rw [hA, hI] at h1
  change 12096 = Nat.card (OuterAutomorphisms.Outer Y) * 6048 at h1
  omega

namespace SmithConf

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}
variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem q_facts (q₁ : ↥(Finn ζ F))
    (hqq : iota hs q₁ * iota hs q₁ = piU ζ (zetaU ζ))
    (hqC : ∀ c ∈ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)),
      iota hs q₁ * c = c * iota hs q₁)
    (hqZ : ∀ n ∈ (iota (F := F) hs).range,
      (∀ m ∈ (iota (F := F) hs).range, n * m = m * n) → n ∈ zpowers (iota hs q₁)) :
    (q₁ : X) * q₁ = ζ ∧
    (∀ m : X, m * ζ = ζ * m → m * q₁ * m⁻¹ = q₁ ∨ m * q₁ * m⁻¹ = (q₁ : X)⁻¹) ∧
    ∀ τ ∈ CorB.conjCent ζ, (q₁ : X) * τ * (q₁ : X)⁻¹ = τ := by
  have hζF : ζ ∈ Finn ζ F := hC.zeta_mem_Finn
  have hιζ : iota (F := F) hs ⟨ζ, hζF⟩ = piU ζ (zetaU ζ) := iota_of_mem_U hs ⟨ζ, hζF⟩ (zetaU ζ).2
  have hs2 : orderOf (piU ζ (zetaU ζ)) = 2 := hC.orderOf_piU hs (IsConj.refl ζ)
  have hss : piU ζ (zetaU ζ) * piU ζ (zetaU ζ) = 1 := by
    rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one _
  have hs1 : piU ζ (zetaU ζ) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hq₁q₁ : (q₁ : X) * q₁ = ζ := by
    have h1 : iota hs (q₁ * q₁) = iota hs ⟨ζ, hζF⟩ := by rw [map_mul, hqq, hιζ]
    exact congrArg Subtype.val (hC.iota_injective hs h1)
  have hq₁c : ∀ h : ↥(Finn ζ F), q₁ * h = h * q₁ := by
    intro h
    have h1 := hqC _ ((hC.iota_range_props hs).1 ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul] at h1
    exact hC.iota_injective hs h1
  refine ⟨hq₁q₁, fun m hm => ?_, fun τ hτ => ?_⟩
  · have hmi : m⁻¹ * ζ = ζ * m⁻¹ := (Commute.inv_left (show Commute m ζ from hm)).eq
    set w : ↥(Finn ζ F) := ⟨_, hC.conj_mem_Finn_of_comm hm q₁.2⟩ with hw
    have hwc : ∀ n ∈ (iota (F := F) hs).range, iota hs w * n = n * iota hs w := by
      rintro _ ⟨h, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h2 := congrArg Subtype.val (hq₁c ⟨_, hC.conj_mem_Finn_of_comm hmi h.2⟩)
      change (q₁ : X) * (m⁻¹ * h * m⁻¹⁻¹) = (m⁻¹ * h * m⁻¹⁻¹) * q₁ at h2
      change m * q₁ * m⁻¹ * h = h * (m * q₁ * m⁻¹)
      calc m * q₁ * m⁻¹ * h = m * ((q₁ : X) * (m⁻¹ * h * m⁻¹⁻¹)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * h * m⁻¹⁻¹) * q₁) * m⁻¹ := by rw [h2]
        _ = h * (m * q₁ * m⁻¹) := by group
    have hwZ := hqZ _ ⟨w, rfl⟩ hwc
    have hww : iota hs w * iota hs w = iota hs q₁ * iota hs q₁ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change m * q₁ * m⁻¹ * (m * q₁ * m⁻¹) = (q₁ : X) * q₁
      rw [show m * q₁ * m⁻¹ * (m * q₁ * m⁻¹) = m * ((q₁ : X) * q₁) * m⁻¹ by group, hq₁q₁, hm,
        mul_inv_cancel_right]
    have h4 : iota hs q₁ * iota hs q₁ * (iota hs q₁ * iota hs q₁) = 1 := by rw [hqq, hss]
    have h2 : iota hs q₁ * iota hs q₁ ≠ 1 := by rw [hqq]; exact hs1
    rcases eq_or_eq_inv_of_mem_zpowers_sq h4 h2 hwZ hww with h1 | h1
    · exact Or.inl (congrArg Subtype.val (hC.iota_injective hs h1))
    · rw [← map_inv] at h1
      exact Or.inr (congrArg Subtype.val (hC.iota_injective hs h1))
  · refine hC.conj_eq_of_conjAut_fix hs hτ.2 ?_
    rw [conjAut_eq_iota hs]
    have hτC : piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩ ∈
        centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hτ.1
    rw [hqC _ hτC, mul_inv_cancel_right]

omit [Finite X] hs in
theorem false_of_q_facts (q₁ : X) (hq₁q₁ : q₁ * q₁ = ζ)
    (hq₁M : ∀ m : X, m * ζ = ζ * m → m * q₁ * m⁻¹ = q₁ ∨ m * q₁ * m⁻¹ = q₁⁻¹)
    (hq₁τ : ∀ τ ∈ CorB.conjCent ζ, q₁ * τ * q₁⁻¹ = τ)
    (hact : ∀ τ ∈ CorB.conjCent ζ, ∃ h ∈ F, h * h = 1 ∧ ∀ f ∈ F, h * f * h⁻¹ = τ * f * τ⁻¹) :
    False := by
  have hζζ : ζ * ζ = 1 := hC.star.mul_self
  obtain ⟨τ, hτc, hτne⟩ := hC.nonIsolated
  obtain ⟨g, hg⟩ := isConj_iff.mp hτc.2
  set τ' := g⁻¹ * ζ * g with hτ'
  set y := g⁻¹ * q₁ * g with hydef
  have hτ'c : τ' ∈ CorB.conjCent ζ := by
    refine ⟨?_, isConj_iff.mpr ⟨g⁻¹, by rw [hτ']; group⟩⟩
    calc τ' * ζ = g⁻¹ * (ζ * τ) * g := by rw [hτ', ← hg]; group
      _ = g⁻¹ * (τ * ζ) * g := by rw [hτc.1]
      _ = ζ * τ' := by rw [hτ', ← hg]; group
  have hτ'ne : τ' ≠ ζ := by
    intro h
    have h' : g⁻¹ * ζ * g = ζ := h
    have h2 : g * ζ * g⁻¹ = ζ := by
      calc g * ζ * g⁻¹ = g * (g⁻¹ * ζ * g) * g⁻¹ := by rw [h']
        _ = ζ := by group
    exact hτne (by rw [← hg]; exact h2)
  have hy : y * ζ = ζ * y := by
    have h1 := hq₁τ τ hτc
    have h2 : q₁ * τ = τ * q₁ := by
      calc q₁ * τ = q₁ * τ * q₁⁻¹ * q₁ := by group
        _ = τ * q₁ := by rw [h1]
    calc y * ζ = g⁻¹ * (q₁ * τ) * g := by rw [hydef, ← hg]; group
      _ = g⁻¹ * (τ * q₁) * g := by rw [h2]
      _ = ζ * y := by rw [hydef, ← hg]; group
  have hyy : y * y = τ' := by
    rw [hydef, hτ', show g⁻¹ * q₁ * g * (g⁻¹ * q₁ * g) = g⁻¹ * (q₁ * q₁) * g by group, hq₁q₁]
  have hτ'F : τ' ∉ F := fun h => hτ'ne (hC.hyp.conj_mem_F τ' h hτ'c.2)
  have hyc : ∀ x ∈ F, x * τ' = τ' * x → y * x = x * y := by
    intro x hx hxτ
    have hgx : (g * x * g⁻¹) * ζ = ζ * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * ζ = g * (x * τ') * g⁻¹ := by rw [hτ']; group
        _ = g * (τ' * x) * g⁻¹ := by rw [hxτ]
        _ = ζ * (g * x * g⁻¹) := by rw [hτ']; group
    have hconj : x * y * x⁻¹ = g⁻¹ * ((g * x * g⁻¹) * q₁ * (g * x * g⁻¹)⁻¹) * g := by
      rw [hydef]; group
    rcases hq₁M _ hgx with h1 | h1
    · rw [h1, ← hydef] at hconj
      calc y * x = x * y * x⁻¹ * x := by rw [hconj]
        _ = x * y := by group
    · exfalso
      rw [h1, show g⁻¹ * q₁⁻¹ * g = y⁻¹ by rw [hydef]; group] at hconj
      have h3 : x * (y * x⁻¹ * y⁻¹) ∈ F :=
        mul_mem hx (hC.hyp.conj_mem y (mem_centralizer_singleton_iff.mpr hy) x⁻¹ (inv_mem hx))
      have h4 : x * (y * x⁻¹ * y⁻¹) = τ'⁻¹ := by
        calc x * (y * x⁻¹ * y⁻¹) = (x * y * x⁻¹) * y⁻¹ := by group
          _ = (y * y)⁻¹ := by rw [hconj]; group
          _ = τ'⁻¹ := by rw [hyy]
      rw [h4] at h3
      exact hτ'F (by simpa using inv_mem h3)
  obtain ⟨u, huF, -, huc, huu⟩ := hC.exists_sq_eq_zeta hτ'c hτ'ne hy hyc hyy
  obtain ⟨e, heF, hee, hconj⟩ := hact τ' hτ'c
  have hcomm : ∀ x ∈ F, x * e = e * x → u * x = x * u := by
    intro x hx hxe
    refine huc x hx ?_
    have h1 : τ' * x * τ'⁻¹ = x := by rw [← hconj x hx, ← hxe, mul_inv_cancel_right]
    calc x * τ' = τ' * x * τ'⁻¹ * τ' := by rw [h1]
      _ = τ' * x := by group
  have hez : e * ζ = ζ * e := hC.comm_zeta heF
  have hne : ζ ≠ 1 := hC.zeta_ne_one
  rcases hC.eq_of_comm_centralizer heF huF hcomm with h | h | h | h
  · rw [h, one_mul] at huu
    exact hne huu.symm
  · rw [h, hζζ] at huu
    exact hne huu.symm
  · rw [h, hee] at huu
    exact hne huu.symm
  · have h1 : e * ζ * (e * ζ) = 1 := by
      calc e * ζ * (e * ζ) = e * (ζ * e) * ζ := by group
        _ = e * (e * ζ) * ζ := by rw [← hez]
        _ = (e * e) * (ζ * ζ) := by group
        _ = 1 := by rw [hee, hζζ, one_mul]
    rw [h, h1] at huu
    exact hne huu.symm

end SmithConf

theorem smith59Input_of (hR : U33CentInput) : Smith59Input := by
  intro X _ _ ζ F hC hU
  have hs : IsSimpleGroup (UZ ζ) := Timmesfeld.isSimpleGroup_of_lieModel hU
  have hF2 : Nat.card F ≤ 2 * Nat.card (Finn ζ F) :=
    hC.card_le_mul_card_Finn (k := 2) fun H _ =>
      (card_le_card_group H).trans (card_outer_le_two_of_psu33 (conj_injective hs) hU)
  obtain ⟨hNC, hNn, hN2, hsN, hcardN⟩ := hC.iota_range_props hs
  have hwidth := hC.hyp.width
  have h16 : 2 ^ 4 ≤ Nat.card (SmithConf.iota (F := F) hs).range := by
    rw [hcardN]
    omega
  obtain ⟨hinvN, _, ⟨q₁, rfl⟩, hqq, hqC, hqZ⟩ :=
    hR (UZ ζ) hU _ (hC.orderOf_piU hs (IsConj.refl ζ)) _ hNC hNn hN2 hsN h16
  obtain ⟨hq₁q₁, hq₁M, hq₁τ⟩ := hC.q_facts hs q₁ hqq hqC hqZ
  refine hC.false_of_q_facts q₁ hq₁q₁ hq₁M hq₁τ fun τ hτ => ?_
  refine hC.exists_involution_conj_eq hs hτ (hinvN _ ?_ ?_)
  · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hτ.1
  · rw [← pow_two, ← hC.orderOf_piU hs hτ.2]
    exact pow_orderOf_eq_one _

end S63

end CFSG.LargeExtraspecial
