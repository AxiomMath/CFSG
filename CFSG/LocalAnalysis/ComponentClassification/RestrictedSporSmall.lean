module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSporadic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB
open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsSmallOrder (N : ℕ) : Prop :=
  N = 2520 ∨ N = 20160 ∨ ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ 2 * N = q * (q ^ 2 - 1)

theorem two_mul_ordA_one {q : ℕ} (hq : Odd q) : 2 * Open.ordA 1 q = q * (q ^ 2 - 1) := by
  have hg : Nat.gcd (1 + 1) (q - 1) = 2 := by
    obtain ⟨k, rfl⟩ := hq
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have hev : 2 ∣ q * (q ^ 2 - 1) :=
    (even_iff_two_dvd.1 (Nat.Odd.sub_odd hq.pow odd_one)).mul_left _
  unfold Open.ordA
  rw [hg, show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  exact Nat.mul_div_cancel' hev

theorem isSmallOrder_of_smallCentralQuotient {Y : Type} [Group Y] (h : SmallCentralQuotient Y) :
    IsSmallOrder (Nat.card (Y ⧸ center Y)) := by
  rcases h with ⟨p, f, hp, hp2, -, h5, hm⟩ | ⟨⟨e⟩⟩ | h34
  · refine Or.inr (Or.inr ⟨p ^ f, (hp.odd_of_ne_two hp2).pow, h5, ?_⟩)
    rw [card_of_lieModel_psl_two hp2 hm]
    exact two_mul_ordA_one (hp.odd_of_ne_two hp2).pow
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  · exact Or.inr (Or.inl (card_of_lieModel_L34 h34))

theorem three_dvd_of_isSmallOrder {N : ℕ} (h : IsSmallOrder N) : 3 ∣ N := by
  rcases h with rfl | rfl | ⟨q, -, -, hq⟩
  · norm_num
  · norm_num
  · have h3 : 3 ∣ q * (q ^ 2 - 1) := by
      have hmod : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
      rcases hmod with h | h | h
      · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
      · refine Dvd.dvd.mul_left ?_ _
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.sub_mod_eq_zero_of_mod_eq]
        rw [pow_two, Nat.mul_mod, h]
      · refine Dvd.dvd.mul_left ?_ _
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.sub_mod_eq_zero_of_mod_eq]
        rw [pow_two, Nat.mul_mod, h]
    rw [← hq] at h3
    exact (Nat.Coprime.dvd_mul_left (by norm_num)).1 h3

theorem cubic_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem not_isSmallOrder_of_between {N q₀ : ℕ} (h1 : q₀ * (q₀ ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (q₀ + 1) * ((q₀ + 1) ^ 2 - 1)) (h3 : N ≠ 2520) (h4 : N ≠ 20160) :
    ¬ IsSmallOrder N := by
  rintro (rfl | rfl | ⟨q, -, -, hq⟩)
  · exact h3 rfl
  · exact h4 rfl
  · rcases le_or_gt q q₀ with hle | hlt
    · have := cubic_mono hle
      omega
    · have hle : q₀ + 1 ≤ q := hlt
      have := cubic_mono hle
      omega

theorem not_isSmallOrder_dvd {c q₁ : ℕ} (hc : 0 < c) (hq₁ : 2 * c < q₁ * (q₁ ^ 2 - 1))
    (hsmall : ∀ q < q₁, q % 2 = 1 → 5 ≤ q → c % (q * (q ^ 2 - 1) / 2) ≠ 0)
    (h2520 : ¬ 2520 ∣ c) (h20160 : ¬ 20160 ∣ c) : ∀ N, IsSmallOrder N → ¬ N ∣ c := by
  rintro N (rfl | rfl | ⟨q, hodd, h5, hq⟩) hN
  · exact h2520 hN
  · exact h20160 hN
  · rcases lt_or_ge q q₁ with hlt | hge
    · have hN' : N = q * (q ^ 2 - 1) / 2 := by omega
      exact hsmall q hlt (Nat.odd_iff.1 hodd) h5 (hN' ▸ Nat.mod_eq_zero_of_dvd hN)
    · have := cubic_mono hge
      have := Nat.le_of_dvd hc hN
      omega

theorem not_small_of_not_three {Y : Type} [Group Y] (h : ¬ 3 ∣ Nat.card Y) :
    ¬ SmallCentralQuotient Y := fun hs =>
  h ((three_dvd_of_isSmallOrder (isSmallOrder_of_smallCentralQuotient hs)).trans
    (Subgroup.card_quotient_dvd_card _))

theorem not_small_of_card_quotient {Y : Type} [Group Y]
    (h : ¬ IsSmallOrder (Nat.card (Y ⧸ center Y))) : ¬ SmallCentralQuotient Y := fun hs =>
  h (isSmallOrder_of_smallCentralQuotient hs)

theorem not_small_of_card_dvd {Y : Type} [Group Y] {c : ℕ}
    (hc : ∀ N, IsSmallOrder N → ¬ N ∣ c) (h : Nat.card Y ∣ c) : ¬ SmallCentralQuotient Y :=
  fun hs => hc _ (isSmallOrder_of_smallCentralQuotient hs)
    ((Subgroup.card_quotient_dvd_card _).trans h)

theorem isoInvariant_not_small : IsoInvariant fun Y _ => ¬ SmallCentralQuotient Y :=
  fun _ _ _ _ e h hs => h (smallCentralQuotient_of_mulEquiv e.symm hs)

theorem map_fixSub_conjNormal {A : Type*} [Group A] (W : Subgroup A) [W.Normal] (a : A) :
    (fixSub (MulAut.conjNormal a : MulAut W)).map W.subtype = W ⊓ centralizer ({a} : Set A) := by
  ext x
  simp only [mem_map, mem_fixSub, coe_subtype, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have := congrArg Subtype.val hy
    simp only [MulAut.conjNormal_apply] at this
    calc (y : A) * a = a * y * a⁻¹ * a := by rw [this]
      _ = a * y := by group
  · rintro ⟨hx, hxa⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_, rfl⟩
    simp only [MulAut.conjNormal_apply]
    rw [← hxa]
    group

theorem exists_isComponent_fixSub_of_le {A : Type*} [Group A] {W L : Subgroup A} [W.Normal]
    {a : A} (hLW : L ≤ W) (hL : Assembly.IsComponentOf L (centralizer ({a} : Set A))) :
    ∃ B : Subgroup (fixSub (MulAut.conjNormal a : MulAut W)), IsComponent B ∧
      Nonempty (B ≃* L) := by
  set X := fixSub (MulAut.conjNormal a : MulAut W) with hX
  have hLX : Assembly.IsComponentOf L (W ⊓ centralizer ({a} : Set A)) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hLX' : Assembly.IsComponentOf ((L.subgroupOf W).map W.subtype) (X.map W.subtype) := by
    rw [map_subgroupOf_eq_of_le hLW, hX, map_fixSub_conjNormal]
    exact hLX
  have h1 := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff W.subtype_injective).1 hLX'
  refine ⟨(L.subgroupOf W).subgroupOf X,
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h1.1).1 h1, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe h1.1).trans (subgroupOfEquivOfLe hLW)

theorem conjNormal_not_mem_inner {A : Type*} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : a ∉ W) :
    (MulAut.conjNormal a : MulAut W) ∉ inner W := by
  rintro ⟨w, hw⟩
  apply ha
  have h : (w : A)⁻¹ * a ∈ centralizer (W : Set A) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut W => ((φ ⟨x, hx⟩ : W) : A)) hw
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc x * ((w : A)⁻¹ * a) = (w : A)⁻¹ * ((w : A) * x * (w : A)⁻¹) * a := by group
      _ = (w : A)⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
      _ = (w : A)⁻¹ * a * x := by group
  rw [hCW, mem_bot, inv_mul_eq_one] at h
  rw [← h]
  exact w.2

theorem conjNormal_mul_self {A : Type*} [Group A] {W : Subgroup A} [W.Normal] {a : A}
    (ha : orderOf a = 2) :
    (MulAut.conjNormal a : MulAut W) * MulAut.conjNormal a = 1 := by
  rw [← map_mul, ← sq, ← ha, pow_orderOf_eq_one, map_one]

theorem sporadicCase_of_comps {s : TauCeti.SporadicName}
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (fixSub α) fun Y _ => ¬ SmallCentralQuotient Y) :
    SporadicCase s := by
  intro A _ _ W _ hWs hWnab hCW hcat hsW a ha L hLW hne hL hstd hs
  exfalso
  have hsmall := smallCentralQuotient_of_smallSource hs
  by_cases haW : a ∈ W
  · obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_centralizer_of_mem haW hLW hL
    have ha' : orderOf (⟨a, haW⟩ : W) = 2 := by rw [Subgroup.orderOf_mk, ha]
    exact hin W hsW _ ha' B hB (smallCentralQuotient_of_mulEquiv eB hsmall)
  · obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_fixSub_of_le (a := a) hLW hL
    exact hout W hWs hWnab hsW _ (conjNormal_mul_self ha) (conjNormal_not_mem_inner hCW haW) B hB
      (smallCentralQuotient_of_mulEquiv eB hsmall)

theorem outer_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ α : MulAut (NativeSporadic.Carrier s), α ∈ inner (NativeSporadic.Carrier s))
    (G : Type) [Group G] [Finite G] (_ : IsSimpleGroup G) (_ : ∃ x y : G, x * y ≠ y * x)
    (hG : Nonempty (G ≃* NativeSporadic.Carrier s)) (α : MulAut G) (_ : α * α = 1)
    (hα : α ∉ inner G) :
    CompsSatisfy (fixSub α) fun Y _ => ¬ SmallCentralQuotient Y := by
  obtain ⟨e⟩ := hG
  exact absurd (hinner (transportAut e α)) (transportAut_not_mem_inner e hα)

end CFSG.ComponentClassification.RestrictedStd.Spor
