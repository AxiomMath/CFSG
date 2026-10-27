module

public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBCore
public import CFSG.GH74.Generic.BProg.B2.WeakSigGen4

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup WeakSigGen

namespace WeakSigCaseB

theorem center_trivial_of_simple {J : Type} [Group J] (hs : IsSimpleGroup J) (hq : IsQuasisimple J) :
    ∀ z : J, (∀ y : J, y * z = z * y) → z = 1 := by
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun y => hz y
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hc : a * b = b * a := by
      have : b ∈ Subgroup.center J := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.mp this a)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

theorem two_dvd_natCard_of_nc2 {J : Type} [Group J] (hnc2 : NC2 J) : 2 ∣ Nat.card J := by
  obtain ⟨x, ⟨n, hn⟩, y, hy⟩ := hnc2
  have hx1 : x ≠ 1 := fun hx => hy (by rw [hx]; simp)
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using ha))
  have h2 : 2 ∣ orderOf x := ha ▸ dvd_pow_self 2 ha0
  exact h2.trans (orderOf_dvd_natCard x)

theorem noncentral_two_elt_of_nc2 {Y J : Type} [Group Y] [Group J] (L : Subgroup Y) (e : L ≃* J)
    (hnc2 : NC2 J) : ∃ c ∈ L, (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ ∃ y ∈ L, y * c ≠ c * y := by
  obtain ⟨x, ⟨n, hn⟩, y, hy⟩ := hnc2
  refine ⟨(e.symm x : Y), (e.symm x).2, ⟨n, ?_⟩, (e.symm y : Y), (e.symm y).2, fun hcomm => hy ?_⟩
  · have := congrArg (fun z : J => ((e.symm z : L) : Y)) hn
    simpa [map_pow] using this
  · apply e.symm.injective
    apply Subtype.ext
    simpa using hcomm

theorem exists_data_of_locE3 {Y J : Type} [Group Y] [Finite Y] [Group J] (L : Subgroup Y)
    (e : L ≃* J) {D₀ : Subgroup Y} (hD₀ : CFSG.IsElementaryAbelian 2 ↥D₀)
    (hr : pRank 2 ↥D₀ = 2 ∨ pRank 2 ↥D₀ = 3) (hDL : D₀ ≤ normalizer (L : Set Y))
    (hE3 : ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → LocE3 α) :
    ∃ E₁ : Subgroup Y, E₁ ≤ D₀ ∧ pRank 2 ↥D₀ - 1 ≤ pRank 2 ↥E₁ ∧
      ∃ c ∈ L, c ∈ centralizer (E₁ : Set Y) ∧ (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧
        ∃ y ∈ L, y * c ≠ c * y := by
  set α : ↥D₀ →* MulAut J := (actOn L e).comp (Subgroup.inclusion hDL) with hα
  obtain ⟨E, hE, x, hx, ⟨n, hn⟩, y, hy⟩ := hE3 ↥D₀ α ⟨hD₀, hr⟩
  refine ⟨E.map D₀.subtype, Subgroup.map_subtype_le E, ?_, (e.symm x : Y), (e.symm x).2, ?_,
    ⟨n, ?_⟩, (e.symm y : Y), (e.symm y).2, fun hcomm => hy ?_⟩
  · rw [← pRank_comap_subtype hD₀ (Subgroup.map_subtype_le E),
      Subgroup.comap_map_eq_self_of_injective D₀.subtype_injective E]
    exact hE
  · rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hmem : α d ∈ E.map α := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    have h1 : α d x = x := hx _ hmem
    have h2 := coe_symm_actOn L e (Subgroup.inclusion hDL d) x
    have h3 : α d x = actOn L e (Subgroup.inclusion hDL d) x := rfl
    rw [← h3, h1] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2.symm
  · have := congrArg (fun z : J => ((e.symm z : L) : Y)) hn
    simpa [map_pow] using this
  · apply e.symm.injective
    apply Subtype.ext
    simpa using hcomm

end WeakSigCaseB

open WeakSigCaseB in
theorem weakSig2TwoG4_of_weakSig2D4 {J : Type} [Group J] (hs : IsSimpleGroup J)
    (hq : IsQuasisimple J) (hnc2 : NC2 J)
    (hE3 : ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → LocE3 α)
    (h : WeakSig2D4 J) : WeakSig2TwoG4 J := by
  intro Y _ _ _ hY L hL hLJ D W hD hk hW hDW hC hO
  obtain ⟨e⟩ := hLJ
  by_cases hDL : D ≤ normalizer (L : Set Y)
  · exact h Y hY L hL ⟨e⟩ D W hD hk hW hDL hDW (fun E hE hr x _ hx => hC E hE hr hx)
  · obtain ⟨s, hsD, hsN⟩ : ∃ s ∈ D, s ∉ normalizer (L : Set Y) := by
      by_contra hcon
      push Not at hcon
      exact hDL hcon
    obtain ⟨L', hL'⟩ := hO
    have hss : s * s = 1 := (forall_of_isElementaryAbelian hD).2 s hsD
    have hLs' : conjugate L s = L' :=
      (hL' s hsD).resolve_left fun h' => hsN (conjugate_eq_self_iff.mp h')
    have hdich : ∀ d ∈ D, d ∈ normalizer (L : Set Y) ∨ d * s ∈ normalizer (L : Set Y) := by
      intro d hd
      by_cases hdN : d ∈ normalizer (L : Set Y)
      · exact Or.inl hdN
      · right
        have h1 : conjugate L d = L' :=
          (hL' d hd).resolve_left fun h' => hdN (conjugate_eq_self_iff.mp h')
        rw [← conjugate_eq_self_iff, ← conjugate_conjugate, h1, ← hLs', conjugate_conjugate, hss,
          conjugate_one]
    have hJcen := center_trivial_of_simple hs hq
    have hcen : ∀ l ∈ L, (∀ y ∈ L, y * l = l * y) → l = 1 := by
      intro l hl hcl
      have h1 : e ⟨l, hl⟩ = 1 := by
        apply hJcen
        intro y
        obtain ⟨y', rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (hcl y'.1 y'.2))
      have h2 : (⟨l, hl⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h2
    have hLs : IsSimpleGroup ↥L := by
      have := hs
      exact e.isSimpleGroup
    have hLeven : 2 ∣ Nat.card ↥L := by
      rw [Nat.card_congr e.toEquiv]
      exact two_dvd_natCard_of_nc2 hnc2
    obtain ⟨hD₀, hrk⟩ := rank_D₀ hD hsD hsN hdich
    refine caseB_core hL hcen hLs hLeven hD hk hW hDW hC hsD hsN hdich ?_
      (fun D' W' hD' hk' hW' hD'L hD'W' hC' => h Y hY L hL ⟨e⟩ D' W' hD' hk' hW' hD'L hD'W' hC')
    rcases hk with hk2 | hk3
    · obtain ⟨c, hcL, hc2, hcn⟩ := noncentral_two_elt_of_nc2 L e hnc2
      refine ⟨⊥, bot_le, by omega, c, hcL, ?_, hc2, hcn⟩
      rw [mem_centralizer_iff]
      intro h' hh
      have := Subgroup.mem_bot.mp hh
      subst this
      simp
    · exact exists_data_of_locE3 L e hD₀ (Or.inl (by omega)) inf_le_right hE3

theorem weakSig2TwoG4_of_genLoc4 {J : Type} [Group J] (hs : IsSimpleGroup J)
    (hq : IsQuasisimple J) (hnc2 : NC2 J)
    (hE3 : ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → LocE3 α)
    (h : GenLoc4 J) : WeakSig2TwoG4 J :=
  weakSig2TwoG4_of_weakSig2D4 hs hq hnc2 hE3
    (weakSig2D4_of_genLoc4 hq (WeakSigCaseB.two_dvd_natCard_of_nc2 hnc2) hnc2 h)

end CFSG.GH74.Generic.BProg.B2
