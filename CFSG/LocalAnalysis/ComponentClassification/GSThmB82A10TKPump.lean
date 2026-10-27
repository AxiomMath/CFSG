module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TK
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Defs

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

namespace Ctx.CaseIIIp

variable {c : Ctx X} (e : c.CaseIIIp)

theorem nonempty_equiv_of_mem_kernel {b : X} {Y : Subgroup X}
    (hbK : b ∈ coreActionKernel e.K) (hYK : Y ≤ e.K ⊓ centralizer ({b} : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))))
    (hb : orderOf b = 2) (hbw : b ∈ centralizer ({e.w} : Set X)) :
    Nonempty (↥e.K ⧸ pPrimeCore 2 ↥e.K ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  have hbP2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hKq := isQuasisimple_of_isPComponent e.K_le e.isPComponent_K
  obtain ⟨-, -, hKsub, -, -⟩ := id e.isPComponent_K
  set F := GSLit.fixedLayer e.K (zpowers b) with hFdef
  have hFle : F ≤ e.K ⊓ centralizer ({b} : Set X) := by
    have h := GSLit.fixedLayer_le_inf e.K (zpowers b)
    rwa [centralizer_zpowers_eq] at h
  have hFpc : IsPComponent 2
      (F.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))) := by
    have h := GSLit.fixedLayer_isPComponent e.K_le hKsub (zpowers_le.mpr hbw)
      (zpowers_le.mpr hbK) hbP2 hKq
    rwa [centralizer_zpowers_eq] at h
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore hKq (zpowers_le.mpr hbK) hbP2).1
  obtain ⟨-, eF, -⟩ := restriction_quotient_mulEquiv (hFle.trans inf_le_left) hsup
  have hKC : e.K ⊓ centralizer ({b} : Set X) ≤
      centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X) :=
    inf_le_inf_right _ e.K_le
  have hYF : Y ≤ F := by
    have h := le_layerIn_of_isPComponent hYK (isPComponent_of_le_of_le hYK hKC hY)
    rw [← centralizer_zpowers_eq] at h
    exact h
  have hYq := isQuasisimple_of_isPComponent (hYK.trans hKC) hY
  have hYeq : Y = F := eq_of_le_of_le_of_not_isSolvable (hYK.trans hKC) (hFle.trans hKC) hY
    hFpc le_rfl hYF (not_isSolvable_of_isQuasisimple hYq)
  exact ⟨eF.symm.trans (Sol78.coreQuotCongr (MulEquiv.subgroupCongr hYeq.symm))⟩

theorem pump (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hA8 : EvenPump.A8PumpInput) {b : X}
    {Y : Subgroup X} (hbw : b ∈ centralizer ({e.w} : Set X)) (hb : orderOf b = 2)
    (hbN : b ∈ normalizer (e.K : Set X)) (hbK : b ∉ coreActionKernel e.K)
    (hYK : Y ≤ e.K ⊓ centralizer ({b} : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))))
    {s : ℕ} (hs : Even s) (hs8 : 8 ≤ s)
    (eY : ↥Y ⧸ pPrimeCore 2 ↥Y ≃* alternatingGroup (Fin s)) :
    (∃ m : ℕ, Even m ∧ 8 ≤ m ∧
        Nonempty (↥e.K ⧸ Open.fusionZStar ↥e.K ≃* alternatingGroup (Fin m))) ∨
      (10 ≤ s ∧ Nonempty (↥e.K ⧸ Open.fusionZStar ↥e.K ≃* Blueprint.NativeSporadic.Carrier .HN)) ∨
      (s = 8 ∧ (Blueprint.LieModel (↥e.K ⧸ Open.fusionZStar ↥e.K) .PSL 4 2 2 ∨
        Nonempty (↥e.K ⧸ Open.fusionZStar ↥e.K ≃* Blueprint.NativeSporadic.Carrier .HS))) := by
  have hbP2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hYC : Y ≤ centralizer ({e.w} : Set X) := hYK.trans (inf_le_left.trans e.K_le)
  rcases Nat.lt_or_ge s 10 with hs10 | hs10
  ·
    obtain rfl : s = 8 := by
      obtain ⟨k, hk⟩ := hs
      omega
    let x : ↥(centralizer ({e.w} : Set X)) := ⟨b, hbw⟩
    have hx : orderOf x = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hb
    have hxN : x ∈ normalizer
        ((e.K.subgroupOf (centralizer ({e.w} : Set X)) : Subgroup _) : Set _) := by
      rw [mem_normalizer_iff]
      intro h
      exact mem_normalizer_iff.mp hbN h
    have hCH : (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X)).subgroupOf
        (centralizer ({e.w} : Set X)) = centralizer ({x} : Set _) := by
      ext h
      rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff (g := b),
        mem_centralizer_singleton_iff (g := x)]
      constructor
      · rintro ⟨-, h1⟩
        exact Subtype.ext h1
      · intro h1
        exact ⟨h.2, congrArg Subtype.val h1⟩
    have hT'M : Y.subgroupOf (centralizer ({e.w} : Set X)) ≤
        e.K.subgroupOf (centralizer ({e.w} : Set X)) := fun t ht =>
      mem_subgroupOf.mpr (hYK (mem_subgroupOf.mp ht)).1
    have hT'C : Y.subgroupOf (centralizer ({e.w} : Set X)) ≤ centralizer ({x} : Set _) := by
      rw [← hCH]
      exact fun t ht => mem_subgroupOf.mpr ⟨t.2, (hYK (mem_subgroupOf.mp ht)).2⟩
    have hT'pc : IsPComponent 2 ((Y.subgroupOf (centralizer ({e.w} : Set X))).subgroupOf
        (centralizer ({x} : Set _))) := by
      rw [← hCH]
      exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
        Nat.prime_two).mpr hY
    let eT : ↥(Y.subgroupOf (centralizer ({e.w} : Set X))) ≃* ↥Y := subgroupOfEquivOfLe hYC
    let eT8 := (Sol78.coreQuotCongr eT).trans eY
    have hT'Z := EvenPump.fusionZStar_eq_of_alt (by norm_num) eT8
    have hex : (Open.fusionZStar ↥(Y.subgroupOf (centralizer ({e.w} : Set X)))).map
          (Y.subgroupOf (centralizer ({e.w} : Set X))).subtype ≤
        (pPrimeCore 2 ↥(Y.subgroupOf (centralizer ({e.w} : Set X)))).map
          (Y.subgroupOf (centralizer ({e.w} : Set X))).subtype ⊔
        (Open.fusionZStar ↥(e.K.subgroupOf (centralizer ({e.w} : Set X)))).map
          (e.K.subgroupOf (centralizer ({e.w} : Set X))).subtype := by
      rw [hT'Z]
      exact le_sup_left
    let eM : ↥(e.K.subgroupOf (centralizer ({e.w} : Set X))) ≃* ↥e.K :=
      subgroupOfEquivOfLe e.K_le
    rcases hA8 _ e.kGroup_centralizer_w _ e.isPComponent_K x hx hxN _ hT'M hT'C hT'pc hex
        ⟨(QuotientGroup.quotientMulEquivOfEq hT'Z).trans eT8⟩ with
      ⟨m', hm', hm8, ⟨eA⟩⟩ | hL | ⟨⟨eHS⟩⟩
    · exact Or.inl ⟨m', hm', hm8, ⟨(Sol78.fusionZStarQuotCongr eM).symm.trans eA⟩⟩
    · exact Or.inr (Or.inr ⟨rfl, Or.inl
        (Blueprint.LieModel.of_mulEquiv (Sol78.fusionZStarQuotCongr eM) hL)⟩)
    · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨(Sol78.fusionZStarQuotCongr eM).symm.trans eHS⟩⟩)
  ·
    have hEk : Nat.card (zpowers b) ≤ 2 * Nat.card ↥(zpowers b ⊓ coreActionKernel e.K) := by
      rw [Nat.card_zpowers, hb]
      have := Nat.card_pos (α := ↥(zpowers b ⊓ coreActionKernel e.K))
      omega
    have hTE : Y ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
      rw [centralizer_zpowers_eq]
      exact hYK.trans inf_le_right
    have hT : IsPComponent 2 (Y.subgroupOf
        (centralizer ({e.w} : Set X) ⊓ centralizer ((zpowers b : Subgroup X) : Set X))) := by
      rw [centralizer_zpowers_eq]
      exact hY
    rcases pumpStep' hcore hHN e.kGroup_centralizer_w e.K_le e.isPComponent_K
        (zpowers_le.mpr hbw) hbP2 (zpowers_le.mpr hbN) hEk (hYK.trans inf_le_left) hTE hT
        (Or.inl ⟨s, hs, hs10, ⟨eY⟩⟩) with ⟨n, hn, hn10, heK⟩ | heK
    · exact Or.inl ⟨n, hn, by omega, heK⟩
    · exact Or.inr (Or.inl ⟨hs10, heK⟩)

end Ctx.CaseIIIp

end CFSG.ComponentClassification.GSThmB.A10T
