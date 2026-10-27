module

public import CFSG.GH74.GLS.Bg.Pu5.BalABasic
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements
public import CFSG.GH74.GLS.Bg.Iii2.Basic

public section

namespace CFSG.GH74.GLS.Bg.Pu5.BalA

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Bg.Iii2 CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IDiag_eq {b : G} (hb : orderOf b = 2) (K : Subgroup G) :
    IDiag b K = pLayerOf 2 ((K ⊔ cmap b K) ⊓ centralizer ({b} : Set G)) := by
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two hb
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hcm : cmap b K = conjugate K b := by
    rw [show conjugate K b = cmap b⁻¹ K from rfl, hinv]
  unfold IDiag
  rw [hcm, inf_comm]

omit [Finite G] in
theorem mem_centralizer_of_comm {a b : G} (hab : a * b = b * a) :
    b ∈ centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr hab.symm

omit [Finite G] in
theorem comm_of_mem_centralizer {a b : G} (hab : b ∈ centralizer ({a} : Set G)) : a * b = b * a :=
  (Subgroup.mem_centralizer_singleton_iff.mp hab).symm

omit [Finite G] in
theorem barMk_eq_iff {C : Subgroup G} (w v : ↥C) :
    TwoThin.barMk ↥C w = TwoThin.barMk ↥C v ↔ (w : G)⁻¹ * (v : G) ∈ pPrimeCoreOf 2 C := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨u, hu, hu'⟩
    have : u = w⁻¹ * v := Subtype.ext hu'
    rwa [← this]

omit [Finite G] in
theorem swapDiag_eq_barMk {C : Subgroup G} (s k : ↥C) :
    TwoThin.barMk ↥C k * ((TwoThin.barMk ↥C s)⁻¹ * TwoThin.barMk ↥C k * TwoThin.barMk ↥C s) =
      TwoThin.barMk ↥C (k * (s⁻¹ * k * s)) := by
  simp only [map_mul, map_inv]

theorem odd_orderOf_of_mem_pPrimeCoreOf {C : Subgroup G} {n : G} (hn : n ∈ pPrimeCoreOf 2 C) :
    Odd (orderOf n) := by
  have h1 : orderOf (⟨n, hn⟩ : ↥(pPrimeCoreOf 2 C)) ∣ Nat.card (pPrimeCoreOf 2 C) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (TwoThin.card_pPrimeCoreOf_odd C).of_dvd_nat h1

theorem diag_cover_conv {a b : G} (hb : orderOf b = 2) (hab : a * b = b * a) {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({a} : Set G)) K) (hbK : b ∉ normalizer (K : Set G)) :
    (∀ k ∈ K, ∃ l ∈ IDiag b K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)),
        l = k * (b * k * b⁻¹) * o) ∧
      ∀ l ∈ IDiag b K, ∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)),
        l = k * (b * k * b⁻¹) * o := by
  have hbC : b ∈ centralizer ({a} : Set G) := mem_centralizer_of_comm hab
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two hb
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨hAB, hbar⟩ := IG_bar_gen hb hab hK hbK hbC
  set C := centralizer ({a} : Set G) with hCdef
  set π := TwoThin.barMk ↥C with hπ
  set s : ↥C := ⟨b, hbC⟩ with hs
  have hKC : K ≤ C := hK.1
  have hIC : IDiag b K ≤ C :=
    (IDiag_le_sup b K).trans (sup_le hKC (isPCompIn_conjugate hab hK).1)
  refine ⟨fun k hk => ?_, fun l hl => ?_⟩
  · have hkC : k ∈ C := hKC hk
    have hmem : π ⟨k, hkC⟩ ∈ (K.subgroupOf C).map π := ⟨⟨k, hkC⟩, hk, rfl⟩
    have hd : swapDiag hAB ⟨π ⟨k, hkC⟩, hmem⟩ ∈ ((IDiag b K).subgroupOf C).map π := by
      rw [hbar]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw, hwπ⟩ := hd
    have hwl : (w : G) ∈ IDiag b K := hw
    have h1 : π w = π (⟨k, hkC⟩ * (s⁻¹ * ⟨k, hkC⟩ * s)) := by
      rw [hwπ, swapDiag_apply, ← swapDiag_eq_barMk]
    have h2 := (barMk_eq_iff _ _).1 h1
    refine ⟨(w : G), hwl, ((w : G)⁻¹ * (k * (b⁻¹ * k * b)))⁻¹, inv_mem ?_, ?_⟩
    · simpa [hs] using h2
    · rw [hinv]
      group
  · have hlC : l ∈ C := hIC hl
    have hmem : π ⟨l, hlC⟩ ∈ ((IDiag b K).subgroupOf C).map π := ⟨⟨l, hlC⟩, hl, rfl⟩
    rw [hbar] at hmem
    obtain ⟨x, hx⟩ := hmem
    obtain ⟨k', hk', hk'x⟩ := x.2
    have hkK : (k' : G) ∈ K := hk'
    have h1 : π ⟨l, hlC⟩ = π (k' * (s⁻¹ * k' * s)) := by
      rw [← hx, swapDiag_apply, ← swapDiag_eq_barMk, hk'x]
    have h2 := (barMk_eq_iff _ _).1 h1
    refine ⟨(k' : G), hkK, ((k' : G) * (b⁻¹ * (k' : G) * b))⁻¹ * l, ?_, ?_⟩
    · have := inv_mem h2
      simpa [hs, mul_assoc] using this
    · rw [hinv]
      group

theorem diag_two_elt {a b : G} (hb : orderOf b = 2) (hab : a * b = b * a) {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({a} : Set G)) K) (hbK : b ∉ normalizer (K : Set G))
    {g : G} (hgX : g ∈ (K ⊔ cmap b K) ⊓ centralizer ({b} : Set G))
    (hg2 : ∃ n : ℕ, g ^ (2 ^ n) = 1)
    (hgd : ∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)),
      g = k * (b * k * b⁻¹) * o) : g ∈ IDiag b K := by
  obtain ⟨k, hk, o, ho, rfl⟩ := hgd
  obtain ⟨l, hl, o', ho', hl'⟩ := (diag_cover_conv hb hab hK hbK).1 k hk
  have hlX : l ∈ (K ⊔ cmap b K) ⊓ centralizer ({b} : Set G) := by
    rw [IDiag_eq hb K] at hl
    exact TwoThin.pLayerOf_le 2 _ hl
  have hgn : k * (b * k * b⁻¹) * o = l * (o'⁻¹ * o) := by
    rw [hl']
    group
  have hnO : o'⁻¹ * o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)) := mul_mem (inv_mem ho') ho
  have hnX : o'⁻¹ * o ∈ (K ⊔ cmap b K) ⊓ centralizer ({b} : Set G) := by
    have : o'⁻¹ * o = l⁻¹ * (k * (b * k * b⁻¹) * o) := by
      rw [hgn]
      group
    rw [this]
    exact mul_mem (inv_mem hlX) hgX
  have hnN : o'⁻¹ * o ∈ normalizer ((IDiag b K : Subgroup G) : Set G) := by
    rw [IDiag_eq hb K]
    exact mem_normalizer_pLayerOf hnX
  obtain ⟨m, hm⟩ := hg2
  exact IG327F.mem_of_two_power_of_odd hl hnN (odd_orderOf_of_mem_pPrimeCoreOf hnO) hgn hm

end CFSG.GH74.GLS.Bg.Pu5.BalA

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Bg.Pu5.BalA

theorem diagLayer_of : DiagLayerS := by
  intro G _ _ hG a b ha hb hab K hK hbK
  have hKC : IsPCompIn 2 (centralizer ({a} : Set G)) K := rr_pcomp hK
  have hab' : a * b = b * a := comm_of_mem_centralizer hab
  refine ⟨IDiag b K, IDiag_eq hb K, IG_i_gen hb hab' hKC hbK, ?_,
    (diag_cover_conv hb hab' hKC hbK).1, (diag_cover_conv hb hab' hKC hbK).2, ?_⟩
  · rw [IDiag_eq hb K]
    exact TwoThin.pLayerOf_le 2 _
  · intro g hg hg2 hgd
    exact diag_two_elt hb hab' hKC hbK hg hg2 hgd

end CFSG.GH74.GLS.Bg.Pu5
