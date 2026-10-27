module

public import CFSG.GH74.GLS.Stage4.T2NumGtSingular
public import CFSG.GH74.GLS.Stage4.T2NumGtDim
public import CFSG.GH74.GLS.Stage4.T2NumGtPrimeEq
public import CFSG.GH74.GLS.Stage4.T2NumRed

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ch6T2NumGt_of_steps (h1 : Ch6T2Rem) (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (hS : Ch6GtTS) (hP : Ch6GtP) (hD : Ch6GtD) (hM : Ch6GtMixed) : Ch6T2NumGt := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn hlt
  by_cases hmod : q₁ % 4 = q₂ % 4
  · obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
    obtain ⟨t, hRem⟩ := h1 G hStd hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ hSet
    obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
      h3 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hmod
    obtain ⟨F, hF5⟩ := h4 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
    obtain ⟨a, hau, hWeyl⟩ :=
      h5 G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂ hLoc
        hCoord hF5
    let N₃ : T2N3 G := ⟨⟨N₁, F⟩, a⟩
    have hSec : Ch6Sec5 N₃ u := ⟨hLoc, hF5, hWeyl, hau⟩
    have := hSet.finite₂
    have : Fintype F₂ := Fintype.ofFinite F₂
    obtain ⟨p, -, ⟨n, hp, hcard⟩⟩ := FiniteField.card' F₂
    have hq₂p : q₂ = p ^ (n : ℕ) := by rw [← hSet.card₂, Nat.card_eq_fintype_card, hcard]
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := hSet.odd₂
      rw [hq₂p] at this
      exact (Nat.not_even_iff_odd.2 this) (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
    have hN₃z : N₃.z = z := hz
    have hN₃K₁ : N₃.K₁ = K₁ := hK₁
    have hN₃K₂ : N₃.K₂ = K₂ := hK₂
    have hN₃q₁ : N₃.q₁ = q₁ := hq₁
    have hN₃q₂ : N₃.q₂ = q₂ := hq₂
    obtain ⟨y, R, hTS⟩ := hS G hStd hr Gs q₁ q₂ hAt h99 hn hlt z K₁ K₂ F₁ F₂ t hSet hRem p n hp hp2
      hq₂p hmod N₃ u hN₃z hN₃K₁ hN₃K₂ hN₃q₁ hN₃q₂ hSec
    obtain ⟨m, hm⟩ := hP G Gs q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ t hSet hRem p n hp hp2 hq₂p N₃ u hN₃z
      hN₃K₁ hN₃K₂ hN₃q₁ hN₃q₂ hCoord hSec y R hTS
    have h3q : q₁ = q₂ ^ 3 :=
      hD G Gs q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ t hSet hRem p n m hp hp2 hq₂p hm N₃ u hN₃z hN₃K₁
        hN₃K₂ hN₃q₁ hN₃q₂ hCoord hSec y R hTS
    exact ⟨p, hp, hp2, ⟨m, hm⟩, ⟨n, hq₂p⟩, Or.inr h3q⟩
  · exact (hM G hStd hr Gs q₁ q₂ hAt h99 hn hlt hmod).elim

theorem ch6T2NumGt_of_leaves
    (h1 : Ch6T2Rem) (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (hL : SDWreathedLayer) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h11c : IVK_11_1c_dim) (hM : Ch6GtMixed) : Ch6T2NumGt :=
  ch6T2NumGt_of_steps h1 h3 h4 h5
    (ch6Gt_singular (ch6T2Prop56GtGen_of_layer_gA hL hGA)) ch6Gt_primeEq
    (ch6Gt_dim h11c) hM

end CFSG.GH74.GLS.Stage4.Rest
