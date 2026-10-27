module

public import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Gen
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups

namespace GenLocPsl2Full

variable {F : Type} [Field F] [Finite F]

theorem isCoatom_centralizer_involution_nonsplit {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 3)
    (h11 : 11 ≤ p ^ f) {t : PSL2MatrixGroup F} (ht : orderOf t = 2) :
    IsCoatom (centralizer ({t} : Set (PSL2MatrixGroup F))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h11
      omega
    · exact h
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf0, hF⟩
  have hF2 : ringChar F ≠ 2 := CFSG.Glauberman.Dickson.MaxUp.ringChar_ne_two hF hp2
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  have hScard : Nat.card (CFSG.PSL2Table.nonsplitTorus ν) = (Fintype.card F + 1) / 2 :=
    CFSG.Glauberman.Dickson.MaxStructure.card_nonsplitTorus_eq hF2 hν
  have hSeven : 2 ∣ Nat.card (CFSG.PSL2Table.nonsplitTorus ν) := by
    rw [hScard, hq]
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 hSeven
  have ht₀' : orderOf (t₀ : PSL2MatrixGroup F) = 2 := by rw [Subgroup.orderOf_coe, ht₀]
  have hinv : ∀ x : PSL2MatrixGroup F, orderOf x = 2 →
      BenderSuzuki.PFAppendixIII.IsInvolution x :=
    fun x hx => ⟨fun h => by rw [h, orderOf_one] at hx; omega,
      by have h := pow_orderOf_eq_one x; rwa [hx] at h⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd
    (t₀ : PSL2MatrixGroup F) t (hinv _ ht₀') (hinv _ ht)
  have hR : zpowers t ≤ (CFSG.PSL2Table.nonsplitTorus ν).map (MulAut.conj g).toMonoidHom := by
    rw [zpowers_le]
    exact ⟨t₀, t₀.2, by rw [← hg]; rfl⟩
  have hR1 : zpowers t ≠ ⊥ := by
    intro h
    have : t ∈ (⊥ : Subgroup (PSL2MatrixGroup F)) := h ▸ mem_zpowers t
    rw [mem_bot] at this
    rw [this, orderOf_one] at ht
    omega
  have hle : centralizer ({t} : Set (PSL2MatrixGroup F)) ≤
      (normalizer (CFSG.PSL2Table.nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
        (MulAut.conj g).toMonoidHom := by
    calc centralizer ({t} : Set (PSL2MatrixGroup F)) =
          centralizer (zpowers t : Set (PSL2MatrixGroup F)) := by
          rw [zpowers_eq_closure, centralizer_closure]
      _ ≤ normalizer (zpowers t : Set (PSL2MatrixGroup F)) := centralizer_le_normalizer _
      _ ≤ _ := CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_nonsplitTorus hF2
          (by omega) hν g hR hR1
  have hcard : Nat.card ((normalizer (CFSG.PSL2Table.nonsplitTorus ν :
      Set (PSL2MatrixGroup F))).map (MulAut.conj g).toMonoidHom) ≤
      Nat.card (centralizer ({t} : Set (PSL2MatrixGroup F))) := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      CFSG.PSL2Table.card_normalizer_nonsplitTorus hF2 (by omega) hν, hScard,
      ((CFSG.Walter.psl2_centralizer_involution F hF (hp.odd_of_ne_two hp2) hf0 ht).2 h4).1, hq]
    omega
  rw [Subgroup.eq_of_le_of_card_ge hle hcard,
    CFSG.Glauberman.Dickson.MaxStructure.isCoatom_map_conj_iff]
  exact CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_nonsplitTorus hF hp2 (by omega)
    (by omega) (by omega) hν

end GenLocPsl2Full

section

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem psl2_isCoatom_centralizer_involution
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq : 11 ≤ p ^ f) {t : PSL2MatrixGroup F}
    (ht : orderOf t = 2) : IsCoatom (centralizer ({t} : Set (PSL2MatrixGroup F))) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hpodd.pow (n := f))
    omega
  rcases h4 with h4 | h4
  · exact ComponentClassification.AutL2Facts.isCoatom_centralizer_involution
      (Fact.out : p.Prime) hp2 hF h4 (by omega) ht
  · exact GenLocPsl2Full.isCoatom_centralizer_involution_nonsplit (Fact.out : p.Prime) hp2 hF h4
      hq ht

theorem psl2_sup_centralizer_eq_top (hF : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (hq : 11 ≤ p ^ f) {u u' : PSL2MatrixGroup F} (hu : orderOf u = 2)
    (hu' : orderOf u' = 2) (hne : u ≠ u') (_hc : u * u' = u' * u) :
    centralizer ({u} : Set (PSL2MatrixGroup F)) ⊔ centralizer ({u'} : Set (PSL2MatrixGroup F)) =
      ⊤ := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq; omega
    · exact h
  refine (psl2_isCoatom_centralizer_involution hF hp2 hq hu).sup_eq_top_of_ne
    (psl2_isCoatom_centralizer_involution hF hp2 hq hu') ?_
  exact GenLocPsl2Gen.centralizer_ne_of_center hu hu' hne
    (CFSG.Walter.psl2_center_centralizer_involution F hF hpodd hf (by omega) hu)

end

end CFSG.GH74.Generic.BProg.B2
