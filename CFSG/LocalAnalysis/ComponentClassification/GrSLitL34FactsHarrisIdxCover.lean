module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxTools
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.HarrisLit (fixedPoints innAut twoPart)

theorem orderOf_quotAut {Y : Type} [Group Y] {τ : MulAut Y} (hτ : orderOf τ = 2)
    (h1 : quotAut τ ≠ 1) : orderOf (quotAut τ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ h1
  have h2 : τ * τ = 1 := by rw [← pow_two, ← hτ, pow_orderOf_eq_one]
  rw [pow_two, ← quotAut_mul, h2, quotAut_one]

theorem twoJ2OuterInvolutionIndex :
    ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
      Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.J2) → Nat.card ↥(center Y) = 2 →
      ∀ τ : MulAut Y, orderOf τ = 2 → τ ∉ innAut Y →
        4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y) := by
  intro Y _ _ hq ⟨e⟩ hZ τ hτ hτi
  have : Group.IsPerfect Y := hq.1
  have hqi : quotAut τ ∉ innAut (Y ⧸ center Y) := fun h => hτi (mem_innAut_of_quotAut h)
  have hq1 : quotAut τ ≠ 1 := fun h => hqi (h ▸ (innAut _).one_mem)
  set ψ := e.trans j2PermEquiv with hψ
  have hσ2 : orderOf (MulAut.congr ψ (quotAut τ)) = 2 := by
    rw [orderOf_congr]
    exact orderOf_quotAut hτ hq1
  have hσi : MulAut.congr ψ (quotAut τ) ∉ innAut ↥j2P := by
    rw [congr_mem_innAut_iff]
    exact hqi
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, hcard, hinn⟩ := exists_row_of_autModel j2_autModel
    (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩) hcover hσ2
  have hout : r.outer = true := by
    by_contra h
    exact hσi (hinn.2 (by simpa using h))
  have h336 : r.centOrder = 336 := by
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
      rw [← hmap]
      exact List.mem_map_of_mem hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [hout] at h
      exact absurd h (by decide)
    · rw [hout] at h
      exact absurd h (by decide)
  have hdvd := card_fixedPoints_dvd τ
  rw [← card_fixedPoints_congr ψ, hcard, h336, hZ] at hdvd
  have h1 : twoPart (fixedPoints τ) ≤ 2 ^ 5 :=
    twoPart_le_of_dvd_mul (m := 21) ⟨10, rfl⟩ (by simpa using hdvd)
  have h2 : twoPart (⊤ : Subgroup Y) = 2 ^ 8 :=
    twoPart_top_eq (m := 4725) ⟨2362, rfl⟩ (by
      rw [(center Y).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr ψ.toEquiv, card_j2P,
        hZ]; norm_num)
  rw [h2]
  norm_num at h1 ⊢
  omega

theorem twoHSInnerInvolutionIndex :
    ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
      Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.HS) → Nat.card ↥(center Y) = 2 →
      ∀ τ : MulAut Y, orderOf τ = 2 → τ ∈ innAut Y →
        Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
          Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) →
        4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y) := by
  intro Y _ _ hq ⟨e⟩ hZ τ hτ hτi ⟨f⟩
  have : Group.IsPerfect Y := hq.1
  have hq1 : quotAut τ ≠ 1 := fun h => by
    have h' : τ = 1 := eq_one_of_mul_inv_mem_center fun y => by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← quotAut_mk,
        h, MulAut.one_apply, mul_inv_cancel]
    rw [h', orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  set ψ := e.trans hsPermEquiv with hψ
  have hσ2 : orderOf (MulAut.congr ψ (quotAut τ)) = 2 := by
    rw [orderOf_congr]
    exact orderOf_quotAut hτ hq1
  have hσi : MulAut.congr ψ (quotAut τ) ∈ innAut ↥hsP := by
    rw [congr_mem_innAut_iff]
    obtain ⟨y, rfl⟩ := hτi
    exact ⟨QuotientGroup.mk y, (quotAut_conj y).symm⟩
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, hcard, hinn⟩ := exists_row_of_autModel hs_autModel
    (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩) hcover hσ2
  have hout : r.outer = false := hinn.1 hσi
  have hco : r.centOrder = 7680 ∨ r.centOrder = 2880 := by
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320), (true, 23100, 1920)] := by
      rw [← hmap]
      exact List.mem_map_of_mem hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · rw [hout] at h
      exact absurd h (by decide)
    · rw [hout] at h
      exact absurd h (by decide)
  have h1440 : 1440 ∣ Nat.card (fixedPoints τ) := by
    have hF : Nat.card (generalizedFitting ↥(fixedPoints τ)) = 1440 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_prod, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
      have h4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rw [h4]
      decide
    rw [← hF]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd := card_fixedPoints_dvd τ
  rw [← card_fixedPoints_congr ψ, hcard, hZ] at hdvd
  have h2880 : r.centOrder = 2880 := by
    rcases hco with h | h
    · exfalso
      rw [h] at hdvd
      have h9 : 9 ∣ 7680 * 2 := dvd_trans (by norm_num : 9 ∣ 1440) (dvd_trans h1440 hdvd)
      norm_num at h9
    · exact h
  rw [h2880] at hdvd
  have h1 : twoPart (fixedPoints τ) ≤ 2 ^ 7 :=
    twoPart_le_of_dvd_mul (m := 45) ⟨22, rfl⟩ (by simpa using hdvd)
  have h2 : twoPart (⊤ : Subgroup Y) = 2 ^ 10 :=
    twoPart_top_eq (m := 86625) ⟨43312, rfl⟩ (by
      rw [(center Y).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr ψ.toEquiv, card_hsP,
        hZ]; norm_num)
  rw [h2]
  norm_num at h1 ⊢
  omega

end CFSG.ComponentClassification.GrSLit.L34Facts
