module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterRep
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.AGLEmbedding.ChevOuter
  CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

namespace TD42

theorem conj_injective {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
    have h1 := congrArg (fun f : MulAut X => f y) hx
    change x * y * x⁻¹ = y at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem card_outer (hZ : Subgroup.center lineGroup = ⊥) {n : ℕ}
    (hT : Nat.card lineGroup = n) (hA : Nat.card (MulAut lineGroup) = 3 * n) (hn : 0 < n) :
    Nat.card (Outer lineGroup) = 3 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Inn lineGroup)
  have h2 : Nat.card (Inn lineGroup) = n := by
    rw [← hT]
    exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective hZ)).toEquiv).symm
  rw [h2, hA] at h1
  have : Nat.card (Outer lineGroup) * n = 3 * n := h1.symm
  exact Nat.eq_of_mul_eq_mul_right hn this

theorem exists_conj_mul_phiT (hQ : Nat.card (Outer lineGroup) = 3) (α : MulAut lineGroup) :
    ∃ (g : lineGroup) (j : ℕ), j < 3 ∧ α = MulAut.conj g * phiT ^ j := by
  set q : MulAut lineGroup →* Outer lineGroup := QuotientGroup.mk' (Inn lineGroup) with hq
  have hq1 : q phiT ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff phiT).1 h
    exact phiT_ne_conj g hg.symm
  have h3 : (q phiT) ^ 3 = 1 := by rw [← map_pow, phiT_pow_three, map_one]
  have hord : orderOf (q phiT) = 3 :=
    orderOf_eq_prime h3 hq1
  have hz : Subgroup.zpowers (q phiT) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hQ]
  have hmem : q α ∈ Subgroup.zpowers (q phiT) := by rw [hz]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hm' : (q phiT) ^ (m % 3).toNat = q α := by
    rw [← hm, zpow_eq_zpow_emod m (n := 3) (by exact_mod_cast h3)]
    have : (0 : ℤ) ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    rw [← zpow_natCast, Int.toNat_of_nonneg this]
  have hin : α * (phiT ^ (m % 3).toNat)⁻¹ ∈ Inn lineGroup := by
    rw [← QuotientGroup.eq_one_iff]
    change q (α * (phiT ^ (m % 3).toNat)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hm', mul_inv_cancel]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hin
  refine ⟨g, (m % 3).toNat, by omega, ?_⟩
  rw [hg]
  group

theorem exists_inner_of_card_nine (hZ : Subgroup.center lineGroup = ⊥)
    (hQ : Nat.card (Outer lineGroup) = 3) {E : Subgroup (MulAut lineGroup)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9) :
    ∃ s : lineGroup, s ≠ 1 ∧ s ^ 3 = 1 ∧ MulAut.conj s ∈ E := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set f : E →* Outer lineGroup := (QuotientGroup.mk' (Inn lineGroup)).comp E.subtype with hf
  have hf1 : Nat.card f.ker * Nat.card f.range = Nat.card E := by
    rw [← Subgroup.index_ker f, Subgroup.card_mul_index]
  have hrange : Nat.card f.range ≤ 3 := by
    rw [← hQ]
    exact Subgroup.card_le_card_group _
  have hker : 1 < Nat.card f.ker := by
    by_contra hcon
    have h1 : Nat.card f.ker ≤ 1 := by omega
    have : Nat.card E ≤ 1 * 3 := by
      rw [← hf1]
      exact Nat.mul_le_mul h1 hrange
    omega
  haveI : Nontrivial f.ker := Finite.one_lt_card_iff_nontrivial.1 hker
  obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (1 : f.ker)
  have hin : (e : MulAut lineGroup) ∈ Inn lineGroup := by
    have : QuotientGroup.mk' (Inn lineGroup) (e : MulAut lineGroup) = 1 := MonoidHom.mem_ker.1 he
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hin
  have he1 : (e : MulAut lineGroup) ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro rfl
    exact he1 (by rw [← hs, map_one])
  · apply conj_injective hZ
    rw [map_pow, hs, map_one]
    exact hE.2 _ e.2
  · rw [hs]
    exact e.2

@[expose] def trT (y : lineGroup) : GF8 :=
  (((y : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8).trace

theorem trT_conj (g y : lineGroup) : trT (g * y * g⁻¹) = trT y := by
  unfold trT
  set G : Matrix (Fin 8) (Fin 8) GF8 := (((g : lineGroup) : GL (Fin 8) GF8) :
    Matrix (Fin 8) (Fin 8) GF8) with hG
  set Gi : Matrix (Fin 8) (Fin 8) GF8 := ((((g : lineGroup) : GL (Fin 8) GF8)⁻¹ :
    GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) with hGi
  have hinv : Gi * G = 1 := by
    rw [hG, hGi]
    exact Units.inv_mul ((g : lineGroup) : GL (Fin 8) GF8)
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  rw [← hG, ← hGi, Matrix.trace_mul_comm, ← mul_assoc, hinv, one_mul]

theorem trT_phiT_pow (n : ℕ) (y : lineGroup) : trT ((phiT ^ n) y) = frobF^[n] (trT y) := by
  unfold trT
  rw [coe_phiT_pow]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', trace_frob, ih]

theorem inner_of_fixed_trace (hQ : Nat.card (Outer lineGroup) = 3) (y : lineGroup)
    (h1 : frobF (trT y) ≠ trT y) (h2 : frobF (frobF (trT y)) ≠ trT y) {α : MulAut lineGroup}
    (hα : α y = y) : ∃ g : lineGroup, α = MulAut.conj g := by
  obtain ⟨g, j, hj, rfl⟩ := exists_conj_mul_phiT hQ α
  have key : ∀ n : ℕ, (MulAut.conj g * phiT ^ n) y = y → frobF^[n] (trT y) = trT y := by
    intro n hn
    have h3 : g * (phiT ^ n) y * g⁻¹ = y := by
      have := hn
      rwa [MulAut.mul_apply, MulAut.conj_apply] at this
    have := congrArg trT h3
    rw [trT_conj, trT_phiT_pow] at this
    exact this
  interval_cases j
  · exact ⟨g, by simp⟩
  · exact absurd (key 1 hα) (by simpa using h1)
  · exact absurd (key 2 hα) (by simpa using h2)

end TD42

end CFSG.LocalAnalysis.GLTheoremA

end
