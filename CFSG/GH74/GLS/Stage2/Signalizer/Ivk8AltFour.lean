module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
public import CFSG.GH74.GLS.Stage1.Thm4.L97a
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.LocalAnalysis.OddStandard.GlueAlt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Equiv Equiv.Perm CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private def cast4 {n : ℕ} (hn : 4 ≤ n) : Fin 4 ≃ {x : Fin n // x.val < 4} where
  toFun i := ⟨Fin.castLE hn i, by simp⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := by ext; simp
  right_inv x := by ext; simp

private def klA : Perm (Fin 4) := swap 0 1 * swap 2 3

private def klB : Perm (Fin 4) := swap 0 2 * swap 1 3

theorem exists_klein_alt {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : ↥(alternatingGroup (Fin n)), a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧
      b ≠ 1 ∧ a ≠ b := by
  let ι : Perm (Fin 4) →* Perm (Fin n) := Equiv.Perm.extendDomainHom (cast4 hn)
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective _
  have hsign : ∀ σ : Perm (Fin 4), Perm.sign σ = 1 → ι σ ∈ alternatingGroup (Fin n) := by
    intro σ h
    rw [Perm.mem_alternatingGroup]
    show Perm.sign (σ.extendDomain (cast4 hn)) = 1
    rw [Perm.sign_extendDomain, h]
  have hAs : Perm.sign klA = 1 := by decide
  have hBs : Perm.sign klB = 1 := by decide
  have hAA : klA * klA = 1 := by decide
  have hBB : klB * klB = 1 := by decide
  have hAB : klA * klB = klB * klA := by decide
  have hA1 : klA ≠ 1 := by decide
  have hB1 : klB ≠ 1 := by decide
  have hAB' : klA ≠ klB := by decide
  refine ⟨⟨ι klA, hsign _ hAs⟩, ⟨ι klB, hsign _ hBs⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, hAA, map_one]; rfl)
  · exact Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, hBB, map_one]; rfl)
  · exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, hAB])
  · intro h
    exact hA1 (hι (by simpa using congrArg Subtype.val h))
  · intro h
    exact hB1 (hι (by simpa using congrArg Subtype.val h))
  · intro h
    exact hAB' (hι (congrArg Subtype.val h))

theorem exists_four_alt {Y : Type} [Group Y] {n : ℕ} (hn : 4 ≤ n)
    (e : Y ≃* alternatingGroup (Fin n)) : ∃ V : Subgroup Y, IVK.IsFourSubgroup V := by
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_klein_alt hn
  obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_involutions ha hb hab ha1 hb1 hne
  exact ⟨V.map e.symm.toMonoidHom,
    hat_isFourSubgroup_map hV e.symm.toMonoidHom e.symm.injective⟩

theorem exists_four_le_comp_of_center_bot {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : CFSG.IsQuasisimple ↥J) {n : ℕ} (hn : 5 ≤ n) (h1 : center ↥J = ⊥)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin n)) :
    ∃ U : Subgroup A, U ≤ J ∧ IVK.IsFourSubgroup U := by
  have _ := hJ
  let π : ↥J →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥J))
  have hπ : Function.Bijective π := by
    refine ⟨?_, e.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    rw [injective_iff_map_eq_one]
    intro x hx
    have h2 : e (QuotientGroup.mk x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, h1, Subgroup.mem_bot] at h2
    exact h2
  obtain ⟨V, hV⟩ := exists_four_alt (Y := ↥J) (by omega) (MulEquiv.ofBijective π hπ)
  exact ⟨V.map J.subtype, Subgroup.map_subtype_le V,
    hat_isFourSubgroup_map hV J.subtype J.subtype_injective⟩

theorem exists_four_le_comp_of_alt {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : CFSG.IsQuasisimple ↥J) {n : ℕ} (hn : 8 ≤ n)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin n)) :
    ∃ U : Subgroup A, U ≤ J ∧ IVK.IsFourSubgroup U := by
  have hperf : Group.IsPerfect ↥J := hJ.1
  have hle := CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt hn e
  have hpos : 0 < Nat.card (center ↥J) := Nat.card_pos
  have hcases : Nat.card (center ↥J) = 1 ∨ Nat.card (center ↥J) = 2 := by omega
  rcases hcases with h1 | h2
  · exact exists_four_le_comp_of_center_bot hJ (by omega) (Subgroup.card_eq_one.1 h1) e
  · obtain ⟨π, hπ, -⟩ := Stage1.Thm4.L97.exists_twoCover (Lh := ↥J) (n := n) ⟨hJ, h2, ⟨e⟩⟩
    have hrank : 4 ≤ CFSG.pRank 2 ↥J := IVK.Lifted.four_le_pRank_of_twoCover hπ hn
    obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_two_le_pRank (by omega : 2 ≤ CFSG.pRank 2 ↥J)
    exact ⟨V.map J.subtype, Subgroup.map_subtype_le V,
      hat_isFourSubgroup_map hV J.subtype J.subtype_injective⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
