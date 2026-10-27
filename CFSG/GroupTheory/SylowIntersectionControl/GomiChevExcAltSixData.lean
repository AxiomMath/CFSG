module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EGroup
public import CFSG.GroupTheory.PermSylowTwo.Alt
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
public import CFSG.Mathlib.Decide.Bounded
import CFSG.LocalAnalysis.ComponentClassification.Sol78AltCentralizer
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.GroupTheory.GomiExcAltSix

open Equiv Subgroup CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X3E

@[expose] def alt6PairStab : Subgroup S6 where
  carrier := {x | ((x : Perm (Fin 6)) 4 = 4 ∧ (x : Perm (Fin 6)) 5 = 5) ∨
    ((x : Perm (Fin 6)) 4 = 5 ∧ (x : Perm (Fin 6)) 5 = 4)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Perm.mul_apply] at ha hb ⊢
    rcases ha with ⟨ha4, ha5⟩ | ⟨ha4, ha5⟩ <;> rcases hb with ⟨hb4, hb5⟩ | ⟨hb4, hb5⟩ <;>
      simp [ha4, ha5, hb4, hb5]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
    rcases ha with ⟨ha4, ha5⟩ | ⟨ha4, ha5⟩
    · exact Or.inl ⟨Perm.inv_eq_iff_eq.2 ha4.symm, Perm.inv_eq_iff_eq.2 ha5.symm⟩
    · exact Or.inr ⟨Perm.inv_eq_iff_eq.2 ha5.symm, Perm.inv_eq_iff_eq.2 ha4.symm⟩

instance decidableMemAlt6PairStab : DecidablePred (· ∈ alt6PairStab) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem card_alt6PairStab : Nat.card alt6PairStab = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem gx_mem_alt6PairStab : gx ∈ alt6PairStab := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem mem_alt6PairStab_of_mem_R0list : ∀ g ∈ R0list, g ∈ alt6PairStab := by
  decide +kernel

theorem R0_le_alt6PairStab : R0 ≤ alt6PairStab := fun g hg =>
  mem_alt6PairStab_of_mem_R0list g (mem_R0.1 hg)

theorem apply_four_of_mem_alt6PairStab : ∀ x : S6, x ∈ alt6PairStab →
    (x : Perm (Fin 6)) ^ 3 = 1 → (x : Perm (Fin 6)) 4 = 4 := by
  decide +kernel

theorem c33_apply_ne : ∀ j : Fin 6, (c[0, 1, 2] * c[3, 4, 5] : Perm (Fin 6)) j ≠ j := by
  decide +kernel

theorem isSylowOf_R0 : IsSylowOf 2 R0 ⊤ := by
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 3) (by rw [card_R0]; norm_num)
  · rw [Subgroup.relIndex_top_right]
    have h := Subgroup.card_mul_index R0
    rw [card_R0, card_S6] at h
    have : R0.index = 45 := by omega
    rw [this]
    norm_num

private theorem normalizer_R0 : normalizer (R0 : Set S6) = R0 := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf R0 ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp isSylowOf_R0
  have h := CFSG.GroupTheory.PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt (n := 6) le_rfl
    Subgroup.topEquiv hS
  rwa [top_inf_eq] at h

theorem isGomiAtom_R0_alt6PairStab : CFSG.GroupTheory.IsGomiAtom ⊤ R0 alt6PairStab := by
  refine (CFSG.GroupTheory.isGomiAtom_top_iff_covBy R0 alt6PairStab).2 ?_
  rw [normalizer_R0, covBy_iff_lt_and_eq_or_eq]
  refine ⟨lt_of_le_of_ne R0_le_alt6PairStab ?_, fun C hRC hCA => ?_⟩
  · intro h
    have h1 := card_R0
    have h2 := card_alt6PairStab
    rw [h] at h1
    omega
  · have h8 : 8 ∣ Nat.card C := by
      have := Subgroup.card_dvd_of_le hRC
      rwa [card_R0] at this
    have h24 : Nat.card C ∣ 24 := by
      have := Subgroup.card_dvd_of_le hCA
      rwa [card_alt6PairStab] at this
    have hge : 8 ≤ Nat.card C := Nat.le_of_dvd Nat.card_pos h8
    have hle : Nat.card C ≤ 24 := Nat.le_of_dvd (by norm_num) h24
    have hcases : Nat.card C = 8 ∨ Nat.card C = 24 := by
      interval_cases Nat.card C <;> omega
    rcases hcases with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hRC (by rw [card_R0, h])).symm
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hCA (by rw [card_alt6PairStab, h]))

theorem eq_top_of_card_eq_24_of_lt {B C : Subgroup S6} (hB : Nat.card B = 24) (hBC : B < C) :
    C = ⊤ := by
  have hdvd : 24 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hBC.le
    rwa [hB] at this
  have hne : Nat.card C ≠ 24 := by
    intro h
    have hle : Nat.card C ≤ Nat.card B := by rw [h, hB]
    exact hBC.ne (Subgroup.eq_of_le_of_card_ge hBC.le hle)
  have hindex : Nat.card C * C.index = 360 := by
    rw [Subgroup.card_mul_index, card_S6]
  by_contra hC
  have hidx : 6 ≤ C.index :=
    CFSG.ComponentClassification.Sol78.le_index_of_mulEquiv_alternating (m := 6) (by norm_num)
      (MulEquiv.refl S6) hC
  have hge : 24 ≤ Nat.card C := Nat.le_of_dvd Nat.card_pos hdvd
  have hle : C.index ≤ 15 := by
    by_contra h
    rw [not_le] at h
    have h2 : 24 * 16 ≤ Nat.card C * C.index := Nat.mul_le_mul hge h
    omega
  interval_cases C.index <;> omega

private def permOfList (p : List (Fin 6)) : Perm (Fin 6) :=
  p.zipIdx.foldl (fun k a => swap (Fin.ofNat 6 a.2) (k a.1) * k) 1

private def stdConj (g : Perm (Fin 6)) : Perm (Fin 6) :=
  permOfList ((((List.finRange 6).filter fun i => decide (i < g i)).flatMap fun a => [a, g a]) ++
    (List.finRange 6).filter fun i => decide (g i = i))

private theorem stdConj_conj : ∀ g : Perm (Fin 6), g * g = 1 → Perm.sign g = -1 →
    stdConj g * g * (stdConj g)⁻¹ = swap 0 1 ∨
      stdConj g * g * (stdConj g)⁻¹ = swap 0 1 * swap 2 3 * swap 4 5 := by
  decide +kernel

private theorem commute_conj_of_commute_swap : ∀ x : Perm (Fin 6), x * swap 0 1 = swap 0 1 * x →
    x * (swap 2 3 * swap 4 5) * x⁻¹ * (swap 2 3 * swap 4 5) =
      swap 2 3 * swap 4 5 * (x * (swap 2 3 * swap 4 5) * x⁻¹) := by
  decide +kernel

private theorem commute_conj_of_commute_swap3 : ∀ x : Perm (Fin 6),
    x * (swap 0 1 * swap 2 3 * swap 4 5) = swap 0 1 * swap 2 3 * swap 4 5 * x →
    x * (swap 0 1 * swap 2 3) * x⁻¹ * (swap 0 1 * swap 2 3) =
      swap 0 1 * swap 2 3 * (x * (swap 0 1 * swap 2 3) * x⁻¹) := by
  decide +kernel

private theorem conj_back {g s u v : Perm (Fin 6)} (hsg : s * g * s⁻¹ = v)
    (hu : ∀ x, x * v = v * x → x * u * x⁻¹ * u = u * (x * u * x⁻¹)) (x : Perm (Fin 6))
    (hx : x * g = g * x) :
    x * (s⁻¹ * u * s) * x⁻¹ * (s⁻¹ * u * s) = s⁻¹ * u * s * (x * (s⁻¹ * u * s) * x⁻¹) := by
  have hcomm : (s * x * s⁻¹) * v = v * (s * x * s⁻¹) := by
    rw [← hsg]
    calc (s * x * s⁻¹) * (s * g * s⁻¹) = s * (x * g) * s⁻¹ := by group
      _ = s * (g * x) * s⁻¹ := by rw [hx]
      _ = (s * g * s⁻¹) * (s * x * s⁻¹) := by group
  have h := hu (s * x * s⁻¹) hcomm
  have h2 := congrArg (fun z => s⁻¹ * z * s) h
  calc x * (s⁻¹ * u * s) * x⁻¹ * (s⁻¹ * u * s)
      = s⁻¹ * ((s * x * s⁻¹) * u * (s * x * s⁻¹)⁻¹ * u) * s := by group
    _ = s⁻¹ * (u * ((s * x * s⁻¹) * u * (s * x * s⁻¹)⁻¹)) * s := h2
    _ = s⁻¹ * u * s * (x * (s⁻¹ * u * s) * x⁻¹) := by group

private theorem exists_of_conj_data {g s u v : Perm (Fin 6)} (hsg : s * g * s⁻¹ = v)
    (hu : ∀ x, x * v = v * x → x * u * x⁻¹ * u = u * (x * u * x⁻¹))
    (hsgn : Perm.sign u = 1) (hu1 : u ≠ 1) (hu2 : u * u = 1) (huv : u * v = v * u) :
    Perm.sign (s⁻¹ * u * s) = 1 ∧ (s⁻¹ * u * s) ≠ 1 ∧
      (s⁻¹ * u * s) * (s⁻¹ * u * s) = 1 ∧
      (s⁻¹ * u * s) * g = g * (s⁻¹ * u * s) ∧
      ∀ x : Perm (Fin 6), x * g = g * x →
        x * (s⁻¹ * u * s) * x⁻¹ * (s⁻¹ * u * s) =
          s⁻¹ * u * s * (x * (s⁻¹ * u * s) * x⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_, fun x hx => conj_back hsg hu x hx⟩
  · rw [map_mul, map_mul, Perm.sign_inv, hsgn, mul_one]
    exact Int.units_mul_self (Perm.sign s)
  · intro ht
    have : u = 1 := by
      calc u = s * (s⁻¹ * u * s) * s⁻¹ := by group
        _ = s * 1 * s⁻¹ := by rw [ht]
        _ = 1 := by group
    exact hu1 this
  · calc (s⁻¹ * u * s) * (s⁻¹ * u * s) = s⁻¹ * (u * u) * s := by group
      _ = 1 := by rw [hu2]; group
  · have hconjt : (MulAut.conj s) (s⁻¹ * u * s) = u := by
      simp only [MulAut.conj_apply]; group
    have hconjg : (MulAut.conj s) g = v := by simpa [MulAut.conj_apply] using hsg
    refine (MulAut.conj s).injective ?_
    conv_lhs => rw [map_mul]
    conv_rhs => rw [map_mul]
    rw [hconjt, hconjg, huv]

theorem exists_commuting_conj_of_odd_involution {g : Perm (Fin 6)} (hg : g * g = 1)
    (hs : Perm.sign g = -1) :
    ∃ t : Perm (Fin 6), Perm.sign t = 1 ∧ t ≠ 1 ∧ t * t = 1 ∧ t * g = g * t ∧
      ∀ x : Perm (Fin 6), x * g = g * x → x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by
  rcases stdConj_conj g hg hs with h | h
  · refine ⟨(stdConj g)⁻¹ * (swap 2 3 * swap 4 5) * stdConj g, ?_⟩
    exact exists_of_conj_data h commute_conj_of_commute_swap (by decide) (by decide) (by decide)
      (by decide)
  · refine ⟨(stdConj g)⁻¹ * (swap 0 1 * swap 2 3) * stdConj g, ?_⟩
    exact exists_of_conj_data h commute_conj_of_commute_swap3 (by decide) (by decide) (by decide)
      (by decide)

end CFSG.GroupTheory.GomiExcAltSix
