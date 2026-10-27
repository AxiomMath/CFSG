module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu FinGen FinGlue
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace FinM22

theorem card_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G) (y : ↥H) :
    Nat.card ↥(centralizer ({y} : Set ↥H)) = Nat.card ↥(centralizerIn H (y : G)) := by
  have hmap : (centralizer ({y} : Set ↥H)).map H.subtype = centralizerIn H (y : G) := by
    ext x
    simp only [mem_map, mem_centralizerIn, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy, rfl⟩
  rw [← hmap, card_map_of_injective H.subtype_injective]

theorem isCyclic_outer {G : Type} [Group G] [Finite G] (hc : center G = ⊥)
    (h : Nat.card (MulAut G) ≤ 2 * Nat.card G) : IsCyclic (Outer G) := by
  have hinn : Nat.card (inner G) = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center' hc)).toEquiv).symm
  have hcard := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [hinn] at hcard
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hle : Nat.card (Outer G) ≤ 2 := by
    have : Nat.card (Outer G) * Nat.card G ≤ 2 * Nat.card G := hcard ▸ h
    exact Nat.le_of_mul_le_mul_right this hpos
  have hfin : Finite (MulAut G) :=
    Finite.of_injective (fun α : MulAut G => (α : G → G)) DFunLike.coe_injective
  have hpos' : 0 < Nat.card (Outer G) := Nat.card_pos
  rcases (by omega : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2) with h1 | h2
  · have : Subsingleton (Outer G) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2


theorem card_centralizerIn :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (m := 2) (by norm_num) [m22Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
  have hC : centralizerIn m22Certificate.originalSubgroup m22Rep1 =
      m22CentQ1.originalSubgroup := by
    refine centralizerIn_eq_of_le _ _ hK1 (c := 1155) ?_ ?_
    · rw [← hsz]
      exact hsize m22Rep1 (by simp)
    · rw [hKc1, m22Certificate_originalSubgroup, m22_card]
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [centralizerIn_conj _ hc, card_map_of_injective (MulEquiv.injective _), hC, hKc1]

end FinM22

theorem finCellB_m22
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .M22) : FinCellB Y := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M22 := e
  refine finCellB_of (NoFourPerf.of_equiv (MulAut.congr e')
    (noFourPerf_mulAut_of_cyclic m22_center_eq_bot'
      (FinM22.isCyclic_outer m22_center_eq_bot' m22_mulAut_card) fun y hy => ?_))
  have hy' : orderOf (y : Equiv.Perm (Fin 22)) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hcard : Nat.card ↥(centralizer ({y} : Set ↥NativeSporadic.M22)) = 2 ^ 7 * 3 ^ 1 := by
    rw [FinM22.card_centralizer_subtype, FinM22.card_centralizerIn _ y.2 hy']
    norm_num
  exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hcard

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
