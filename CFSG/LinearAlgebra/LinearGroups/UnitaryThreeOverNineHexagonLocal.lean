module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonLines
public import CFSG.GroupTheory.SevenInvolutionWreathLaw
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Assembly CFSG.GroupTheory

variable {F : Type} [Field F]

theorem involutionGraph_statedSU (hF : Nat.card F = 9) :
    (∀ z : {g : StatedSU 3 3 F // orderOf g = 2},
      ((involutionGraph (StatedSU 3 3 F)).neighborSet z).ncard = 6) ∧
    (¬ ∃ a b c d : {g : StatedSU 3 3 F // orderOf g = 2}, [a, b, c, d].Nodup ∧
      (involutionGraph (StatedSU 3 3 F)).Adj a b ∧ (involutionGraph (StatedSU 3 3 F)).Adj b c ∧
      (involutionGraph (StatedSU 3 3 F)).Adj c d ∧ (involutionGraph (StatedSU 3 3 F)).Adj d a ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj a c ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj b d) ∧
    ¬ ∃ a b c d e : {g : StatedSU 3 3 F // orderOf g = 2}, [a, b, c, d, e].Nodup ∧
      (involutionGraph (StatedSU 3 3 F)).Adj a b ∧ (involutionGraph (StatedSU 3 3 F)).Adj b c ∧
      (involutionGraph (StatedSU 3 3 F)).Adj c d ∧ (involutionGraph (StatedSU 3 3 F)).Adj d e ∧
      (involutionGraph (StatedSU 3 3 F)).Adj e a ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj a c ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj a d ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj b d ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj b e ∧
      ¬ (involutionGraph (StatedSU 3 3 F)).Adj c e := by
  have h := unitaryFieldData_of_card hF
  have : Finite (StatedSU 3 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hF
  obtain ⟨⟨s, t, w, hs, ht, hw⟩, hall⟩ := wreath_sylow_model hF i hi
  obtain ⟨hst, hs4, ht4, hinter, hw2, hwout, hsw, htw, -, -, hx, -, -, -⟩ := hall s t w hs ht hw
  have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
    rw [gramForm_e0_left]
    exact one_ne_zero
  have hxτ : (s * t) ^ 2 = (tauLine h hF (lineOf _ hv) : StatedSU 3 3 F) :=
    Subtype.ext (Units.ext (by rw [hx, coe_tauLine_e0 rfl]))
  have h7 := ncard_involutions_centralizer (h := h) (hF := hF) (L₀ := lineOf _ hv) rfl
  rw [← hxτ] at h7
  obtain ⟨-, h6, -, -, hsq, hpent⟩ := seven_involution_centralizer_wreath_law_and_small_polygons
    (fun u v hu hv => isConj_of_orderOf_eq_two hF hu hv) _ s t w hst hs4 ht4 hinter hw2 hwout hsw
    htw rfl h7
  exact ⟨h6, hsq, hpent⟩

theorem adj_tauLine_iff (h : UnitaryFieldData 3 1 F) (hF : Nat.card F = 9)
    (a b : NonisoLine F) :
    (involutionGraph (StatedSU 3 3 F)).Adj (tauLine h hF a) (tauLine h hF b) ↔
      a ≠ b ∧ Orth a b := by
  rw [SevenInvolutionWreathLaw.adj_iff_ne_and_commute]
  constructor
  · rintro ⟨hne, hc⟩
    have hab : a ≠ b := fun e => hne (by rw [e])
    exact ⟨hab, (orth_iff h a b).mpr ((tauLine_commute_iff hab).mp hc)⟩
  · rintro ⟨hab, horth⟩
    exact ⟨fun e => hab (tauLine_injective e),
      (tauLine_commute_iff hab).mpr ((orth_iff h a b).mp horth)⟩

theorem ncard_orth (hF : Nat.card F = 9) (p : NonisoLine F) :
    {q : NonisoLine F | Orth p q}.ncard = 6 := by
  have h := unitaryFieldData_of_card hF
  have himg : (fun q => tauLine h hF q) '' {q : NonisoLine F | Orth p q} =
      (involutionGraph (StatedSU 3 3 F)).neighborSet (tauLine h hF p) := by
    ext z
    obtain ⟨q, rfl⟩ := tauLine_surjective (h := h) (hF := hF) z
    rw [SimpleGraph.mem_neighborSet, adj_tauLine_iff]
    constructor
    · rintro ⟨q', hq', hq'q⟩
      rw [← tauLine_injective hq'q]
      exact ⟨hq'.ne, hq'⟩
    · rintro ⟨-, hpq⟩
      exact ⟨q, hpq, rfl⟩
  rw [← Set.ncard_image_of_injective _ (tauLine_injective (h := h) (hF := hF)), himg,
    (involutionGraph_statedSU hF).1]

theorem not_exists_orth_square (hF : Nat.card F = 9) :
    ¬ ∃ a b c d : NonisoLine F, [a, b, c, d].Nodup ∧ Orth a b ∧ Orth b c ∧ Orth c d ∧
      Orth d a ∧ ¬ Orth a c ∧ ¬ Orth b d := by
  have h := unitaryFieldData_of_card hF
  rintro ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hac, hbd⟩
  refine (involutionGraph_statedSU hF).2.1 ⟨tauLine h hF a, tauLine h hF b, tauLine h hF c,
    tauLine h hF d, hnd.map tauLine_injective, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (adj_tauLine_iff h hF a b).mpr ⟨hab.ne, hab⟩
  · exact (adj_tauLine_iff h hF b c).mpr ⟨hbc.ne, hbc⟩
  · exact (adj_tauLine_iff h hF c d).mpr ⟨hcd.ne, hcd⟩
  · exact (adj_tauLine_iff h hF d a).mpr ⟨hda.ne, hda⟩
  · exact fun hadj => hac ((adj_tauLine_iff h hF a c).mp hadj).2
  · exact fun hadj => hbd ((adj_tauLine_iff h hF b d).mp hadj).2

theorem not_exists_orth_pentagon (hF : Nat.card F = 9) :
    ¬ ∃ a b c d e : NonisoLine F, [a, b, c, d, e].Nodup ∧ Orth a b ∧ Orth b c ∧ Orth c d ∧
      Orth d e ∧ Orth e a ∧ ¬ Orth a c ∧ ¬ Orth a d ∧ ¬ Orth b d ∧ ¬ Orth b e ∧ ¬ Orth c e := by
  have h := unitaryFieldData_of_card hF
  rintro ⟨a, b, c, d, e, hnd, hab, hbc, hcd, hde, hea, hac, had, hbd, hbe, hce⟩
  refine (involutionGraph_statedSU hF).2.2 ⟨tauLine h hF a, tauLine h hF b, tauLine h hF c,
    tauLine h hF d, tauLine h hF e, hnd.map tauLine_injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (adj_tauLine_iff h hF a b).mpr ⟨hab.ne, hab⟩
  · exact (adj_tauLine_iff h hF b c).mpr ⟨hbc.ne, hbc⟩
  · exact (adj_tauLine_iff h hF c d).mpr ⟨hcd.ne, hcd⟩
  · exact (adj_tauLine_iff h hF d e).mpr ⟨hde.ne, hde⟩
  · exact (adj_tauLine_iff h hF e a).mpr ⟨hea.ne, hea⟩
  · exact fun hadj => hac ((adj_tauLine_iff h hF a c).mp hadj).2
  · exact fun hadj => had ((adj_tauLine_iff h hF a d).mp hadj).2
  · exact fun hadj => hbd ((adj_tauLine_iff h hF b d).mp hadj).2
  · exact fun hadj => hbe ((adj_tauLine_iff h hF b e).mp hadj).2
  · exact fun hadj => hce ((adj_tauLine_iff h hF c e).mp hadj).2

theorem finite_nonisoLine (hF : Nat.card F = 9) : Finite (NonisoLine F) :=
  Nat.finite_of_card_ne_zero (by rw [card_nonisoLine hF]; norm_num)

theorem finite_hexLine (hF : Nat.card F = 9) : Finite (HexLine F) := by
  have := finite_nonisoLine hF
  exact Subtype.finite

theorem ncard_lines_through (hF : Nat.card F = 9) (p : NonisoLine F) :
    {T : HexLine F | p ∈ T.1}.ncard = 3 := by
  classical
  have := finite_nonisoLine hF
  have := finite_hexLine hF
  have := Fintype.ofFinite (NonisoLine F)
  have := Fintype.ofFinite (HexLine F)
  set s : Finset (NonisoLine F) := Finset.univ.filter fun q => Orth p q with hs
  set t : Finset (HexLine F) := Finset.univ.filter fun T => p ∈ T.1 with ht
  have hs6 : s.card = 6 := by
    rw [← ncard_orth hF p, ← Set.ncard_coe_finset, hs, Finset.coe_filter]
    simp only [Finset.mem_univ, true_and]
  have hm : ∀ q ∈ s, (t.bipartiteAbove (fun q T => q ∈ T.1) q).card = 1 := by
    intro q hq
    have hpq : Orth p q := (Finset.mem_filter.mp hq).2
    obtain ⟨T, hpT, hqT⟩ := exists_line hF hpq
    rw [Finset.card_eq_one]
    refine ⟨T, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun T' hT' => ?_⟩⟩
    · rw [Finset.mem_bipartiteAbove, ht, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ T, hpT⟩, hqT⟩
    · rw [Finset.mem_bipartiteAbove, ht, Finset.mem_filter] at hT'
      exact eq_of_mem_of_mem hF hpq.ne hT'.1.2 hT'.2 hpT hqT
  have hn : ∀ T ∈ t, (s.bipartiteBelow (fun q T => q ∈ T.1) T).card = 2 := by
    intro T hT
    have hpT : p ∈ T.1 := (Finset.mem_filter.mp hT).2
    have heq : s.bipartiteBelow (fun q T => q ∈ T.1) T = T.1.erase p := by
      ext q
      rw [Finset.mem_bipartiteBelow, hs, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hpq⟩, hqT⟩
        exact ⟨hpq.ne.symm, hqT⟩
      · rintro ⟨hqp, hqT⟩
        exact ⟨⟨Finset.mem_univ q, orth_of_mem T hpT hqT (Ne.symm hqp)⟩, hqT⟩
    rw [heq, Finset.card_erase_of_mem hpT, T.2.1]
  have hdc := Finset.card_mul_eq_card_mul (fun (q : NonisoLine F) (T : HexLine F) => q ∈ T.1)
    hm hn
  rw [hs6] at hdc
  have hset : {T : HexLine F | p ∈ T.1} = (t : Set (HexLine F)) := by
    ext T
    simp [ht]
  rw [hset, Set.ncard_coe_finset]
  omega

theorem card_hexLine (hF : Nat.card F = 9) : Nat.card (HexLine F) = 63 := by
  classical
  have := finite_nonisoLine hF
  have := finite_hexLine hF
  have := Fintype.ofFinite (NonisoLine F)
  have := Fintype.ofFinite (HexLine F)
  have hm : ∀ p ∈ (Finset.univ : Finset (NonisoLine F)),
      ((Finset.univ : Finset (HexLine F)).bipartiteAbove (fun p T => p ∈ T.1) p).card = 3 := by
    intro p _
    refine Eq.trans ?_ (ncard_lines_through hF p)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext T
    simp
  have hn : ∀ T ∈ (Finset.univ : Finset (HexLine F)),
      ((Finset.univ : Finset (NonisoLine F)).bipartiteBelow (fun p T => p ∈ T.1) T).card = 3 := by
    intro T _
    refine Eq.trans ?_ T.2.1
    congr 1
    ext q
    simp [Finset.mem_bipartiteBelow]
  have hdc := Finset.card_mul_eq_card_mul (fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1)
    hm hn
  rw [Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, card_nonisoLine hF] at hdc
  omega

end CFSG.LinearGroups.UnitaryThreeOverNine
