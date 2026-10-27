module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmSix
public import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

theorem minusPair_of_isAnisoPair {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {a b : V} (h : IsAnisoPair Q a b) : MinusPair Q a b := by
  have ha : Q a ≠ 0 := by
    intro h0
    have := (h.2 1 0 (by rw [one_smul, zero_smul, add_zero, h0])).1
    exact one_ne_zero this
  have hb : Q b ≠ 0 := by
    intro h0
    have := (h.2 0 1 (by rw [zero_smul, one_smul, zero_add, h0])).2
    exact one_ne_zero this
  exact ⟨zmod_two_eq_one_of_ne_zero ha, zmod_two_eq_one_of_ne_zero hb, h.1⟩

theorem exists_frame_minus (m : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * m)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m) :
    ∃ l : List (V × V), IsFrame Q l ∧ l.length = m := by
  induction m using Nat.strong_induction_on generalizing V with
  | _ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      exact ⟨[], IsFrame.nil, rfl⟩
    · by_cases hm1 : m = 1
      · subst hm1
        have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
          intro h
          exact absurd (htype.mp h) (by norm_num)
        haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
        obtain ⟨a, ha0⟩ := exists_ne (0 : V)
        have hQa : Q a = 1 := by
          rcases eq_or_ne (Q a) 0 with h0 | h1
          · exfalso
            apply hminus
            refine ⟨Submodule.span (ZMod 2) {a}, ?_, ?_⟩
            · rw [finrank_span_singleton ha0, hdim]
            · rintro x hx
              rw [Submodule.mem_span_singleton] at hx
              obtain ⟨c, rfl⟩ := hx
              rw [QuadraticMap.map_smul, h0, smul_zero]
          · exact zmod_two_eq_one_of_ne_zero h1
        obtain ⟨b, hb⟩ : ∃ b : V, polar Q a b = 1 := by
          by_contra h
          push Not at h
          have hzero : ∀ y : V, polar Q a y = 0 := fun y =>
            not_not.mp fun h0 => h y (zmod_two_eq_one_of_ne_zero h0)
          exact ha0 (hQ.1 a fun y => by
            simpa [QuadraticMap.polarBilin_apply_apply] using hzero y)
        have hQb : Q b = 1 := by
          rcases eq_or_ne (Q b) 0 with h0 | h1
          · exfalso
            have hb0 : b ≠ 0 := by
              rintro rfl
              rw [polar_zero_right] at hb
              exact zero_ne_one hb
            apply hminus
            refine ⟨Submodule.span (ZMod 2) {b}, ?_, ?_⟩
            · rw [finrank_span_singleton hb0, hdim]
            · rintro x hx
              rw [Submodule.mem_span_singleton] at hx
              obtain ⟨c, rfl⟩ := hx
              rw [QuadraticMap.map_smul, h0, smul_zero]
          · exact zmod_two_eq_one_of_ne_zero h1
        exact ⟨[(a, b)], IsFrame.cons ⟨hQa, hQb, hb⟩ (by intro q hq; simp at hq) IsFrame.nil,
          rfl⟩
      · have hm2 : 2 ≤ m := by omega
        obtain ⟨a, b, hab⟩ := exists_isAnisoPair hQ hdim hm2
        let U : Submodule (ZMod 2) V := orthPerp Q (Submodule.span (ZMod 2) {a, b})
        have hUdim : finrank (ZMod 2) U = 2 * (m - 1) := by
          have hcompl := hab.isCompl_span_orthPerp
          have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
          have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {a, b}) = 2 :=
            hab.finrank_span_pair
          rw [h2, hdim] at h1
          rw [add_comm] at h1
          have h1' : finrank (ZMod 2) U + 2 = 2 * m := by omega
          have h2m : 2 * m = 2 * (m - 1) + 2 := by omega
          rw [h2m] at h1'
          exact Nat.add_right_cancel h1'
        have hUQ : (polarBilin (Q.comp U.subtype)).Nondegenerate :=
          nondegenerate_polarBilin_restrict (polarNondegOn_orthPerp hQ hab.isCompl_span_orthPerp)
        have hpar : Even m ↔ ¬ Even (m - 1) := by
          rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exact ⟨fun _ => by rintro ⟨j, hj⟩; omega, fun _ => ⟨k, by omega⟩⟩
          · exact ⟨fun h => by obtain ⟨j, hj⟩ := h; omega, fun h => by
              exfalso
              apply h
              rw [show 2 * k + 1 - 1 = 2 * k by omega]
              exact ⟨k, by omega⟩⟩
        have htypeU : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp U.subtype) ↔ Even (m - 1) := by
          have hflip := hab.isPlusType_iff_restrict_orthPerp hQ (k := m - 2) (by omega)
          constructor
          · intro hU
            have hnQ : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := fun hQp => (hflip.mp hQp) hU
            have hnm : ¬ Even m := fun he => hnQ (htype.mpr he)
            exact Classical.not_not.mp (hpar.not.mp hnm)
          · intro hUm
            by_contra hU
            exact (hpar.mp (htype.mp (hflip.mpr hU))) hUm
        obtain ⟨l', hl', hlen'⟩ := ih (m - 1) (by omega) (Q := Q.comp U.subtype) hUQ hUdim htypeU
        let l : List (V × V) := (a, b) :: l'.map (fun p : U × U => ((p.1 : V), (p.2 : V)))
        have hl : IsFrame Q l := by
          refine IsFrame.cons (minusPair_of_isAnisoPair hab) ?_ ?_
          · intro q hq
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hq
            have hu : (p.1 : V) ∈ U := p.1.2
            have hv : (p.2 : V) ∈ U := p.2.2
            have ha : a ∈ Submodule.span (ZMod 2) {a, b} :=
              Submodule.subset_span (Set.mem_insert _ _)
            have hb : b ∈ Submodule.span (ZMod 2) {a, b} :=
              Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
            have hua : polar Q a (p.1 : V) = 0 := (mem_orthPerp.1 hu) a ha
            have hub : polar Q b (p.1 : V) = 0 := (mem_orthPerp.1 hu) b hb
            have hva : polar Q a (p.2 : V) = 0 := (mem_orthPerp.1 hv) a ha
            have hvb : polar Q b (p.2 : V) = 0 := (mem_orthPerp.1 hv) b hb
            exact ⟨hua, hva, hub, hvb⟩
          · have hpair : IsFrame Q (l'.map (fun p : U × U => ((p.1 : V), (p.2 : V)))) := by
              refine ⟨?_, ?_⟩
              · intro q hq
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
                obtain ⟨hqa, hqb, hqab⟩ := hl'.pair p hp
                exact ⟨hqa, hqb, hqab⟩
              · refine hl'.perp.map _ ?_
                intro p q hpq
                obtain ⟨h1, h2, h3, h4⟩ := hpq
                exact ⟨h1, h2, h3, h4⟩
            exact hpair
        refine ⟨l, hl, ?_⟩
        change ((a, b) :: l'.map (fun p : U × U => ((p.1 : V), (p.2 : V)))).length = m
        simp only [List.length_cons, List.length_map, hlen']
        omega

theorem exists_frame_five_minus {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ l : List (V × V), IsFrame Q l ∧ l.length = 5 := by
  refine exists_frame_minus 5 hQ hdim ?_
  refine ⟨fun h => absurd h hminus, ?_⟩
  rintro ⟨k, hk⟩
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
