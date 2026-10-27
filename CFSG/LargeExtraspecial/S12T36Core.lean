module

public import CFSG.LargeExtraspecial.S12FourteenMain
public import CFSG.RankThree.Literature.FSmithTheorem2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def FSmith1977cOmegaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 4 ≤ S.width →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
    S.width = 4 ∧ ∃ W : Submodule (ZMod 2) S.Qt,
      2 * finrank (ZMod 2) W = finrank (ZMod 2) S.Qt ∧ ∀ v ∈ W, S.q v = 0

namespace S12T36

theorem card_omegaGroup_eq_of_dvd_two_mul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {V' : Type*}
    [AddCommGroup V'] [Module (ZMod 2) V'] [FiniteDimensional (ZMod 2) V']
    {Q' : QuadraticForm (ZMod 2) V'} (hQ : (polarBilin Q).Nondegenerate)
    (hQ' : (polarBilin Q').Nondegenerate) {m : ℕ} (hm : 2 ≤ m)
    (hV : finrank (ZMod 2) V = 2 * m) (hV' : finrank (ZMod 2) V' = 2 * m)
    (h : Nat.card (omegaGroup Q' hQ') ∣ 2 * Nat.card (omegaGroup Q hQ)) :
    Nat.card (omegaGroup Q' hQ') = Nat.card (omegaGroup Q hQ) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite V' := Module.finite_of_finite (ZMod 2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Nontrivial V' := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite (V' ≃ₗ[ZMod 2] V') :=
    Finite.of_injective (fun g : V' ≃ₗ[ZMod 2] V' => (g : V' → V'))
      fun _ _ e => LinearEquiv.ext (congrFun e)
  obtain ⟨k, hk⟩ := h
  have e1 := S12DW.card_orthogonalGroup_mul_ncard_eq hQ hV
  have e2 := S12DW.card_orthogonalGroup_mul_ncard_eq hQ' hV'
  rw [S12DW.card_orthogonalGroup_eq hQ, S12DW.ncard_eq_zero_eq, S12DW.natCard_eq_four_pow hV,
    hk] at e1
  rw [S12DW.card_orthogonalGroup_eq hQ', S12DW.ncard_eq_zero_eq,
    S12DW.natCard_eq_four_pow hV'] at e2
  have hc := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (S12DW.polar_eq_zero_imp hQ) (S12DW.natCard_eq_four_pow hV)
  have hc' := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q'
    (S12DW.polar_eq_zero_imp hQ') (S12DW.natCard_eq_four_pow hV')
  set N := {v | Q v = 1}.ncard
  set N' := {v | Q' v = 1}.ncard
  set w := Nat.card (omegaGroup Q' hQ')
  have hpos : 0 < w := Nat.card_pos
  set a := 2 ^ m with ha
  have ha4 : 4 ≤ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have ha2 : 2 ∣ a := dvd_pow_self 2 (by omega)
  have hA : 4 ^ m = a * a := by rw [ha, ← mul_pow]; norm_num
  rw [hA] at hc hc' e1 e2
  have h4a : 4 * a ≤ a * a := Nat.mul_le_mul_right a ha4
  set s := a * a - N with hs
  set s' := a * a - N' with hs'
  have hkey : k * s = 2 * s' := by
    have e3 : w * (k * s) = w * (2 * s') :=
      calc w * (k * s) = w * k * s := by ring
        _ = _ := e1
        _ = w * (2 * s') := by rw [← e2]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  have hspos : 0 < s := by omega
  have hNN : N = N' := by
    by_contra hne
    rcases hc with h1 | h1 <;> rcases hc' with h2 | h2
    · omega
    ·
      have h3 : k * (a * a + a) = 2 * (a * a - a) := by
        calc k * (a * a + a) = k * (2 * s) := by congr 1; omega
          _ = 2 * (k * s) := by ring
          _ = 2 * (2 * s') := by rw [hkey]
          _ = 2 * (a * a - a) := by congr 1; omega
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with hk0 | hk0 | hk0
      · subst hk0
        omega
      · subst hk0
        omega
      · have := Nat.mul_le_mul_right (a * a + a) hk0
        omega
    ·
      have h3 : k * (a * a - a) = 2 * (a * a + a) := by
        calc k * (a * a - a) = k * (2 * s) := by congr 1; omega
          _ = 2 * (k * s) := by ring
          _ = 2 * (2 * s') := by rw [hkey]
          _ = 2 * (a * a + a) := by congr 1; omega
      rcases (show k ≤ 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with hk0 | hk0 | hk0 | hk0
      · have := Nat.mul_le_mul_right (a * a - a) hk0
        omega
      · subst hk0
        have h5 : a * a = 5 * a := by omega
        have : a = 5 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < a) h5
        omega
      · subst hk0
        omega
      · have := Nat.mul_le_mul_right (a * a - a) hk0
        omega
    · omega
  have hk2 : k = 2 := by
    have : k * s = 2 * s := by rw [hkey, hs', ← hNN]
    exact Nat.eq_of_mul_eq_mul_right hspos this
  rw [hk2] at hk
  omega

end S12T36

namespace Setting

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)

theorem Mbar_ne_top (hw : 3 ≤ S.width) : S.Mbar ≠ ⊤ := by
  intro htop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : ∃ x y : G, x * y ≠ y * x := by
    by_contra! hall
    have hc : center S.Q = ⊤ := eq_top_iff.mpr fun x _ =>
      mem_center_iff.mpr fun y => Subtype.ext (Subtype.ext (hall ((y : S.M) : G) (x : S.M)))
    have h2 := S.extraspecial.2.2.2
    rw [hc, Subgroup.card_top, S.card_Q_eq] at h2
    have : 2 ^ 7 ≤ 2 ^ (1 + 2 * S.width) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hchar : CFSG.IsCharacteristicP 2 S.M := by
    change centralizer (CFSG.pCore 2 S.M : Set S.M) ≤ CFSG.pCore 2 S.M
    rw [← S.Q_eq_pCore]
    exact S.centralizer_le
  have hQF : S.Q = CFSG.generalizedFitting S.M := by
    rw [(CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore S.M 2).mp hchar]
    exact S.Q_eq_pCore
  have hΩ : _root_.commutator S.O ≤ S.Mbar := by
    rw [htop]
    exact le_top
  have heq : S.Mbar = _root_.commutator S.O :=
    (CFSG.RankThree.Literature.FSmith.fsmith_theorem_two hG S.orderOf_z hQF S.extraspecial
      S.card_Q_eq hw S.normal hΩ).2
  have h6 : 6 ≤ finrank (ZMod 2) S.Qt := by rw [S.finrank_Qt_eq_two_mul_width]; omega
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hidx := relIndex_omegaGroup S.q S.q_nondegenerate
  have hcomm := CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_subgroupOf
    S.q_nondegenerate h6
  rw [Subgroup.relIndex, ← hcomm, ← heq, htop, Subgroup.index_top] at hidx
  exact absurd hidx (by norm_num)

theorem Mbar_map_eq_timmesfeldOmega (hn : 3 ≤ S.width)
    {q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2)} (hq : timmesfeldNondegenerate q)
    (h : Nonempty (S.Mbar ≃* timmesfeldOmega q) ∨ Nonempty (S.Mbar ≃* timmesfeldIsometries q)) :
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q := by
  have hq' := s12_polarBilin_nondegenerate hq
  have hfinV : finrank (ZMod 2) (Fin (2 * S.width) → ZMod 2) = 2 * S.width :=
    Module.finrank_fin_fun _
  have hfinQ : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Nontrivial (Fin (2 * S.width) → ZMod 2) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hOq := S12DW.card_orthogonalGroup_eq hq'
  have hOQ : Nat.card S.O = 2 * Nat.card (omegaGroup S.q S.q_nondegenerate) :=
    S12DW.card_orthogonalGroup_eq S.q_nondegenerate
  have hM : Nat.card S.Mbar = Nat.card (omegaGroup q hq') ∨
      Nat.card S.Mbar = 2 * Nat.card (omegaGroup q hq') := by
    rcases h with h | h
    · obtain ⟨φ⟩ := h
      left
      rw [Nat.card_congr φ.toEquiv, s12_timmesfeldOmega_eq q hq']
    · obtain ⟨φ⟩ := h
      right
      rw [Nat.card_congr φ.toEquiv, s12_timmesfeldIsometries_eq, hOq]
  have hdvd : Nat.card (omegaGroup q hq') ∣ 2 * Nat.card (omegaGroup S.q S.q_nondegenerate) := by
    rw [← hOQ]
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card S.Mbar)
    rcases hM with hM | hM
    · exact hM ▸ dvd_rfl
    · exact hM ▸ dvd_mul_left _ _
  have hΩ := S12T36.card_omegaGroup_eq_of_dvd_two_mul S.q_nondegenerate hq' (by omega) hfinQ
    hfinV hdvd
  rcases hM with hM | hM
  ·
    have hidx : S.Mbar.index = 2 := by
      have h1 := Subgroup.card_mul_index S.Mbar
      rw [hM, hΩ, hOQ] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans (mul_comm _ _))
    have : S.Mbar.Normal := Subgroup.normal_of_index_eq_two hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcardq : Nat.card (S.O ⧸ S.Mbar) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have : IsCyclic (S.O ⧸ S.Mbar) := isCyclic_of_prime_card hcardq
    have hcomm : _root_.commutator S.O ≤ S.Mbar :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative
    rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_subgroupOf
      S.q_nondegenerate (by omega)] at hcomm
    have hle : omegaGroup S.q S.q_nondegenerate ≤ S.Mbar.map S.O.subtype := fun g hg =>
      ⟨⟨g, omegaGroup_le S.q S.q_nondegenerate hg⟩, hcomm hg, rfl⟩
    have hcard : Nat.card (S.Mbar.map S.O.subtype) = Nat.card S.Mbar :=
      (Nat.card_congr (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).toEquiv).symm
    rw [s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
    exact (Subgroup.eq_of_le_of_card_ge hle (hcard.trans (hM.trans hΩ)).le).symm
  ·
    exfalso
    refine S.Mbar_ne_top hn (Subgroup.eq_top_of_card_eq _ ?_)
    rw [hM, hΩ, hOQ]

end Setting

theorem timmesfeld36Input_of (h : FSmith1977cOmegaInput) : Timmesfeld36Input := by
  intro G _ _ _ S hn ⟨q, hq, hiso⟩
  have hM := S.Mbar_map_eq_timmesfeldOmega (by omega) hq hiso
  obtain ⟨h4, hW⟩ := h G S hn hM
  exact ⟨h4, hW, hM⟩

end CFSG.LargeExtraspecial
