module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

private theorem map_conj_map_conj {X : Type*} [Group X] (A : Subgroup X) (a b : X) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem add_card_le_pRank_of_components {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {A : Subgroup X} {a : ℕ} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ a)
    (s : Finset (Subgroup X))
    (hs : ∀ C ∈ s, CFSG.IsComponent C ∧ A ≤ centralizer (C : Set X) ∧
      ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e) :
    a + s.card ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  classical
  have main : ∀ s : Finset (Subgroup X),
      (∀ C ∈ s, CFSG.IsComponent C ∧ A ≤ centralizer (C : Set X) ∧
        ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e) →
      ∃ B : Subgroup X, A ≤ B ∧ B ≤ A ⊔ s.sup id ∧ IsElemAbelian p B ∧
        Nat.card B = p ^ (a + s.card) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨A, le_rfl, le_sup_left, hA, by rw [Finset.card_empty, add_zero, hAc]⟩
    | insert D s hD ih =>
        intro hs'
        have hs : ∀ C ∈ s, CFSG.IsComponent C ∧ A ≤ centralizer (C : Set X) ∧
            ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e :=
          fun C hC => hs' C (Finset.mem_insert_of_mem hC)
        obtain ⟨B, hAB, hBle, hBab, hBcard⟩ := ih hs
        obtain ⟨hDcomp, hAD, e, heD, hord, hnce⟩ := hs' D (Finset.mem_insert_self D s)
        have hscent : s.sup id ≤ centralizer (D : Set X) := by
          refine Finset.sup_le fun C hC => ?_
          have hCcomp : CFSG.IsComponent C := (hs C hC).1
          have hCD : C ≠ D := fun h => hD (h ▸ hC)
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            ((CFSG.LocalCores.distinct_components_commute hCcomp hDcomp).resolve_left hCD)
        have hBcent : B ≤ centralizer (D : Set X) := hBle.trans (sup_le hAD hscent)
        obtain ⟨hTab, hTcard⟩ := isElemAbelian_sup_zpowers hp hBab hBcard hBcent heD hord hnce
        refine ⟨B ⊔ zpowers e, hAB.trans le_sup_left, ?_, hTab, ?_⟩
        · rw [Finset.sup_insert]
          refine sup_le (hBle.trans (sup_le_sup_left le_sup_right A)) ?_
          exact (Subgroup.zpowers_le.mpr heD).trans (le_sup_left.trans le_sup_right)
        · rw [Finset.card_insert_of_notMem hD, ← Nat.add_assoc]
          exact hTcard
  obtain ⟨B, -, -, hBab, hBcard⟩ := main s hs
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hBab hBcard

theorem conj_pow_injective {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {q : X} {n : ℕ}
    (hq : orderOf q = p ^ n) {C : Subgroup X} (hqC : q ∉ normalizer (C : Set X)) :
    Function.Injective (fun i : Fin p => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) := by
  have key : ∀ a b : Fin p, (a : ℕ) ≤ (b : ℕ) →
      C.map (MulAut.conj (q ^ (a : ℕ))).toMonoidHom =
      C.map (MulAut.conj (q ^ (b : ℕ))).toMonoidHom → a = b := by
    intro a b hab h
    have hq_d_mem : q ^ ((b : ℕ) - (a : ℕ)) ∈ normalizer (C : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h1 : (C.map (MulAut.conj (q ^ (a : ℕ))).toMonoidHom).map
          (MulAut.conj ((q ^ (a : ℕ))⁻¹)).toMonoidHom = C := by
        rw [map_conj_map_conj, inv_mul_cancel, map_one]
        exact Subgroup.map_id C
      have h2 : (C.map (MulAut.conj (q ^ (b : ℕ))).toMonoidHom).map
          (MulAut.conj ((q ^ (a : ℕ))⁻¹)).toMonoidHom =
          C.map (MulAut.conj (q ^ ((b : ℕ) - (a : ℕ)))).toMonoidHom := by
        have hqd : (q ^ (a : ℕ))⁻¹ * q ^ (b : ℕ) = q ^ ((b : ℕ) - (a : ℕ)) := by
          rw [← zpow_natCast q (a : ℕ), ← zpow_natCast q (b : ℕ),
            ← zpow_natCast q ((b : ℕ) - (a : ℕ)), ← zpow_neg, ← zpow_add]
          congr 1
          omega
        rw [map_conj_map_conj, hqd]
      have hconj := congrArg (fun D : Subgroup X =>
        D.map (MulAut.conj ((q ^ (a : ℕ))⁻¹)).toMonoidHom) h
      rw [h1, h2] at hconj
      exact hconj.symm
    by_cases hd0 : (b : ℕ) - (a : ℕ) = 0
    · exact Fin.ext (by omega)
    · exfalso
      have hd : 0 < (b : ℕ) - (a : ℕ) := Nat.pos_of_ne_zero hd0
      have hdp : (b : ℕ) - (a : ℕ) < p := by have := b.2; omega
      have hcop : Nat.Coprime ((b : ℕ) - (a : ℕ)) (p ^ n) := by
        have hpd : Nat.Coprime p ((b : ℕ) - (a : ℕ)) :=
          (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hd hdp)
        exact (Nat.coprime_comm.mp hpd).pow_right n
      have hqmem : q ∈ Subgroup.zpowers (q ^ ((b : ℕ) - (a : ℕ))) := by
        have hcop' : Nat.Coprime (orderOf q) ((b : ℕ) - (a : ℕ)) := by
          rw [hq]
          exact hcop.symm
        have hord_eq : orderOf (q ^ ((b : ℕ) - (a : ℕ))) = orderOf q := by
          rw [orderOf_pow' q (Nat.pos_iff_ne_zero.mp hd), hcop'.gcd_eq_one, Nat.div_one]
        have hle : Subgroup.zpowers (q ^ ((b : ℕ) - (a : ℕ))) ≤ Subgroup.zpowers q :=
          Subgroup.zpowers_le.mpr (by
            simpa using Subgroup.zpow_mem_zpowers q (((b : ℕ) - (a : ℕ) : ℕ) : ℤ))
        haveI : Finite ↥(Subgroup.zpowers q) :=
          (orderOf_pos_iff.mp (by rw [hq]; exact pow_pos hp.pos n)).finite_zpowers
        have hcard : Nat.card (Subgroup.zpowers (q ^ ((b : ℕ) - (a : ℕ)))) =
            Nat.card (Subgroup.zpowers q) := by
          rw [Nat.card_zpowers, Nat.card_zpowers, hord_eq]
        have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
        rw [heq]
        exact Subgroup.mem_zpowers q
      exact hqC (Subgroup.zpowers_le.mpr hq_d_mem hqmem)
  intro i j hij
  rcases le_total (i : ℕ) (j : ℕ) with hle | hle
  · exact key i j hle hij
  · exact (key j i hle hij.symm).symm

theorem centralizer_layer_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hR : CFSG.pCore p (StarGroup p H) = ⊥) :
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) = ⊥ := by
  have h := centralizer_pCore_sup_layer_le hp H
  rw [hR, bot_sup_eq] at h
  exact le_bot_iff.mp h

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
