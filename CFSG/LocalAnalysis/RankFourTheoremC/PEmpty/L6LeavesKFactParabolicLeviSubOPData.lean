module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPBlocks

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding Matrix QuadraticMap
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem leviData_plusFlagStab_top (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hrD : r ∈ D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K - 1) : OrthPlusLeviData ↥(plusFlagStab K r D) p := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have ht : D.sup id = r := le_antisymm (Finset.sup_le hD') (Finset.le_sup (f := id) hrD)
  refine orthPlus_leviData_of_sum (ι₁ := ↥D) (ι₂ := Empty)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => Unit) hp (by omega)
    (fun b => slRange K (b.1 - predCut D b.1)) (fun _ => ⊥)
    (fun b => plusEBlockHom hD' b.2) (fun e => e.elim) ?_ ?_ (fun e => e.elim) ?_
    (fun e => e.elim)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    rw [ht] at hx ⊢
    rw [show 2 * r - r = r by omega] at hx
    have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈ plusCutSpace r K r := by
      rw [← flag_eq_plusCutSpace le_rfl, ← smul_flag_of_mem_plusFlagStab g.2 (Or.inr hrD)]
      rw [← flag_eq_plusCutSpace le_rfl] at hx
      exact ⟨x, hx, rfl⟩
    exact sub_mem hgx hx
  · intro b x hx
    obtain ⟨q, h1, h2, -⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    exact ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun e => e.elim⟩
  · intro b g hx hx1
    exact orthPlus_gl_block_data hp h5 hpK hx hx1

theorem leviData_plusFlagStab_res (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht3 : D.sup id + 3 ≤ r) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K - 1) : OrthPlusLeviData ↥(plusFlagStab K r D) p := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  set t := D.sup id with htdef
  have ht : t = 0 ∨ t ∈ D := sup_eq_zero_or_mem D
  have htm : t + (r - t) = r := by omega
  have hm : 3 ≤ r - t := by omega
  have hDt : ∀ d ∈ D, d ≤ t := fun d hd => Finset.le_sup (f := id) hd
  refine orthPlus_leviData_of_sum (ι₁ := ↥D) (ι₂ := Unit)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K)
    (G₂ := fun _ => (Fin (r - t) ⊕ Fin (r - t) → K) ≃ₗ[K] (Fin (r - t) ⊕ Fin (r - t) → K))
    hp (by omega) (fun b => slRange K (b.1 - predCut D b.1))
    (fun _ => orthElementaryGroup (quadPlus (r - t) K))
    (fun b => plusEBlockHom hD' b.2) (fun _ => plusResAut hD' ht htm) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht htm
      (plusResBlockHom_eq_one_of_plusResAut hD' ht htm ((hN g hg).2 ())) hx
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun _ => ?_⟩
    change matrixEquiv (r - t) K (plusResBlockHom hD' ht htm q) = 1
    rw [h3 ht htm (hDt b b.2), map_one]
  · rintro ⟨⟩ h hh
    exact ⟨⟨plusResExt K htm h, plusResExt_mem_plusFlagStab htm hm hDt hh⟩,
      plusResAut_plusResExt hD' ht htm _, fun ⟨⟩ hne => absurd rfl hne,
      fun b => plusEBlockHom_plusResExt hD' htm hDt b.2 _⟩
  · intro b g hx hx1
    exact orthPlus_gl_block_data hp h5 hpK hx hx1
  · intro j g hx hx1
    exact orthPlus_res_block_data hm hp h5 (plusResAut_mem_orthogonalGroup hD' ht htm g) hx hx1

theorem leviData_plusFlagStab_two (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht2 : D.sup id + 2 = r) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K - 1) : OrthPlusLeviData ↥(plusFlagStab K r D) p := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have hDt : ∀ d ∈ D, d ≤ D.sup id := fun d hd => Finset.le_sup (f := id) hd
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩
  have ht : D.sup id = 0 ∨ D.sup id ∈ D := sup_eq_zero_or_mem D
  refine orthPlus_leviData_of_sum (ι₁ := ↥D) (ι₂ := Fin 2)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => GL (Fin 2) K) hp
    (by omega) (fun b => slRange K (b.1 - predCut D b.1)) (fun _ => slRange K 2)
    (fun b => plusEBlockHom hD' b.2) (plusFamHom K hr hD₂ hD' ht ht2) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht ht2 (plusResBlockHom_eq_one_of_plusResAut hD'
      ht ht2 (plusResAut_eq_one_of_plusFamHom hr hD₂ hD' ht ht2 ((hN g hg).2 0)
        ((hN g hg).2 1))) hx
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun j => ?_⟩
    refine plusFamHom_eq_one hr hD₂ hD' ht ht2 ?_ j
    change matrixEquiv 2 K (plusResBlockHom hD' ht ht2 q) = 1
    rw [h3 ht ht2 (hDt b b.2), map_one]
  · intro j x hx
    obtain ⟨A, rfl⟩ := hx
    fin_cases j
    · have hq := plusResExt_iotaTwo_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaTwo hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e0, fun j' hj' => ?_, fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact absurd rfl hj'
      · exact e1
    · have hq := plusResExt_iotaOne_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaOne hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e1, fun j' hj' => ?_, fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact e0
      · exact absurd rfl hj'
  · intro b g hx hx1
    exact orthPlus_gl_block_data hp h5 hpK hx hx1
  · intro j g hx hx1
    exact orthPlus_gl_block_data hp h5 hpK hx hx1

theorem leviData_plusFlagStab (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r)
    (hr1 : r - 1 ∈ D → r ∈ D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K - 1) : OrthPlusLeviData ↥(plusFlagStab K r D) p := by
  have hle : D.sup id ≤ r := Finset.sup_le fun d hd => (hD d hd).2
  rcases sup_eq_zero_or_mem D with h0 | hmem
  · exact leviData_plusFlagStab_res hr hD (by omega) hp h5 hpK
  · by_cases htop : D.sup id = r
    · exact leviData_plusFlagStab_top hr hD (htop ▸ hmem) hp h5 hpK
    · by_cases h1 : D.sup id + 1 = r
      · exfalso
        have := Finset.le_sup (f := id) (hr1 (by rw [← h1, Nat.add_sub_cancel]; exact hmem))
        simp only [id] at this
        omega
      · by_cases h2 : D.sup id + 2 = r
        · exact leviData_plusFlagStab_two hr hD h2 hp h5 hpK
        · exact leviData_plusFlagStab_res hr hD (by omega) hp h5 hpK

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
