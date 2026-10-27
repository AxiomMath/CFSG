module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem card_le_of_mulEquiv_mulAut {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p k : ℕ}
    (h : ∀ E : Subgroup (MulAut Y), CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ k)
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have h1 := h (E.map (MulAut.congr e).toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective hinj] at h1

theorem congr_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem meets_inner_of_mulEquiv_mulAut {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : ∀ D : Subgroup (MulAut Y), CFSG.Open.IsElemAbelian p D → Nat.card D = p ^ 2 →
      ∃ x ∈ D ⊓ (MulAut.conj : Y →* MulAut Y).range, x ≠ 1)
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian p D) (hc : Nat.card D = p ^ 2) :
    ∃ x ∈ D ⊓ (MulAut.conj : X →* MulAut X).range, x ≠ 1 := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  obtain ⟨x', hx', hx1⟩ := h (D.map (MulAut.congr e).toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hD _)
    (by rw [Subgroup.card_map_of_injective hinj, hc])
  obtain ⟨hxD, ⟨y, rfl⟩⟩ := Subgroup.mem_inf.1 hx'
  obtain ⟨x, hxD, hxx⟩ := Subgroup.mem_map.1 hxD
  refine ⟨x, Subgroup.mem_inf.2 ⟨hxD, e.symm y, ?_⟩, ?_⟩
  · have h2 : MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
      rw [congr_conj, MulEquiv.apply_symm_apply]
    apply (MulAut.congr e).injective
    refine h2.trans ?_
    exact hxx.symm
  · rintro rfl
    exact hx1 (by rw [← hxx]; exact map_one _)

theorem exists_mulEquiv_projectiveSL {X : Type} [Group X] {n r f : ℕ}
    (hm : StatedClassicalModel X .PSL n r f) :
    ∃ (K : Type) (_ : Field K), Nat.card K = r ^ f ∧ Finite K ∧
      Nonempty (X ≃* projectiveSL n K) := by
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := hm
  exact ⟨K, inferInstance, hK, hfin,
    ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

theorem exists_mulEquiv_primeFormP {X : Type} [Group X] {n r f : ℕ}
    (hm : StatedClassicalModel X .PSU n r f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData r f K),
      ¬(n = 3 ∧ r ^ f = 2) ∧ 3 ≤ n ∧
        Nonempty (X ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hU : UnitaryFieldData r f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ r ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  exact ⟨K, inferInstance, hU, hq, hn3,
    ⟨(e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

theorem card_le_pow_of_psl_model {X : Type} [Group X] {n r f p : ℕ}
    (hm : StatedClassicalModel X .PSL n r f) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (r ^ f - 1)) (E : Subgroup (MulAut X))
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ n := by
  obtain ⟨K, _, hK, hfin, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL hm
  refine card_le_of_mulEquiv_mulAut e (fun E' hE' => ?_) E hE
  exact card_le_pow_projectiveSL hn hp hp2 (by rw [hK]; exact hpg.trans (Nat.gcd_dvd_right _ _)) E'
    hE'

theorem meets_inner_of_psl_model {X : Type} [Group X] {n r f p : ℕ}
    (hm : StatedClassicalModel X .PSL n r f) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (r ^ f - 1)) (hg : ¬ p ^ 2 ∣ Nat.gcd n (r ^ f - 1))
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian p D) (hc : Nat.card D = p ^ 2) :
    ∃ x ∈ D ⊓ (MulAut.conj : X →* MulAut X).range, x ≠ 1 := by
  obtain ⟨K, _, hK, hfin, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL hm
  refine meets_inner_of_mulEquiv_mulAut e (fun D' hD' hc' => ?_) D hD hc
  exact meets_inner_projectiveSL hn hp hp2
    (by rw [hK]; exact hpg.trans (Nat.gcd_dvd_right _ _)) (by rwa [hK]) D' hD' hc'

theorem card_le_pow_of_psu_model {X : Type} [Group X] {n r f p : ℕ}
    (hm : StatedClassicalModel X .PSU n r f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (r ^ f + 1)) (E : Subgroup (MulAut X))
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ n := by
  obtain ⟨K, _, hU, hq, hn, ⟨e⟩⟩ := exists_mulEquiv_primeFormP hm
  refine card_le_of_mulEquiv_mulAut e (fun E' hE' => ?_) E hE
  exact card_le_pow_unitary hU hn hq hp hp2 (hpg.trans (Nat.gcd_dvd_right _ _)) E' hE'

theorem meets_inner_of_psu_model {X : Type} [Group X] {n r f p : ℕ}
    (hm : StatedClassicalModel X .PSU n r f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ Nat.gcd n (r ^ f + 1)) (hg : ¬ p ^ 2 ∣ Nat.gcd n (r ^ f + 1))
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian p D) (hc : Nat.card D = p ^ 2) :
    ∃ x ∈ D ⊓ (MulAut.conj : X →* MulAut X).range, x ≠ 1 := by
  obtain ⟨K, _, hU, hq, hn, ⟨e⟩⟩ := exists_mulEquiv_primeFormP hm
  refine meets_inner_of_mulEquiv_mulAut e (fun D' hD' hc' => ?_) D hD hc
  exact meets_inner_unitary hU hn hq hp hp2 (hpg.trans (Nat.gcd_dvd_right _ _)) hg D' hD' hc'

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
