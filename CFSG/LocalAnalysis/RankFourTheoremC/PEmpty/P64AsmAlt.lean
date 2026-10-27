module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmL2p2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmAltRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup
open scoped Nat

namespace P64Asm

theorem not_pow_three_dvd_aut_alt6 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {M : ℕ}
    (h360 : 360 ∣ M) (hle : M ≤ 1440) (hpos : 0 < M) : ¬ p ^ 3 ∣ M := by
  intro h3
  obtain ⟨m, rfl⟩ := h360
  have hm4 : m ≤ 4 := by omega
  have hm0 : 1 ≤ m := by omega
  have hp3 : p ^ 3 ≤ 360 * m := Nat.le_of_dvd hpos h3
  have hp11 : p ≤ 11 := by
    by_contra hcon
    push Not at hcon
    have : 12 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hcon 3
    omega
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 := by
    interval_cases p <;> first | omega | (exfalso; norm_num at hp)
  rcases hcases with rfl | rfl | rfl <;> interval_cases m <;> norm_num at h3

end P64Asm

theorem kdI278Alt_holds : KDI278Alt := by
  intro p hp hp5 Z _ _ K hKn hK hcen hrk Q
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨n, hn5, ⟨e⟩⟩ := hK
  let e' : ↥K ≃* alternatingGroup (Fin n) := e
  let θ : Z →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr e').toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hθ : Function.Injective θ :=
    (MulAut.congr e').injective.comp (P64Asm.conjNormal_injective hcen)
  have hn3 : n < 3 * p := by
    by_contra hge
    push Not at hge
    obtain ⟨E, hEel, hEc⟩ := P64Asm.exists_elemAbelian_alt hp hp2 hge
    have hE'el : IsElemAbelian p ((E.map e'.symm.toMonoidHom).map K.subtype) :=
      IsElemAbelian.map (IsElemAbelian.map hEel _) _
    have hE'c : Nat.card ((E.map e'.symm.toMonoidHom).map K.subtype) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective e'.symm.injective, hEc]
    have := SU1.le_pRank hp.one_lt (le_top : _ ≤ (⊤ : Subgroup Z)) hE'el hE'c
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvd : p ^ k ∣ Nat.card (MulAut (alternatingGroup (Fin n))) := by
    rw [← hk]
    exact (Subgroup.card_subgroup_dvd_card (Q : Subgroup Z)).trans
      (Subgroup.card_dvd_of_injective θ hθ)
  have hk2 : k ≤ 2 := by
    by_cases h6 : n = 6
    · subst h6
      have hle :=
        CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
      haveI : Finite (MulAut (alternatingGroup (Fin 6))) := inferInstance
      have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
      have h360 : 360 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
        have h3 : Nat.card K = 360 := by
          rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
          decide
        have h1 : Nat.card K ∣ Nat.card Z := Subgroup.card_subgroup_dvd_card K
        rw [h3] at h1
        exact h1.trans (Subgroup.card_dvd_of_injective θ hθ)
      by_contra hk3
      push Not at hk3
      exact P64Asm.not_pow_three_dvd_aut_alt6 hp hp5 h360 hle hpos
        ((pow_dvd_pow p hk3).trans hdvd)
    · have hcard : Nat.card (MulAut (alternatingGroup (Fin n))) = n ! := by
        rw [← Nat.card_congr (Equiv.ofBijective _
          (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 h6)),
          Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [hcard] at hdvd
      have h1 : k ≤ padicValNat p (n !) :=
        (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp hdvd
      have hnp : n < p ^ 2 := by nlinarith
      have h2 : padicValNat p (n !) = n / p := by
        rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow (by omega) hnp)]
        simp
      have h3 : n / p < 3 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
      omega
  exact P64Asm.isMulCommutative_of_card_dvd_sq hp (by rw [hk]; exact pow_dvd_pow p hk2)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
