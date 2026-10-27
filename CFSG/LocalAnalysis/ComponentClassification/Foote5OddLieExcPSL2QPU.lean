module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Odd
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Even

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem sixteen_dvd_card_of_lieModel_psp_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : LieModel X .PSp 2 p f) :
    16 ∣ Nat.card X := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hadm : StatedLieAdmissible .PSp 2 p f :=
    ⟨hp, hf, le_rfl, fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      rw [h] at hodd
      exact absurd hodd (by decide)⟩
  obtain ⟨-, hc, -⟩ := hO X .PSp 2 p f hadm hX
  have hc' : Nat.card X * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1) := hc
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at hc'
  generalize hQ : p ^ f = Q at hc' hodd
  have hQ1 : 1 ≤ Q := hodd.pos
  have hg : Nat.gcd 2 (Q - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hc'' : Nat.card X * 2 = Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by
    rw [hg] at hc'
    exact hc'
  have h8 : 8 ∣ Q ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hodd
  have h16 : 16 ∣ Q ^ 4 - 1 := by
    have h4 : Q ^ 4 - 1 = (Q ^ 2 - 1) * (Q ^ 2 + 1) := by
      have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
      have h2 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ1
      zify [h1, h2]
      ring
    rw [h4]
    exact Nat.mul_dvd_mul h8 (even_iff_two_dvd.mp hodd.pow.add_one)
  have h128 : 128 ∣ Nat.card X * 2 := by
    rw [hc'']
    exact Dvd.dvd.mul_left (Nat.dvd_trans (by norm_num) (Nat.mul_dvd_mul h8 h16)) _
  omega

theorem false_of_lieModel_psp_two_of_twistedG2 (hO : LieOrderFormulasInput) {M : Type}
    [Group M] [Finite M] (hZ2 : IsPGroup 2 (center M)) {L : Subgroup M}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) {p' f' : ℕ} (hp' : p'.Prime) (hp'2 : p' ≠ 2)
    (hf' : 1 ≤ f') (hLm : LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f') {r e : ℕ}
    (hS : ReeTitsModel (M ⧸ center M) .twistedG2 r e) : False := by
  have hs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases hLm with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 p' f' h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hZL := center_eq_bot_of_isQuasisimple_of_isSimpleGroup hLq hs
  have hinj : Function.Injective ((QuotientGroup.mk' (center M)).comp L.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun l hl => ?_
    have hlZ : (l : M) ∈ center M := (QuotientGroup.eq_one_iff (l : M)).1 hl
    obtain ⟨k, hk⟩ := hZ2 ⟨_, hlZ⟩
    refine eq_one_of_mem_center_of_center_quot_eq_bot hZL hlZ (k := k) ?_
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
    exact h1
  have hdvd1 : Nat.card ↥L ∣ Nat.card (M ⧸ center M) := Subgroup.card_dvd_of_injective _ hinj
  have hdvd2 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card ↥L :=
    Subgroup.card_quotient_dvd_card _
  have h16 := sixteen_dvd_card_of_lieModel_psp_two hO hp' hp'2 hf' hLm
  obtain rfl : r = 3 := hS.1.2.2.2.1
  exact not_sixteen_dvd_card_of_lieModel_twistedG2 hO hS.1
    (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hS⟩))) (h16.trans (hdvd2.trans hdvd1))

theorem cfQPUJExc_holds :
    GSThmB.CFQPUJExc := by
  intro M _ _ p' f' p f hc hexc
  obtain ⟨-, hZ2, hp', hp'2, hf', -, hp, -, -, h5, -, -, E, L, t, J, J₀, -, hLE, hLc, -, hLm, -,
    htt, htZ, hJle, hJc, hJm, -⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eJ : ↥J ≃* ↥(J.subgroupOf (centralizer ({t} : Set M))) :=
    (Subgroup.subgroupOfEquivOfLe hJle).symm
  have hJm' : LieModel (↥(J.subgroupOf (centralizer ({t} : Set M))) ⧸
      pPrimeCore 2 ↥(J.subgroupOf (centralizer ({t} : Set M)))) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm
  rcases hexc with ⟨τ, r, e, hτ, hm⟩ | ⟨τ, r, e, hτ, hm⟩ | ⟨r, e, hm⟩
  ·
    by_cases hr2 : r = 2
    · subst hr2
      exact false_of_even_exceptional hZ2 (Or.inl ⟨τ, e, hτ, hm⟩) htt htZ hJc hJm'
    · exact noPSLTwoOddCentreComponent_of_mem hτ M hZ2 r e hm.1.1 hr2 hm.1
        (Or.inr (Or.inl ⟨rfl, hτ, hm⟩)) t htt htZ _ hJc p f hp h5 hJm'
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    ·
      let eL : ↥(L.subgroupOf (GSThmB.QPUJ.autFixed E)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLE
      obtain ⟨-, -, hq⟩ :=
        (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 hLc
      have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) hq
      exact false_of_lieModel_psp_two_of_twistedG2 lieOrderFormulasInput hZ2 hLq hp' hp'2 hf'
        hLm hm
    · exact false_of_even_exceptional hZ2 (Or.inr (Or.inl ⟨r, e, Or.inl hm⟩)) htt htZ hJc hJm'
    · exact false_of_even_exceptional hZ2 (Or.inr (Or.inl ⟨r, e, Or.inr hm⟩)) htt htZ hJc hJm'
  · exact false_of_even_exceptional hZ2 (Or.inr (Or.inr ⟨r, e, hm⟩)) htt htZ hJc hJm'

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
