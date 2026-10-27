module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniCent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAUniAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open Subgroup

theorem exists_unitaryFieldData {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) :
    ∃ r f : ℕ, q = r ^ f ∧ Nonempty (UnitaryFieldData r f K) := by
  obtain ⟨r, hr⟩ := CharP.exists K
  have hrp : r.Prime := CharP.char_is_prime K r
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm'⟩ := FiniteField.card K r
  have hm : Nat.card K = r ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm'
  have hq2 : q ^ 2 = r ^ (m : ℕ) := hK.symm.trans hm
  have hdvd : q ∣ r ^ (m : ℕ) := hq2 ▸ dvd_pow_self q two_ne_zero
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hrp).1 hdvd
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, pow_zero] at hi
      omega
    · exact h0
  have hmi : (m : ℕ) = 2 * i := by
    have : r ^ (2 * i) = r ^ (m : ℕ) := by rw [← hq2, hi, ← pow_mul, mul_comm]
    exact (Nat.pow_right_injective hrp.two_le this).symm
  exact ⟨r, i, hi, ⟨⟨hrp, hi1, by rw [hm, hmi]⟩⟩⟩

theorem not_pow_omega {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q ^ 2) {ω : Kˣ}
    (hω : orderOf ω = p ^ (q + 1).factorization p) : ∀ b : K, b ^ p ≠ (ω : K) := by
  have ha : 1 ≤ (q + 1).factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpq
  refine not_pow_of_orderOf hp ha hω ?_
  rw [hK]
  intro hd
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      exact absurd (Nat.dvd_one.1 hpq) hp.ne_one
    · omega⟩
  have hfac : (q' + 1) ^ 2 - 1 = q' * (q' + 1 + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have hnp : ¬ p ∣ q' := by
    intro h1
    have h2 : p ∣ (q' + 1 + 1) - q' := Nat.dvd_sub hpq h1
    have h3 : (q' + 1 + 1) - q' = 2 := by omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hcop : Nat.Coprime (p ^ ((q' + 1 + 1).factorization p + 1)) q' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnp)
  rw [hfac] at hd
  have h4 := hcop.dvd_of_dvd_mul_left hd
  exact Nat.pow_succ_factorization_not_dvd (by omega) hp h4

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

theorem mem_gramSU_one_of_stated {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ StatedSU n (r ^ f) K) :
    g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hg' : g ∈ unitarySU r f K n := hg
  rwa [unitarySU_eq_gramSU h n] at hg'

theorem mem_stated_of_mem_gramSU_one {n : ℕ} {g : GL (Fin n) K}
    (hg : g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g ∈ StatedSU n (r ^ f) K := by
  have : g ∈ unitarySU r f K n := by
    rw [unitarySU_eq_gramSU h n]
    exact hg
  exact this

@[expose] noncomputable def statedEquiv {n : ℕ} (hn : 1 ≤ n) :
    StatedProj (StatedSU n (r ^ f) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (unitaryPSUEquiv h hn).symm.trans
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
      ext z
      constructor
      · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
        exact ⟨c, hcN, hcn, hy⟩
      · rintro ⟨c, hcN, hcn, hz⟩
        exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
          MulEquiv.apply_symm_apply _ _⟩))

theorem statedEquiv_mk {n : ℕ} (hn : 1 ≤ n) (g : StatedSU n (r ^ f) K) :
    statedEquiv h hn (QuotientGroup.mk g) =
      (QuotientGroup.mk (⟨(g : GL (Fin n) K), mem_gramSU_one_of_stated h g.2⟩ :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have h1 : (unitaryPSUEquiv h hn).symm (QuotientGroup.mk g) = unitaryProj h n g :=
    (MulEquiv.symm_apply_eq _).2 (unitaryPSUEquiv_unitaryProj h hn g).symm
  unfold statedEquiv
  rw [MulEquiv.trans_apply, h1]
  rfl

variable {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal]

theorem thetaP_eq_conjHom {x : Y} {n : ℕ} (hn : 1 ≤ n)
    (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSU n (r ^ f) K)) (y : GL (Fin n) K)
    (hy : y ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hact : ∀ (g g' : ↥L) (A B : ↥(StatedSU n (r ^ f) K)), x * (g : Y) * x⁻¹ = (g' : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin n) K) = y * (A : GL (Fin n) K) * y⁻¹ →
      e (QuotientGroup.mk g') = QuotientGroup.mk B) :
    thetaP L (e.trans (statedEquiv h hn)) x = primeFormConjHom h _ ⟨y, hy⟩ := by
  ext z
  obtain ⟨w, rfl⟩ := (e.trans (statedEquiv h hn)).surjective z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk g))
  have hmemB : y * (A : GL (Fin n) K) * y⁻¹ ∈ StatedSU n (r ^ f) K :=
    mem_stated_of_mem_gramSU_one h (conj_mem_gramSU h _ hy (mem_gramSU_one_of_stated h A.2))
  set B : ↥(StatedSU n (r ^ f) K) := ⟨y * (A : GL (Fin n) K) * y⁻¹, hmemB⟩ with hB
  have h1 : e (QuotientGroup.mk (MulAut.conjNormal x g)) = QuotientGroup.mk B :=
    hact g (MulAut.conjNormal x g) A B (by simp [MulAut.conjNormal_apply]) hA.symm rfl
  have hL : thetaP L (e.trans (statedEquiv h hn)) x
      ((e.trans (statedEquiv h hn)) (QuotientGroup.mk g)) =
        statedEquiv h hn (e (QuotientGroup.mk (MulAut.conjNormal x g))) := by
    rw [thetaP_apply, MulEquiv.symm_apply_apply, theta_mk]
    rfl
  rw [hL, h1]
  change _ = primeFormConjHom h _ ⟨y, hy⟩ (statedEquiv h hn (e (QuotientGroup.mk g)))
  rw [← hA, statedEquiv_mk, statedEquiv_mk, primeFormConjHom_mk]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem kd292CaseAUni_holds : KD292CaseAUni := by
  intro p Y _ _ P x z L hcfg hzero hmodel T hT2 hxN _ hTL
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hL := hcfg.comp
  have hLu := hcfg.uniq
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hCp : IsPGroup p (centralizer (L : Set Y)) :=
    I292.centralizer_isPGroup hY.core hL hLu hzero.pCore_cyclic hzero.omega_le
  obtain ⟨q, K, instF, instFin, e, ŷ, ω, hK, hpq, hŷu, hŷp, hω, hact⟩ := hmodel
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := exists_unitaryFieldData hK hq2
  have hn3 : 3 ≤ p := by omega
  have hq : ¬(p = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hn1 : 1 ≤ p := hp.one_lt.le
  have hŷ : ŷ ∈ primeFormUnitary hU ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hŷu
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := not_pow_det hp hp2 hŷp' (not_pow_omega hp hp2 hpq hK hω)
  set eP := e.trans (statedEquiv hU hn1) with heP
  have hx : thetaP L eP x = primeFormConjHom hU _ ⟨ŷ, hŷ⟩ :=
    thetaP_eq_conjHom hU hn1 e ŷ hŷ hact
  have hDn : (primeFormD hU ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)).Normal := by
    rw [← ker_primeFormFieldFactor hU isPrimeFormGram_one hn3 hq]
    infer_instance
  set D := primeFormD hU ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hDdef
  have h2elt : ∀ s ∈ T, ∃ k, s ^ (2 ^ k) = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hT2 ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hD : ∀ s ∈ T, thetaP L eP s ∈ D → s = 1 := by
    intro s hs hsD
    obtain ⟨k, hk⟩ := h2elt s hs
    have hα : (thetaP L eP s) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hin := two_elt_mem_inner hU hn3 hq hodd hsD hα
    exact eq_one_of_thetaP_mem_inner L eP hp hp2 hCp hT2 hTL hs hin
  have hxD : thetaP L eP x ∈ D := by
    rw [hx]
    exact ⟨_, rfl⟩
  have hcomm := commute_of_thetaP L eP hxN D hxD hD
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  obtain ⟨k, hk⟩ := h2elt t ht
  have hα : (thetaP L eP t) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hc : thetaP L eP t * primeFormConjHom hU _ ⟨ŷ, hŷ⟩ =
      primeFormConjHom hU _ ⟨ŷ, hŷ⟩ * thetaP L eP t := by
    rw [← hx, ← map_mul, ← map_mul, hcomm t ht]
  have hDt := mem_primeFormD_of_commute hU hn3 hq hodd (y := ⟨ŷ, hŷ⟩) hdet hα hc
  exact hD t ht hDt

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
