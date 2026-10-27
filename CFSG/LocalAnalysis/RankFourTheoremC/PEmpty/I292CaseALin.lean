module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniCent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAIdx
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def KD292LinLangInput : Prop :=
  ∀ (p : ℕ) (K : Type) [Field K] [Finite K], p.Prime → 5 ≤ p →
    ∀ y : GL (Fin p) K, (∀ b : K, b ^ p ≠ (y : Matrix (Fin p) (Fin p) K).det) →
    ∀ T : Subgroup (MulAut (projectiveSL p K)), IsPGroup 2 T → T ⊓ linearAutGroup p K = ⊥ →
      (∀ t ∈ T, t * conjAut p K y = conjAut p K y * t) →
      ∃ R : Subgroup (MulAut (projectiveSL p K)), R ≤ linearAutGroup p K ∧ IsPGroup p R ∧
        ¬ p ∣ R.relIndex (linearAutGroup p K) ∧ ∀ t ∈ T, ∀ r ∈ R, t * r = r * t

theorem kd292CaseALin_of_input (hinp : KD292LinLangInput) : KD292CaseALin := by
  intro p Y _ _ P x z L hcfg hzero hmodel T hT2 hxN hTC hTL
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
  obtain ⟨K, instF, instFin, e, ŷ, ω, hpK, hŷp, hω, hact⟩ := hmodel
  have hn3 : 3 ≤ p := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hKcard : 1 < Nat.card K := Finite.one_lt_card
  have hωnp : ∀ b : K, b ^ p ≠ (ω : K) := by
    have ha : 1 ≤ (Nat.card K - 1).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp (by omega) hpK
    exact not_pow_of_orderOf hp ha hω (Nat.pow_succ_factorization_not_dvd (by omega) hp)
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := not_pow_det hp hp2 hŷp' hωnp
  set eP := e.trans (statedEquivL p K) with heP
  have hx : thetaP L eP x = conjAut p K ŷ := thetaP_eq_conjAut e ŷ hact
  obtain ⟨hDn, hab, -⟩ := lin_structure (K := K) hn3
  set D := linearAutGroup p K with hDdef
  have hkerθ : (thetaP L eP).ker = centralizer (L : Set Y) := by
    ext y
    rw [MonoidHom.mem_ker, thetaP_eq_one_iff]
  have hker_p : IsPGroup p (thetaP L eP).ker := hkerθ ▸ hCp
  have h2elt : ∀ s ∈ T, ∃ k, s ^ (2 ^ k) = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hT2 ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hD : ∀ s ∈ T, thetaP L eP s ∈ D → s = 1 := by
    intro s hs hsD
    obtain ⟨k, hk⟩ := h2elt s hs
    have hα : (thetaP L eP s) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hin := two_elt_mem_inner_lin (K := K) (n := p) hp.one_lt.le hodd hsD hα
    exact eq_one_of_thetaP_mem_inner L eP hp hp2 hCp hT2 hTL hs hin
  have hxD : thetaP L eP x ∈ D := by
    rw [hx]
    exact conjAut_mem_linearAutGroup ŷ
  have hcomm := commute_of_thetaP L eP hxN D hxD hD
  have hTt2 : IsPGroup 2 (T.map (thetaP L eP)) := hT2.map (thetaP L eP)
  have hTtD : T.map (thetaP L eP) ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨t, ht, rfl⟩, hwD⟩
    rw [Subgroup.mem_bot, hD t ht hwD, map_one]
  have hTtc : ∀ w ∈ T.map (thetaP L eP), w * conjAut p K ŷ = conjAut p K ŷ * w := by
    rintro w ⟨t, ht, rfl⟩
    rw [← hx, ← map_mul, ← map_mul, hcomm t ht]
  obtain ⟨R, hRD, hRp, hRidx, hRc⟩ := hinp p K hp hp5 ŷ hdet _ hTt2 hTtD hTtc
  have hIle : inner (projectiveSL p K) ≤ (thetaP L eP).range := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := eP.surjective w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨(l : Y), thetaP_of_mem L eP l⟩
  have hdvd : (inner (projectiveSL p K)).relIndex D ∣ p :=
    (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := p) hp.one_lt.le).trans
      (Nat.gcd_dvd_left _ _)
  have hDS : D ≤ (thetaP L eP).range :=
    le_of_relIndex_dvd_prime hp hIle hdvd (conjAut_mem_linearAutGroup ŷ) ⟨x, hx⟩
      (conjAut_not_mem_inner hn3 ŷ hdet)
  have hperf' : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤ := hcfg.data.perf
  have hDidx := not_dvd_index_comap_of_commutator hp (thetaP L eP) D hab hperf'
  obtain ⟨Q, hQ⟩ := exists_sylow_comap (thetaP L eP) D R hRD hDS hker_p hRp hRidx hDidx
  refine ⟨Q, ?_⟩
  have hTC' : ∀ t ∈ T, ∀ c ∈ (thetaP L eP).ker, t * c = c * t := by
    intro t ht c hc
    rw [hkerθ] at hc
    exact hTC t ht c hc
  have hQ' : ∀ t ∈ T, ∀ q ∈ (Q : Subgroup Y), thetaP L eP t * thetaP L eP q =
      thetaP L eP q * thetaP L eP t := by
    intro t ht q hq
    rw [hQ] at hq
    exact hRc _ ⟨t, ht, rfl⟩ _ hq
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact commute_of_ker_central hp hp2 (thetaP L eP) hker_p hT2 hTC' hQ' t ht q hq

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
