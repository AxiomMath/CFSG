module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4Outer
public import Certificates.Certificate17526
import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec4.Item434D42

theorem noNormalPPrime_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {p : ℕ} {y : G} (h : NoNormalPPrime p (centralizer {e y})) :
    NoNormalPPrime p (centralizer {y}) := by
  intro N hNC hNn hNc
  have hmap : N.map e.toMonoidHom = ⊥ := by
    refine h _ ?_ ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : n * y = y * n := mem_centralizer_singleton_iff.1 (hNC hn)
      rw [mem_centralizer_singleton_iff]
      change e n * e y = e y * e n
      rw [← map_mul, hn', map_mul]
    · rintro g hg _ ⟨n, hn, rfl⟩
      have hg' : e.symm g ∈ centralizer {y} := by
        rw [mem_centralizer_singleton_iff] at hg ⊢
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg]
      refine ⟨e.symm g * n * (e.symm g)⁻¹, hNn _ hg' n hn, ?_⟩
      change e (e.symm g * n * (e.symm g)⁻¹) = g * e n * g⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · rwa [Subgroup.card_map_of_injective e.injective]
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap

theorem evalW_mem_closure {m : ℕ} {gs : Array (Array ℕ)} (hm : m ≤ gs.size) :
    ∀ w : List (Fin m × Bool), CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
      (fun i : Fin m => permOfArr 2457 gs[i.val]!) w ∈ closure (permsA 2457 gs)
  | [] => one_mem _
  | ⟨i, b⟩ :: w => by
    have hi : permOfArr 2457 gs[i.val]! ∈ closure (permsA 2457 gs) :=
      subset_closure ⟨i.val, lt_of_lt_of_le i.2 hm, rfl⟩
    have ih := evalW_mem_closure hm w
    simp only [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW, List.map_cons,
      List.prod_cons] at ih ⊢
    refine mul_mem ?_ ih
    cases b
    · exact inv_mem hi
    · exact hi

theorem of_uFlag {x u : Array ℕ} {X U : Equiv.Perm (Fin 2457)} (hx : Rep 2457 x X)
    (hu : Rep 2457 u U) (h : uFlag 2457 x u = true) :
    U ^ 3 = 1 ∧ U ≠ 1 ∧ U ≠ X ∧ U ≠ X ^ 2 := by
  simp only [uFlag, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨(eqA_iff (rep_powArr hu 3) rep_idA).1 h2, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [(eqA_iff hu rep_idA).2 e] at h1
    exact absurd h1 (by decide)
  · rw [(eqA_iff hu hx).2 e] at h3
    exact absurd h3 (by decide)
  · rw [(eqA_iff hu (rep_powArr hx 2)).2 e] at h4
    exact absurd h4 (by decide)

@[expose] noncomputable def d4UA : Equiv.Perm (Fin 2457) :=
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
    (fun i : Fin 3 => permOfArr 2457 d4CAGens[i.val]!) uWordA

@[expose] noncomputable def d4UB : Equiv.Perm (Fin 2457) :=
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
    (fun i : Fin 5 => permOfArr 2457 d4CBGens[i.val]!) uWordB

theorem localU_spec :
    (d4UA ∈ closure (permsA 2457 d4CAGens) ∧ d4UA ^ 3 = 1 ∧ d4UA ≠ 1 ∧ d4UA ≠ d4X 0 ∧
      d4UA ≠ d4X 0 ^ 2) ∧
    (d4UB ∈ closure (permsA 2457 d4CBGens) ∧ d4UB ^ 3 = 1 ∧ d4UB ≠ 1 ∧ d4UB ≠ d4X 1 ∧
      d4UB ≠ d4X 1 ^ 2) := by
  have h := Certificates.certificate17526
  simp only [localUCheck, Bool.and_eq_true] at h
  have hA := rep_evalWA (m := 3) (gs := d4CAGens)
    (fun k hk => enumOK_gens_valid (centOKP_enum d4_caseA_check) hk) (by simp [d4CAGens]) uWordA
  have hB := rep_evalWA (m := 5) (gs := d4CBGens)
    (fun k hk => enumOK_gens_valid (centOKP_enum d4_caseB_check.2) hk) (by simp [d4CBGens])
    uWordB
  exact ⟨⟨evalW_mem_closure (by simp [d4CAGens]) uWordA,
      of_uFlag (rep_of_validA (d4Lines_valid (by norm_num))) hA h.1⟩,
    ⟨evalW_mem_closure (by simp [d4CBGens]) uWordB,
      of_uFlag (rep_of_validA (d4Lines_valid (by norm_num))) hB h.2⟩⟩

theorem noNormalPPrime_of_local {gs : Array (Array ℕ)} {c : ArrCert} {x : Array ℕ}
    {X : Equiv.Perm (Fin 2457)} (hx : Rep 2457 x X) (hX3 : X ^ 3 = 1) {fuel : ℕ}
    {selfPt pairWit : Array ℕ} (hE : enumOK 2457 gs d4Keys c = true)
    (hloc : localOK 2457 fuel x c.pts selfPt pairWit = true)
    (hC : closure (permsA 2457 gs) = centralizer {X} ⊓ d4P) {U : Equiv.Perm (Fin 2457)}
    (hU : U ∈ closure (permsA 2457 gs) ∧ U ^ 3 = 1 ∧ U ≠ 1 ∧ U ≠ X ∧ U ≠ X ^ 2) {e : ℕ}
    (he : e = 1 ∨ e = 2) (z : ↥d4P) (hz : (z : Equiv.Perm (Fin 2457)) = X ^ e) :
    NoNormalPPrime 3 (centralizer {z}) := by
  obtain ⟨hUC, hU3, hU1, hUX, hUX2⟩ := hU
  intro N hNC hNn hNc
  have hUCP : U ∈ centralizer {X} ⊓ d4P := hC ▸ hUC
  let u : ↥d4P := ⟨U, hUCP.2⟩
  have hu : u ∈ centralizer {z} := by
    have h := mem_fix_of_coe_mem (c := u) hz hUCP.1
    rwa [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj] at h
  have hun : u ∈ normalizer (N : Set ↥d4P) := by
    rw [← fixSub_conj_eq_centralizer] at hNn hu
    exact mem_normalizer_of_mem_fixSub hNn hu
  have hD := eq_bot_of_localOK d4Keys_lt hE hx hloc hUC hU3 hU1 hUX hUX2
    (D := N.map d4P.subtype)
    (by
      rintro _ ⟨n, hn, rfl⟩
      have h := hNC hn
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj] at h
      exact hC ▸ coe_mem_of_mem_fix hX3 he hz h)
    (by
      rw [Subgroup.card_map_of_injective d4P.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNc)
    (Subgroup.le_normalizer_map d4P.subtype ⟨u, hun, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ d4P.subtype_injective).1 hD

theorem noNormalPPrime_centralizer_d4P
    (y : ↥d4P) (hy : orderOf y = 3) : NoNormalPPrime 3 (centralizer {y}) := by
  have hyo : orderOf (y : Equiv.Perm (Fin 2457)) = 3 := by rw [orderOf_coe]; exact hy
  obtain ⟨k, hk, j, hj, e, he, hyk⟩ := exists_conj_rep d4Q_le card_d4Q
    (fun j => permOfArr 2457 d4Lines[j]!) (fun c => permOfArr 2457 d4Lines[c]!)
    (fun j => permOfArr 2457 d4Trans[j]!) (fun j => d4Rec.getD j 0) (r := 31)
    (fun g hg hg3 => d4_lines hg hg3) (fun j hj => d4_trans hj) y.2 hyo
  have hrec : d4Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec d4_lines_check.2.2.2 hj)
  let κ : ↥d4P := ⟨k, hk⟩
  have hz : ((κ⁻¹ * y * κ : ↥d4P) : Equiv.Perm (Fin 2457)) = d4X (d4Rec.getD j 0) ^ e := by
    show k⁻¹ * (y : Equiv.Perm (Fin 2457)) * k = _
    rw [hyk]
    simp only [d4X]
    group
  refine noNormalPPrime_centralizer_of_mulEquiv
    ((MulAut.conj κ⁻¹ : MulAut ↥d4P) : ↥d4P ≃* ↥d4P) ?_
  have hc : ((MulAut.conj κ⁻¹ : MulAut ↥d4P) : ↥d4P ≃* ↥d4P) y = κ⁻¹ * y * κ := by
    rw [MulAut.conj_apply, inv_inv]
  rw [hc]
  obtain ⟨hA, hB⟩ := localU_spec
  rcases (by omega : d4Rec.getD j 0 = 0 ∨ d4Rec.getD j 0 = 1) with h | h
  · rw [h] at hz
    exact noNormalPPrime_of_local (rep_of_validA (d4Lines_valid (by norm_num)))
      (d4X_cube (by norm_num)) (centOKP_enum d4_caseA_check) d4_local_check.1 d4_caseA.1 hA he
      _ hz
  · rw [h] at hz
    exact noNormalPPrime_of_local (rep_of_validA (d4Lines_valid (by norm_num)))
      (d4X_cube (by norm_num)) (centOKP_enum d4_caseB_check.2) d4_local_check.2 d4_caseB.1 hB he
      _ hz

section TriD4Two


theorem isLocallyBalancedAbs_three_one_triD4_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥d4P) :
    IsLocallyBalancedAbs 3 1 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv _ ψ.symm.toEquiv
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) le_rfl K hK σ hσ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  refine isLocallyBalancedAbs_one_of_hom_pGroup (n := 1) Nat.prime_three hinj Θ
    (fun α hα => ?_) (fun g => ?_) (fun x hx3 hx1 => Or.inr ?_)
  · have h : α ∈ Θ.ker := hα
    rw [hker] at h
    exact h
  · rw [pow_one]
    have h := pow_card_eq_one' (x := g)
    rwa [hcard, mul_one] at h
  · by_cases hin : x ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
    · obtain ⟨y, rfl⟩ := hin
      have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hx3, map_one])
      have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
      rw [fixSub_conj_eq_centralizer]
      refine noNormalPPrime_centralizer_of_mulEquiv ψ (noNormalPPrime_centralizer_d4P (ψ y) ?_)
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hy3 hy1
    · exact (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.coreFreeAt_three_D4_outer
        Nat.prime_two (by norm_num) le_rfl hK σ hσ x hx3 hin).1

theorem isLocallyBalancedAbs_three_one_triD42 {q : TauCeti.PrimePower} (hq : IsTwoPow q 1)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
  obtain ⟨φ8, hcard⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8 hq.1 hq.2 hv
  obtain ⟨ψ8⟩ := nonempty_mulEquiv_d4P φ8 hcard
  rw [hq.1, hq.2] at hK hσ
  exact IsLocallyBalancedAbs.of_mulEquiv eK
    (isLocallyBalancedAbs_three_one_triD4_two hK σ hσ (eK.symm.trans ψ8))

theorem bal207LocalBalRow_triD42 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExc3D42 d := by
  rintro p d ⟨rfl, hd⟩
  obtain ⟨q, hv, hq, rfl⟩ := excTriD4_index hd
  exact isLocallyBalancedAbs_three_one_triD42 hq hv

end TriD4Two

end CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

end
