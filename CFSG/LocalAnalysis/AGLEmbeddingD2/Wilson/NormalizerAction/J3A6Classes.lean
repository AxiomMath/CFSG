module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27Classes
public import Certificates.Certificate12624

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.Asc83Table
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

section Main


set_option linter.unusedSectionVars false

theorem evalW_mem_closure' {m : ℕ} {G : Type*} [Group G] (g : Fin m → G)
    (w : List (Fin m × Bool)) :
    CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW g w ∈
      Subgroup.closure (Set.range g) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    have : CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW g (x :: w) =
        (cond x.2 (g x.1) (g x.1)⁻¹) *
          CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW g w := by
      simp [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW]
    rw [this]
    refine Subgroup.mul_mem _ ?_ ih
    cases x.2
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨x.1, rfl⟩)
    · exact Subgroup.subset_closure ⟨x.1, rfl⟩

@[irreducible] noncomputable def uu : Equiv.Perm (Fin 6156) := evalW j3tD j3tWu

@[irreducible] noncomputable def vv : Equiv.Perm (Fin 6156) := evalW j3tD j3tWv

theorem rep_uu : Rep 6156 (evalWA 6156 j3tDGens j3tWu) uu := by
  unfold uu; exact rep_evalWA_j3tD j3tWu

theorem rep_vv : Rep 6156 (evalWA 6156 j3tDGens j3tWv) vv := by
  unfold vv; exact rep_evalWA_j3tD j3tWv

theorem uu_pow3 : uu ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_uu 3) rep_idA).1 Certificates.certificate12624.1

theorem vv_pow3 : vv ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_vv 3) rep_idA).1 Certificates.certificate12624.2.1

theorem uu_comm_vv : Commute uu vv := by
  unfold uu vv
  exact j3t_det.2.2

theorem uu_mem : uu ∈ Subgroup.closure (Set.range j3tD) := by
  unfold uu; exact evalW_mem_closure' _ _

theorem vv_mem : vv ∈ Subgroup.closure (Set.range j3tD) := by
  unfold vv; exact evalW_mem_closure' _ _

@[expose] noncomputable def uvEl (m : ℕ) : Equiv.Perm (Fin 6156) := uu ^ (m / 3) * vv ^ (m % 3)

theorem rep_uvEl (m : ℕ) : Rep 6156 (Certificates.j3uvElt m) (uvEl m) :=
  rep_compA (rep_powArr rep_uu _) (rep_powArr rep_vv _)

theorem uvEl_ne {m m' : ℕ} (hm : m < 9) (hm' : m' < m) : uvEl m ≠ uvEl m' := by
  have h := Certificates.certificate12624.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  have h1 := h m hm m' hm'
  intro heq
  have := (eqA_iff (rep_uvEl m) (rep_uvEl m')).2 heq
  rw [this] at h1
  exact absurd h1 (by decide)

theorem fixN_uvEl {m : ℕ} (hm : m < 9) (h0 : m ≠ 0) : fixN (uvEl m) = 0 := by
  have h := Certificates.certificate12624.2.2.2
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [card_fixed_eq_j3fix (rep_uvEl m)]
  exact (h m hm).resolve_left h0

theorem uvEl_inj {m m' : ℕ} (hm : m < 9) (hm' : m' < 9) (h : uvEl m = uvEl m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.symm (uvEl_ne hm' hlt)
  · exact heq
  · exact absurd h (uvEl_ne hm hgt)

@[expose] noncomputable def xs : Fin 2 → Equiv.Perm (Fin 6156) := fun i => if i = 0 then uu else vv

theorem xs_pow (i : Fin 2) : xs i ^ 3 = 1 := by
  unfold xs
  split_ifs
  · exact uu_pow3
  · exact vv_pow3

theorem xs_comm (i j : Fin 2) : Commute (xs i) (xs j) := by
  unfold xs
  split_ifs
  · exact Commute.refl _
  · exact uu_comm_vv
  · exact uu_comm_vv.symm
  · exact Commute.refl _

theorem basisProd_xs (a : Fin 2 → ZMod 3) :
    basisProd xs a = uvEl (3 * (a 0).val + (a 1).val) := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have e1 : (3 * (a 0).val + (a 1).val) / 3 = (a 0).val := by omega
  have e2 : (3 * (a 0).val + (a 1).val) % 3 = (a 1).val := by omega
  rw [uvEl, e1, e2]
  simp [basisProd, List.ofFn_succ, xs]

theorem xs_inj : Function.Injective (basisProd xs) := by
  intro a b h
  rw [basisProd_xs, basisProd_xs] at h
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have g0 := ZMod.val_lt (b 0)
  have g1 := ZMod.val_lt (b 1)
  have := uvEl_inj (by omega) (by omega) h
  funext i
  fin_cases i
  · exact ZMod.val_injective 3 (by simp only [Fin.zero_eta]; omega)
  · exact ZMod.val_injective 3 (by simp only [Fin.mk_one]; omega)

theorem exists_sylow_S :
    ∃ S : Subgroup (Equiv.Perm (Fin 6156)), S ≤ Subgroup.closure (Set.range j3tD) ∧
      Nat.card S = 9 ∧ ∀ y ∈ S, y ≠ 1 → fixN y = 0 := by
  refine ⟨Subgroup.closure (Set.range xs), ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    unfold xs
    split_ifs
    · exact uu_mem
    · exact vv_mem
  · rw [card_closure_basis xs_pow xs_comm xs_inj]; norm_num
  · intro y hy hy1
    obtain ⟨a, ha⟩ := basisHom_surjective xs_pow xs_comm ⟨y, hy⟩
    have hya : y = basisProd xs (Multiplicative.toAdd a) := by
      rw [← coe_basisHom xs_pow xs_comm, ha]
    have h0 := ZMod.val_lt (Multiplicative.toAdd a 0)
    have h1 := ZMod.val_lt (Multiplicative.toAdd a 1)
    rw [hya, basisProd_xs] at hy1 ⊢
    have hm : 3 * (Multiplicative.toAdd a 0).val + (Multiplicative.toAdd a 1).val ≠ 0 := by
      intro h0'
      rw [h0'] at hy1
      apply hy1
      simp [uvEl]
    exact fixN_uvEl (by omega) hm

theorem fixN_zero_of_mem_D {y : Equiv.Perm (Fin 6156)}
    (hy : y ∈ Subgroup.closure (Set.range j3tD)) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) : fixN y = 0 := by
  obtain ⟨S, hSD, hS9, hSfix⟩ := exists_sylow_S
  set D : Subgroup (Equiv.Perm (Fin 6156)) := Subgroup.closure (Set.range j3tD) with hD
  have hD360 : Nat.card D = 360 := j3t_derived.2
  have hfac : (Nat.card D).factorization 3 = 2 := by
    rw [hD360, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num]
    exact factorization_pow_mulG Nat.prime_three (by norm_num)
  have hS'9 : Nat.card (S.subgroupOf D) = 3 ^ (Nat.card D).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSD).toEquiv, hS9, hfac]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ss : Sylow 3 ↥D := Sylow.ofCard (S.subgroupOf D) hS'9
  set y' : ↥D := ⟨y, hy⟩ with hy'
  have hy'3 : orderOf y' = 3 := by
    have h3 : y' ^ 3 = 1 := Subtype.ext hy3
    have h1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    exact orderOf_eq_prime h3 h1
  have hp : IsPGroup 3 (Subgroup.zpowers y') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy'3]; norm_num
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥D P Ss
  have hyP : y' ∈ (P : Subgroup ↥D) := hP (Subgroup.mem_zpowers y')
  have hmem : (MulAut.conj g) y' ∈ (Ss : Subgroup ↥D) := by
    have h1 : (MulAut.conj g) y' ∈ (g • P : Sylow 3 ↥D) := by
      have := Set.smul_mem_smul_set (a := MulAut.conj g) (show y' ∈ (P : Set ↥D) from hyP)
      rw [← Sylow.coe_smul] at this
      exact this
    rw [hg] at h1
    exact h1
  have hmemS : (g : Equiv.Perm (Fin 6156)) * y * (g : Equiv.Perm (Fin 6156))⁻¹ ∈ S := by
    have : ((MulAut.conj g) y' : ↥D) ∈ (S.subgroupOf D) := hmem
    exact Subgroup.mem_subgroupOf.1 this
  have hne : (g : Equiv.Perm (Fin 6156)) * y * (g : Equiv.Perm (Fin 6156))⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y = (g : Equiv.Perm (Fin 6156))⁻¹ * ((g : Equiv.Perm (Fin 6156)) * y *
        (g : Equiv.Perm (Fin 6156))⁻¹) * (g : Equiv.Perm (Fin 6156)) := by group
    rw [this, h]; group
  have := hSfix _ hmemS hne
  rwa [fixN_conj] at this

theorem j3_a6_threeElements_class {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {x : Q}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hC : Nat.card (centralizer ({x} : Set Q)) = 1080)
    (I : Subgroup Q) (hI : I ≤ centralizer ({x} : Set Q)) (hperf : ⁅I, I⁆ = I) :
    ∀ y ∈ I, y ≠ 1 → y ^ 3 = 1 → Nat.card (centralizer ({y} : Set Q)) = 243 := by
  set ψ : Q ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  have hord3 : ∀ z : Q, z ^ 3 = 1 → z ≠ 1 → orderOf ((ψ z : ↥j3P) : Equiv.Perm (Fin 6156)) = 3 := by
    intro z hz3 hz1
    have h3 : ((ψ z : ↥j3P) : Equiv.Perm (Fin 6156)) ^ 3 = 1 := by
      have := congrArg (fun w : ↥j3P => (w : Equiv.Perm (Fin 6156)))
        (show ψ z ^ 3 = 1 from (map_pow ψ z 3).symm.trans ((congrArg ψ hz3).trans (map_one _)))
      simpa using this
    have h1 : ((ψ z : ↥j3P) : Equiv.Perm (Fin 6156)) ≠ 1 := by
      intro h
      apply hz1
      exact (map_eq_one_iff _ ψ.injective).1 (Subtype.ext h)
    exact orderOf_eq_prime h3 h1
  obtain ⟨k0, hk0, c, hc, e', he', hxeq⟩ := j3t_fusion (ψ x).2 (hord3 x hx3 hx1)
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x
  have hcXA : c = j3tXA := by
    rcases hc with rfl | hcB
    · rfl
    · exfalso
      have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
      rw [hcB] at hxeq
      have hcard : Nat.card (centralizer ({((ψ x : ↥j3P) : Equiv.Perm (Fin 6156))} :
          Set (Equiv.Perm (Fin 6156))) ⊓ j3P : Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
        rw [hxeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
          ← j3t_caseB.1, j3t_caseB.2]
      rw [hcard2, hcard] at hC
      omega
  subst hcXA
  have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
  set kk : ↥j3P := ⟨k0⁻¹, Subgroup.inv_mem _ hk0⟩ with hkk
  set ρ : Q ≃* ↥j3P := ψ.trans (MulAut.conj kk) with hρ
  have hρapp : ∀ z : Q, ((ρ z : ↥j3P) : Equiv.Perm (Fin 6156)) =
      k0⁻¹ * ((ψ z : ↥j3P) : Equiv.Perm (Fin 6156)) * k0 := by
    intro z; rfl
  have hρx : ((ρ x : ↥j3P) : Equiv.Perm (Fin 6156)) = j3tXA ^ e' := by
    rw [hρapp, hxeq]; group
  set Ip : Subgroup (Equiv.Perm (Fin 6156)) := I.map (j3P.subtype.comp ρ.toMonoidHom) with hIp
  have hIpC : Ip ≤ centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, (ρ z).2⟩
    have hzx := Subgroup.mem_centralizer_singleton_iff.1 (hI hz)
    have : (ρ z : ↥j3P) * ρ x = ρ x * ρ z := by
      rw [← map_mul, ← map_mul, hzx]
    have h2 := congrArg (fun w : ↥j3P => (w : Equiv.Perm (Fin 6156))) this
    simp only [Subgroup.coe_mul] at h2
    rw [hρx] at h2
    have h3 : ((ρ z : ↥j3P) : Equiv.Perm (Fin 6156)) ∈
        centralizer ({j3tXA ^ e'} : Set (Equiv.Perm (Fin 6156))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact h2
    rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.centralizer_pow_eq hA3 he'] at h3
    exact h3
  have hIpperf : ⁅Ip, Ip⁆ = Ip := by
    rw [hIp, ← Subgroup.map_commutator, hperf]
  have hIpD : Ip ≤ Subgroup.closure (Set.range j3tD) := by
    rw [← hIpperf]
    exact (Subgroup.commutator_mono hIpC hIpC).trans j3t_derived.1
  intro y hy hy1 hy3
  have hyD : ((ρ y : ↥j3P) : Equiv.Perm (Fin 6156)) ∈ Subgroup.closure (Set.range j3tD) :=
    hIpD ⟨y, hy, rfl⟩
  have hz3 : ((ρ y : ↥j3P) : Equiv.Perm (Fin 6156)) ^ 3 = 1 := by
    have := congrArg (fun w : ↥j3P => (w : Equiv.Perm (Fin 6156)))
      (show ρ y ^ 3 = 1 from (map_pow ρ y 3).symm.trans ((congrArg ρ hy3).trans (map_one _)))
    simpa using this
  have hz1 : ((ρ y : ↥j3P) : Equiv.Perm (Fin 6156)) ≠ 1 := by
    intro h
    apply hy1
    exact (map_eq_one_iff _ ρ.injective).1 (Subtype.ext h)
  have hfix := fixN_zero_of_mem_D hyD hz1 hz3
  have hzo : orderOf ((ρ y : ↥j3P) : Equiv.Perm (Fin 6156)) = 3 := orderOf_eq_prime hz3 hz1
  rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ρ y]
  exact (card_cent_j3P_of_fix (ρ y).2 hzo).2 hfix

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
