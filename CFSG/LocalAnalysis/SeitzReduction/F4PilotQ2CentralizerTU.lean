module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Generic

variable {G : Type*} [Group G]

theorem mul_pow_mul_inv_pow_mem {Q M : Subgroup G} (hMN : M ≤ normalizer (Q : Set G)) {q m : G}
    (hq : q ∈ Q) (hm : m ∈ M) (k : ℕ) : (q * m) ^ k * (m ^ k)⁻¹ ∈ Q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m ^ k * q * (m ^ k)⁻¹ ∈ Q := (mem_normalizer_iff.1 (hMN (pow_mem hm k)) q).1 hq
    have e : (q * m) ^ (k + 1) * (m ^ (k + 1))⁻¹ =
        ((q * m) ^ k * (m ^ k)⁻¹) * (m ^ k * q * (m ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih h1

theorem odd_orderOf_of_mul_mem {Q M : Subgroup G} (hMN : M ≤ normalizer (Q : Set G))
    (hQM : Q ⊓ M = ⊥) {q m : G} (hq : q ∈ Q) (hm : m ∈ M) (hodd : Odd (orderOf (q * m))) :
    Odd (orderOf m) := by
  have h := mul_pow_mul_inv_pow_mem hMN hq hm (orderOf (q * m))
  rw [pow_orderOf_eq_one, one_mul] at h
  have h1 : (m ^ orderOf (q * m))⁻¹ = 1 := by
    have h2 := mem_inf.2 ⟨h, inv_mem (pow_mem hm (orderOf (q * m)))⟩
    rwa [hQM, mem_bot] at h2
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one (inv_eq_one.1 h1))

theorem commutator_sup_eq_self_of_closure_odd [Finite G] {Q M : Subgroup G} (hQ : IsPGroup 2 Q)
    (hMN : M ≤ normalizer (Q : Set G)) (hM : ⁅M, M⁆ = M) {S : Set G}
    (hSN : ∀ c ∈ S, c ∈ Q ⊔ M) (hSodd : ∀ c ∈ S, Odd (orderOf c)) (hQS : Q ≤ closure S) :
    ⁅Q ⊔ M, Q ⊔ M⁆ = Q ⊔ M := by
  set N := Q ⊔ M with hNdef
  have hcomm : ⁅N, N⁆ = (commutator N).map N.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hMc : M ≤ ⁅N, N⁆ := hM ▸ commutator_mono le_sup_right le_sup_right
  have hSc : ∀ c ∈ S, c ∈ ⁅N, N⁆ := by
    intro c hc
    have hcN := hSN c hc
    have hcN' : c ∈ ((Q ⊔ M : Subgroup G) : Set G) := hcN
    rw [coe_mul_of_right_le_normalizer_left _ _ hMN] at hcN'
    obtain ⟨q, hq, m, hm, hqm⟩ := Set.mem_mul.1 hcN'
    have hqN : q ∈ N := mem_sup_left hq
    have hmN : m ∈ N := mem_sup_right hm
    set f : N →* Abelianization N := Abelianization.of with hf
    have hfm : f ⟨m, hmN⟩ = 1 := by
      have hm' := hMc hm
      rw [hcomm] at hm'
      obtain ⟨m', hm'c, hm'm⟩ := hm'
      rw [show (⟨m, hmN⟩ : N) = m' from Subtype.ext hm'm.symm, ← MonoidHom.mem_ker, hf,
        Abelianization.ker_of]
      exact hm'c
    have hfc : f ⟨c, hcN⟩ = f ⟨q, hqN⟩ := by
      rw [show (⟨c, hcN⟩ : N) = ⟨q, hqN⟩ * ⟨m, hmN⟩ from Subtype.ext hqm.symm, map_mul, hfm,
        mul_one]
    obtain ⟨n, hn⟩ := hQ ⟨q, hq⟩
    have hq2 : q ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h1 : orderOf (f ⟨c, hcN⟩) ∣ 2 ^ n := by
      rw [hfc]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have : (⟨q, hqN⟩ : N) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hq2)
      rw [this, map_one]
    have h2 : orderOf (f ⟨c, hcN⟩) ∣ orderOf c := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have : (⟨c, hcN⟩ : N) ^ orderOf c = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have hcop : Nat.Coprime (2 ^ n) (orderOf c) :=
      Nat.Coprime.pow_left n ((Nat.coprime_two_left).2 (hSodd c hc))
    have hord : orderOf (f ⟨c, hcN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, ← MonoidHom.mem_ker, hf, Abelianization.ker_of] at hord
    rw [hcomm]
    exact ⟨_, hord, rfl⟩
  have hQc : Q ≤ ⁅N, N⁆ := hQS.trans ((closure_le _).2 hSc)
  exact le_antisymm (CFSG.Quasithin.A3.commutator_self_le N) (sup_le hQc hMc)

theorem map_closure_odd_mulAut (α : MulAut G) (M : Subgroup G) :
    (closure {c : G | c ∈ M ∧ Odd (orderOf c)}).map α.toMonoidHom =
      closure {c : G | c ∈ M.map α.toMonoidHom ∧ Odd (orderOf c)} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨d, ⟨hdM, hdo⟩, rfl⟩
    refine ⟨⟨d, hdM, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hdo
  · rintro ⟨⟨d, hdM, rfl⟩, hco⟩
    refine ⟨d, ⟨hdM, ?_⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hco

end Generic

theorem nodesTU_eq_f4MidJ : nodesTU = f4MidJ := by
  ext j
  simp only [nodesTU, f4MidJ, Set.mem_ofPred_eq]
  revert j
  decide

section TU

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def oddB2Levi : Subgroup (adjointGroup .F4 K) :=
  closure {c : adjointGroup .F4 K | c ∈ B2Levi K ∧ Odd (orderOf c)}

variable (K) in
@[expose] def FactOddB2LeviTwo : Prop :=
  ⁅oddB2Levi K, oddB2Levi K⁆ = oddB2Levi K ∧
    ∀ N : Subgroup (oddB2Levi K), N.Normal → IsPGroup 2 N → N = ⊥

theorem perfectCore_centralizer_zTU_two [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hB : FactOddB2LeviTwo K) :
    perfectCore (centralizer ({zT K * zU K} : Set (adjointGroup .F4 K))) =
      radicalTU K ⊔ oddB2Levi K := by
  have := finite_adjointGroup_F4 (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQp, hQM, hinf, hMN⟩ := isTwoRadicalDecomp_zTU (K := K)
  have hM'M : oddB2Levi K ≤ B2Levi K := (closure_le _).2 fun c hc => hc.1
  have hgenN : ∀ c ∈ {c : adjointGroup .F4 K | c * (zT K * zU K) = (zT K * zU K) * c ∧
      Odd (orderOf c)}, c ∈ radicalTU K ⊔ oddB2Levi K := by
    rintro c ⟨hcz, hco⟩
    have hcC : c ∈ ((radicalTU K ⊔ B2Levi K : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
      rw [hQM]
      exact mem_centralizer_singleton_iff.2 hcz
    rw [coe_mul_of_right_le_normalizer_left _ _ hMN] at hcC
    obtain ⟨q, hq, m, hm, rfl⟩ := Set.mem_mul.1 hcC
    exact mul_mem (mem_sup_left hq)
      (mem_sup_right (subset_closure ⟨hm, odd_orderOf_of_mul_mem hMN hinf hq hm hco⟩))
  have hQO : radicalTU K ≤ closure {c : adjointGroup .F4 K |
      c * (zT K * zU K) = (zT K * zU K) * c ∧ Odd (orderOf c)} := by
    intro u hu
    rw [radicalTU, mem_subgroupOf, nodesTU_eq_f4MidJ] at hu
    exact parabolicRadical_mid_le_closure_odd hK hu
  have hNperf := commutator_sup_eq_self_of_closure_odd hQp (hM'M.trans hMN) hB.1 hgenN
    (fun c hc => hc.2) hQO
  apply le_antisymm
  · have hPz : ∀ x ∈ perfectCore (centralizer ({zT K * zU K} : Set (adjointGroup .F4 K))),
        x * (zT K * zU K) = (zT K * zU K) * x :=
      fun x hx => mem_centralizer_singleton_iff.1 (perfectCore_le _ hx)
    exact (le_closure_odd_of_le_commutator le_rfl hPz (perfectCore_perfect _).ge).trans
      ((closure_le _).2 hgenN)
  · refine le_perfectCore_of_perfect ?_ hNperf
    rw [← hQM]
    exact sup_le_sup_left hM'M _

theorem factF3TUTwo_of_factOddB2LeviTwo [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hB : FactOddB2LeviTwo K) : FactF3TUTwo K := by
  have := finite_adjointGroup_F4 (K := K)
  obtain ⟨-, -, hTU⟩ := conj_nD_zT_zU (K := K)
  obtain ⟨-, -, hlTU⟩ := map_conj_nD_levis (K := K)
  obtain ⟨hQp, -, hinf, hMN⟩ := isTwoRadicalDecomp_zTU (K := K)
  have hM'M : oddB2Levi K ≤ B2Levi K := (closure_le _).2 fun c hc => hc.1
  set α : MulAut (adjointGroup .F4 K) := MulAut.conj (nD K) with hα
  have hlevi : leviQ2 K .tu = (oddB2Levi K).map α.toMonoidHom := by
    rw [oddB2Levi, map_closure_odd_mulAut, hlTU]
    rfl
  refine ⟨(radicalTU K).map α.toMonoidHom, hQp.map _, ?_, ?_, ?_, ?_⟩
  · rw [← hTU, centralizer_singleton_mulAut, ← CFSG.Quasithin.map_perfectCore,
      perfectCore_centralizer_zTU_two hK hB, Subgroup.map_sup, hlevi]
  · rw [hlevi, disjoint_iff, ← map_inf_eq _ _ _ α.injective, eq_bot_iff]
    refine (map_mono ?_).trans (Subgroup.map_bot _).le
    rw [← hinf]
    exact inf_le_inf_left _ hM'M
  · rw [hlevi, ← map_equiv_normalizer_eq]
    exact map_mono (hM'M.trans hMN)
  · exact EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv
      (((oddB2Levi K).equivMapOfInjective α.toMonoidHom α.injective).trans
        (MulEquiv.subgroupCongr hlevi.symm)) hB.2

end TU

end CFSG.SeitzReduction.F4Pilot
