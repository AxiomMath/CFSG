module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Bridge

variable {G : Type*} [Group G]

theorem open_isSubnormal_top_of_mathlib {H : Subgroup G} (h : H.IsSubnormal) :
    CFSG.Open.IsSubnormal H ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

theorem mathlib_isSubnormal_of_open_top {H : Subgroup G} (h : CFSG.Open.IsSubnormal H ⊤) :
    H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

theorem open_isSubnormal_of_subgroupOf {X K : Subgroup G} (hKX : K ≤ X)
    (h : (K.subgroupOf X).IsSubnormal) : CFSG.Open.IsSubnormal K X :=
  (CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 h

theorem subgroupOf_isSubnormal_of_open {X K : Subgroup G} (h : CFSG.Open.IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal :=
  CFSG.Open.IsSubnormal.subgroupOf h

end Bridge

section CComp

variable {G : Type} [Group G]

theorem mem_cComp_of_isComponentIn {K X : Subgroup G} (h : IsComponentIn K X) : K ∈ cComp X := by
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn h
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, open_isSubnormal_of_subgroupOf h.1 h.2.2, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hsubK : CFSG.Open.IsSubnormal K' K :=
      Quasithin.A3.subnormal_of_le_of_le hsub hlt.le h.1
    obtain ⟨P, hPK, hPn, hK'P⟩ := Quasithin.A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

theorem isComponentIn_of_mem_cComp {K X : Subgroup G} (h : K ∈ cComp X)
    (hq : CFSG.IsQuasisimple ↥K) : IsComponentIn K X :=
  ⟨le_of_mem_cComp h,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp h)).symm hq,
    subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp h)⟩

variable [Finite G]

theorem oddCore_le_center_of_quasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (heven : 2 ∣ Nat.card L) : CFSG.oddCore ↥L ≤ Subgroup.center ↥L := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : (CFSG.oddCore ↥L).Normal) with
    h | h
  · exfalso
    have hodd : Odd (Nat.card (CFSG.oddCore ↥L)) := EscapingLocal.odd_card_oddCore L
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)
  · exact h

theorem isTwoComponentIn_of_isComponentIn {K X : Subgroup G} (h : IsComponentIn K X)
    (heven : 2 ∣ Nat.card K) : IsTwoComponentIn K X := by
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn h
  exact ⟨mem_cComp_of_isComponentIn h,
    (CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.oddCore ↥K)
      (oddCore_le_center_of_quasisimple hq heven)).1⟩

end CComp

section Two

variable {Q : Type*} [Group Q] [Finite Q]

theorem pCore_le_center_of_oddCore_quotient (hQ : CFSG.IsQuasisimple (Q ⧸ CFSG.oddCore Q)) :
    CFSG.pCore 2 Q ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Q with hO
  set P := CFSG.pCore 2 Q with hPdef
  have hPn : P.Normal := inferInstance
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hmapn : (P.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map hPn _ (QuotientGroup.mk'_surjective O)
  have hmap2 : IsPGroup 2 (P.map (QuotientGroup.mk' O)) := hP2.map _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hmapn with h | h
  · exfalso
    have hall : IsPGroup 2 (Q ⧸ O) := by
      have := hmap2
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent (Q ⧸ O) := IsPGroup.isNilpotent hall
    have hsolv : Group.IsSolvable (Q ⧸ O) := inferInstance
    have hnt : Nontrivial (Q ⧸ O) := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    have hperf : Group.IsPerfect (Q ⧸ O) := hQ.1
    exact Group.IsPerfect.not_isSolvable (Q ⧸ O) hsolv
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hc : QuotientGroup.mk' O x ∈ Subgroup.center (Q ⧸ O) := h ⟨x, hx, rfl⟩
    have hcy := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' O y)
    have hcO : y * x * y⁻¹ * x⁻¹ ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcy
    have hcP : y * x * y⁻¹ * x⁻¹ ∈ P := by
      refine P.mul_mem ?_ (P.inv_mem hx)
      have := hPn.conj_mem x hx y
      simpa [mul_assoc] using this
    have hodd : Odd (Nat.card O) := EscapingLocal.odd_card_oddCore Q
    have hord : orderOf (y * x * y⁻¹ * x⁻¹) = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP2 ⟨_, hcP⟩
      have hk' : orderOf (y * x * y⁻¹ * x⁻¹) = 2 ^ k := (Subgroup.orderOf_coe (⟨_, hcP⟩ : P)).trans hk
      have hdvd : orderOf (y * x * y⁻¹ * x⁻¹) ∣ Nat.card O :=
        Subgroup.orderOf_dvd_natCard O hcO
      have hodd2 : Odd (2 ^ k) := by
        rw [← hk']
        exact hodd.of_dvd_nat hdvd
      have : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hodd2) (by
          rw [Nat.even_pow]
          exact ⟨even_two, hk0⟩)
      rw [hk', this, pow_zero]
    have h1 : y * x * y⁻¹ * x⁻¹ = 1 := orderOf_eq_one_iff.mp hord
    calc y * x = y * x * y⁻¹ * x⁻¹ * (x * y) := by group
      _ = x * y := by rw [h1, one_mul]

theorem pCore_le_center_of_isQuasisimple (hQ : CFSG.IsQuasisimple Q) :
    CFSG.pCore 2 Q ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (CFSG.pCore 2 Q).Normal := inferInstance
  have hP2 : IsPGroup 2 (CFSG.pCore 2 Q) := CFSG.pCore_isPGroup
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hPn with h | h
  · exfalso
    have hall : IsPGroup 2 Q := by
      rw [h] at hP2
      exact hP2.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent Q := IsPGroup.isNilpotent hall
    have hsolv : Group.IsSolvable Q := inferInstance
    have hnt : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    have hperf : Group.IsPerfect Q := hQ.1
    exact Group.IsPerfect.not_isSolvable Q hsolv
  · exact h

theorem center_le_pCore_of_oddCore_eq_bot (hO : CFSG.oddCore Q = ⊥) : Subgroup.center Q ≤ CFSG.pCore 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf z)
    (orderOf_pos z).ne'
  have hz' : z ^ (2 ^ a) = 1 := by
    have hcen : Subgroup.zpowers (z ^ (2 ^ a)) ≤ Subgroup.center Q := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ hz _
    have hnorm : (Subgroup.zpowers (z ^ (2 ^ a))).Normal := Subgroup.normal_of_le_center hcen
    have hodd : Odd (Nat.card (Subgroup.zpowers (z ^ (2 ^ a)))) := by
      rw [Nat.card_zpowers, orderOf_pow' _ (by positivity), hord]
      have : Nat.gcd (2 ^ a * m) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (dvd_mul_right _ _)
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    have hle : Subgroup.zpowers (z ^ (2 ^ a)) ≤ CFSG.oddCore Q :=
      le_sSup (show Subgroup.zpowers (z ^ (2 ^ a)) ∈
        {N : Subgroup Q | N.Normal ∧ Odd (Nat.card N)} from ⟨hnorm, hodd⟩)
    rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    exact hle
  have hm1 : m = 1 := by
    have h1 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hz'
    rw [hord] at h1
    have : m ∣ 1 := by
      have h2 : 2 ^ a * m ∣ 2 ^ a * 1 := by simpa using h1
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
    exact Nat.dvd_one.mp this
  have hcenz : Subgroup.zpowers z ≤ Subgroup.center Q := by
    rw [Subgroup.zpowers_le]; exact hz
  have hnorm : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hcenz
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := a) ?_
    rw [Nat.card_zpowers, hord, hm1, mul_one]
  have hle : Subgroup.zpowers z ≤ CFSG.pCore 2 Q :=
    le_sSup (show Subgroup.zpowers z ∈ {K : Subgroup Q | K.Normal ∧ IsPGroup 2 K} from
      ⟨hnorm, hp⟩)
  exact hle (Subgroup.mem_zpowers z)

theorem pPrimeCore_quotient_eq_bot_of_eq (N : Subgroup Q) [N.Normal]
    (h : N = CFSG.pPrimeCore 2 Q) : CFSG.pPrimeCore 2 (Q ⧸ N) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst h
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2

end Two

section OddTwo

variable {G : Type} [Group G] [Finite G]

theorem oddTwoCore_eq_center {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (heven : 2 ∣ Nat.card L) : oddTwoCore L = Subgroup.center ↥L := by
  have hO : CFSG.oddCore ↥L ≤ Subgroup.center ↥L := oddCore_le_center_of_quasisimple hq heven
  obtain ⟨hq', hcomap, -⟩ := CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.oddCore ↥L) hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.oddCore (↥L ⧸ CFSG.oddCore ↥L) = ⊥ := by
    have h1 : CFSG.oddCore ↥L = CFSG.pPrimeCore 2 ↥L :=
      (CFSG.oddCore_eq_piCore ↥L).trans (CFSG.pPrimeCore_eq_piCore ↥L 2).symm
    have h2 : CFSG.oddCore (↥L ⧸ CFSG.oddCore ↥L) = CFSG.pPrimeCore 2 (↥L ⧸ CFSG.oddCore ↥L) :=
      (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
    rw [h2]
    exact pPrimeCore_quotient_eq_bot_of_eq (CFSG.oddCore ↥L) h1
  have hp : CFSG.pCore 2 (↥L ⧸ CFSG.oddCore ↥L) = Subgroup.center (↥L ⧸ CFSG.oddCore ↥L) :=
    le_antisymm (pCore_le_center_of_isQuasisimple hq')
      (center_le_pCore_of_oddCore_eq_bot hbot)
  unfold oddTwoCore
  rw [hp]
  exact hcomap

theorem oddTwoIso_iff_center {J L : Subgroup G} (hJ : CFSG.IsQuasisimple ↥J)
    (hJe : 2 ∣ Nat.card J) (hL : CFSG.IsQuasisimple ↥L) (hLe : 2 ∣ Nat.card L) :
    OddTwoIso J L → Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  rintro ⟨e⟩
  have h1 := oddTwoCore_eq_center hJ hJe
  have h2 := oddTwoCore_eq_center hL hLe
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h1.symm).trans
    (e.trans (QuotientGroup.quotientMulEquivOfEq h2))⟩

omit [Finite G] in
theorem isQuasisimple_of_simple_O2_quotient [Finite G] {J : Subgroup G} (hperf : ⁅J, J⁆ = J)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.oddCore ↥J))
    (hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J))
    (hnc : ∃ a b : ↥J ⧸ CFSG.pCore 2 ↥J, a * b ≠ b * a) : CFSG.IsQuasisimple ↥J :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (CFSG.pCore 2 ↥J)
    (pCore_le_center_of_oddCore_quotient hq) (Subgroup.isPerfect_iff.mpr hperf) hs hnc

end OddTwo

end CFSG.QuasithinUnique.Id2519
