module

public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterDefs
public import CFSG.HardMathSupport.Dickson.I271.Support.ChevInner
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Outer

variable {X : Type} [Group X]

theorem actHom_conj_of_mem (K : Subgroup X) {k : X} (hk : k ∈ K) :
    actHom K ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem exists_inner_of_actHom_mem_innerAut {K : Subgroup X} (hperf : commutator ↥K = ⊤) {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X))
    (h : actHom K ⟨a, haN⟩ ∈ innerAut (↥K ⧸ Subgroup.center ↥K)) :
    ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨k', k'.2, ?_⟩
  set kN : ↥(Subgroup.normalizer (K : Set X)) := ⟨k', Subgroup.le_normalizer k'.2⟩ with hkN
  set n : ↥(Subgroup.normalizer (K : Set X)) := ⟨a, haN⟩ with hn
  have hk : actHom K kN = MulAut.conj (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) :=
    actHom_conj_of_mem K k'.2
  have h1 : (kN⁻¹ * n) ∈ (actHom K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, hs]
    exact inv_mul_cancel _
  have hker : (actHom K).ker =
      (Subgroup.centralizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X)) :=
    ker_i271Act hperf (MulEquiv.refl _)
  rw [hker, Subgroup.mem_subgroupOf] at h1
  simpa [hkN, hn] using h1

theorem actHom_pow_eq_one {K : Subgroup X} {a : X} (haN : a ∈ Subgroup.normalizer (K : Set X))
    {p : ℕ} (hap : a ^ p = 1) : (actHom K ⟨a, haN⟩) ^ p = 1 := by
  rw [← map_pow]
  have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
    Subtype.ext (by simpa using hap)
  rw [this, map_one]

theorem center_eq_bot_of_outer [Finite X] {p : ℕ} (hK65 : KD65 p) {K B : Subgroup X}
    (hH : Chev204Hyp p K B) {a : X} (haB : a ∈ B)
    (hout : ¬ ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    Subgroup.center ↥K = ⊥ := by
  have hp := hH.prime
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hO : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have haN := hH.norm haB
  have hap : a ^ p = 1 := hH.scp.2.1.2 a haB
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  haveI : Fact p.Prime := ⟨hp⟩
  have hout' : actHom K ⟨a, haN⟩ ∉ innerAut (↥K ⧸ Subgroup.center ↥K) :=
    fun h => hout (exists_inner_of_actHom_mem_innerAut hq.1 haN h)
  exact hK65 (↥K ⧸ Subgroup.center ↥K) hq.2 (exists_noncomm_of_isQuasisimple hq) hH.chev
    ⟨_, actHom_pow_eq_one haN hap, hout'⟩ ↥K hq (i271h_center_isPGroup hp hO)
    ⟨MulEquiv.refl _⟩

theorem no_component_of_inner [Finite X] {p : ℕ} (hp : p.Prime) (hKD : KDChevInner p)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hChev : IsChevSimple p (↥K ⧸ Subgroup.center ↥K)) {a : X} (hap : a ^ p = 1)
    (haC : a ∉ Subgroup.centralizer (K : Set X)) {k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) {J : Subgroup X}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) : False := by
  have hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K := by
    intro hz
    apply haC
    have hk1 : k ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    have : a = k * (k⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ hk1 hc
  have hkp : (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K := by
    have hcomm : Commute k (k⁻¹ * a) := Subgroup.mem_centralizer_iff.1 hc k hk
    have h1 : k ^ p * (k⁻¹ * a) ^ p = 1 := by
      rw [← hcomm.mul_pow]
      have : k * (k⁻¹ * a) = a := by group
      rw [this, hap]
    have h2 : k ^ p ∈ Subgroup.centralizer (K : Set X) := by
      have : k ^ p = ((k⁻¹ * a) ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 g g.2)
  exact not_glaPComponent_of_inner hp hKD hq hChev hk hc hkZ hkp hJ

end Outer

section CoreFree

variable {X : Type} [Group X] [Finite X]

theorem coreFree_of_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOut : DefCharOuterCoreFree)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥)
    (hLie : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p)
    (hexc : ¬ (p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K)))
    {H : Subgroup (MulAut (barOf p K))} (hH : innerAut (barOf p K) ≤ H)
    {d : MulAut (barOf p K)} (hd : d ∉ innerAut (barOf p K)) (hdp : orderOf d = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) = ⊥ := by
  obtain ⟨idx, ⟨e⟩, hchar⟩ := hLie
  have hΦinj : Function.Injective (autBarToQuot p hO) := autBarToQuot_injective p hO hq.1
  have hinnS : innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H.map (autBarToQuot p hO) := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj (barOfEquiv p hO x), hH ⟨_, rfl⟩, ?_⟩
    rw [autBarToQuot_conj]
    simp
  have hdout : autBarToQuot p hO d ∉ innerAut (↥K ⧸ Subgroup.center ↥K) := by
    rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    apply hd
    have hq' : autBarToQuot p hO (MulAut.conj (barOfEquiv p hO x)) = autBarToQuot p hO d := by
      rw [autBarToQuot_conj]
      simpa using hs
    have : d = MulAut.conj (barOfEquiv p hO x) := (hΦinj hq').symm
    rw [this]
    exact ⟨_, rfl⟩
  have hxord : orderOf (autBarToQuot p hO d) = p := by
    rw [orderOf_injective (autBarToQuot p hO) hΦinj]
    exact hdp
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hS := hOut (↥K ⧸ Subgroup.center ↥K) hq.2 (exists_noncomm_of_isQuasisimple hq) idx ⟨e⟩ p hp
    hp2 hchar hexc (autBarToQuot p hO d) hxord hdout (H.map (autBarToQuot p hO)) hinnS
  rw [← map_inf_centralizer_of_injective (autBarToQuot p hO) hΦinj,
    ← map_glaPPrimeCoreOf_of_injective p (autBarToQuot p hO) hΦinj] at hS
  exact (Subgroup.map_eq_bot_iff_of_injective _ hΦinj).1 hS

theorem isCompLocallyBalanced_of_charp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDC : DefCharInnerCoreFree) (hOut : DefCharOuterCoreFree) {K A : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥)
    (hLie : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p)
    (hexc : ¬ (p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K))) :
    IsCompLocallyBalanced p 1 A K := by
  intro D hD H hH hDH
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card D = p := by simpa using hD.2.2
  have hnt : 1 < Nat.card D := by rw [hcard]; exact hp.one_lt
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
    exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩
  have hdp : orderOf d = p := orderOf_eq_prime (hD.2.1.2 d hdD) hd1
  have key : GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) = ⊥ := by
    by_cases hin : d ∈ innerAut (barOf p K)
    · exact coreFree_of_inner hp hp2 hDC hq hO hLie hH hin hdp
    · exact coreFree_of_outer hp hp2 hOut hq hO hLie hexc hH hin hdp
  unfold localDeltaIn
  refine eq_bot_iff.2 ?_
  exact (iInf_le_of_le d (iInf_le_of_le hdD (iInf_le _ hd1))).trans key.le

end CoreFree

end CFSG.HardMathSupport.Dickson.I271
