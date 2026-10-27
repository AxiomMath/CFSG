module

public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.BProg.Assembly

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure S3PairData (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup G) : Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  hJ : IsJ2 x K
  hq : IsQuasisimple ↥K
  hr : 1 < pRank 2 ↥(CxK x K)
  shape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)

section Basic

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

omit [Finite G] in
theorem centralizer_le_centralizerSection (K : Subgroup G) :
    centralizer (K : Set G) ≤ centralizerSection K (pPrimeCoreOf 2 K) := fun _ hc =>
  C3.Layer1.Back.mem_centralizerSection_of_centralizes
    (fun k hk => (Subgroup.mem_centralizer_iff.1 hc k hk).symm) (TwoThin.pPrimeCoreOf_le K)

theorem S3PairData.x2 (h : S3PairData G x K) : orderOf x = 2 := h.hJ.1.1.1

theorem S3PairData.hKpc (h : S3PairData G x K) : IsPCompIn 2 (centralizer ({x} : Set G)) K :=
  h.hJ.1.1.2.2

theorem S3PairData.hILo (h : S3PairData G x K) : IsILo 2 x K := h.hJ.1.1

theorem S3PairData.term (h : S3PairData G x K) : IsPTerminal 2 x K := h.hJ.2.2

theorem S3PairData.le (h : S3PairData G x K) : K ≤ centralizer ({x} : Set G) := h.hKpc.1

theorem S3PairData.shape3 (h : S3PairData G x K) : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := h.shape

theorem S3PairData.hatQ (h : S3PairData G x K) : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
  TwoThin.isQuasisimple_hat h.hKpc

theorem S3PairData.simple_hat (h : S3PairData G x K) : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) :=
  PilotS3.isSimpleGroup_of_qShape3 h.shape3

theorem S3PairData.center_le (h : S3PairData G x K) : center ↥K ≤ pPrimeCore 2 ↥K := by
  intro z hz
  have h1 := PilotS3.center_trivial_of_shape3 h.hKpc h.shape3 (QuotientGroup.mk z) (fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.1 hz g))
  exact (QuotientGroup.eq_one_iff z).1 h1

theorem odd_card_pPrimeCore_two' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem S3PairData.odd_center (h : S3PairData G x K) : Odd (Nat.card (center ↥K)) :=
  (odd_card_pPrimeCore_two' ↥K).of_dvd_nat (Subgroup.card_dvd_of_le h.center_le)

theorem S3PairData.two_dvd_card (h : S3PairData G x K) : 2 ∣ Nat.card ↥K := by
  have : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) := h.simple_hat
  have hev : Even (Nat.card (↥K ⧸ pPrimeCore 2 ↥K)) :=
    even_card_of_nonabelian_simple (S45.exists_noncomm_of_isQuasisimple h.hatQ)
  exact (even_iff_two_dvd.1 hev).trans (Subgroup.card_quotient_dvd_card _)

theorem S3PairData.pPrimeCore_eq_center (h : S3PairData G x K) : pPrimeCore 2 ↥K = center ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ h.center_le
  rcases quasisimple_normal_subgroups h.hq (CFSG.pPrimeCore_normal (p := 2) (G := ↥K)) with
    htop | hle
  · exfalso
    have h1 := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)
    rw [htop, Subgroup.card_top] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd h1 h.two_dvd_card) (by norm_num)
  · exact hle

theorem S3PairData.two_le_pRank_K (h : S3PairData G x K) : 2 ≤ pRank 2 ↥K :=
  two_le_pRank_of_isQuasisimple_of_odd_center h.hq h.odd_center

theorem S3PairData.cxk_le (h : S3PairData G x K) : CxK x K ≤ centralizer (K : Set G) :=
  CxK_le_centralizer h.hq

theorem S3PairData.x_mem_cxk (h : S3PairData G x K) : x ∈ CxK x K := mem_CxK_self h.le

theorem S3PairData.rank3 (h : S3PairData G x K) {y : G} (hy : orderOf y = 2) :
    3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact h.hyp.rank
  exact TwoThin.rankThreeCentralizers G h.hyp.simple h.hyp.nonab h3 y hy

theorem S3PairData.exists_e (h : S3PairData G x K) :
    ∃ e : G, e ∈ CxK x K ∧ orderOf e = 2 ∧ e ≠ x := by
  obtain ⟨a, b, haH, hbH, ha2, hb2, hab, hne⟩ :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.exists_two_involutions_of_two_le_pRank
      (Nat.succ_le_of_lt h.hr)
  by_cases hax : a = x
  · exact ⟨b, hbH, hb2, fun h' => hne (hax.trans h'.symm)⟩
  · exact ⟨a, haH, ha2, hax⟩

theorem S3PairData.isCompIn_of_comm (h : S3PairData G x K) {y : G} (hy : y ∈ CxK x K)
    (hy2 : orderOf y = 2)
    (hS : ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥) :
    IsCompIn (centralizer ({y} : Set G)) K := by
  have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
  have hyK : y ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.1 hy).2
  have hKy : K ≤ centralizer ({y} : Set G) := by
    intro k hk
    have := Subgroup.mem_centralizer_iff.1 (h.cxk_le hy) k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 this
  obtain ⟨K', hlt⟩ := TwoThin.exists_pumpup_of_involution h.x2 hy2 h.hKpc hyC hyK h.hILo
    (h.rank3 hy2)
  obtain ⟨hxN, ⟨e⟩⟩ := h.term.2.1 y K' hlt
  have hle : TwoThin.hatCard K' ≤ TwoThin.hatCard K :=
    (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hK'c, -, -, -, hcases⟩ :=
    C3.Layer1.PumpRigid.rigid_step hlt (TwoThin.mem_centralizer_symm hyC) hle
  have hKpcK : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) K := by
    have hsub : (K.subgroupOf (K ⊓ centralizer ({y} : Set G))).IsSubnormal := by
      have : K.subgroupOf (K ⊓ centralizer ({y} : Set G)) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        exact inf_le_left
      rw [this]
      exact Subgroup.IsSubnormal.top
    exact isPCompIn_of_subnormal_block (le_inf le_rfl hKy) hsub h.hq
  have hΛK : K = Λ := hΛ.uniq K hKpcK
  rcases hcases with ⟨-, hbar⟩ | ⟨hxn, -⟩
  swap
  · exact absurd hxN hxn
  rw [← hΛK] at hbar
  have hsubn : (S45.barSub y K).IsSubnormal := by
    have h1 := (C3.Layer1.PumpCalc.isComponent_bar hK'c).2
    rw [← hbar] at h1
    exact h1
  have hcomm : ∀ a ∈ K, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)), a * w = w * a := by
    intro a ha w hw
    have h1 : ⁅a, w⁆ ∈ ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator ha hw
    rw [hS, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hsub := BProg.isSubnormal_of_barSub_of_comm hsubn hcomm
  exact ⟨hKy, CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKy).symm h.hq, hsub⟩

end Basic

end CFSG.GH74.Generic.BProg.B1
