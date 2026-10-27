module

public import CFSG.GH74.Generic.BProg.B1.Stage3aSD1
import CFSG.GH74.AS16.Standard
import CFSG.GH74.Generic.S3.PumpLift

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial CFSG.ABGLocalTools
open scoped commutatorElement

section GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem exists_central_involution_of_isPGroup {R : Subgroup G} (hR : IsPGroup 2 ↥R) {x : G}
    (hxR : x ∈ R) (hx2 : orderOf x = 2) :
    ∃ y ∈ R, orderOf y = 2 ∧ ∀ r ∈ R, y * r = r * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPnt : Nontrivial ↥R := by
    refine ⟨⟨⟨x, hxR⟩, 1, fun h => ?_⟩⟩
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx2
    omega
  have hZnt : Nontrivial ↥(center ↥R) := hR.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥R) := hR.to_subgroup _
  obtain ⟨z, hz2⟩ : ∃ z : ↥(center ↥R), orderOf z = 2 := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    have h1 : 1 < Nat.card ↥(center ↥R) := Finite.one_lt_card
    have hn1 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      omega
    have h2 : 2 ∣ Nat.card ↥(center ↥R) := by
      rw [hn]; exact dvd_pow_self 2 hn1
    exact exists_prime_orderOf_dvd_card' (G := ↥(center ↥R)) 2 h2
  refine ⟨(((z : ↥R)) : G), (z : ↥R).2, ?_, fun r hr => ?_⟩
  · have h1 : orderOf (z : ↥R) = 2 := by rw [Subgroup.orderOf_coe]; exact hz2
    rw [Subgroup.orderOf_coe]; exact h1
  · have h1 : (z : ↥R) * ⟨r, hr⟩ = ⟨r, hr⟩ * (z : ↥R) :=
      (Subgroup.mem_center_iff.1 z.2 ⟨r, hr⟩).symm
    exact congrArg Subtype.val h1

theorem isUniversalComponent_of_sylow {M R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (M : Set G)))
    (hcomp : ∀ s ∈ R, orderOf s = 2 → IsCompIn (centralizer ({s} : Set G)) M) :
    IsUniversalComponent M := by
  intro t ht ht2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; simp)
  obtain ⟨g, hgC, hgle⟩ := Th2.exists_cj_le_of_isSylowOf hR (zpowers_le.2 ht) hTp
  have ht'R : g * t * g⁻¹ ∈ R :=
    hgle ((Th2.mem_cj_iff g _ _).2 (by
      rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group]; exact mem_zpowers t))
  have ht'2 : orderOf (g * t * g⁻¹) = 2 := by
    rw [show g * t * g⁻¹ = (MulAut.conj g) t by simp, MulEquiv.orderOf_eq, ht2]
  have hcomp' := hcomp _ ht'R ht'2
  have hconj := AS16.isCompIn_conj hcomp' g
  have hgc : ∀ m ∈ M, g * m = m * g := fun m hm => (mem_centralizer_iff.1 hgC m hm).symm
  have hK : conjugate M g = M := by
    ext k
    rw [AS16.mem_conjugate_iff']
    constructor
    · intro h
      have hk : k = g⁻¹ * (g * k * g⁻¹) * g := by group
      have h2 := hgc _ h
      have h3 : g⁻¹ * (g * k * g⁻¹) * g = g * k * g⁻¹ := by
        calc g⁻¹ * (g * k * g⁻¹) * g
            = g⁻¹ * ((g * k * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * k * g⁻¹)) := by rw [h2]
          _ = g * k * g⁻¹ := by group
      rw [hk, h3]; exact h
    · intro hk
      have : g * k * g⁻¹ = k := by rw [hgc k hk]; group
      rw [this]; exact hk
  have ht'eq : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  rw [hK, AS16.conjugate_centralizer_singleton, ht'eq] at hconj
  exact (isComponentOf_iff_isComponent_subgroupOf hconj.1).2 hconj.2

end GroupTheory

section SDSylow

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem S3PairData.exists_sylow_chain (h : S3PairData G x K) :
    ∃ Q R : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ IsSylowOf 2 R (centralizer (K : Set G)) ∧
      Q ≤ R ∧ x ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := CxK x K with hH
  have hxH : x ∈ H := h.x_mem_cxk
  let X : ↥H := ⟨x, hxH⟩
  have hXord : orderOf X = 2 := by rw [Subgroup.orderOf_mk]; exact h.x2
  have hXp : IsPGroup 2 ↥(zpowers X) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hXord]; simp)
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  set Q : Subgroup G := (S : Subgroup ↥H).map H.subtype with hQ
  have hQs : IsSylowOf 2 Q H := ⟨S, rfl⟩
  have hxQ : x ∈ Q := ⟨X, hXS (mem_zpowers X), rfl⟩
  set C := centralizer (K : Set G) with hC
  have hQC : Q ≤ C := hQs.le.trans h.cxk_le
  have hQp : IsPGroup 2 ↥Q := hQs.isPGroup
  have hQ' : IsPGroup 2 ↥(Q.subgroupOf C) := hQp.comap_subtype
  obtain ⟨S', hQS'⟩ := hQ'.exists_le_sylow
  set R : Subgroup G := (S' : Subgroup ↥C).map C.subtype with hR
  have hRs : IsSylowOf 2 R C := ⟨S', rfl⟩
  have hQR : Q ≤ R := by
    intro q hq
    exact ⟨⟨q, hQC hq⟩, hQS' (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  exact ⟨Q, R, hQs, hRs, hQR, hxQ⟩

theorem S3PairData.pumpUpLT_of_isCompIn (h : S3PairData G x K) {y : G} (hy : y ∈ CxK x K)
    (hy2 : orderOf y = 2) (hc : IsCompIn (centralizer ({y} : Set G)) K) :
    PumpUpLT 2 x K y K := by
  have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
  have hyK : y ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.1 hy).2
  have hKy : K ≤ centralizer ({y} : Set G) := hc.1
  have hKsubC : (K.subgroupOf (centralizer ({y} : Set G))).IsSubnormal := hc.2.2
  have hKpcK : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) K := by
    have hsub : (K.subgroupOf (K ⊓ centralizer ({y} : Set G))).IsSubnormal := by
      have : K.subgroupOf (K ⊓ centralizer ({y} : Set G)) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        exact inf_le_left
      rw [this]
      exact Subgroup.IsSubnormal.top
    exact isPCompIn_of_subnormal_block (le_inf le_rfl hKy) hsub h.hq
  have hKle : K ≤ pumpUp 2 K y := by
    have h1 : K ≤ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) := le_sSup hKpcK
    intro k hk
    refine (le_iSup₂ (f := fun g (_ : g ∈ pLayerOf 2 (centralizer ({y} : Set G))) =>
      (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))).map (MulAut.conj g).toMonoidHom) 1
      (one_mem _)) ?_
    exact ⟨k, h1 hk, by simp⟩
  have hsub' : (K.subgroupOf (pumpUp 2 K y)).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hKsubC (TwoThin.pumpUp_le_centralizer K y)
  refine ⟨h.hILo, ⟨hy2, by simpa [oBound] using h.rank3 hy2,
    isPCompIn_of_subnormal_block hKy hKsubC h.hq⟩, hyC, hyK,
    isPCompIn_of_subnormal_block hKle hsub' h.hq⟩

theorem S3PairData.sylow_eq (h : S3PairData G x K)
    (hS : ∀ y ∈ CxK x K, orderOf y = 2 → y ≠ x → ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥)
    {Q R : Subgroup G} (hQs : IsSylowOf 2 Q (CxK x K))
    (hRs : IsSylowOf 2 R (centralizer (K : Set G))) (hQR : Q ≤ R) (hxQ : x ∈ Q) : R = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : R ≤ centralizer (K : Set G) := hRs.le
  have hRcs : ∀ r ∈ R, r ∈ centralizerSection K (pPrimeCoreOf 2 K) := fun r hr =>
    centralizer_le_centralizerSection K (hRC hr)
  have hRx : R ⊓ centralizer ({x} : Set G) = Q := by
    refine hQs.eq_of_le (le_inf hQR (hQs.le.trans inf_le_left)) (fun g hg => ?_)
      (hRs.isPGroup.to_inf_left)
    exact ⟨hg.2, hRcs g hg.1⟩
  have hxR : x ∈ R := hQR hxQ
  obtain ⟨y, hyR, hy2, hyc⟩ := exists_central_involution_of_isPGroup hRs.isPGroup hxR h.x2
  by_cases hyx : y = x
  ·
    rw [← hRx]
    refine (inf_eq_left.2 fun r hr => ?_).symm
    have := hyc r hr
    rw [hyx] at this
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  · have hyCx : y ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hyc x hxR)
    have hyQ : y ∈ Q := by rw [← hRx]; exact ⟨hyR, hyCx⟩
    have hyCxK : y ∈ CxK x K := ⟨hyCx, hRcs y hyR⟩
    have hcomp := h.isCompIn_of_comm hyCxK hy2 (hS y hyCxK hy2 hyx)
    have hlt := h.pumpUpLT_of_isCompIn hyCxK hy2 hcomp
    have hQy := h.term.2.2 Q hQs y K hlt hyQ (fun q hq => hyc q (hQR hq))
    refine hQy.eq_of_le hQR (fun r hr => ?_) hRs.isPGroup
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hyc r hr).symm, hRcs r hr⟩

theorem S3PairData.isUniversalComponent (h : S3PairData G x K)
    (hS : ∀ y ∈ CxK x K, orderOf y = 2 → y ≠ x → ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥) :
    IsUniversalComponent K := by
  obtain ⟨Q, R, hQs, hRs, hQR, hxQ⟩ := h.exists_sylow_chain
  have hRQ : R = Q := h.sylow_eq hS hQs hRs hQR hxQ
  refine isUniversalComponent_of_sylow hRs fun s hsR hs2 => ?_
  have hsQ : s ∈ CxK x K := by rw [hRQ] at hsR; exact hQs.le hsR
  by_cases hsx : s = x
  · rw [hsx]
    exact ⟨h.le, CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe h.le).symm h.hq,
      CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
        (TwoThin.isPCompIn_two_iff.1 h.hKpc).2.1 Subgroup.IsSubnormal.top⟩
  · exact h.isCompIn_of_comm hsQ hs2 (hS s hsQ hs2 hsx)

end SDSylow

end CFSG.GH74.Generic.BProg.B1
