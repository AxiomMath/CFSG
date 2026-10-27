module

public import CFSG.GH74.GLS.C3.Layer1.EvenSpor
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73G
public import CFSG.GH74.Generic.S45.LEvSporCorr
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1.Bk

theorem nonempty_equiv_alt_five_of_quasisimple {Kb : Type} [Group Kb] [Finite Kb]
    (hq : CFSG.IsQuasisimple Kb)
    (e : (Kb ⧸ pPrimeCore 2 Kb) ≃* alternatingGroup (Fin 5)) :
    Nonempty (Kb ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (Kb ⧸ pPrimeCore 2 Kb) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (inferInstance : (pPrimeCore 2 Kb).Normal) with h | h
  · exfalso
    have hidx : (pPrimeCore 2 Kb).index = 60 := hcard
    rw [h, Subgroup.index_top] at hidx
    omega
  · obtain ⟨-, -, -, -, -, ⟨f⟩, -⟩ :=
      CFSG.Semidihedral.Principal.odd_central_alternating_five_extension_splits_over_derived_subgroup
        (α := Fin 5) (by simp) (pPrimeCore 2 Kb) h (odd_card_pPrimeCore Kb) ⟨e⟩
    have htop : commutator Kb = ⊤ := hq.1.commutator_eq_top
    exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans f⟩

theorem x_mem_M {G : Type} [Group G] [Finite G] {x y : G} {K T S M L : Subgroup G}
    (hs : P85Struct x y K T S M L) : x ∈ M := by
  have hstd := hs.toP85Setup.choice.std
  exact (hs.toP85Setup.hQ.le.trans inf_le_left : T ⊓ CxK x K ≤ M)
    ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩

theorem p85_bar_data {G : Type} [Group G] [Finite G] {x y : G} {K T S M L : Subgroup G}
    (hs : P85Struct x y K T S M L)
    (hK5 : Nonempty ((↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin 5)))
    (hxM : x ∈ M) :
    Nonempty (↥(imgM M K) ≃* alternatingGroup (Fin 5)) ∧
      IsSylowOf 2 (imgM M (T ⊓ CxK x K)) (centralizer (imgM M K : Set (Mb M))) ∧
      2 ≤ pRank 2 ↥(imgM M (T ⊓ CxK x K)) ∧
      barMk ↥M ⟨x, hxM⟩ ∈ imgM M (T ⊓ CxK x K) ∧
      orderOf (barMk ↥M ⟨x, hxM⟩) = 2 ∧
      IsPCompIn 2 (centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) (imgM M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsetup := hs.toP85Setup
  have hstd := hsetup.choice.std
  have hKM := hsetup.KM
  have hQ := hsetup.hQ
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hx2 : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hstd.orderOf_x
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 := orderOf_barMk hx2
  have hxbQ : barMk ↥M ⟨x, hxM⟩ ∈ imgM M (T ⊓ CxK x K) :=
    mem_imgM_iff.2 ⟨⟨x, hxM⟩, hxQ, rfl⟩
  have hsyl : IsSylowOf 2 (imgM M (T ⊓ CxK x K)) (centralizer (imgM M K : Set (Mb M))) :=
    isSylowOf_imgM_cmbar hKM hQ
  have hxC : barMk ↥M ⟨x, hxM⟩ ∈ centralizer (imgM M K : Set (Mb M)) := hsyl.le hxbQ
  have hcomm : ∀ k ∈ imgM M K, barMk ↥M ⟨x, hxM⟩ * k = k * barMk ↥M ⟨x, hxM⟩ := fun k hk =>
    (mem_centralizer_iff.1 hxC k hk).symm
  have hcompIn : IsCompIn (centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) (imgM M K) :=
    hs.terminal _ hxb2 hcomm
  have hKq : CFSG.IsQuasisimple ↥(imgM M K) := isQuasisimple_of_isCompIn' hcompIn
  obtain ⟨e⟩ := hK5
  have hKev : 2 ∣ Nat.card ↥(imgM M K) := by
    have h1 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∣ Nat.card ↥(imgM M K) :=
      Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥(imgM M K)))
        (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    rw [h2] at h1
    exact (by norm_num : 2 ∣ 60).trans h1
  have hrank : 2 ≤ pRank 2 ↥(imgM M (T ⊓ CxK x K)) := by
    obtain ⟨f⟩ := equiv_imgM hQM hQ.isPGroup
    have hE : CFSG.IsElementaryAbelian 2 ↥(imgM M (T ⊓ CxK x K)) :=
      CFSG.GH74.Generic.S45.IsElementaryAbelian.of_mulEquiv f.symm hs.Qelem
    have hE' : CFSG.IsElementaryAbelian 2 ↥(⊤ : Subgroup ↥(imgM M (T ⊓ CxK x K))) :=
      CFSG.GH74.Generic.S45.IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv hE
    have hc : Nat.card ↥(⊤ : Subgroup ↥(imgM M (T ⊓ CxK x K))) = 2 ^ 2 := by
      rw [Subgroup.card_top, ← Nat.card_congr f.toEquiv, hs.Qcard]
      norm_num
    exact CFSG.LieType.SteinbergBR.le_pRank_of_card Nat.one_lt_two _ hE' hc
  exact ⟨nonempty_equiv_alt_five_of_quasisimple hKq e, hsyl, hrank, hxbQ, hxb2,
    isPCompIn_two_of_isCompIn_of_even hcompIn hKev⟩

theorem sporAutCfg_of_P85 {G : Type} [Group G] [Finite G] {x y : G} {K T S M L : Subgroup G}
    (hs : P85Struct x y K T S M L)
    (hK5 : Nonempty ((↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin 5)))
    (hcard : Nat.card (Mb M) = 2 * Nat.card ↥(imgM M L))
    (hsp : NativeSporadic.IsSporadic ↥(imgM M L) .M12 ∨ NativeSporadic.IsSporadic ↥(imgM M L) .J2)
    (hxM : x ∈ M) :
    SporAutCfg (⊤ : Subgroup (Mb M)) (imgM M L) (imgM M K) (imgM M (T ⊓ CxK x K))
      (barMk ↥M ⟨x, hxM⟩) := by
  obtain ⟨hK5', hsyl, hrank, hxbQ, hxb2, hcomp⟩ := p85_bar_data hs hK5 hxM
  refine ⟨hs.socle, imgM_mono hs.toP85Setup.hL.1, hK5', ?_, hsp, ?_, hrank, hxbQ, hxb2, ?_⟩
  · rw [Subgroup.card_top]
    exact hcard
  · rw [inf_top_eq]
    exact hsyl
  · rw [inf_top_eq]
    exact hcomp

end CFSG.GH74.GLS.Th2.P85.Sp
