module

public import CFSG.GH74.Generic.BProg.B3.S3Rk3Glue
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Basic
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk3Trans

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G}

theorem mem_pPrimeCoreOf_of_piC (hc : Cfg x y K T) {g : G} (hgK : g ∈ K) (h1 : piC x g = 1) :
    g ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgC : g ∈ centralizer ({x} : Set G) := hc.hK.1 hgK
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set N : Subgroup G := K ⊓ pPrimeCoreOf 2 C with hN
  have hNK : N ≤ K := inf_le_left
  have hnorm : K ≤ normalizer (N : Set G) := by
    intro k hk
    have hkC : k ∈ C := hc.hK.1 hk
    have hkO : k ∈ normalizer ((pPrimeCoreOf 2 C : Subgroup G) : Set G) :=
      S3Rk3Glue.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hkC)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 := (Subgroup.mem_normalizer_iff.mp hkO n)
    constructor
    · intro hn
      exact Subgroup.mem_inf.2 ⟨S3Rk3Glue.conj_mem_of_mem_normalizer
        (Subgroup.le_normalizer hk) (Subgroup.mem_inf.1 hn).1, h1.1 (Subgroup.mem_inf.1 hn).2⟩
    · intro hn
      exact Subgroup.mem_inf.2 ⟨by
        have h3 := S3Rk3Glue.conj_mem_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hk))
          (Subgroup.mem_inf.1 hn).1
        have e : k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n := by group
        rwa [e] at h3, h1.2 (Subgroup.mem_inf.1 hn).2⟩
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    have h1 := RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 C
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right)) h1
  have hle := RankThree.PartTwo.Sec14.le_pPrimeCoreOf hNK hnorm hcop
  refine hle (Subgroup.mem_inf.2 ⟨hgK, ?_⟩)
  rw [piC_of_mem x hgC] at h1
  have h2 : (⟨g, hgC⟩ : ↥C) ∈ pPrimeCore 2 ↥C := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨⟨g, hgC⟩, h2, rfl⟩

theorem mem_CxK_of_piC (hc : Cfg x y K T) {t : G} (htC : t ∈ centralizer ({x} : Set G))
    (ht : piC x t ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x))) : t ∈ CxK x K := by
  have hKC : K ≤ centralizer ({x} : Set G) := hc.hK.1
  have htK : t ∈ normalizer (K : Set G) := S3Rk3Glue.mem_normalizer_K hc htC
  refine Subgroup.mem_inf.2 ⟨htC, htK, S3Rk3Glue.mem_normalizer_pPrimeCoreOf htK, fun k hk => ?_⟩
  have hkt : ⁅k, t⁆ ∈ K := by
    have h1 : t * k⁻¹ * t⁻¹ ∈ K := S3Rk3Glue.K_conj_mem hc htC (inv_mem hk)
    have e : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hk h1
  refine mem_pPrimeCoreOf_of_piC hc hkt ?_
  rw [S3L3Facts.piC_commutator x (hKC hk) htC]
  have hkb : piC x k ∈ S3.imgBar x K :=
    S3.mem_imgBar.2 ⟨⟨k, hKC hk⟩, hk, (piC_of_mem x (hKC hk)).symm⟩
  exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 ht _ hkb)

theorem mem_KC_of_piC (hc : Cfg x y K T) {t : G} (htC : t ∈ centralizer ({x} : Set G))
    (ht : piC x t ∈ S3.imgBar x K ⊔ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x))) : t ∈ K ⊔ CxK x K := by
  obtain ⟨kb, hkb, cb, hcb, hpt⟩ := S3Rk1Basic.exists_mul_of_mem_sup
    (fun h hh k hk => mem_centralizer_iff.1 hk h hh) ht
  obtain ⟨g, hgK, hg⟩ := S3.mem_imgBar.1 hkb
  have hk₀C : (g : G) ∈ centralizer ({x} : Set G) := g.2
  have hs : (g : G)⁻¹ * t ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).inv_mem hk₀C) htC
  have hπs : piC x ((g : G)⁻¹ * t) = cb := by
    rw [piC_mul x ((centralizer ({x} : Set G)).inv_mem hk₀C) htC, piC_inv x hk₀C,
      piC_of_mem x hk₀C, hg, hpt]
    group
  have hsC : (g : G)⁻¹ * t ∈ CxK x K := mem_CxK_of_piC hc hs (hπs ▸ hcb)
  have e : t = (g : G) * ((g : G)⁻¹ * t) := by group
  rw [e]
  exact (K ⊔ CxK x K).mul_mem (Subgroup.mem_sup_left hgK) (Subgroup.mem_sup_right hsC)

end S3Rk3Trans

end CFSG.GH74.Generic.BProg.B3
