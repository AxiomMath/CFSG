module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Ctx29

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_cSec {K E : Subgroup G}
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) (hEK : E ≤ K)
    (hEp : IsPGroup 2 ↥E) {e : G} (he : e ∈ E) (hec : e ∈ cSec K) : e = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e' : ↥K := ⟨e, hEK he⟩ with he'
  have hcent : ∀ g : ↥K ⧸ pPrimeCore 2 ↥K,
      g * (QuotientGroup.mk e') = (QuotientGroup.mk e') * g := by
    intro g
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective g
    have hO : ⁅(k' : G), e⁆ ∈ pPrimeCoreOf 2 K := hec.2.2 k' k'.2
    obtain ⟨o, ho, hoe⟩ := hO
    have hoeq : o = ⁅k', e'⁆ := Subtype.ext hoe
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⁅k', e'⁆ = 1 := by
      rw [← hoeq]
      exact (QuotientGroup.eq_one_iff o).2 ho
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have h2 : (QuotientGroup.mk e' : ↥K ⧸ pPrimeCore 2 ↥K) = 1 := hZ _ hcent
  have h3 : e' ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff e').1 h2
  exact S3Theta52.eq_one_of_mem_of_mem_pPrimeCoreOf hEp he ⟨e', h3, rfl⟩

omit [Finite G] in
theorem mem_cSec_of_le_centralizer {x : G} {K : Subgroup G}
    (hK : K ≤ centralizer ({x} : Set G)) : x ∈ cSec K := by
  have hN : x ∈ normalizer (K : Set G) := S3Theta52.mem_normalizer_of_le_centralizer hK
  refine ⟨hN, TwoThin.mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
  have h1 : ⁅k, x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hK hk))
  rw [h1]
  exact one_mem _

end S3Ctx29

end CFSG.GH74.Generic.BProg.B3
