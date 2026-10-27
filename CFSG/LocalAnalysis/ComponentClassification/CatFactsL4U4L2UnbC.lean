module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L2UnbB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Unb

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem not_le_pPrimeCore {J : Subgroup G} (hK : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨
    IsL2Type 7 (J ⧸ pPrimeCore 2 J)) : ¬ J ≤ (pPrimeCore 2 ↥J).map J.subtype := by
  intro hJ
  have hsimp : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := by
    rcases hK with h | h
    · exact isSimpleGroup_of_lieModel_psl_two h
    · exact isSimpleGroup_of_lieModel_psl_two h
  have htop : pPrimeCore 2 ↥J = ⊤ := by
    rw [eq_top_iff]
    intro j _
    obtain ⟨c, hc, hcj⟩ := hJ j.2
    have : c = j := Subtype.ext hcj
    rw [← this]
    exact hc
  obtain ⟨u, v, huv⟩ := exists_pair_ne (↥J ⧸ pPrimeCore 2 ↥J)
  apply huv
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  rw [QuotientGroup.eq, htop]
  exact mem_top _

theorem commutator_mem_of_coreActionKernel {J : Subgroup G} {g : G}
    (hg : g ∈ coreActionKernel J) {j : G} (hj : j ∈ J) :
    j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 ↥J).map J.subtype :=
  hg.2 j hj

variable [Finite G]

theorem l2UnbalancingSylow_body :
    ∀ (G : Type) [Group G] [Finite G] (a x : G) (J P : Subgroup G), GSUnbalancingTriple a x J →
      (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) →
      IsSylowTwoIn P J → ¬ P ≤ centralizer ({x} : Set G) := by
  intro G _ _ a x J P hU hK hP hPx
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hx2, -, -, -, hJx, hJD⟩ := gsUnbalancingTriple_iff.mp hU
  have hxN : x ∈ normalizer (J : Set G) := GSThmB.mem_normalizer_of_gsUnbalancingTriple hU
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  set K := ↥J ⧸ pPrimeCore 2 ↥J with hKdef
  set D := (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
    centralizer ({a} : Set G) with hD
  have hDN : D ≤ normalizer (J : Set G) := by
    have h := le_normalizer_commutator D J
    rw [commutator_comm, hJD] at h
    exact h
  set xb := GSThmB.oddBarConj J ⟨x, hxN⟩ with hxb
  obtain ⟨hPJ, Q, hQ⟩ := hP
  set Sb : Sylow 2 K := Q.mapSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
    (QuotientGroup.mk'_surjective _) with hSb
  have hxS : ∀ s ∈ (Sb : Subgroup K), xb s = s := by
    intro s hs
    rw [hSb, Sylow.coe_mapSurjective] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    have hqP : (q : G) ∈ P := by
      have : q ∈ P.subgroupOf J := by rw [← hQ]; exact hq
      exact mem_subgroupOf.1 this
    have hxq : x * q * x⁻¹ = q := by
      have := mem_centralizer_singleton_iff.mp (hPx hqP)
      rw [← this]; group
    rw [QuotientGroup.mk'_apply, hxb, GSThmB.oddBarConj_apply_mk]
    congr 1
    exact Subtype.ext hxq
  have hxb2 : xb * xb = 1 := by
    rw [hxb, ← map_mul]
    have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext hxx
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    have hker := GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one h1
    apply not_le_pPrimeCore hK
    refine le_trans (le_of_eq hJx.symm) ?_
    rw [commutator_le]
    intro j hj y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hk : (x ^ k)⁻¹ ∈ coreActionKernel J := inv_mem (zpow_mem hker k)
    have h1 := commutator_mem_of_coreActionKernel hk (inv_mem hj)
    rw [commutatorElement_def]
    rwa [inv_inv, inv_inv] at h1
  have hDker : ∀ d ∈ D, d ∈ coreActionKernel J := by
    intro d hd
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨d, hDN hd⟩)
    obtain ⟨c, hc, hcd⟩ := (mem_inf.mp hd).1
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf d = orderOf (⟨c, hc⟩ : pPrimeCore 2 (centralizer ({x} : Set G))) := by
        rw [← hcd, subtype_apply, Subgroup.orderOf_mk]
        exact Subgroup.orderOf_coe c
      have h2 := orderOf_dvd_natCard (⟨c, hc⟩ : pPrimeCore 2 (centralizer ({x} : Set G)))
      have h3 := pPrimeCore_coprime_card (p := 2) (G := centralizer ({x} : Set G))
      rw [Nat.coprime_two_left] at h3
      rw [h1]
      exact h3.of_dvd_nat h2
    have hψodd : Odd (orderOf (GSThmB.oddBarConj J ⟨d, hDN hd⟩)) := by
      have := orderOf_map_dvd (GSThmB.oddBarConj J) (⟨d, hDN hd⟩ : ↥(normalizer (J : Set G)))
      rw [Subgroup.orderOf_mk] at this
      exact hodd.of_dvd_nat this
    have hdx : d * x = x * d := by
      have hc' : (c : G) ∈ centralizer ({x} : Set G) := c.2
      have := mem_centralizer_singleton_iff.mp hc'
      rw [← hcd]
      exact this
    have hcomm : GSThmB.oddBarConj J ⟨d, hDN hd⟩ * xb = xb * GSThmB.oddBarConj J ⟨d, hDN hd⟩ := by
      rw [hxb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdx
    exact eq_one_of_odd_comm hK Sb hxS hxb2 hxb1 hψodd hcomm
  apply not_le_pPrimeCore hK
  refine le_trans (le_of_eq hJD.symm) ?_
  rw [commutator_le]
  intro j hj d hd
  have h1 := commutator_mem_of_coreActionKernel (hDker _ (inv_mem hd)) (inv_mem hj)
  rw [commutatorElement_def]
  rwa [inv_inv, inv_inv] at h1

end L2Unb

end CFSG.ComponentClassification.CatFactsL4U4
