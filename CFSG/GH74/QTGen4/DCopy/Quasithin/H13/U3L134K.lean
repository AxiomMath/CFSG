module

public import CFSG.Quasithin.H13.U3L134K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L13x8

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank.Ccomm
open scoped Pointwise

theorem stmt13_3_4K_of_F4
    (h1332 : Stmt13_3_2_F4) : Stmt13_3_4K_F4 := by
  intro G _ _ T L K X hH hK hTX hXN hnot p hp hpX
  by_contra hne
  push Not at hne
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L hH K hK
  set C := centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K with hCdef

  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (quotAct K).comp (Subgroup.inclusion hXN)
    with hφ
  have hker : φ.ker = C.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact quotAct_eq_one_iff K _
  have hcard : C.relIndex X = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [hcard] at hpX
  obtain ⟨⟨β, hβ⟩, hβo⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.range) p hpX
  have hβo' : orderOf β = p := by
    rw [Subgroup.orderOf_mk] at hβo
    exact hβo

  obtain ⟨k₀, hk₀⟩ := index_innAut_eq_two_pow hQ
  have hβI : β ∈ innAut (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have h1 : β ^ (innAut (↥K ⧸ CFSG.pCore 2 ↥K)).index ∈ innAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Subgroup.pow_index_mem _ β
    rw [hk₀] at h1
    exact mem_of_pow_two_pow_mem h1 (hp.odd_of_ne_two hne.1)
      (by rw [← hβo']; exact pow_orderOf_eq_one β)

  have hsylG : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hH.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [relIndex_top_right]
    exact hH.sylow.2
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := isSylowTwoOf_of_le hsylG le_sup_right
  have hsylK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hP : IsPGroup 2 ((T ⊓ K).subgroupOf K) :=
    hsylK.2.1.of_equiv (subgroupOfEquivOfLe hsylK.1).symm
  let P : Sylow 2 ↥K := hP.toSylow hsylK.2.2
  let ψ : ↥K →* ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    ((MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).codRestrict (innAut (↥K ⧸ CFSG.pCore 2 ↥K))
      fun k => ⟨_, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, ⟨q, rfl⟩⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, rfl⟩
  set R := (φ.range ⊓ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).subgroupOf
    (innAut (↥K ⧸ CFSG.pCore 2 ↥K)) with hRdef
  have hPR : ((P.mapSurjective hψ : Sylow 2 _) : Subgroup _) ≤ R := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨z, hz, rfl⟩
    have hzT : (z : G) ∈ T := (mem_inf.1 (mem_subgroupOf.1
      (show z ∈ (T ⊓ K).subgroupOf K from hz))).1
    rw [hRdef, mem_subgroupOf]
    refine mem_inf.2 ⟨⟨⟨z, hTX hzT⟩, ?_⟩, (ψ z).2⟩
    show quotAct K ⟨z, hXN (hTX hzT)⟩ = _
    rw [show (⟨z, hXN (hTX hzT)⟩ : ↥(normalizer (K : Set G))) = ⟨z, le_normalizer z.2⟩ from rfl,
      quotAct_of_mem]
    rfl
  have hβR : (⟨β, hβI⟩ : ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K))) ∈ R := by
    rw [hRdef, mem_subgroupOf]
    exact mem_inf.2 ⟨hβ, hβI⟩
  have hRt := SylOvergroupProp.of_mulEquiv (innAutEquiv _) (sylOvergroupProp_quotCenter hQ) R
    ⟨_, hPR⟩ p hp hne.1 hne.2 ⟨_, hβR, by rw [Subgroup.orderOf_mk, hβo']⟩
  have hIX : innAut (↥K ⧸ CFSG.pCore 2 ↥K) ≤ φ.range := by
    intro γ hγ
    have : (⟨γ, hγ⟩ : ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K))) ∈ R := hRt ▸ mem_top _
    rw [hRdef, mem_subgroupOf] at this
    exact (mem_inf.1 this).1

  set A := (quotAct K).range with hA
  have hIA : innAut (↥K ⧸ CFSG.pCore 2 ↥K) ≤ A := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨k, le_normalizer k.2⟩, quotAct_of_mem K k.2⟩
  set AT := (T.subgroupOf (normalizer (K : Set G))).map (quotAct K) with hAT
  have hATX : AT ≤ φ.range := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨t, hTX (mem_subgroupOf.1 ht)⟩, rfl⟩
  have hATA : AT ≤ A := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hodd : ¬ 2 ∣ AT.relIndex A := by
    intro h
    apply hH.sylow.2
    have e1 := relIndex_map_dvd (quotAct K)
      (le_top : T.subgroupOf (normalizer (K : Set G)) ≤ ⊤)
    rw [← MonoidHom.range_eq_map, relIndex_top_right] at e1
    exact h.trans (e1.trans (relIndex_dvd_index_of_le hTK))
  have hdvd1 : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A ∣ 2 ^ k₀ :=
    (relIndex_dvd_of_le_left A le_sup_right).trans
      (hk₀ ▸ relIndex_dvd_index_of_le hIA)
  have hdvd2 : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A ∣ AT.relIndex A :=
    relIndex_dvd_of_le_left A le_sup_left
  have hone : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A = 1 := by
    have hcop : Nat.Coprime (2 ^ k₀) (AT.relIndex A) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  have hAX : A ≤ φ.range :=
    (relIndex_eq_one.1 hone).trans (sup_le hATX hIX)

  apply hnot
  intro n hn
  obtain ⟨x, hx⟩ := hAX ⟨⟨n, hn⟩, rfl⟩
  have h1 : quotAct K ((Subgroup.inclusion hXN x)⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [map_mul, map_inv]
    change (φ x)⁻¹ * quotAct K ⟨n, hn⟩ = 1
    rw [hx, inv_mul_cancel]
  have h2 := (quotAct_eq_one_iff K _).1 h1
  have e : n = (x : G) * ((x : G)⁻¹ * n) := by group
  rw [e]
  exact mul_mem_sup x.2 h2

end CFSG.Quasithin.H13.U3
