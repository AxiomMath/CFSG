module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ClassicalInvolution CFSG.Sporadic.Ly CFSG.Sporadic.Schreier

theorem ivk93cov_ly :
    Ivk93CovEq (fun X _ => NativeSporadic.IsSporadic X .Ly) 11 := by
  obtain ⟨hkey, hq, hZ, hKcard⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  intro L _ _ hL y _ n B hc
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hc.ord
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hcz⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
    (Subgroup.mem_top _) hord
  obtain ⟨G, hG, φ, hqG, hcardG, hZG⟩ : ∃ (G : Type) (_ : Group G)
      (φ : ↥(centralizer ({y} : Set L)) ≃* G),
      CFSG.IsQuasisimple G ∧ Nat.card G = 39916800 ∧ Nat.card ↥(center G) = 2 :=
    ⟨↥LyProof.KJ, inferInstance,
      (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hcz]; simp)).trans
        ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey)),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hq, hKcard, hZ⟩
  have hq' : CFSG.IsQuasisimple ↥(centralizer ({y} : Set L)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqG
  have hBeq := hc.eq_centralizer_of_quasisimple hq'
  have hcard : Nat.card ↥(centralizer ({y} : Set L)) = 39916800 := by
    rw [Nat.card_congr φ.toEquiv]
    exact hcardG
  have hZc : Nat.card ↥(center ↥(centralizer ({y} : Set L))) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact hZG
  have hN : (pPrimeCore 2 ↥(centralizer ({y} : Set L))).Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({y} : Set L)))) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({y} : Set L)))
  have hO : pPrimeCore 2 ↥(centralizer ({y} : Set L)) = ⊥ := by
    rcases LocalCores.quasisimple_normal_subgroups hq' hN with h0 | h0
    · exfalso
      have h2 : 2 ∣ Nat.card ↥(centralizer ({y} : Set L)) := by
        rw [hcard]
        norm_num
      have : Nat.card ↥(pPrimeCore 2 ↥(centralizer ({y} : Set L))) = Nat.card ↥(centralizer ({y} : Set L)) := by
        rw [h0]
        exact Subgroup.card_top
      rw [this] at hcop
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)
    · have h1 : Nat.card ↥(pPrimeCore 2 ↥(centralizer ({y} : Set L))) ∣ Nat.card ↥(center ↥(centralizer ({y} : Set L))) :=
        Subgroup.card_dvd_of_le h0
      rw [hZc] at h1
      exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hcop.symm h1)
  have hq1 := hc.card_quot
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B)
  rw [hBeq] at hq1 hc1
  rw [hq1, hO, Subgroup.card_bot, mul_one, hcard] at hc1
  have h11 : n.factorial = Nat.factorial 11 := by
    rw [← hc1]
    norm_num [Nat.factorial]
  by_contra hne
  have hlt : n < 11 := lt_of_le_of_ne hc.le_eleven (fun h => hne h.symm)
  have := (Nat.factorial_lt (by have := hc.eight; omega)).2 hlt
  omega

theorem ivk93cov_ly_oneClass
    {L : Type} [Group L] [Finite L] (hL : NativeSporadic.IsSporadic L .Ly) (u v : L)
    (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v := by
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥J := e.trans lyEquivJ
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  have key : ∀ w : L, orderOf w = 2 → ∃ c : ↥J, e' w = c * LyProof.zJ * c⁻¹ := by
    intro w hw
    have hord : orderOf (e' w) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hw
    obtain ⟨c, -, hcz⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' w)
      (Subgroup.mem_top _) hord
    exact ⟨c, hcz⟩
  obtain ⟨c₁, h₁⟩ := key u hu
  obtain ⟨c₂, h₂⟩ := key v hv
  refine isConj_iff.2 ⟨e'.symm (c₂ * c₁⁻¹), ?_⟩
  apply e'.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h₁, h₂]
  group

end CFSG.GH74.GLS.IVK.Proofs2
