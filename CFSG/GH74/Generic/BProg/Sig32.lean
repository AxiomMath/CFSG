module

public import CFSG.GH74.GLS.C3.Layer1.Th2SigHalf

public section

namespace CFSG.GH74.GLS.Th2SigHalf

open Subgroup

variable {G : Type} [Group G]

theorem AG_inf_centralizer_le_supK [Finite G] {k : ℕ} (hk : 1 ≤ k) {A S S' : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hweak : IsWeakKBal k A)
    (hS : S ∈ CFSG.Open.signalizerFunctorEk 2 k A) (hS' : S' ∈ CFSG.Open.signalizerFunctorEk 2 k A) :
    AG S ⊓ centralizer (S' : Set G) ≤ AG S' ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)) := by
  obtain ⟨s, hsS, hs1⟩ := Th2Sig6.exists_ne_one_of_card (k := k) hk hS.2
  have hcopAG : Nat.Coprime 2 (Nat.card ↥(AG S)) := Th2Sig6.coprime_card_AG hsS hs1
  have hcopY : Nat.Coprime 2 (Nat.card ↥(AG S ⊓ centralizer (S' : Set G))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopAG
  have hAnorm : A ≤ normalizer ((AG S ⊓ centralizer (S' : Set G) : Subgroup G) : Set G) :=
    fun q hq => mem_normalizer_inf (mem_normalizer_AG_of_le hAe hS.1 hq)
      (Subgroup.le_normalizer (mem_centralizer_of_le hAe hS'.1 hq))
  have hfact := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two A (AG S ⊓ centralizer (S' : Set G)) (CFSG.IsElementaryAbelian.isPGroup 2 ↥A)
    hAnorm hcopY
  have hcomm : ⁅AG S ⊓ centralizer (S' : Set G), A⁆ ≤ AG S' := by
    refine Th2Sig6.le_AG fun s' hs' hs'1 => ?_
    refine Subgroup.commutator_le.mpr fun h hh k' hk' => ?_
    exact hweak S (Th2Sig6.isE_of_card hAe hS.1 hS.2) s' (hS'.1 hs') hs'1 h
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hh).1,
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs') (Subgroup.mem_inf.mp hh).2⟩) k' hk'
  have hcentr : (AG S ⊓ centralizer (S' : Set G)) ⊓ centralizer (A : Set G) ≤
      pPrimeCoreOf 2 (centralizer (A : Set G)) := by
    have h1 : AG S ⊓ centralizer (A : Set G) ≤ pPrimeCoreOf 2 (centralizer (A : Set G)) :=
      le_pPrimeCoreOf_of_normalizes inf_le_right
        (fun c hc => mem_normalizer_inf (mem_normalizer_AG_of_mem_centralizer hS.1 hc)
          (Subgroup.le_normalizer hc))
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopAG)
    exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans h1
  exact le_of_eq_of_le hfact.symm (sup_le_sup hcomm hcentr)

theorem sup_inf_centralizer_leK [Finite G] {k : ℕ} (hk : 1 ≤ k) {A S S' : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hweak : IsWeakKBal k A)
    (hS : S ∈ CFSG.Open.signalizerFunctorEk 2 k A) (hS' : S' ∈ CFSG.Open.signalizerFunctorEk 2 k A) :
    (AG S ⊔ pPrimeCoreOf 2 (centralizer (A : Set G))) ⊓ centralizer (S' : Set G) ≤
      AG S' ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)) := by
  have hZC : pPrimeCoreOf 2 (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    Th2Sig6.pPrimeCoreOf_le
  have hZnorm : pPrimeCoreOf 2 (centralizer (A : Set G)) ≤ normalizer (AG S : Set G) :=
    le_normalizer_AG_of_le_centralizer hS.1 hZC
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _ hZnorm x).mp hx1
  have hzS' : z ∈ centralizer (S' : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS'.1) (hZC hz)
  have haS' : a ∈ centralizer (S' : Set G) := by
    simpa using mul_mem hx2 (inv_mem hzS')
  exact mul_mem (AG_inf_centralizer_le_supK hk hAe hweak hS hS' (Subgroup.mem_inf.mpr ⟨ha, haS'⟩))
    (Subgroup.mem_sup_right hz)

theorem thetaHalf_le_iSupK [Finite G] {k : ℕ} {A : Subgroup G} (hAe : CFSG.IsElementaryAbelian 2 ↥A)
    (hAr : k ≤ CFSG.pRank 2 ↥A) (Z : Subgroup G) :
    thetaHalf k A ≤
      ⨆ (S : Subgroup G) (_ : S ∈ CFSG.Open.signalizerFunctorEk 2 k A), (AG S ⊔ Z) := by
  refine sup_le (iSup₂_le fun D hD => ?_) ?_
  · have hnorm : A ≤ normalizer (AG D : Set G) := fun q hq =>
      mem_normalizer_AG_of_le hAe hD.1 hq
    refine (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ hnorm).trans ?_
    obtain ⟨S, hSD, hScard⟩ := Th2Sig6.exists_sub_card hD.2.1 hD.2.2
    exact (Th2Sig6.AG_anti hSD).trans
      (le_sup_left.trans (le_iSup₂_of_le S ⟨hSD.trans hD.1, hScard⟩ le_rfl))
  · obtain ⟨S, hSA, hScard⟩ := Th2Sig6.exists_sub_card hAe hAr
    exact (Th2Sig6.AG_anti hSA).trans
      (le_sup_left.trans (le_iSup₂_of_le S ⟨hSA, hScard⟩ le_rfl))

end CFSG.GH74.GLS.Th2SigHalf

namespace CFSG.GH74.GLS

open Subgroup

theorem b_ig_21_6_halfK (k : ℕ) (hk : 1 ≤ k) (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (hAE : IsE (k + 2) ⊤ A) (hweak : IsWeakKBal k A) : Odd (Nat.card ↥(thetaHalf k A)) := by
  obtain ⟨-, hAe, hAr⟩ := hAE
  have hAe' : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp hAe
  have hAcard : 2 ^ (k + 2) ≤ Nat.card ↥A := Th2Sig6.two_pow_le_card hAe hAr
  have hZC : pPrimeCoreOf 2 (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    Th2Sig6.pPrimeCoreOf_le
  have hZodd : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer (A : Set G)))) :=
    TwoThin.card_pPrimeCoreOf_odd _
  have hAGodd : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 k A, Odd (Nat.card ↥(AG S)) := by
    intro S hS
    obtain ⟨s, hsS, hs1⟩ := Th2Sig6.exists_ne_one_of_card (k := k) hk hS.2
    exact Nat.coprime_two_left.mp (Th2Sig6.coprime_card_AG hsS hs1)
  have hcop : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 k A,
      Nat.Coprime 2 (Nat.card ↥(AG S ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)))) := by
    intro S hS
    refine Nat.coprime_two_left.mpr ?_
    rw [sup_comm]
    exact Th2SigHalf.odd_card_sup_of_le_normalizer
      (Th2SigHalf.le_normalizer_AG_of_le_centralizer hS.1 hZC) hZodd (hAGodd S hS)
  have h := CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_two G k hk A hAe'
    hAcard (fun S => AG S ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)))
    (fun S hS => sup_le Th2Sig6.AG_le_centralizer
      (hZC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS.1))))
    hcop
    (fun S hS q hq => Th2SigHalf.mem_normalizer_sup (Th2SigHalf.mem_normalizer_AG_of_le hAe hS.1 hq)
      (Th2SigHalf.mem_normalizer_of_le_centralizer hZC hq))
    (fun S hS S' hS' => Th2SigHalf.sup_inf_centralizer_leK hk hAe hweak hS hS')
    (fun S hS => Th2Sig6.hypB_two_of_coprime _ (hcop S hS))
  obtain ⟨⟨hcopW, -⟩, -, -, -⟩ := h
  have hAr2 : k ≤ CFSG.pRank 2 ↥A := by omega
  exact (Nat.coprime_two_left.mp hcopW).of_dvd_nat
    (Subgroup.card_dvd_of_le (Th2SigHalf.thetaHalf_le_iSupK hAe hAr2 _))

theorem b_ig_21_6_three_halves (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (hAE : IsE 3 ⊤ A) (hweak : IsWeakKBal 1 A) : Odd (Nat.card ↥(thetaHalf 1 A)) :=
  b_ig_21_6_halfK 1 le_rfl G A hAE hweak

end CFSG.GH74.GLS
