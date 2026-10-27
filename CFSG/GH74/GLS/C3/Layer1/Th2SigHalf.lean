module

public import CFSG.GH74.GLS.C3.Layer1.Th2Sig6
public import CFSG.GH74.GLS.C3.Layer1.Th2SigStmt

public section

namespace CFSG.GH74.GLS.Th2SigHalf

open Subgroup

variable {G : Type} [Group G]

theorem odd_card_sup_of_le_normalizer [Finite G] {H N : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

theorem mem_normalizer_sup {H K : Subgroup G} {q : G} (hH : q ∈ normalizer (H : Set G))
    (hK : q ∈ normalizer (K : Set G)) : q ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ {q : G}, q ∈ normalizer (H : Set G) → q ∈ normalizer (K : Set G) →
      ∀ h ∈ H ⊔ K, q * h * q⁻¹ ∈ H ⊔ K := by
    intro q hH hK
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj q).toMonoidHom := by
      refine sup_le (fun h hh => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hH h).mp hh)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hK k).mp hk)
    exact fun h hh => hle hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key hH hK h, fun hh => ?_⟩
  have := key (inv_mem hH) (inv_mem hK) _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {H K : Subgroup G} {q : G} (hH : q ∈ normalizer (H : Set G))
    (hK : q ∈ normalizer (K : Set G)) : q ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

theorem le_pPrimeCoreOf_of_normalizes {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set G)) (hcop : Nat.Coprime 2 (Nat.card N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ CFSG.pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

theorem mem_normalizer_AG_of_le {A S : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) (hSA : S ≤ A)
    {q : G} (hq : q ∈ A) : q ∈ normalizer (AG S : Set G) :=
  Th2Sig6.mem_normalizer_AG fun _ hd => Th2Sig6.mul_comm_of_isElementaryAbelian hA hq (hSA hd)

theorem mem_normalizer_AG_of_mem_centralizer {A S : Subgroup G} (hSA : S ≤ A) {z : G}
    (hz : z ∈ centralizer (A : Set G)) : z ∈ normalizer (AG S : Set G) :=
  Th2Sig6.mem_normalizer_AG fun _ hd => (Subgroup.mem_centralizer_iff.mp hz _ (hSA hd)).symm

theorem le_normalizer_AG_of_le_centralizer {A S Y : Subgroup G} (hSA : S ≤ A)
    (hY : Y ≤ centralizer (A : Set G)) : Y ≤ normalizer (AG S : Set G) :=
  fun _ hz => mem_normalizer_AG_of_mem_centralizer hSA (hY hz)

theorem mem_normalizer_of_le_centralizer {A Y : Subgroup G} (hY : Y ≤ centralizer (A : Set G)) {q : G}
    (hq : q ∈ A) : q ∈ normalizer (Y : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mpr hY hq)

theorem mem_centralizer_of_le {A S' : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) (hSA : S' ≤ A)
    {q : G} (hq : q ∈ A) : q ∈ centralizer (S' : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hd =>
    Th2Sig6.mul_comm_of_isElementaryAbelian hA (hSA hd) hq

theorem AG_inf_centralizer_le_sup [Finite G] {A S S' : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hweak : IsWeakKBal 2 A)
    (hS : S ∈ CFSG.Open.signalizerFunctorEk 2 2 A) (hS' : S' ∈ CFSG.Open.signalizerFunctorEk 2 2 A) :
    AG S ⊓ centralizer (S' : Set G) ≤ AG S' ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)) := by
  obtain ⟨s, hsS, hs1⟩ := Th2Sig6.exists_ne_one_of_card (k := 2) (by norm_num) hS.2
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
    refine Subgroup.commutator_le.mpr fun h hh k hk => ?_
    exact hweak S (Th2Sig6.isE_of_card hAe hS.1 hS.2) s' (hS'.1 hs') hs'1 h
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hh).1,
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs') (Subgroup.mem_inf.mp hh).2⟩) k hk
  have hcentr : (AG S ⊓ centralizer (S' : Set G)) ⊓ centralizer (A : Set G) ≤
      pPrimeCoreOf 2 (centralizer (A : Set G)) := by
    have h1 : AG S ⊓ centralizer (A : Set G) ≤ pPrimeCoreOf 2 (centralizer (A : Set G)) :=
      le_pPrimeCoreOf_of_normalizes inf_le_right
        (fun c hc => mem_normalizer_inf (mem_normalizer_AG_of_mem_centralizer hS.1 hc)
          (Subgroup.le_normalizer hc))
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopAG)
    exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans h1
  exact le_of_eq_of_le hfact.symm (sup_le_sup hcomm hcentr)

theorem sup_inf_centralizer_le [Finite G] {A S S' : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hweak : IsWeakKBal 2 A)
    (hS : S ∈ CFSG.Open.signalizerFunctorEk 2 2 A) (hS' : S' ∈ CFSG.Open.signalizerFunctorEk 2 2 A) :
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
  exact mul_mem (AG_inf_centralizer_le_sup hAe hweak hS hS' (Subgroup.mem_inf.mpr ⟨ha, haS'⟩))
    (Subgroup.mem_sup_right hz)

theorem thetaHalf_le_iSup [Finite G] {A : Subgroup G} (hAe : CFSG.IsElementaryAbelian 2 ↥A)
    (hAr : 2 ≤ CFSG.pRank 2 ↥A) (Z : Subgroup G) :
    thetaHalf 2 A ≤
      ⨆ (S : Subgroup G) (_ : S ∈ CFSG.Open.signalizerFunctorEk 2 2 A), (AG S ⊔ Z) := by
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

theorem b_ig_21_6_half : B_IG_21_6_half := by
  intro G _ _ A hAE _ hweak
  obtain ⟨-, hAe, hAr⟩ := hAE
  have hAe' : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp hAe
  have hAcard : 2 ^ (2 + 2) ≤ Nat.card ↥A := Th2Sig6.two_pow_le_card hAe hAr
  have hZC : pPrimeCoreOf 2 (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    Th2Sig6.pPrimeCoreOf_le
  have hZodd : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer (A : Set G)))) :=
    TwoThin.card_pPrimeCoreOf_odd _
  have hAGodd : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 2 A, Odd (Nat.card ↥(AG S)) := by
    intro S hS
    obtain ⟨s, hsS, hs1⟩ := Th2Sig6.exists_ne_one_of_card (k := 2) (by norm_num) hS.2
    exact Nat.coprime_two_left.mp (Th2Sig6.coprime_card_AG hsS hs1)
  have hcop : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 2 A,
      Nat.Coprime 2 (Nat.card ↥(AG S ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)))) := by
    intro S hS
    refine Nat.coprime_two_left.mpr ?_
    rw [sup_comm]
    exact Th2SigHalf.odd_card_sup_of_le_normalizer
      (Th2SigHalf.le_normalizer_AG_of_le_centralizer hS.1 hZC) hZodd (hAGodd S hS)
  have h := CFSG.SignalizerFunctorTheorem.signalizer_functor_theorem_two G 2 (by norm_num) A hAe'
    hAcard (fun S => AG S ⊔ pPrimeCoreOf 2 (centralizer (A : Set G)))
    (fun S hS => sup_le Th2Sig6.AG_le_centralizer
      (hZC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS.1))))
    hcop
    (fun S hS q hq => Th2SigHalf.mem_normalizer_sup (Th2SigHalf.mem_normalizer_AG_of_le hAe hS.1 hq)
      (Th2SigHalf.mem_normalizer_of_le_centralizer hZC hq))
    (fun S hS S' hS' => Th2SigHalf.sup_inf_centralizer_le hAe hweak hS hS')
    (fun S hS => Th2Sig6.hypB_two_of_coprime _ (hcop S hS))
  obtain ⟨⟨hcopW, -⟩, -, -, -⟩ := h
  have hAr2 : 2 ≤ CFSG.pRank 2 ↥A := by omega
  exact (Nat.coprime_two_left.mp hcopW).of_dvd_nat
    (Subgroup.card_dvd_of_le (Th2SigHalf.thetaHalf_le_iSup hAe hAr2 _))

end CFSG.GH74.GLS
