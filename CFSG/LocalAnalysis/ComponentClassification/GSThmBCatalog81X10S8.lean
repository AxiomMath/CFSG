module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10B
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X10

theorem isDoubleCoverOfAlt_seven_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : GH74.GLS.IsDoubleCoverOfAlt Q 7) : GH74.GLS.IsDoubleCoverOfAlt Q' 7 := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp hq, ?_, ⟨?_⟩⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  · exact (QuotientGroup.congr (center Q) (center Q') e (map_center_eq e)).symm.trans φ

theorem classical_of_twoA7 {G : Type} [Group G] [Finite G] {z₀ : G} {J : Subgroup G}
    (hJC : J ≤ centralizer {z₀}) (hJ : IsPComponent 2 (J.subgroupOf (centralizer {z₀})))
    (hA7 : GH74.GLS.IsDoubleCoverOfAlt (J ⧸ pPrimeCore 2 J) 7) :
    Open.IsSubnormal J (centralizer ({z₀} : Set G)) ∧
      (∃ S : Sylow 2 J, ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      Open.classicalInvolutionWitness J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : CFSG.pRank 2 J ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
    obtain ⟨hq, hc, hφ⟩ := hA7
    obtain ⟨π, hπ⟩ := GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt
      (H := J ⧸ pPrimeCore 2 J) (n := 7) ⟨hq, inferInstance, hc, hφ⟩
    exact (GH74.GLS.IVK.Lifted.pRank_eq_one_of_twoCover_seven hπ).le
  have hA : IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two J)).symm
      (TBLit.twoComponent_coreQuotient_quasisimple hJC hJ)
  obtain ⟨-, -, -, -, -, -, r, hr, hSJ, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hA
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨eS⟩ := hSJ S
  refine ⟨TBLit.open_isSubnormal_of_isPComponent hJC hJ, ⟨S, r, hr, ⟨eS⟩⟩, .inr ?_⟩
  obtain ⟨hq, hc, ⟨φ⟩⟩ := isDoubleCoverOfAlt_seven_congr
    (QuotientGroup.quotientMulEquivOfEq (TBLit.classicalInvolutionOddCore_eq J)).symm hA7
  exact ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, hc, ⟨φ⟩⟩

theorem exists_pComponent_of_isComponent {G : Type} [Group G] [Finite G] {z₀ : G}
    (hz2 : z₀ * z₀ = 1) (C : Subgroup G) (hC : ∀ c ∈ C, c * z₀ = z₀ * c) (hz₀C : z₀ ∈ C)
    (W : Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) (hWq : IsQuasisimple W) (hsub : W.IsSubnormal)
    (hz : QuotientGroup.mk' (pPrimeCore 2 ↥C) ⟨z₀, hz₀C⟩ ∈ W) :
    ∃ J₀ : Subgroup G, J₀ ≤ C ∧ IsPComponent 2 (J₀.subgroupOf C) ∧ z₀ ∈ J₀ ∧
      Nonempty (J₀ ⧸ pPrimeCore 2 J₀ ≃* W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  have hWO : pPrimeCore 2 W = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 W hsub,
      pPrimeCore_quotient_pPrimeCore_eq_bot, bot_subgroupOf]
  obtain ⟨hL, hLJ⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 W ⟨hWq, hsub⟩
  set L := CatalogueBPrimeJoin.canonicalPrimeLift 2 W with hLdef
  set J₀ := L.map C.subtype with hJ₀
  have hJ₀C : J₀ ≤ C := map_subtype_le L
  have hJ₀L : J₀.subgroupOf C = L := by
    ext x
    rw [mem_subgroupOf, hJ₀, mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨J₀, hJ₀C, hJ₀L ▸ hL, ?_, ?_⟩
  ·
    have hmem : π ⟨z₀, hz₀C⟩ ∈ L.map π := by
      rw [hLJ]
      exact hz
    obtain ⟨l, hlL, hlz⟩ := hmem
    obtain ⟨o, ho⟩ : ∃ o : C, o = (⟨z₀, hz₀C⟩ : C)⁻¹ * l := ⟨_, rfl⟩
    have hoO : o ∈ pPrimeCore 2 ↥C := by
      rw [ho, ← QuotientGroup.eq]
      exact hlz.symm
    have hcomm : (⟨z₀, hz₀C⟩ : C) * o = o * ⟨z₀, hz₀C⟩ := Subtype.ext (hC o o.2).symm
    have hz2' : (⟨z₀, hz₀C⟩ : C) * ⟨z₀, hz₀C⟩ = 1 := Subtype.ext hz2
    have hodd : Odd (orderOf o) := by
      have h1 := orderOf_dvd_natCard (⟨o, hoO⟩ : ↥(pPrimeCore 2 ↥C))
      rw [Subgroup.orderOf_mk] at h1
      have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥C) :=
        (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥C))
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact fun h3 => h2 (h3.trans h1)
    have hl : l = ⟨z₀, hz₀C⟩ * o := by rw [ho, mul_inv_cancel_left]
    have h1 := pow_eq_of_odd hz2' hcomm hodd
    rw [← hl] at h1
    have h2 : l ^ orderOf o ∈ L := pow_mem hlL _
    rw [h1] at h2
    exact mem_map_of_mem C.subtype h2
  ·
    obtain ⟨-, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection π
      (QuotientGroup.mk'_surjective _) OddQuot.not_two_dvd_card_ker
    obtain ⟨e₂, -⟩ := hiso L hL
    let e₁ : L ≃* J₀ := L.equivMapOfInjective C.subtype C.subtype_injective
    have r₁ : J₀ ⧸ pPrimeCore 2 J₀ ≃* L ⧸ pPrimeCore 2 L :=
      (QuotientGroup.congr (pPrimeCore 2 L) (pPrimeCore 2 J₀) e₁ (pPrimeCore_map_iso 2 e₁)).symm
    let e₃ : ↥(L.map π) ≃* W := MulEquiv.subgroupCongr hLJ
    have r₃ : ↥(L.map π) ⧸ pPrimeCore 2 ↥(L.map π) ≃* W ⧸ pPrimeCore 2 W :=
      QuotientGroup.congr _ _ e₃ (pPrimeCore_map_iso 2 e₃)
    have r₄ : W ⧸ pPrimeCore 2 W ≃* W :=
      (QuotientGroup.quotientMulEquivOfEq hWO).trans QuotientGroup.quotientBot
    exact ⟨((r₁.trans e₂).trans r₃).trans r₄⟩

theorem classical_of_subnormal {G : Type} [Group G] [Finite G] {z₀ : G} (hz2 : z₀ * z₀ = 1)
    (W : Subgroup (↥(centralizer ({z₀} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({z₀} : Set G))))
    (hsub : W.IsSubnormal)
    (hz : QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₀} : Set G)))
      ⟨z₀, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ W)
    (hW : (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (W ⧸ pPrimeCore 2 W ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
      GH74.GLS.IsDoubleCoverOfAlt (W ⧸ pPrimeCore 2 W) 7) :
    ∃ J₀ : Subgroup G, z₀ ∈ J₀ ∧ Open.IsSubnormal J₀ (centralizer ({z₀} : Set G)) ∧
      (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      Open.classicalInvolutionWitness J₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWO : pPrimeCore 2 W = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 W hsub,
      pPrimeCore_quotient_pPrimeCore_eq_bot, bot_subgroupOf]
  let r₄ : W ⧸ pPrimeCore 2 W ≃* W :=
    (QuotientGroup.quotientMulEquivOfEq hWO).trans QuotientGroup.quotientBot
  rcases hW with ⟨K', _, _, r, m, hr, hr2, hm, hK', h5, ⟨eW⟩⟩ | hA7
  · have hWq : IsQuasisimple W :=
      (LocalAnalysis.ComponentInitial.isQuasisimple_congr (r₄.symm.trans eW)).mpr
        (CatFactsSp4.isQuasisimple_SL2' (by omega))
    obtain ⟨J₀, hJ₀C, hJ₀p, hzJ₀, ⟨e₀⟩⟩ := exists_pComponent_of_isComponent hz2 _
      (fun c hc => mem_centralizer_singleton_iff.mp hc) _ W hWq hsub hz
    obtain ⟨hs, hS, hw⟩ :=
      classical_of_SL2 hJ₀C hJ₀p hr hr2 hm hK' ((e₀.trans r₄.symm).trans eW)
    exact ⟨J₀, hzJ₀, hs, hS, hw⟩
  · have hW7 := isDoubleCoverOfAlt_seven_congr r₄ hA7
    obtain ⟨J₀, hJ₀C, hJ₀p, hzJ₀, ⟨e₀⟩⟩ := exists_pComponent_of_isComponent hz2 _
      (fun c hc => mem_centralizer_singleton_iff.mp hc) _ W hW7.1 hsub hz
    obtain ⟨hs, hS, hw⟩ :=
      classical_of_twoA7 hJ₀C hJ₀p (isDoubleCoverOfAlt_seven_congr e₀.symm hW7)
    exact ⟨J₀, hzJ₀, hs, hS, hw⟩

theorem gs81Step10S8 {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}
    {d : H₁.Data}
    (W : Subgroup (↥(centralizer ({h.a * d.z} : Set H)) ⧸
      pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))
    (hsub : W.IsSubnormal)
    (hz : QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H)))
      ⟨h.a * d.z, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ W)
    (hW : (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (W ⧸ pPrimeCore 2 W ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
      GH74.GLS.IsDoubleCoverOfAlt (W ⧸ pPrimeCore 2 W) 7) :
    ∃ (z₀ : H) (J₀ : Subgroup H), orderOf z₀ = 2 ∧ z₀ ∈ J₀ ∧
      Open.IsSubnormal J₀ (centralizer ({z₀} : Set H)) ∧
      (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      Open.classicalInvolutionWitness J₀ := by
  have haa := Six.a_mul_a_self h.toHyp52
  have haz2 : h.a * d.z * (h.a * d.z) = 1 := by
    calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
      _ = h.a * (h.a * d.z) * d.z := by rw [d.z_comm_a]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, d.z_mul_self]
  have haz1 : h.a * d.z ≠ 1 := by
    intro h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right haa]
  obtain ⟨J₀, hzJ₀, hs, hS, hw⟩ := classical_of_subnormal haz2 W hsub hz hW
  exact ⟨h.a * d.z, J₀, orderOf_eq_prime (by rw [pow_two]; exact haz2) haz1, hzJ₀, hs, hS, hw⟩

end X10

end CFSG.ComponentClassification.GSThmB
