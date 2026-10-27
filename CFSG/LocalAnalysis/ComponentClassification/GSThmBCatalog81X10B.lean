module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10A
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X10

theorem classical_of_SL2 {G : Type} [Group G] [Finite G] {z₀ : G} {J : Subgroup G}
    (hJC : J ≤ centralizer {z₀}) (hJ : IsPComponent 2 (J.subgroupOf (centralizer {z₀})))
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (e : J ⧸ pPrimeCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Open.IsSubnormal J (centralizer ({z₀} : Set G)) ∧
      (∃ S : Sylow 2 J, ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      Open.classicalInvolutionWitness J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  let e' : J ⧸ pPrimeCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f) :=
    e.trans (ClassicalModels.specialLinearFieldEquiv
      (ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hK) (Fin 2))
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hrank : CFSG.pRank 2 J ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e']
    exact TBLit.pRank_two_SL2_le_one hchar
  have hA : IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two J)).symm
      (TBLit.twoComponent_coreQuotient_quasisimple hJC hJ)
  obtain ⟨-, -, -, -, -, -, r, hr, hSJ, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hA
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨eS⟩ := hSJ S
  refine ⟨TBLit.open_isSubnormal_of_isPComponent hJC hJ, ⟨S, r, hr, ⟨eS⟩⟩, ?_⟩
  exact .inl ⟨p, f, inferInstance, hp2, by omega,
    ⟨(QuotientGroup.quotientMulEquivOfEq (TBLit.classicalInvolutionOddCore_eq J)).trans e'⟩⟩

theorem exists_pComponent_of_subnormal {G : Type} [Group G] [Finite G] {z₀ : G}
    (hz2 : z₀ * z₀ = 1) {J : Subgroup G} (hJC : J ≤ centralizer {z₀}) (hzJ : z₀ ∈ J) {K : Type}
    [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (e : J ⧸ pPrimeCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsub : ((J.subgroupOf (centralizer {z₀})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₀} : Set G))))).IsSubnormal) :
    ∃ J₀ : Subgroup G, J₀ ≤ centralizer {z₀} ∧
      IsPComponent 2 (J₀.subgroupOf (centralizer {z₀})) ∧ z₀ ∈ J₀ ∧
      Nonempty (J₀ ⧸ pPrimeCore 2 J₀ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z₀} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set J' := J.subgroupOf C with hJ'
  set Jb := J'.map π with hJb
  have hJbO : pPrimeCore 2 Jb = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 Jb hsub,
      pPrimeCore_quotient_pPrimeCore_eq_bot, bot_subgroupOf]
  obtain ⟨q₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π OddQuot.not_two_dvd_card_ker J'
  let eJ : J' ≃* J := subgroupOfEquivOfLe hJC
  have q₀ : J' ⧸ pPrimeCore 2 J' ≃* J ⧸ pPrimeCore 2 J :=
    QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)
  have eb : Jb ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (((QuotientGroup.quotientMulEquivOfEq hJbO).trans QuotientGroup.quotientBot).symm.trans
      q₁.symm).trans (q₀.trans e)
  have hJbq : IsQuasisimple Jb :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr eb).mpr (CatFactsSp4.isQuasisimple_SL2' h4)
  obtain ⟨hL, hLJ⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 Jb ⟨hJbq, hsub⟩
  set L := CatalogueBPrimeJoin.canonicalPrimeLift 2 Jb with hLdef
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
    have hz₀C : z₀ ∈ C := mem_centralizer_singleton_iff.mpr rfl
    have hmem : π ⟨z₀, hz₀C⟩ ∈ L.map π := by
      rw [hLJ]
      exact mem_map_of_mem _ (show (⟨z₀, hz₀C⟩ : C) ∈ J' from hzJ)
    obtain ⟨l, hlL, hlz⟩ := hmem
    obtain ⟨o, ho⟩ : ∃ o : C, o = (⟨z₀, hz₀C⟩ : C)⁻¹ * l := ⟨_, rfl⟩
    have hoO : o ∈ pPrimeCore 2 ↥C := by
      rw [ho, ← QuotientGroup.eq]
      exact hlz.symm
    have hcomm : (⟨z₀, hz₀C⟩ : C) * o = o * ⟨z₀, hz₀C⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp o.2).symm
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
    let e₃ : ↥(L.map π) ≃* Jb := MulEquiv.subgroupCongr hLJ
    have r₃ : ↥(L.map π) ⧸ pPrimeCore 2 ↥(L.map π) ≃* Jb ⧸ pPrimeCore 2 Jb :=
      QuotientGroup.congr _ _ e₃ (pPrimeCore_map_iso 2 e₃)
    have r₄ : Jb ⧸ pPrimeCore 2 Jb ≃* Jb :=
      (QuotientGroup.quotientMulEquivOfEq hJbO).trans QuotientGroup.quotientBot
    exact ⟨(((r₁.trans e₂).trans r₃).trans r₄).trans eb⟩

theorem gs81Step10B {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}
    {d : H₁.Data} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {J : Subgroup H}
    (hJ : AzComp K d J)
    (hsub : ((J.subgroupOf (centralizer {h.a * d.z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))).IsSubnormal) :
    ∃ (z₀ : H) (J₀ : Subgroup H), orderOf z₀ = 2 ∧ z₀ ∈ J₀ ∧
      Open.IsSubnormal J₀ (centralizer ({z₀} : Set H)) ∧
      (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      Open.classicalInvolutionWitness J₀ := by
  obtain ⟨hJLC, -, hazJ, ⟨e⟩⟩ := hJ
  have hJC : J ≤ centralizer {h.a * d.z} := hJLC.trans inf_le_right
  have haa := Six.a_mul_a_self h.toHyp52
  have haz2 : h.a * d.z * (h.a * d.z) = 1 := by
    calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
      _ = h.a * (h.a * d.z) * d.z := by rw [d.z_comm_a]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, d.z_mul_self]
  have haz1 : h.a * d.z ≠ 1 := by
    intro h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right haa]
  obtain ⟨J₀, hJ₀C, hJ₀p, hazJ₀, ⟨e₀⟩⟩ :=
    exists_pComponent_of_subnormal haz2 hJC hazJ (by omega) e hsub
  obtain ⟨hs, hS, hw⟩ := classical_of_SL2 hJ₀C hJ₀p hp hp2 hf hK e₀
  exact ⟨h.a * d.z, J₀, orderOf_eq_prime (by rw [pow_two]; exact haz2) haz1, hazJ₀, hs, hS, hw⟩

end X10

end CFSG.ComponentClassification.GSThmB
