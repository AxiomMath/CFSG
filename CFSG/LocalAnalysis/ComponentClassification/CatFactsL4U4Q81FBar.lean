module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81E8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mk_center (z : X) :
    (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) ∈ center (MBar z) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)

theorem orderOf_mk_self {z : X} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) = 2 := by
  have hsq : (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({z} : Set X))) ^ 2 =
      1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]; rfl)
  refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]) ?_
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem component_tBar (h219 : Harris82Lemma219Input) {z t : X}
    (htz : t ∈ centralizer ({z} : Set X)) (ht : orderOf t = 2)
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {A : Subgroup (MBar z)} (hA : IsComponent A) :
    (QuotientGroup.mk ⟨t, htz⟩ : MBar z) ∈ normalizer (A : Set (MBar z)) ∧
      IsPGroup 2 (↥(A ⊓ centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)}) ⧸
        pPrimeCore 2 ↥(A ⊓ centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))
    (QuotientGroup.mk'_surjective _) (GSThmB.OddQuot.not_two_dvd_card_ker
      (H := ↥(centralizer ({z} : Set X))))
  have hAp : IsPComponent 2 A :=
    (isTwoComponent_iff_isPComponent A).mp ((isTwoComponent_iff_isComponent hO A).mpr hA)
  obtain ⟨L, hL, hLA⟩ := hbij.surjOn hAp
  set K : Subgroup X := L.map (centralizer ({z} : Set X)).subtype with hK
  have hKF : K ≤ centralizer ({z} : Set X) := map_subtype_le L
  have hKL : K.subgroupOf (centralizer ({z} : Set X)) = L := by
    rw [hK, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
  have hK2 : IsTwoComponentIn K (centralizer {z}) := by
    rw [isTwoComponentIn_iff hKF, hKL]
    exact hL
  have hKt := map_conj_eq_of_isTwoComponentIn h219 ht htz hC hK2
  obtain ⟨-, -, hN, hP⟩ := Lemma47.fbar_component htz ht hC hK2 hKt
  rw [hKL] at hN hP
  have hLA' : L.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) = A := hLA
  rw [hLA'] at hN hP
  exact ⟨hN, hP⟩

theorem component_not_le_centralizer (h219 : Harris82Lemma219Input) {z t : X}
    (htz : t ∈ centralizer ({z} : Set X)) (ht : orderOf t = 2)
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {A : Subgroup (MBar z)} (hA : IsComponent A) :
    ¬ A ≤ centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)} := by
  intro hle
  obtain ⟨-, hP⟩ := component_tBar h219 htz ht hC hA
  have hAinf : A ⊓ centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)} = A := inf_eq_left.mpr hle
  have hP' : IsPGroup 2 (↥A ⧸ pPrimeCore 2 ↥A) :=
    isPGroup_quot_of_mulEquiv (MulEquiv.subgroupCongr hAinf) hP
  have : Group.IsPerfect ↥A := hA.1.1
  have hbot := eq_bot_of_isPerfect_of_isPGroup_quotient hP' (J := ⊤)
    (Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥A)).symm.toMonoidHom)
      (MulEquiv.surjective _))
  have hnt := LocalCores.isQuasisimple_nontrivial hA.1
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥A
  apply hab
  have ha : a ∈ (⊤ : Subgroup ↥A) := mem_top a
  have hb : b ∈ (⊤ : Subgroup ↥A) := mem_top b
  rw [hbot, mem_bot] at ha hb
  rw [ha, hb]

variable {z : X} {R : Subgroup X}

theorem isSylowOf_barR (hR : IsSylowOf 2 R ⊤) (hRz : R ≤ centralizer ({z} : Set X)) :
    IsSylowOf 2 ((R.subgroupOf (centralizer {z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 R (centralizer {z}) := hR.of_le hRz le_top
  have h2 := isSylowOf_subgroupOf h1 (le_refl _)
  rw [subgroupOf_self] at h2
  have h3 := isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) h2
  rwa [← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h3

theorem center_barR (hR : IsPGroup 2 R) (hRz : R ≤ centralizer ({z} : Set X))
    (hZ : R ⊓ centralizer (R : Set X) = zpowers z) :
    (R.subgroupOf (centralizer {z})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) ⊓
      centralizer (((R.subgroupOf (centralizer {z})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) : Subgroup (MBar z)) :
          Set (MBar z)) =
      zpowers (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) := by
  have hzR : z ∈ R := by
    have : z ∈ R ⊓ centralizer (R : Set X) := by rw [hZ]; exact mem_zpowers z
    exact (mem_inf.mp this).1
  have hRp : IsPGroup 2 (R.subgroupOf (centralizer ({z} : Set X))) :=
    hR.of_equiv (subgroupOfEquivOfLe hRz).symm
  apply le_antisymm
  · rintro y ⟨⟨r, hr, rfl⟩, hyc⟩
    have hrZ : (r : X) ∈ R ⊓ centralizer (R : Set X) := by
      refine mem_inf.mpr ⟨hr, mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 := mem_centralizer_iff.mp hyc
        (QuotientGroup.mk' _ ⟨x, hRz hx⟩) ⟨⟨x, hRz hx⟩, hx, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      have h2 := GSThmB.OddQuot.injOn_of_isPGroup hRp
        (mul_mem (show (⟨x, hRz hx⟩ : ↥(centralizer ({z} : Set X))) ∈
          R.subgroupOf (centralizer {z}) from hx) hr)
        (mul_mem hr (show (⟨x, hRz hx⟩ : ↥(centralizer ({z} : Set X))) ∈
          R.subgroupOf (centralizer {z}) from hx)) h1
      exact congrArg Subtype.val h2
    rw [hZ] at hrZ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hrZ
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  · rw [zpowers_le]
    refine ⟨⟨⟨z, _⟩, hzR, rfl⟩, mem_centralizer_iff.mpr fun y _ => ?_⟩
    exact (mem_center_iff.mp (mk_center z) y)

end Q81

end CFSG.ComponentClassification.HarrisLit
