module

public import CFSG.CharacterTheory.Semidihedral.CentralizerResidual
public import CFSG.Foundations.Basic

public section

namespace CFSG.Semidihedral.CoreResidual

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual

variable {H : Type*} [Group H] [Finite H]

theorem pPrimeCore_le_primeResidual (p : ℕ) [Fact p.Prime] :
    pPrimeCore p H ≤ primeResidual p H := by
  intro x hx
  apply pPrime_element_mem_primeResidual
  intro hdvd
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
    (pPrimeCore_coprime_card (G := H) (p := p)))
      (hdvd.trans ((pPrimeCore p H).orderOf_dvd_natCard hx))

theorem pPrimeCore_map_characteristic_eq (p : ℕ) [Fact p.Prime]
    (K : Subgroup H) [K.Characteristic] (hK : pPrimeCore p H ≤ K) :
    (pPrimeCore p K).map K.subtype = pPrimeCore p H := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  · have hsub : (pPrimeCore p H).subgroupOf K ≤ pPrimeCore p K := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
      exact pPrimeCore_coprime_card
    rw [← Subgroup.map_subgroupOf_eq_of_le hK]
    exact Subgroup.map_mono hsub

theorem pPrimeCore_primeResidual_map (p : ℕ) [Fact p.Prime] :
    (pPrimeCore p (primeResidual p H)).map (primeResidual p H).subtype =
      pPrimeCore p H :=
  pPrimeCore_map_characteristic_eq p _ (pPrimeCore_le_primeResidual p)

omit [Finite H] in
theorem oddCore_eq_twoPrimeCore : oddCore H = pPrimeCore 2 H := by
  rw [oddCore_eq_piCore, pPrimeCore_eq_piCore]

@[expose] noncomputable def coreQuotientSylowEquiv (p : ℕ) [Fact p.Prime]
    (P : Sylow p H) :
    P ≃* P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore p H)) := by
  let q := QuotientGroup.mk' (pPrimeCore p H)
  let h := q.subgroupMap (P : Subgroup H)
  have hi : Function.Injective h := by
    intro x y hxy
    exact quotient_pPrimeCore_subgroupMap_injective (P : Subgroup H) P.isPGroup'
      (congrArg Subtype.val hxy)
  exact (MulEquiv.ofBijective h ⟨hi, q.subgroupMap_surjective _⟩).trans
    (MulEquiv.subgroupCongr
      (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore p H)) P).symm)

theorem coreQuotientSylowEquiv_coe (p : ℕ) [Fact p.Prime] (P : Sylow p H) (x : P) :
    (coreQuotientSylowEquiv p P x : H ⧸ pPrimeCore p H) =
      QuotientGroup.mk' (pPrimeCore p H) (x : H) := rfl

theorem coreQuotientSylowEquiv_order (p : ℕ) [Fact p.Prime] (P : Sylow p H) (x : P) :
    orderOf (coreQuotientSylowEquiv p P x : H ⧸ pPrimeCore p H) = orderOf x := by
  rw [coreQuotientSylowEquiv_coe]
  exact orderOf_injective _
    (quotient_pPrimeCore_subgroupMap_injective (P : Subgroup H) P.isPGroup') x

theorem coreQuotient_involution_order (P : Sylow 2 H) (t : H) (htP : t ∈ P)
    (ht : orderOf t = 2) : orderOf (QuotientGroup.mk' (pPrimeCore 2 H) t) = 2 := by
  rw [← coreQuotientSylowEquiv_coe 2 P (⟨t, htP⟩ : P), coreQuotientSylowEquiv_order]
  exact (Subgroup.orderOf_coe (⟨t, htP⟩ : P)).symm.trans ht

theorem coreQuotient_unique_involution (P : Sylow 2 H) (t : H)
    (ht : t ∈ Subgroup.center H)
    (hP : ∀ x : P, orderOf x = 2 → (x : H) = t)
    (x : H ⧸ pPrimeCore 2 H) (hx : orderOf x = 2) :
    x = QuotientGroup.mk' (pPrimeCore 2 H) t := by
  let T := P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 H))
  let e := coreQuotientSylowEquiv 2 P
  have htwo : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow T x htwo
  have hyorder : orderOf (y : H ⧸ pPrimeCore 2 H) = 2 :=
    (conjugate_orderOf_eq hxy).symm.trans hx
  have haorder : orderOf (e.symm y) = 2 := by
    have h := coreQuotientSylowEquiv_order 2 P (e.symm y)
    change orderOf (e (e.symm y) : H ⧸ pPrimeCore 2 H) = orderOf (e.symm y) at h
    rw [e.apply_symm_apply] at h
    exact h.symm.trans hyorder
  have hy : (y : H ⧸ pPrimeCore 2 H) = QuotientGroup.mk' (pPrimeCore 2 H) t := by
    have h := coreQuotientSylowEquiv_coe 2 P (e.symm y)
    change (e (e.symm y) : H ⧸ pPrimeCore 2 H) =
      QuotientGroup.mk' (pPrimeCore 2 H) (e.symm y : H) at h
    rw [e.apply_symm_apply, hP _ haorder] at h
    exact h
  rw [hy] at hxy
  have htbar : QuotientGroup.mk' (pPrimeCore 2 H) t ∈
      Subgroup.center (H ⧸ pPrimeCore 2 H) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (pPrimeCore 2 H))
      (Subgroup.mem_map_of_mem _ ht)
  exact (conjugate_to_central_iff htbar).mp hxy

variable {G : Type*} [Group G] [Finite G]

theorem centralizerCore_le_residual (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    pPrimeCore 2 (involutionCentralizer n S f) ≤ oddResidual n S f :=
  pPrimeCore_le_primeResidual 2

theorem centralizerCore_eq_residualCore_map (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    pPrimeCore 2 (involutionCentralizer n S f) =
      (pPrimeCore 2 (oddResidual n S f)).map (oddResidual n S f).subtype :=
  (pPrimeCore_primeResidual_map 2).symm

theorem centralizerCore_disjoint_involution (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    Disjoint (pPrimeCore 2 (involutionCentralizer n S f))
      (Subgroup.zpowers (centralInvolution n S f)) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [Nat.card_zpowers, centralInvolution_order n hn S f]
  exact (pPrimeCore_coprime_card (p := 2)).symm

@[expose] noncomputable def residualSylow (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : Sylow 2 (oddResidual n S f) :=
  (oddResidual_sylow n hn S f hG).choose

theorem residualSylow_eq (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    (residualSylow n hn S f hG : Subgroup (oddResidual n S f)) =
      (centralizerQuaternion n hn S f).subgroupOf (oddResidual n S f) :=
  (oddResidual_sylow n hn S f hG).choose_spec

@[expose] noncomputable def residualQuaternionEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    QuaternionGroup (2 ^ (n - 3)) ≃* residualSylow n hn S f hG :=
  (centralizerQuaternionEquiv n hn S f).trans
    ((Subgroup.subgroupOfEquivOfLe
      (centralizerQuaternion_le_oddResidual n hn S f hG)).symm.trans
        (MulEquiv.subgroupCongr (residualSylow_eq n hn S f hG).symm))

theorem residualQuaternionEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (x : QuaternionGroup (2 ^ (n - 3))) :
    ((residualQuaternionEquiv n hn S f hG x : oddResidual n S f) :
      involutionCentralizer n S f) =
        (centralizerQuaternionEquiv n hn S f x : involutionCentralizer n S f) := rfl

@[expose] def residualInvolution (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : oddResidual n S f :=
  ⟨centralInvolution n S f, centralInvolution_mem_oddResidual n hn S f hG⟩

theorem residualInvolution_mem_center (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    residualInvolution n hn S f hG ∈ Subgroup.center (oddResidual n S f) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S f) x

theorem residualInvolution_mem_sylow (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    residualInvolution n hn S f hG ∈ residualSylow n hn S f hG := by
  change residualInvolution n hn S f hG ∈
    (residualSylow n hn S f hG : Subgroup (oddResidual n S f))
  rw [residualSylow_eq]
  exact centralInvolution_mem_quaternion n hn S f

theorem residualInvolution_order (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    orderOf (residualInvolution n hn S f hG) = 2 := by
  rw [← Subgroup.orderOf_coe (residualInvolution n hn S f hG)]
  exact centralInvolution_order n hn S f

theorem residualSylow_unique_involution (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (x : residualSylow n hn S f hG)
    (hx : orderOf x = 2) : (x : oddResidual n S f) = residualInvolution n hn S f hG := by
  apply Subtype.ext
  apply oddResidual_unique_involution n hn S f hG (x : oddResidual n S f)
  exact (Subgroup.orderOf_coe x).trans hx

theorem residualCoreQuotient_involution_iff (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (x : oddResidual n S f ⧸ pPrimeCore 2 (oddResidual n S f)) :
    orderOf x = 2 ↔ x = QuotientGroup.mk' (pPrimeCore 2 (oddResidual n S f))
      (residualInvolution n hn S f hG) := by
  constructor
  · exact coreQuotient_unique_involution (residualSylow n hn S f hG)
      (residualInvolution n hn S f hG) (residualInvolution_mem_center n hn S f hG)
      (residualSylow_unique_involution n hn S f hG) x
  · rintro rfl
    exact coreQuotient_involution_order (residualSylow n hn S f hG)
      (residualInvolution n hn S f hG) (residualInvolution_mem_sylow n hn S f hG)
      (residualInvolution_order n hn S f hG)

@[expose] noncomputable def residualCoreQuotientQuaternionEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    QuaternionGroup (2 ^ (n - 3)) ≃*
      (residualSylow n hn S f hG).mapSurjective
        (QuotientGroup.mk'_surjective (pPrimeCore 2 (oddResidual n S f))) :=
  (residualQuaternionEquiv n hn S f hG).trans
    (coreQuotientSylowEquiv 2 (residualSylow n hn S f hG))

theorem residualCoreQuotientQuaternionEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (x : QuaternionGroup (2 ^ (n - 3))) :
    (residualCoreQuotientQuaternionEquiv n hn S f hG x :
      oddResidual n S f ⧸ pPrimeCore 2 (oddResidual n S f)) =
    QuotientGroup.mk' (pPrimeCore 2 (oddResidual n S f))
      (residualQuaternionEquiv n hn S f hG x : oddResidual n S f) := rfl

omit [Finite G] in
theorem residualCoreQuotient_hom_eq_one (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {P : Type*} [Group P]
    (hP : IsPGroup 2 P)
    (φ : oddResidual n S f ⧸ pPrimeCore 2 (oddResidual n S f) →* P) : φ = 1 := by
  have h := oddResidual_hom_eq_one n S f hP
    (φ.comp (QuotientGroup.mk' (pPrimeCore 2 (oddResidual n S f))))
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 (oddResidual n S f)) x
  exact DFunLike.congr_fun h y

end CFSG.Semidihedral.CoreResidual
