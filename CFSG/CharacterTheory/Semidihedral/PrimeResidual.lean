module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.PFsection11_9
public import Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

public section

namespace CFSG.Semidihedral

universe u v

@[expose] def primeResidual (p : ℕ) (H : Type u) [Group H] : Subgroup H :=
  Subgroup.closure {x : H | ¬ p ∣ orderOf x}

theorem pPrime_element_mem_primeResidual {p : ℕ} {H : Type u} [Group H]
    {x : H} (hx : ¬ p ∣ orderOf x) : x ∈ primeResidual p H :=
  Subgroup.subset_closure hx

instance primeResidual_characteristic (p : ℕ) (H : Type u) [Group H] :
    (primeResidual p H).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro e
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  apply pPrime_element_mem_primeResidual
  simpa [orderOf_injective e.toMonoidHom e.injective] using hx

instance primeResidual_normal (p : ℕ) (H : Type u) [Group H] :
    (primeResidual p H).Normal := inferInstance

theorem primeResidual_quotient_isPGroup {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] :
    IsPGroup p (H ⧸ primeResidual p H) :=
  Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem
    (primeResidual p H) (fun _ hx => pPrime_element_mem_primeResidual hx)

theorem pPrime_element_hom_eq_one {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] {P : Type v} [Group P]
    (hP : IsPGroup p P) (f : H →* P) {x : H} (hx : ¬ p ∣ orderOf x) :
    f x = 1 := by
  by_contra hfx
  exact hx ((hP.dvd_orderOf hfx).trans (orderOf_map_dvd f x))

theorem primeResidual_le_ker {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] {P : Type v} [Group P]
    (hP : IsPGroup p P) (f : H →* P) : primeResidual p H ≤ f.ker := by
  rw [primeResidual, Subgroup.closure_le]
  exact fun _ hx => pPrime_element_hom_eq_one hP f hx

theorem primeResidual_hom_eq_one {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] {P : Type v} [Group P]
    (hP : IsPGroup p P) (f : primeResidual p H →* P) : f = 1 := by
  have hle : primeResidual p H ≤ f.ker.map (primeResidual p H).subtype := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    let xK : primeResidual p H := ⟨x, pPrime_element_mem_primeResidual hx⟩
    have hxK : ¬ p ∣ orderOf xK := by
      have horder : orderOf xK = orderOf x :=
        (orderOf_injective (primeResidual p H).subtype Subtype.coe_injective xK).symm
      rw [horder]
      exact hx
    exact Subgroup.mem_map.mpr ⟨xK, pPrime_element_hom_eq_one hP f hxK, rfl⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (hle x.property)
  have hax' : a = x := Subtype.ext hax
  subst a
  exact ha

theorem sylow_abelianization_card {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    Nat.card ((S : Subgroup H).map (Abelianization.of : H →* Abelianization H)) = p := by
  rw [← Subgroup.relIndex_ker, Abelianization.ker_of]
  exact hS

theorem abelian_pGroup_quotient_card_dvd {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p)
    {A : Type v} [Group A] [IsMulCommutative A]
    (hA : IsPGroup p A) (f : H →* A) (hf : Function.Surjective f) :
    Nat.card A ∣ p := by
  have hSf : (S : Subgroup H).map f = ⊤ := by
    exact top_unique ((hA.to_subgroup ⊤).le_sylow_of_normal (S.mapSurjective hf))
  have hcomm : commutator H ≤ f.ker := Abelianization.commutator_subset_ker f
  have hdvd := Subgroup.relIndex_dvd_of_le_left (S : Subgroup H) hcomm
  rw [Subgroup.relIndex_ker, hSf, Subgroup.card_top] at hdvd
  simpa only [Subgroup.relIndex, hS] using hdvd

theorem focal_quotient_card {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    Nat.card (S ⧸ (S : Subgroup H).focalSubgroupOf) = p := by
  rw [← Subgroup.index_eq_card, Subgroup.focalSubgroupOf_def,
    ← Subgroup.commutator_inf_eq_focalSubgroup S, Subgroup.inf_subgroupOf_right]
  exact hS

theorem primeResidual_quotient_isCyclic {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    IsCyclic (H ⧸ primeResidual p H) := by
  let P := H ⧸ primeResidual p H
  let f : H →* P ⧸ commutator P :=
    (QuotientGroup.mk' (commutator P)).comp (QuotientGroup.mk' (primeResidual p H))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective (commutator P)).comp
      (QuotientGroup.mk'_surjective (primeResidual p H))
  have hP : IsPGroup p P := primeResidual_quotient_isPGroup
  have hab : Nat.card (P ⧸ commutator P) ∣ p :=
    abelian_pGroup_quotient_card_dvd S hS (hP.to_quotient (commutator P)) f hf
  have hcyc : IsCyclic (P ⧸ commutator P) := isCyclic_of_card_dvd_prime hab
  exact Section11.theorem_11_9_isCyclic_of_nilpotent_cyclic_abelianization
    hP.isNilpotent hcyc

theorem primeResidual_quotient_card {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    Nat.card (H ⧸ primeResidual p H) = p := by
  let P := H ⧸ primeResidual p H
  have hP : IsPGroup p P := primeResidual_quotient_isPGroup
  have hcyclic : IsCyclic P := primeResidual_quotient_isCyclic S hS
  have hdiv : Nat.card P ∣ p :=
    abelian_pGroup_quotient_card_dvd S hS hP (QuotientGroup.mk' (primeResidual p H))
      (QuotientGroup.mk'_surjective (primeResidual p H))
  let T := S ⧸ (S : Subgroup H).focalSubgroupOf
  have hT : IsPGroup p T := S.isPGroup'.to_quotient _
  have hker : primeResidual p H ≤ (S : Subgroup H).transferFocal.ker :=
    primeResidual_le_ker hT _
  let f : P →* T :=
    QuotientGroup.lift (primeResidual p H) (S : Subgroup H).transferFocal hker
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Subgroup.transferFocal_surjective S y
    exact ⟨QuotientGroup.mk' (primeResidual p H) x, hx⟩
  have hpdiv : p ∣ Nat.card P := by
    rw [← focal_quotient_card S hS]
    exact Subgroup.card_dvd_of_surjective (f := f) hf
  exact Nat.dvd_antisymm hdiv hpdiv

theorem primeResidual_index {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    (primeResidual p H).index = p := by
  rw [Subgroup.index_eq_card]
  exact primeResidual_quotient_card S hS

theorem commutator_le_primeResidual {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    commutator H ≤ primeResidual p H := by
  have hcyclic := primeResidual_quotient_isCyclic S hS
  simpa only [QuotientGroup.ker_mk'] using
    Abelianization.commutator_subset_ker (QuotientGroup.mk' (primeResidual p H))

theorem sylow_primeResidual_relIndex {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    (primeResidual p H).relIndex (S : Subgroup H) = p := by
  let q := QuotientGroup.mk' (primeResidual p H)
  have hSq : (S : Subgroup H).map q = ⊤ :=
    top_unique ((primeResidual_quotient_isPGroup.to_subgroup ⊤).le_sylow_of_normal
      (S.mapSurjective (QuotientGroup.mk'_surjective (primeResidual p H))))
  rw [← QuotientGroup.ker_mk' (primeResidual p H), Subgroup.relIndex_ker,
    hSq, Subgroup.card_top]
  exact primeResidual_quotient_card S hS

theorem sylow_inf_primeResidual_eq_commutator {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    (S : Subgroup H) ⊓ primeResidual p H = (S : Subgroup H) ⊓ commutator H := by
  have hle : (commutator H).subgroupOf (S : Subgroup H) ≤
      (primeResidual p H).subgroupOf (S : Subgroup H) :=
    Subgroup.subgroupOf_mono _ (commutator_le_primeResidual S hS)
  have heq : (commutator H).subgroupOf (S : Subgroup H) =
      (primeResidual p H).subgroupOf (S : Subgroup H) := by
    by_contra hne
    have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
    have hK := sylow_primeResidual_relIndex S hS
    change ((primeResidual p H).subgroupOf (S : Subgroup H)).index = p at hK
    rw [hS, hK] at hlt
    exact (lt_irrefl p) hlt
  have hmap := congrArg (Subgroup.map (S : Subgroup H).subtype) heq
  simpa only [Subgroup.subgroupOf_map_subtype, inf_comm] using hmap.symm

theorem sylow_inf_primeResidual {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    ∃ T : Sylow p (primeResidual p H),
      (T : Subgroup (primeResidual p H)) =
        ((S : Subgroup H) ⊓ primeResidual p H).subgroupOf (primeResidual p H) := by
  let K := primeResidual p H
  have hrel : (S : Subgroup H).relIndex K = S.index := by
    have hprod : (S : Subgroup H).relIndex K * p = S.index * p := by
      calc
        (S : Subgroup H).relIndex K * p = ((S : Subgroup H) ⊓ K).index := by
          rw [Subgroup.index_inf, primeResidual_index S hS]
        _ = K.relIndex (S : Subgroup H) * S.index := by
          rw [inf_comm, Subgroup.index_inf]
        _ = S.index * p := by rw [sylow_primeResidual_relIndex S hS, mul_comm]
    exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hprod
  have hT : IsPGroup p ((S : Subgroup H).subgroupOf K) := S.isPGroup'.comap_subtype
  have hindex : ¬ p ∣ ((S : Subgroup H).subgroupOf K).index := by
    change ¬ p ∣ (S : Subgroup H).relIndex K
    rw [hrel]
    exact S.not_dvd_index
  exact ⟨hT.toSylow hindex, (Subgroup.inf_subgroupOf_right _ _).symm⟩

theorem primeResidual_unique_normal_index {p : ℕ} [Fact p.Prime]
    {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p)
    (J : Subgroup H) (hJ : J.Normal) (hindex : J.index = p) :
    J = primeResidual p H := by
  let : J.Normal := hJ
  have hcard : Nat.card (H ⧸ J) = p ^ 1 := by
    simpa only [pow_one, Subgroup.index_eq_card] using hindex
  have hle : primeResidual p H ≤ J := by
    simpa only [QuotientGroup.ker_mk'] using
      primeResidual_le_ker (IsPGroup.of_card hcard) (QuotientGroup.mk' J)
  apply Eq.symm
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
  rw [hindex, primeResidual_index S hS] at hlt
  exact (lt_irrefl p) hlt

theorem prime_residual_from_prime_sylow_abelianization
    {p : ℕ} [Fact p.Prime] {H : Type u} [Group H] [Finite H] (S : Sylow p H)
    (hS : ((commutator H).subgroupOf (S : Subgroup H)).index = p) :
    (primeResidual p H).Characteristic ∧
      (primeResidual p H).index = p ∧
      IsCyclic (H ⧸ primeResidual p H) ∧
      Nat.card (H ⧸ primeResidual p H) = p ∧
      (S : Subgroup H) ⊓ primeResidual p H = (S : Subgroup H) ⊓ commutator H ∧
      (∃ T : Sylow p (primeResidual p H),
        (T : Subgroup (primeResidual p H)) =
          ((S : Subgroup H) ⊓ commutator H).subgroupOf (primeResidual p H)) ∧
      (∀ J : Subgroup H, J.Normal → J.index = p → J = primeResidual p H) ∧
      (∀ (P : Type v) [Group P] [Finite P], IsPGroup p P →
        ∀ f : primeResidual p H →* P, f = 1) := by
  have hinter := sylow_inf_primeResidual_eq_commutator S hS
  obtain ⟨T, hT⟩ := sylow_inf_primeResidual S hS
  refine ⟨primeResidual_characteristic p H, primeResidual_index S hS,
    primeResidual_quotient_isCyclic S hS, primeResidual_quotient_card S hS,
    hinter, ⟨T, ?_⟩, primeResidual_unique_normal_index S hS, ?_⟩
  · simpa only [hinter] using hT
  · intro P _ _ hP f
    exact primeResidual_hom_eq_one hP f

end CFSG.Semidihedral
