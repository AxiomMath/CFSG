module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Balance
public import CFSG.ClassicalInvolution.LBalance
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem deltaCore_eq_iInf_pPrimeCore {G : Type*} [Group G] (D : Subgroup G) :
    ClassicalInvolution.Balance.deltaCore D = ⨅ (d : G) (_ : d ∈ D) (_ : d ≠ 1),
      (pPrimeCore 2 (centralizer ({d} : Set G))).map (centralizer ({d} : Set G)).subtype := by
  simp only [ClassicalInvolution.Balance.deltaCore, Assembly.Dichotomy.involutionOddCore,
    Assembly.Dichotomy.oddCore_eq_pPrimeCore]

theorem isKleinFour_of_card_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x * x = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  have hsq' : ∀ x : H, x ^ 2 = 1 := fun x => by rw [pow_two, hsq]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq') with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem nonempty_mulEquiv_four {H : Type*} [Group H] {F : Subgroup H} (h4 : Nat.card F = 4)
    (hsq : ∀ f ∈ F, f * f = 1) :
    Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have : IsKleinFour F := isKleinFour_of_card_four h4 fun x => Subtype.ext (hsq x x.2)
  have : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isKleinFour_of_card_four (by rw [Nat.card_prod, Nat.card_eq_fintype_card]; rfl)
      (by decide)
  exact IsKleinFour.nonempty_mulEquiv

section Inner

variable {K : Type} [Group K]

theorem mulAut_mul_conj_mul_inv (φ : MulAut K) (k : K) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_injective_of_center_eq_bot (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ center K := by
    rw [mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut K => φ x) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * a = a * x * a⁻¹ * a := by rw [h]
      _ = a * x := by group
  rw [hZ, mem_bot] at hc
  exact hc

theorem inn_normal (H : Subgroup (MulAut K)) :
    ((MulAut.conj : K →* MulAut K).range.subgroupOf H).Normal := by
  constructor
  rintro x ⟨k, hk⟩ h
  refine ⟨(h : MulAut K) k, ?_⟩
  change MulAut.conj ((h : MulAut K) k) = (h : MulAut K) * (x : MulAut K) * (h : MulAut K)⁻¹
  rw [← mulAut_mul_conj_mul_inv, show MulAut.conj k = (x : MulAut K) from hk]

variable [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
include hnab

theorem center_eq_bot_of_simple : center K = ⊥ :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2

theorem eq_one_of_commute_conj {φ : MulAut K}
    (hφ : ∀ k : K, φ * MulAut.conj k = MulAut.conj k * φ) : φ = 1 := by
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)
  ext k
  have h := hφ k
  have h2 : MulAut.conj (φ k) = MulAut.conj k := by
    rw [← mulAut_mul_conj_mul_inv, h, mul_inv_cancel_right]
  exact hinj h2

variable {H : Subgroup (MulAut K)} (hH : (MulAut.conj : K →* MulAut K).range ≤ H)
include hH

theorem centralizer_inn_eq_bot :
    centralizer (((MulAut.conj : K →* MulAut K).range.subgroupOf H : Subgroup H) : Set H) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  rw [mem_bot]
  apply Subtype.ext
  apply eq_one_of_commute_conj hnab
  intro k
  have hk : (⟨MulAut.conj k, hH ⟨k, rfl⟩⟩ : H) ∈
      (MulAut.conj : K →* MulAut K).range.subgroupOf H := ⟨k, rfl⟩
  have := mem_centralizer_iff.mp hh _ hk
  exact (congrArg Subtype.val this).symm

theorem nonempty_innEquiv : Nonempty (K ≃* (MulAut.conj : K →* MulAut K).range.subgroupOf H) := by
  let ι : K →* H := (MulAut.conj : K →* MulAut K).codRestrict H fun k => hH ⟨k, rfl⟩
  have hinj : Function.Injective ι := fun a b hab =>
    conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab) (congrArg Subtype.val hab)
  have hrange : ι.range = (MulAut.conj : K →* MulAut K).range.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

variable [Finite K]

theorem generalizedFitting_eq_inn :
    GeneralizedFitting.subgroup H = (MulAut.conj : K →* MulAut K).range.subgroupOf H := by
  set I := (MulAut.conj : K →* MulAut K).range.subgroupOf H with hI
  have hIn : I.Normal := inn_normal H
  have hC : centralizer (I : Set H) = ⊥ := centralizer_inn_eq_bot hnab hH
  obtain ⟨e⟩ := nonempty_innEquiv hnab hH
  have hIs : IsSimpleGroup I := e.symm.isSimpleGroup
  have hInab : ∃ a b : I, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hIc : IsComponent I := by
    refine ⟨?_, Subgroup.Normal.isSubnormal hIn⟩
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hInab).1
  rw [← CFSG.generalizedFitting_eq_componentClassification]
  apply le_antisymm
  · refine sup_le ?_ (ClassicalInvolution.layer_le_of_centralizer_eq_bot I hC)
    have hFn : (fittingSubgroup H).Normal := (CFSG.LocalCores.fitting_nilpotent (G := H)).2.1
    have hFnil : Group.IsNilpotent (fittingSubgroup H) :=
      (CFSG.LocalCores.fitting_nilpotent (G := H)).1
    have hFI : fittingSubgroup H ⊓ I = ⊥ := by
      have hn : ((fittingSubgroup H ⊓ I).subgroupOf I).Normal :=
        Subgroup.Normal.subgroupOf (Subgroup.normal_inf_normal _ _) I
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((fittingSubgroup H ⊓ I).subgroupOf I) with
        hb | ht
      · rw [eq_bot_iff]
        intro x hx
        have : (⟨x, (mem_inf.mp hx).2⟩ : I) ∈ (fittingSubgroup H ⊓ I).subgroupOf I := hx
        rw [hb, mem_bot] at this
        rw [mem_bot]
        exact congrArg Subtype.val this
      · exfalso
        have hIF : I ≤ fittingSubgroup H := fun x hx => by
          have : (⟨x, hx⟩ : I) ∈ (fittingSubgroup H ⊓ I).subgroupOf I := ht ▸ mem_top _
          exact (mem_inf.mp this).1
        have : Group.IsSolvable (fittingSubgroup H) := by
          have := hFnil
          infer_instance
        have hsolv : Group.IsSolvable I :=
          Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIF)
            (Subgroup.inclusion_injective hIF)
        have : Group.IsPerfect I := hIc.1.1
        have : Nontrivial I := IsSimpleGroup.toNontrivial
        exact Group.IsPerfect.not_isSolvable I hsolv
    have hcomm : ⁅fittingSubgroup H, I⁆ = ⊥ := by
      rw [eq_bot_iff, ← hFI]
      exact Subgroup.commutator_le_inf _ _
    have hle : fittingSubgroup H ≤ centralizer (I : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hC] at hle
    exact hle.trans bot_le
  · exact (show I ≤ layer H from le_sSup hIc).trans le_sup_right

theorem nonempty_generalizedFitting_equiv : Nonempty (GeneralizedFitting.subgroup H ≃* K) := by
  rw [generalizedFitting_eq_inn hnab hH]
  obtain ⟨e⟩ := nonempty_innEquiv hnab hH
  exact ⟨e.symm⟩

theorem isSimpleGroup_generalizedFitting : IsSimpleGroup (GeneralizedFitting.subgroup H) := by
  obtain ⟨e⟩ := nonempty_generalizedFitting_equiv hnab hH
  exact e.isSimpleGroup

theorem exists_mul_ne_generalizedFitting :
    ∃ a b : GeneralizedFitting.subgroup H, a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_generalizedFitting_equiv hnab hH
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

end Inner

theorem isLocallyTwoBalanced_of_psl34 {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hmodel : Blueprint.LieModel K .PSL 3 2 2) :
    ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  intro H hH F hF4 hF2
  obtain ⟨e'⟩ := nonempty_generalizedFitting_equiv hnab hH
  rw [deltaCore_eq_iInf_pPrimeCore]
  exact deltaCore_eq_bot_of_psl34 (isSimpleGroup_generalizedFitting hnab hH)
    (exists_mul_ne_generalizedFitting hnab hH)
    (LieType.CurtisTits.lieModel_of_mulEquiv e'.symm hmodel) (nonempty_mulEquiv_four hF4 hF2)

end CFSG.ComponentClassification.GrSLit
