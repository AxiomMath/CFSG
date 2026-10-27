module

public import CFSG.ClassicalInvolution.LBalance.SylowFixing
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools

public section

namespace CFSG.ClassicalInvolution.LBalanceProof

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores
  CFSG.GroupTheory Subgroup
open scoped commutatorElement

section

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conjNormal_mem_sylowFixingAut {E : Subgroup X} [E.Normal] (S : Subgroup E) (g : X)
    (hg : ∀ s ∈ S, g * (s : X) = (s : X) * g) :
    (MulAut.conjNormal g : MulAut E) ∈ sylowFixingAut S := by
  simp only [sylowFixingAut, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  intro s hs
  apply Subtype.ext
  change g * (s : X) * g⁻¹ = (s : X)
  rw [hg s hs, mul_inv_cancel_right]
theorem false_of_commutator_le_oddCore (hG : GlaubermanSylowFixingSolvable) (hX : pPrimeCore 2 X = ⊥) (z : X) (hz : orderOf z = 2)
    (P : Sylow 2 (layer X)) (H : Subgroup X) (hH : H = centralizer ({z} : Set X))
    (hPz : (P : Subgroup (layer X)).map (layer X).subtype ≤ H)
    (K : Subgroup H) (hK : IsPComponent 2 K)
    (h2 : (generalizedFitting X).subgroupOf H ≤ normalizer (K : Set H))
    (h3 : ⁅K, (generalizedFitting X).subgroupOf H⁆ ≤
      (Open.componentClassificationOddCore K).map K.subtype) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFnil := (CFSG.LocalCores.fitting_nilpotent (G := X))
  have hFn : (fittingSubgroup X).Normal := hFnil.2.1
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : (layer X).Normal := inferInstance
  have hFs : (generalizedFitting X).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  have hKperf : Group.IsPerfect K := isPerfect_of_isPComponent hK
  have hK2 : TwoComponents.IsTwoComponent K := (CatalogueBAlternating.pComponent_two_iff K).1 hK
  have hLZ : ⁅K.map H.subtype, pCore 2 X⁆ = ⊥ := by
    subst hH
    exact twoComponent_centralizes_pCore hz K hK
  have hFP : fittingSubgroup X ≤ pCore 2 X :=
    le_sSup ⟨hFn, CFSG.isPGroup_of_nilpotent_normal _ hFn hFnil.1 hX⟩
  set S : Subgroup X := (P : Subgroup (layer X)).map (layer X).subtype with hS
  have hSp : IsPGroup 2 S := P.isPGroup'.map (layer X).subtype
  have hSE : S ≤ layer X := Subgroup.map_subtype_le _
  have hSF : S ≤ generalizedFitting X := hSE.trans le_sup_right
  have hSH : S ≤ H := hPz
  let R : Subgroup H := S.subgroupOf H
  have hRp : IsPGroup 2 R := hSp.comap_of_injective H.subtype H.subtype_injective
  have hRY : R ≤ (generalizedFitting X).subgroupOf H := fun r hr => hSF hr
  let M : Subgroup H := (Open.componentClassificationOddCore K).map K.subtype
  have hMK : M ≤ K := Subgroup.map_subtype_le _
  have hMsub : M.subgroupOf K = Open.componentClassificationOddCore K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hMn : (M.subgroupOf K).Normal := by
    rw [hMsub]
    infer_instance
  have hModd : Odd (Nat.card M) := by
    have h : Nat.card M = Nat.card (Open.componentClassificationOddCore K) :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toEquiv).symm
    rw [h]
    exact ComponentClassification.OddCore.odd_card K
  have hRM : R ≤ normalizer (M : Set H) := by
    intro r hr
    have hrK : r ∈ normalizer (K : Set H) := h2 (hRY hr)
    rw [mem_normalizer_iff]
    intro m
    constructor
    · exact fun hm => mul_mem_oddCore_map_of_mem_normalizer K r hrK m hm
    · intro hm
      have hrK' : r⁻¹ ∈ normalizer (K : Set H) := inv_mem hrK
      have h1 := mul_mem_oddCore_map_of_mem_normalizer K r⁻¹ hrK' (r * m * r⁻¹) hm
      have e : r⁻¹ * (r * m * r⁻¹) * r⁻¹⁻¹ = m := by group
      rw [e] at h1
      exact h1
  have hcomm : ⁅K, R⁆ ≤ M := (Subgroup.commutator_mono le_rfl hRY).trans h3
  have hC := exists_centralizer_mul_of_commutator_le K R M hRp hMK hMn hModd hRM hcomm
  have hEcore := pPrimeCore_layer_eq_bot hX
  have hΓ : Group.IsSolvable (sylowFixingAut (P : Subgroup (layer X))) :=
    hG _ hEcore P
  let ρ : X →* MulAut (layer X) := MulAut.conjNormal
  let Kh : Subgroup X := K.map H.subtype
  let Mh : Subgroup X := M.map H.subtype
  have hKhperf : Group.IsPerfect Kh := Group.IsPerfect.map H.subtype
  let PK : Subgroup (MulAut (layer X)) := Kh.map ρ
  have hPKperf : Group.IsPerfect PK := Group.IsPerfect.map ρ
  let N1 : Subgroup (MulAut (layer X)) := Mh.map ρ
  have hN1P : N1 ≤ PK := Subgroup.map_mono (Subgroup.map_mono hMK)
  have hN1n : (N1.subgroupOf PK).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN1P]
    rintro _ _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨H.subtype (k * m * k⁻¹),
      ⟨k * m * k⁻¹, (Subgroup.normal_subgroupOf_iff hMK).1 hMn m k hm hk, rfl⟩,
      by simp [map_mul, map_inv]⟩
  have hMsolv : Group.IsSolvable M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hModd
  have hN1solv : Group.IsSolvable N1 := by
    have h := isSolvable_map_of_isSolvable (ρ.comp H.subtype) M
    have e : N1 = M.map (ρ.comp H.subtype) := by
      show (M.map H.subtype).map ρ = _
      rw [Subgroup.map_map]
    rw [e]
    exact h
  have hPKbot : PK = ⊥ := by
    refine perfect_eq_bot_of_solvable_product PK N1 hN1P hN1n (sylowFixingAut (P : Subgroup (layer X))) ?_
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨c, hcK, m, hm, hkcm⟩ := hC k hk
    refine ⟨ρ (c : X), ?_, ρ (m : X), ⟨(m : X), ⟨m, hm, rfl⟩, rfl⟩, ?_⟩
    · apply conjNormal_mem_sylowFixingAut (E := layer X) (P : Subgroup (layer X)) (c : X)
      intro s hs
      have hsS : ((s : layer X) : X) ∈ S := ⟨s, hs, rfl⟩
      have hsR : (⟨(s : X), hSH hsS⟩ : H) ∈ R := hsS
      have := mem_centralizer_iff.1 hcK.2 _ hsR
      exact (congrArg Subtype.val this).symm
    · rw [hkcm]
      simp [map_mul]
  have hKE : Kh ≤ centralizer ((layer X : Subgroup X) : Set X) := by
    intro g hg
    have hmem : ρ g ∈ PK := ⟨g, hg, rfl⟩
    rw [hPKbot, Subgroup.mem_bot] at hmem
    rw [mem_centralizer_iff]
    intro e he
    have h1 := congrArg (fun φ : MulAut (layer X) => ((φ ⟨e, he⟩ : layer X) : X)) hmem
    have h2 : g * e * g⁻¹ = e := h1
    calc e * g = g * e * g⁻¹ * g := by rw [h2]
      _ = g * e := by group
  have hKF : Kh ≤ centralizer ((fittingSubgroup X : Subgroup X) : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLZ).trans (Subgroup.centralizer_le hFP)
  have hKFs : Kh ≤ centralizer ((generalizedFitting X : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ centralizer ({g} : Set X) := by
      have hle : generalizedFitting X ≤ centralizer ({g} : Set X) := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · rw [mem_centralizer_singleton_iff]
          exact mem_centralizer_iff.1 (hKF hg) y hy
        · rw [mem_centralizer_singleton_iff]
          exact mem_centralizer_iff.1 (hKE hg) y hy
      exact hle hy
    rw [mem_centralizer_singleton_iff] at hy'
    exact hy'
  have hKhF : Kh ≤ generalizedFitting X := fun g hg => centralizer_generalizedFitting_le X (hKFs hg)
  have hcomm0 : ⁅Kh, Kh⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_iff.1 (hKFs hg) y (hKhF hy)
  have hKh_bot : Kh = ⊥ := by
    rw [← Subgroup.commutator_eq_self (H := Kh)]
    exact hcomm0
  have hK_bot : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K H.subtype_injective).1 hKh_bot
  have : Nontrivial K := TwoComponents.nontrivial hK2
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this hK_bot
theorem twoComponent_centralizer_le_layer (hG : GlaubermanSylowFixingSolvable) (hX : pPrimeCore 2 X = ⊥) (z : X) (hz : orderOf z = 2)
    (P : Sylow 2 (layer X))
    (H : Subgroup X) (hH : H = centralizer ({z} : Set X))
    (hPz : (P : Subgroup (layer X)).map (layer X).subtype ≤ H)
    (K : Subgroup H) (hK : IsPComponent 2 K) :
    K.map H.subtype ≤ layer X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFnil := (CFSG.LocalCores.fitting_nilpotent (G := X))
  have hFn : (fittingSubgroup X).Normal := hFnil.2.1
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : (layer X).Normal := inferInstance
  have hFs : (generalizedFitting X).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  have hKperf : Group.IsPerfect K := isPerfect_of_isPComponent hK
  have hK2 : TwoComponents.IsTwoComponent K := (CatalogueBAlternating.pComponent_two_iff K).1 hK
  have hYn : ((generalizedFitting X).subgroupOf H).Normal := Subgroup.normal_subgroupOf
  have hsub : Open.IsSubnormal ((generalizedFitting X).subgroupOf H) ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal hYn.isSubnormal
  rcases TwoComponentSubnormal.contains_or_normalizes_core K
    ((generalizedFitting X).subgroupOf H) hK2 hsub with h1 | ⟨h2, h3⟩
  ·
    have hKF : K.map H.subtype ≤ generalizedFitting X := by
      rintro _ ⟨k, hk, rfl⟩
      exact h1 hk
    have : Group.IsPerfect (K.map H.subtype) := Group.IsPerfect.map H.subtype
    have : Group.IsSolvable (fittingSubgroup X) := by
      have := hFnil.1
      infer_instance
    exact perfect_le_of_le_sup_solvable (K.map H.subtype) (layer X) (fittingSubgroup X) (by
      rw [sup_comm]; exact hKF)
  · exact (false_of_commutator_le_oddCore hG hX z hz P H hH hPz K hK h2 h3).elim
end

end CFSG.ClassicalInvolution.LBalanceProof
