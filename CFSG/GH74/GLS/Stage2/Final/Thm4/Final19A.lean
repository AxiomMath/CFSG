module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.LocalCores CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.ComponentClassification.SmallLocal
open scoped commutatorElement

section Generic

theorem mem_center_of_commutators_central {J : Type*} [Group J] (hperf : Group.IsPerfect J) {x : J}
    (hx : ∀ y : J, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center J) : x ∈ Subgroup.center J := by
  let φ : J →* J :=
    { toFun := fun y => x * y * x⁻¹ * y⁻¹
      map_one' := by simp
      map_mul' := fun y w => by
        have hw := Subgroup.mem_center_iff.mp (hx w) y
        calc x * (y * w) * x⁻¹ * (y * w)⁻¹
            = (x * y * x⁻¹ * y⁻¹) * (y * (x * w * x⁻¹ * w⁻¹) * y⁻¹) := by group
          _ = (x * y * x⁻¹ * y⁻¹) * (x * w * x⁻¹ * w⁻¹) := by rw [hw]; group }
  have hφ : ∀ y, φ y = x * y * x⁻¹ * y⁻¹ := fun y => rfl
  have hle : commutator J ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h : φ b * φ a = φ a * φ b := Subgroup.mem_center_iff.mp (hx a) (φ b)
    simp only [commutatorElement_def, MonoidHom.mem_ker, map_mul, map_inv]
    calc φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹ = φ b * φ a * (φ a)⁻¹ * (φ b)⁻¹ := by rw [h]
      _ = 1 := by group
  rw [Group.IsPerfect.commutator_eq_top] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hle (Subgroup.mem_top y)
  rw [hφ] at h1
  calc y * x = (x * y * x⁻¹ * y⁻¹) * (y * x) := by rw [h1]; group
    _ = x * y := by group

theorem isQuasisimple_of_perfect_central_cover {J K : Type*} [Group J] [Group K] (φ : J →* K)
    (hφ : Function.Surjective φ) (hperf : Group.IsPerfect J) (hker : φ.ker ≤ Subgroup.center J)
    (hK : IsQuasisimple K) : IsQuasisimple J := by
  obtain ⟨_, hsimple, a, b, hab⟩ := hK
  let ψ : J →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = Subgroup.center J := by
    apply le_antisymm
    · intro x hx
      have hxK : φ x ∈ Subgroup.center K := by
        have h1 : QuotientGroup.mk' (Subgroup.center K) (φ x) = 1 := hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      apply mem_center_of_commutators_central hperf
      intro y
      apply hker
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      have h := Subgroup.mem_center_iff.mp hxK (φ y)
      calc φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = φ y * φ x * (φ x)⁻¹ * (φ y)⁻¹ := by rw [← h]
        _ = 1 := by group
    · intro x hx
      have hc : φ x ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := hφ g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      exact (QuotientGroup.eq_one_iff _).mpr hc
  let e : (J ⧸ Subgroup.center J) ≃* (K ⧸ Subgroup.center K) :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  refine ⟨hperf, (MulEquiv.isSimpleGroup_congr e).mpr hsimple, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

end Generic

section Group

variable {X : Type} [Group X] [Finite X]

@[expose] def fitOdd (X : Type) [Group X] : Subgroup X := fittingSubgroup X ⊓ pPrimeCore 2 X

theorem layer_le_pLayer : layer X ≤ pLayer X 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact solvable_prime_complement_core_perfect_layer_lift pPrimeCore_solvable layer_isPerfect
    map_layer_le

omit [Finite X] in
theorem conj_eq_of_comm {j f : X} (h : j * f = f * j) : j * f * j⁻¹ = f := by
  rw [h]
  group

theorem commute_of_perfect_subnormal {J : Subgroup X} (hJ : J.IsSubnormal) (hperf : Group.IsPerfect ↥J)
    (hcent : ∀ j ∈ J, ∀ f ∈ fitOdd X, j * f = f * j) :
    ∀ j ∈ J, ∀ r ∈ J ⊓ pPrimeCore 2 X, j * r = r * j := by
  set R : Subgroup X := J ⊓ pPrimeCore 2 X with hR
  have hRJ : R ≤ J := inf_le_left
  have hRN : R ≤ pPrimeCore 2 X := inf_le_right
  have hRnorm : ∀ j ∈ J, ∀ r ∈ R, j * r * j⁻¹ ∈ R := fun j hj r hr =>
    ⟨J.mul_mem (J.mul_mem hj (hRJ hr)) (J.inv_mem hj),
      (inferInstance : (pPrimeCore 2 X).Normal).conj_mem r (hRN hr) j⟩
  have hRsub : R.IsSubnormal := by
    refine Subgroup.IsSubnormal.step R J hRJ hJ ⟨fun r hr g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    exact hRnorm g g.2 r hr
  have hRsolv : Group.IsSolvable ↥R := by
    have := pPrimeCore_solvable (X := X)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRN)
  have hFR : (fittingSubgroup ↥R).map R.subtype = R ⊓ fittingSubgroup X :=
    fitting_subnormal_intersection hRsub
  have hF2 : ∀ f ∈ R ⊓ fittingSubgroup X, f ∈ fitOdd X := fun f hf => ⟨hf.2, hRN hf.1⟩
  have hcentR : ∀ j ∈ J, ∀ r ∈ R, ∀ f ∈ R ⊓ fittingSubgroup X,
      (r⁻¹ * (j * r * j⁻¹)) * f = f * (r⁻¹ * (j * r * j⁻¹)) := by
    intro j hj r hr f hf
    have hjf : j⁻¹ * f * j = f := by
      have := conj_eq_of_comm (hcent j⁻¹ (J.inv_mem hj) f (hF2 f hf))
      simpa using this
    have hf' : r * f * r⁻¹ ∈ R ⊓ fittingSubgroup X :=
      ⟨R.mul_mem (R.mul_mem hr hf.1) (R.inv_mem hr),
        (inferInstance : (fittingSubgroup X).Normal).conj_mem f hf.2 r⟩
    have hjf' : j * (r * f * r⁻¹) * j⁻¹ = r * f * r⁻¹ :=
      conj_eq_of_comm (hcent j hj _ (hF2 _ hf'))
    have key : (j * r * j⁻¹) * f * (j * r * j⁻¹)⁻¹ = r * f * r⁻¹ := by
      calc (j * r * j⁻¹) * f * (j * r * j⁻¹)⁻¹
          = j * r * (j⁻¹ * f * j) * r⁻¹ * j⁻¹ := by group
        _ = j * (r * f * r⁻¹) * j⁻¹ := by rw [hjf]; group
        _ = r * f * r⁻¹ := hjf'
    calc (r⁻¹ * (j * r * j⁻¹)) * f
        = r⁻¹ * ((j * r * j⁻¹) * f * (j * r * j⁻¹)⁻¹) * (j * r * j⁻¹) := by group
      _ = r⁻¹ * (r * f * r⁻¹) * (j * r * j⁻¹) := by rw [key]
      _ = f * (r⁻¹ * (j * r * j⁻¹)) := by group
  have hdisp : ∀ j ∈ J, ∀ r ∈ R, r⁻¹ * (j * r * j⁻¹) ∈ R ⊓ fittingSubgroup X := by
    intro j hj r hr
    have haR : r⁻¹ * (j * r * j⁻¹) ∈ R := R.mul_mem (R.inv_mem hr) (hRnorm j hj r hr)
    have hcentmem : (⟨_, haR⟩ : ↥R) ∈ Subgroup.centralizer (fittingSubgroup ↥R : Set ↥R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : (g : X) ∈ R ⊓ fittingSubgroup X := by
        rw [← hFR]
        exact ⟨g, hg, rfl⟩
      exact Subtype.ext (hcentR j hj r hr (g : X) hg').symm
    have hmem : (⟨_, haR⟩ : ↥R) ∈ fittingSubgroup ↥R :=
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRsolv hcentmem
    have : r⁻¹ * (j * r * j⁻¹) ∈ (fittingSubgroup ↥R).map R.subtype := ⟨_, hmem, rfl⟩
    rwa [hFR] at this
  have hfix : ∀ j ∈ J, ∀ a ∈ R ⊓ fittingSubgroup X, j * a * j⁻¹ = a := fun j hj a ha =>
    conj_eq_of_comm (hcent j hj a (hF2 a ha))
  have hcomm : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ∀ r ∈ R,
      (j₁ * j₂) * r * (j₁ * j₂)⁻¹ = (j₂ * j₁) * r * (j₂ * j₁)⁻¹ := by
    intro j₁ hj₁ j₂ hj₂ r hr
    have h1 := hdisp j₁ hj₁ r hr
    have h2 := hdisp j₂ hj₂ r hr
    have e1 : j₁ * (r⁻¹ * (j₂ * r * j₂⁻¹)) * j₁⁻¹ = r⁻¹ * (j₂ * r * j₂⁻¹) := hfix j₁ hj₁ _ h2
    have e2 : j₂ * (r⁻¹ * (j₁ * r * j₁⁻¹)) * j₂⁻¹ = r⁻¹ * (j₁ * r * j₁⁻¹) := hfix j₂ hj₂ _ h1
    have e3 := hcentR j₁ hj₁ r hr _ h2
    generalize ha₁ : r⁻¹ * (j₁ * r * j₁⁻¹) = a₁ at *
    generalize ha₂ : r⁻¹ * (j₂ * r * j₂⁻¹) = a₂ at *
    have r1 : j₁ * r * j₁⁻¹ = r * a₁ := by rw [← ha₁]; group
    have r2 : j₂ * r * j₂⁻¹ = r * a₂ := by rw [← ha₂]; group
    calc (j₁ * j₂) * r * (j₁ * j₂)⁻¹ = j₁ * (j₂ * r * j₂⁻¹) * j₁⁻¹ := by group
      _ = j₁ * (r * a₂) * j₁⁻¹ := by rw [r2]
      _ = (j₁ * r * j₁⁻¹) * (j₁ * a₂ * j₁⁻¹) := by group
      _ = (r * a₁) * a₂ := by rw [r1, e1]
      _ = r * (a₂ * a₁) := by rw [mul_assoc, e3]
      _ = (j₂ * r * j₂⁻¹) * (j₂ * a₁ * j₂⁻¹) := by rw [r2, e2, mul_assoc]
      _ = j₂ * (r * a₁) * j₂⁻¹ := by group
      _ = j₂ * (j₁ * r * j₁⁻¹) * j₂⁻¹ := by rw [r1]
      _ = (j₂ * j₁) * r * (j₂ * j₁)⁻¹ := by group
  have hle : ⁅J, J⁆ ≤ Subgroup.centralizer (R : Set X) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := hcomm g₁⁻¹ (J.inv_mem hg₁) g₂⁻¹ (J.inv_mem hg₂) r hr
    have hc : ⁅g₁, g₂⁆ = (g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hc]
    calc r * ((g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹))
        = (g₂⁻¹ * g₁⁻¹)⁻¹ * ((g₂⁻¹ * g₁⁻¹) * r * (g₂⁻¹ * g₁⁻¹)⁻¹) * (g₁⁻¹ * g₂⁻¹) := by group
      _ = (g₂⁻¹ * g₁⁻¹)⁻¹ * ((g₁⁻¹ * g₂⁻¹) * r * (g₁⁻¹ * g₂⁻¹)⁻¹) * (g₁⁻¹ * g₂⁻¹) := by rw [h]
      _ = ((g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹)) * r := by group
  rw [Subgroup.isPerfect_iff.mp hperf] at hle
  intro j hj r hr
  exact (Subgroup.mem_centralizer_iff.mp (hle hj) r hr).symm

theorem isComponent_of_isPComponent {J : Subgroup X} (hJ : IsPComponent 2 J)
    (hcent : ∀ j ∈ J, ∀ f ∈ fitOdd X, j * f = f * j) : IsComponent J := by
  have hperf : Group.IsPerfect ↥J :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hJ
  obtain ⟨K, hK, hsub, hmap, -⟩ := hJ
  have hcomm := commute_of_perfect_subnormal hsub hperf hcent
  refine ⟨?_, hsub⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  have hmem : ∀ x : ↥J, π (x : X) ∈ K := fun x => hmap ▸ Subgroup.mem_map_of_mem π x.2
  let φ : ↥J →* ↥K := (π.comp J.subtype).codRestrict K hmem
  have hφ : Function.Surjective φ := by
    intro k
    have hk : (k : X ⧸ pPrimeCore 2 X) ∈ J.map π := hmap ▸ k.2
    obtain ⟨x, hx, hxk⟩ := hk
    exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
  have hker : φ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxN : (x : X) ∈ pPrimeCore 2 X := by
      have h1 : φ x = 1 := hx
      have h2 : π (x : X) = 1 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subtype.ext (hcomm y y.2 (x : X) ⟨x.2, hxN⟩)
  exact isQuasisimple_of_perfect_central_cover φ hφ hperf hker hK.1

theorem pLayer_eq_layer_of_centralizes (h : ∀ j ∈ pLayer X 2, ∀ f ∈ fitOdd X, j * f = f * j) :
    pLayer X 2 = layer X :=
  le_antisymm
    (sSup_le fun _ hJ => le_sSup
      (isComponent_of_isPComponent hJ fun j hj f hf => h j (le_sSup hJ hj) f hf))
    layer_le_pLayer

end Group

end CFSG.GH74.GLS.Stage2.Final.Thm4
