module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem pCoreOf_le_self (X : Subgroup A) : pCoreOf 2 X ≤ X :=
  Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf (X : Subgroup A) : IsPGroup 2 (pCoreOf 2 X) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype

theorem pcore_subgroupOf_pCoreOf (X : Subgroup A) :
    (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X :=
  Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem normalizer_pCoreOf (X : Subgroup A) : X ≤ normalizer (pCoreOf 2 X : Set A) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le_self X),
    pcore_subgroupOf_pCoreOf]
  exact CFSG.pCore_normal

theorem le_pCoreOf_of_normalizes {X N : Subgroup A} (hN2 : IsPGroup 2 N) (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set A)) : N ≤ pCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hnorm
  have hp : IsPGroup 2 (N.subgroupOf X) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hle : N.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hnormal, hp⟩
  have h2 := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNX] at h2

theorem pCoreOf_le_of_odd_index {X S : Subgroup A} (hS : IsPGroup 2 S) (hSX : S ≤ X)
    (hidx : ¬ 2 ∣ (S.subgroupOf X).index) : pCoreOf 2 X ≤ S := by
  have hSp : IsPGroup 2 (S.subgroupOf X) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  let Q : Sylow 2 ↥X := hSp.toSylow hidx
  have h1 : CFSG.pCore 2 ↥X ≤ S.subgroupOf X :=
    CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX] at h2
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {A : Type} [Group A] [Finite A] {K : Subgroup A}

theorem conj_mem_pCoreOf {x : A} (hx : x ∈ normalizer (K : Set A)) {n : A}
    (hn : n ∈ pCoreOf 2 K) : x * n * x⁻¹ ∈ pCoreOf 2 K := by
  have hxK : ∀ k : A, k ∈ K ↔ x * k * x⁻¹ ∈ K := mem_normalizer_iff.1 hx
  have hxK' : ∀ k : A, k ∈ K ↔ x⁻¹ * k * x ∈ K := mem_normalizer_iff''.1 hx
  let φ : ↥K ≃* ↥K :=
    { toFun := fun k => ⟨x * k * x⁻¹, (hxK k).1 k.2⟩
      invFun := fun k => ⟨x⁻¹ * k * x, (hxK' k).1 k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
  have hmap := CFSG.pCore_map_iso 2 φ
  have hφ : φ n' ∈ CFSG.pCore 2 ↥K := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hn'
  exact Subgroup.mem_map.2 ⟨φ n', hφ, rfl⟩

theorem normalizer_le_normalizer_pCoreOf {Y : Subgroup A} (hY : Y ≤ normalizer (K : Set A)) :
    Y ≤ normalizer (pCoreOf 2 K : Set A) := by
  intro x hx
  refine mem_normalizer_iff.2 fun n => ⟨conj_mem_pCoreOf (hY hx), fun hn => ?_⟩
  have := conj_mem_pCoreOf (hY (Y.inv_mem hx)) hn
  simpa [mul_assoc] using this
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
