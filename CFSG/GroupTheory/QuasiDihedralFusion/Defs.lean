module

public import CFSG.CharacterTheory.Semidihedral.FocalFusion
public import CFSG.CharacterTheory.Wreathed.VNormalizerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.CharacterTheory.Wreathed.BaseFrattini
public import CFSG.GroupTheory.SylowActionKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare

public noncomputable section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter
open CFSG.BenderSuzuki.External

universe u

section SylowTypes

variable (H : Type u) [Group H]

@[expose] def HasSemidihedralSylow (n : ℕ) : Prop :=
  4 ≤ n ∧ ∀ S : Sylow 2 H, Nonempty (SemidihedralGroup n ≃* S)

@[expose] def HasWreathedSylow (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ S : Sylow 2 H, Nonempty ((S : Subgroup H) ≃* Wreath (2 ^ n))

@[expose] def HasQDOrWreathedSylowOfHeight (h : ℕ) : Prop :=
  (h = 1 ∧ ∃ n : ℕ, HasSemidihedralSylow H n) ∨ HasWreathedSylow H h

@[expose] def HasQDOrWreathedSylow : Prop :=
  ∃ h : ℕ, HasQDOrWreathedSylowOfHeight H h

@[expose] def HasGeneralizedQuaternionSylow : Prop :=
  ∀ P : Sylow 2 H, ∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* QuaternionGroup (2 ^ k))

end SylowTypes

section Vocabulary

variable {H : Type u} [Group H]

@[expose] def automizerIndex (T : Subgroup H) : ℕ :=
  (Subgroup.centralizer (T : Set H)).relIndex (Subgroup.normalizer (T : Set H))

theorem automizerIndex_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (R : Subgroup G) :
    automizerIndex (R.map e.toMonoidHom) = automizerIndex R := by
  have hC : (Subgroup.centralizer (R : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((R.map e.toMonoidHom : Subgroup H) : Set H) := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using congrArg e (h z hz)
    · intro h z hz
      have := h (e z) (Subgroup.mem_map_of_mem e.toMonoidHom hz)
      simpa using congrArg e.symm this
  rw [automizerIndex, automizerIndex, ← hC,
    ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]


@[expose] def outerAutomizerIndex (V : Subgroup H) : ℕ :=
  (V ⊔ Subgroup.centralizer (V : Set H)).relIndex (Subgroup.normalizer (V : Set H))

variable (H) in
@[expose] def conjClassCountOfOrder (k : ℕ) : ℕ :=
  (ConjClasses.mk '' {x : H | orderOf x = k}).ncard

@[expose] def centerOf (R : Subgroup H) : Subgroup H :=
  R ⊓ Subgroup.centralizer (R : Set H)

end Vocabulary

section Models

@[expose] def sdFourSubgroup (n : ℕ) : Subgroup (SemidihedralGroup n) :=
  Subgroup.closure {z n, s n}

@[expose] def sdQuaternionEight (n : ℕ) : Subgroup (SemidihedralGroup n) :=
  Subgroup.closure {r n ^ (2 ^ (n - 3)), r n * s n}

variable {H : Type u} [Group H]

@[expose] def qdFour {n : ℕ} (S : Subgroup H) (f : SemidihedralGroup n ≃* S) : Subgroup H :=
  (sdFourSubgroup n).map (FocalFusion.ambientHom n S f)

@[expose] def qdQuaternion {n : ℕ} (S : Subgroup H) (f : SemidihedralGroup n ≃* S) :
    Subgroup H :=
  (sdQuaternionEight n).map (FocalFusion.ambientHom n S f)

end Models

section Alternatives

variable {H : Type u} [Group H]

structure SemidihedralFusionQD {n : ℕ} (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    Prop where
  noIndexTwo : ∀ K : Subgroup H, K.index ≠ 2
  involutionClasses : conjClassCountOfOrder H 2 = 1
  orderFourClasses : conjClassCountOfOrder H 4 = 1
  fourIndex : automizerIndex (qdFour (S : Subgroup H) f) = 6
  quaternionIndex : outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 6

structure SemidihedralFusionQ {n : ℕ} (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    Prop where
  exists_kernel : ∃ K : Subgroup H, K.Normal ∧ K.index = 2 ∧ (∀ M : Subgroup K, M.index ≠ 2) ∧
    HasGeneralizedQuaternionSylow K
  center_weaklyClosed : WeaklyClosedIn (S : Subgroup H) (centerOf (S : Subgroup H))
  involutionClasses : conjClassCountOfOrder H 2 = 2
  orderFourClasses : conjClassCountOfOrder H 4 = 1
  fourIndex : automizerIndex (qdFour (S : Subgroup H) f) = 2
  quaternionIndex : outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 6

structure SemidihedralFusionD {n : ℕ} (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    Prop where
  exists_kernel : ∃ K : Subgroup H, K.Normal ∧ K.index = 2 ∧ (∀ M : Subgroup K, M.index ≠ 2) ∧
    HasDihedralSylowTwo K
  involutionClasses : conjClassCountOfOrder H 2 = 1
  orderFourClasses : conjClassCountOfOrder H 4 = 2
  fourIndex : automizerIndex (qdFour (S : Subgroup H) f) = 6
  quaternionIndex : outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 2

structure SemidihedralFusionComplement {n : ℕ} (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : Prop where
  normalComplement : HasNormalPComplement 2 H
  involutionClasses : conjClassCountOfOrder H 2 = 2
  orderFourClasses : conjClassCountOfOrder H 4 = 2
  fourIndex : automizerIndex (qdFour (S : Subgroup H) f) = 2
  quaternionIndex : outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 2

structure WreathedFusionQD {n : ℕ} (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    Prop where
  noIndexTwo : ∀ K : Subgroup H, K.index ≠ 2
  involutionClasses : conjClassCountOfOrder H 2 = 1
  baseIndex : automizerIndex (modelBase S e) = 6
  quaternionIndex : outerAutomizerIndex (modelV S e) = 6

structure WreathedFusionQ {n : ℕ} (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    Prop where
  exists_kernel : ∃ K : Subgroup H, K.Normal ∧ K.index = 2 ^ n ∧
    (∀ M : Subgroup K, M.index ≠ 2) ∧ HasGeneralizedQuaternionSylow K
  center_weaklyClosed : ∀ Z₀ : Subgroup H, Z₀ ≤ centerOf (S : Subgroup H) →
    WeaklyClosedIn (S : Subgroup H) Z₀
  involutionClasses : conjClassCountOfOrder H 2 = 2
  baseIndex : automizerIndex (modelBase S e) = 2
  quaternionIndex : outerAutomizerIndex (modelV S e) = 6

structure WreathedFusionD {n : ℕ} (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    Prop where
  exists_kernel : ∃ K : Subgroup H, K.Normal ∧ (∀ M : Subgroup K, M.index ≠ 2) ∧
    K ⊓ (S : Subgroup H) = modelBase S e
  involutionClasses : conjClassCountOfOrder H 2 = 2
  baseIndex : automizerIndex (modelBase S e) = 6
  quaternionIndex : outerAutomizerIndex (modelV S e) = 2

structure WreathedFusionComplement {n : ℕ} (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : Prop where
  normalComplement : HasNormalPComplement 2 H
  involutionClasses : conjClassCountOfOrder H 2 = 3
  baseIndex : automizerIndex (modelBase S e) = 2
  quaternionIndex : outerAutomizerIndex (modelV S e) = 2

end Alternatives

section Classes

variable {H : Type u} [Group H]

@[expose] def IsMaximalQuaternionIn (R Y : Subgroup H) : Prop :=
  Y ≤ R ∧
    ((∃ n : ℕ, 4 ≤ n ∧ ∃ ι : R →* SemidihedralGroup n, Function.Injective ι ∧
        (Y.subgroupOf R).map ι = Semidihedral.quaternionSubgroup n) ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ ι : R →* Wreath (2 ^ n), Function.Injective ι ∧
        (Y.subgroupOf R).map ι = Original.Y (2 ^ n))

structure IsQDGroup (H : Type u) [Group H] : Prop where
  sylow : HasQDOrWreathedSylow H
  noIndexTwo : ∀ K : Subgroup H, K.index ≠ 2
  involutions_isConj : ∀ x y : H, orderOf x = 2 → orderOf y = 2 → IsConj x y

structure IsQGroupData (R : Sylow 2 H) (K : Subgroup H) : Prop where
  normal : K.Normal
  index_eq_two_pow : ∃ k : ℕ, K.index = 2 ^ k
  noIndexTwo : ∀ M : Subgroup K, M.index ≠ 2
  quaternion : IsMaximalQuaternionIn (R : Subgroup H) (K ⊓ (R : Subgroup H))
  center_weaklyClosed : ∀ Z₀ : Subgroup H, Z₀ ≤ centerOf (R : Subgroup H) →
    WeaklyClosedIn (R : Subgroup H) Z₀

variable (H) in
@[expose] def IsQGroup : Prop :=
  ∃ (R : Sylow 2 H) (K : Subgroup H), IsQGroupData R K

structure IsDGroupData (K : Subgroup H) : Prop where
  normal : K.Normal
  index_eq_two : K.index = 2
  noIndexTwo : ∀ M : Subgroup K, M.index ≠ 2
  sylow : (∃ n : ℕ, HasSemidihedralSylow H n ∧ HasDihedralSylowTwo K) ∨
    ∃ n : ℕ, HasWreathedSylow H n ∧ ∀ P : Sylow 2 K, IsMulCommutative P

variable (H) in
@[expose] def IsDGroup : Prop :=
  (HasDihedralSylowTwo H ∧ ¬ HasNormalPComplement 2 H) ∨ ∃ K : Subgroup H, IsDGroupData K

@[expose] def IsDGroupWrt (T : Subgroup H) : Prop :=
  IsDGroup H ∧ IsKleinFour T ∧ 3 ∣ automizerIndex T

end Classes

end CFSG.QuasiDihedralFusion
