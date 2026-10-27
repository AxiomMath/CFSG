module

public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut

public section

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {X : Type*} [Group X] {L : Subgroup X} [L.Normal]

@[expose] noncomputable def conjOnCenterQuotient (x : X) :
    MulAut (↥L ⧸ Subgroup.center ↥L) :=
  centerQuotientHom ↥L (MulAut.conjNormal (H := L) x)

theorem conjOnCenterQuotient_apply (x : X) (y : L) :
    conjOnCenterQuotient (L := L) x (QuotientGroup.mk' (Subgroup.center ↥L) y) =
      QuotientGroup.mk' (Subgroup.center ↥L)
        (MulAut.conjNormal (H := L) x y) :=
  onCenterQuotient_apply_mk (MulAut.conjNormal (H := L) x) y

@[expose] noncomputable def conjHom :
    X →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  (centerQuotientHom ↥L).comp (MulAut.conjNormal (H := L))

theorem conjHom_apply (x : X) :
    conjHom (L := L) x = conjOnCenterQuotient (L := L) x := rfl

@[expose] noncomputable def conjOuterHom :
    X →* Outer (↥L ⧸ Subgroup.center ↥L) :=
  (QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))).comp (conjHom (L := L))

theorem conjOuterHom_apply (x : X) :
    conjOuterHom (L := L) x =
      QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))
        (conjHom (L := L) x) := rfl

theorem conjOuterHom_eq_one_of_mem {x : X} (hx : x ∈ L) :
    conjOuterHom (L := L) x = 1 := by
  rw [conjOuterHom_apply]
  change QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))
    (centerQuotientHom ↥L (MulAut.conjNormal (H := L) x)) = 1
  have hconj : centerQuotientHom ↥L (MulAut.conjNormal (H := L) x) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥L) ⟨x, hx⟩) := by
    change centerQuotientHom ↥L (MulAut.conjNormal (H := L) (⟨x, hx⟩ : L)) = _
    rw [MulAut.conjNormal_val (H := L) (h := ⟨x, hx⟩)]
    exact centerQuotient_conj (⟨x, hx⟩ : L)
  rw [hconj]
  exact (QuotientGroup.eq_one_iff (N := inner (↥L ⧸ Subgroup.center ↥L)) _).mpr
    ⟨_, rfl⟩

theorem conjOuterHom_eq_one_of_mem_centralizer {x : X}
    (hx : x ∈ Subgroup.centralizer (L : Set X)) :
    conjOuterHom (L := L) x = 1 := by
  have hx' : MulAut.conjNormal (H := L) x = 1 := by
    rw [← MonoidHom.mem_ker,
      CFSG.LargeEvenClassification.Helpers.conjNormal_ker_eq_centralizer L]
    exact hx
  rw [conjOuterHom_apply, conjHom, MonoidHom.comp_apply, hx', map_one, map_one]

theorem sup_centralizer_le_ker_conjOuterHom :
    L ⊔ Subgroup.centralizer (L : Set X) ≤ (conjOuterHom (L := L)).ker := by
  intro x hx
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  rw [MonoidHom.mem_ker, map_mul, conjOuterHom_eq_one_of_mem hl,
    conjOuterHom_eq_one_of_mem_centralizer hc, mul_one]

theorem ker_conjHom (hL : CFSG.IsComponent L) :
    (conjHom (L := L)).ker = Subgroup.centralizer (L : Set X) := by
  have : Group.IsPerfect ↥L := hL.1.1
  rw [← CFSG.LargeEvenClassification.Helpers.conjNormal_ker_eq_centralizer L]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hx
    exact centerQuotientHom_injective ↥L (by simpa [conjHom] using hx)
  · intro hx
    rw [conjHom, MonoidHom.comp_apply, hx, map_one]

theorem mem_ker_conjHom_iff (hL : CFSG.IsComponent L) {x : X} :
    conjHom (L := L) x = 1 ↔ x ∈ Subgroup.centralizer (L : Set X) := by
  rw [← MonoidHom.mem_ker, ker_conjHom hL]

theorem ker_conjOuterHom (hL : CFSG.IsComponent L) :
    (conjOuterHom (L := L)).ker = L ⊔ Subgroup.centralizer (L : Set X) := by
  have : Group.IsPerfect ↥L := hL.1.1
  apply le_antisymm _ (sup_centralizer_le_ker_conjOuterHom (L := L))
  intro x hx
  apply CFSG.Quasithin.H13.NQCore.mem_sup_centralizer_of_conjNormal_inner
  have hmem : centerQuotientHom ↥L (MulAut.conjNormal (H := L) x) ∈
      inner (↥L ⧸ Subgroup.center ↥L) := by
    rw [← QuotientGroup.eq_one_iff (N := inner (↥L ⧸ Subgroup.center ↥L))]
    simpa [conjOuterHom_apply, conjHom] using hx
  obtain ⟨s, hs⟩ := hmem
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) s
  have h1 : MulAut.conjNormal (H := L) x = MulAut.conjNormal (H := L) (l : X) := by
    apply centerQuotientHom_injective ↥L
    rw [← hs, MulAut.conjNormal_val (H := L) (h := l), centerQuotient_conj l]
  rw [h1]
  exact ⟨l, (MulAut.conjNormal_val (H := L) (h := l)).symm⟩

theorem mem_ker_conjOuterHom_iff (hL : CFSG.IsComponent L) {x : X} :
    conjOuterHom (L := L) x = 1 ↔ x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
  rw [← MonoidHom.mem_ker, ker_conjOuterHom hL]

@[expose] noncomputable def conjQuotientHom :
    (X ⧸ (L ⊔ Subgroup.centralizer (L : Set X))) →*
      Outer (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.lift (N := L ⊔ Subgroup.centralizer (L : Set X))
    (conjOuterHom (L := L)) (sup_centralizer_le_ker_conjOuterHom (L := L))

theorem conjQuotientHom_apply (x : X) :
    conjQuotientHom (L := L)
        (QuotientGroup.mk' (L ⊔ Subgroup.centralizer (L : Set X)) x) =
      conjOuterHom (L := L) x := by
  simp [conjQuotientHom]

theorem conjHom_range_le_outer (hL : CFSG.IsComponent L) :
    Function.Injective (conjQuotientHom (L := L)) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (L ⊔ Subgroup.centralizer (L : Set X)) q
  exact (QuotientGroup.eq_one_iff (N := L ⊔ Subgroup.centralizer (L : Set X)) x).mpr
    ((ker_conjOuterHom hL).le
      (MonoidHom.mem_ker.mpr (by simpa [conjQuotientHom] using hq)))

end CFSG.LieType.OutStructure
