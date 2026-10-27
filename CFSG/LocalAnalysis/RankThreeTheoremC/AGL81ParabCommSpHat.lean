module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpOTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)

structure SpCover {A : Type} [Group A] (Y P : Subgroup A) (r : ℕ) (K : Type) [Field K]
    (I : Set ℕ) where
  ρ : StatedSp r K ≃* ↥Y
  comap_eq : (P.subgroupOf Y).comap ρ.toMonoidHom = flagStabilizer r K I

namespace SpCover

variable {A : Type} [Group A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
  (C : SpCover Y P r K I)

theorem mem_flag_iff (g : StatedSp r K) : g ∈ flagStabilizer r K I ↔ ((C.ρ g : ↥Y) : A) ∈ P := by
  rw [← C.comap_eq]
  rfl

@[expose] noncomputable def toP : ↥(flagStabilizer r K I) →* ↥P :=
  (((Y.subtype).comp C.ρ.toMonoidHom).comp (flagStabilizer r K I).subtype).codRestrict P
    fun q => (C.mem_flag_iff q.1).mp q.2

@[simp] theorem coe_toP (x : ↥(flagStabilizer r K I)) :
    ((C.toP x : ↥P) : A) = ((C.ρ x : ↥Y) : A) := rfl

theorem toP_injective : Function.Injective C.toP := by
  intro x y h
  apply Subtype.ext
  apply C.ρ.injective
  apply Subtype.ext
  exact congrArg (fun z : ↥P => (z : A)) h

theorem toP_surjective (hPY : P ≤ Y) : Function.Surjective C.toP := by
  rintro ⟨w, hw⟩
  have hgQ : C.ρ.symm ⟨w, hPY hw⟩ ∈ flagStabilizer r K I := by
    rw [C.mem_flag_iff, MulEquiv.apply_symm_apply]
    exact hw
  exact ⟨⟨_, hgQ⟩, Subtype.ext (by rw [coe_toP, MulEquiv.apply_symm_apply])⟩

@[expose] noncomputable def toHat : ↥(flagStabilizer r K I) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp C.toP

theorem toHat_surjective (hPY : P ≤ Y) : Function.Surjective C.toHat :=
  (QuotientGroup.mk'_surjective _).comp (C.toP_surjective hPY)

theorem ker_toHat_eq : C.toHat.ker = (CFSG.pCore 2 ↥P).comap C.toP := by
  rw [toHat, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

variable [Finite K] [CharP K 2]

theorem ker_toHat (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hPY : P ≤ Y) :
    C.toHat.ker = (spFlagLeviHom (fun i hi => (hI i hi).2) htI).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI₁ : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  refine le_antisymm ?_ ?_
  ·
    rw [ker_toHat_eq]
    haveI : ((CFSG.pCore 2 ↥P).comap C.toP).Normal := CFSG.pCore_normal.comap _
    exact le_ker_spFlagLeviHom_of_normal_isPGroup hI₀ htI hI₁ hmax _
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥P)).comap_of_injective C.toP C.toP_injective)
  ·
    intro x hx
    have hker : IsPGroup 2 (spFlagLeviHom (K := K) hI₀ htI).ker :=
      isPGroup_ker_spFlagLeviHom hI₀ htI hI₁
    haveI : ((spFlagLeviHom (K := K) hI₀ htI).ker.map C.toP).Normal :=
      (MonoidHom.normal_ker (spFlagLeviHom (K := K) hI₀ htI)).map C.toP (C.toP_surjective hPY)
    have hle : (spFlagLeviHom (K := K) hI₀ htI).ker.map C.toP ≤ CFSG.pCore 2 ↥P :=
      le_sSup ⟨inferInstance, hker.map _⟩
    rw [ker_toHat_eq]
    exact hle ⟨x, hx, rfl⟩

end SpCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
