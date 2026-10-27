module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpBlockCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.GroupTheory.Commutator.SupNormalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (comSp fixSp)
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {B : LinearMap.BilinForm (ZMod 2) V}

theorem nonempty_mulEquiv_pointwiseStab_statedSp
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hV : Module.finrank (ZMod 2) V = 2 * n)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    Nonempty (↥(pointwiseStab (linIsometryGroup B) P) ≃* StatedSp (n - 1) (ZMod 2)) := by
  have hK : Module.finrank (ZMod 2) (B.orthogonal P) = 2 * n - 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBn P, hV, hP2]
  have hK2 : Module.finrank (ZMod 2) (B.orthogonal P) = 2 * (n - 1) := by omega
  have halt : (B.restrict (B.orthogonal P)).IsAlt := fun x => hB.self_eq_zero x.1
  have hnd : (B.restrict (B.orthogonal P)).Nondegenerate :=
    orthogonal_nondegenerate hB hBn hPnd
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_bilinIsometryGroup_equiv_statedSp
      (K := ZMod 2) (V := ↥(B.orthogonal P)) hnd halt
  have hm' : m = n - 1 := by omega
  subst hm'
  exact ⟨(pointwiseStabEquiv hB hPnd).trans e⟩

theorem center_pointwiseStab_eq_bot
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hV : Module.finrank (ZMod 2) V = 2 * n)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    Subgroup.center ↥(pointwiseStab (linIsometryGroup B) P) = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_pointwiseStab_statedSp hB hBn n P hPnd hV hP2
  have h := Subgroup.map_center_eq e
  rw [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (n - 1)] at h
  have h' : Subgroup.map e.toMonoidHom (Subgroup.center
      ↥(pointwiseStab (linIsometryGroup B) P)) =
      Subgroup.map e.toMonoidHom (⊥ : Subgroup ↥(pointwiseStab (linIsometryGroup B) P)) := by
    rw [Subgroup.map_bot]
    exact h
  exact (Subgroup.map_injective e.injective).eq_iff.mp h' 


theorem pointwiseStab_normal_in_centralizer
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    ((pointwiseStab (linIsometryGroup B) P).subgroupOf
      (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)))).Normal := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let D : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) P
  have hCeq : C = Subgroup.zpowers y ⊔ D :=
    centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hDle : D ≤ C := by rw [hCeq]; exact le_sup_right
  rw [Subgroup.normal_subgroupOf_iff hDle]
  intro d c hd hc
  rw [mem_pointwiseStab]
  intro p hp
  have hcinv : c⁻¹ ∈ C := C.inv_mem hc
  have hcinv_maps : ∀ p ∈ P, ((c⁻¹ : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V) p ∈ P :=
    maps_plane_of_mem_centralizer hB hBn y hy3 P hP hcinv
  have hcinv_eq : ((c⁻¹ : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V) =
      ((c : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V)⁻¹ := by simp
  have hd_fix : ((d : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V)
      (((c : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V)⁻¹ p) =
      ((c : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V)⁻¹ p := by
    simpa [hcinv_eq] using mem_pointwiseStab.mp hd _ (hcinv_maps p hp)
  change (((c : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V) *
      ((d : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V) *
        ((c : ↥(linIsometryGroup B)) : V ≃ₗ[ZMod 2] V)⁻¹) p = p
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hd_fix]
  simp

theorem zpowers_normal_in_centralizer
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    ((Subgroup.zpowers y).subgroupOf
      (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)))).Normal := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let A : Subgroup ↥(linIsometryGroup B) := Subgroup.zpowers y
  have hCeq : C = A ⊔ pointwiseStab (linIsometryGroup B) P :=
    centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hAle : A ≤ C := by rw [hCeq]; exact le_sup_left
  apply Subgroup.normal_of_le_center
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro c
  have haA : (a : ↥(linIsometryGroup B)) ∈ A := Subgroup.mem_subgroupOf.mp ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haA
  have hcy : (c : ↥(linIsometryGroup B)) * y = y * (c : ↥(linIsometryGroup B)) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
  have hcy' : Commute y (c : ↥(linIsometryGroup B)) := (commute_iff_eq y _).mpr hcy.symm
  exact ((hcy'.zpow_left k).eq).symm

theorem zpowers_le_centralizer_pointwiseStab
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    (Subgroup.zpowers y).subgroupOf
        (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))) ≤
      Subgroup.centralizer
        (↑((pointwiseStab (linIsometryGroup B) P).subgroupOf
          (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)))) :
          Set ↥(Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)))) := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let A : Subgroup ↥(linIsometryGroup B) := Subgroup.zpowers y
  let D : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) P
  have hCeq : C = A ⊔ D := centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hDle : D ≤ C := by rw [hCeq]; exact le_sup_right
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have haA : (a : ↥(linIsometryGroup B)) ∈ A := Subgroup.mem_subgroupOf.mp ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haA
  have hdD : (d : ↥(linIsometryGroup B)) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hdC : (d : ↥(linIsometryGroup B)) ∈ C := hDle hdD
  have hdy : (d : ↥(linIsometryGroup B)) * y = y * (d : ↥(linIsometryGroup B)) :=
    Subgroup.mem_centralizer_singleton_iff.mp hdC
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
  have hdy' : Commute y (d : ↥(linIsometryGroup B)) := (commute_iff_eq y _).mpr hdy.symm
  exact ((hdy'.zpow_left k).eq).symm

theorem commutator_centralizer_le_pointwiseStab
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    ⁅Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)),
      Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))⁆ ≤
      pointwiseStab (linIsometryGroup B) P := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let A : Subgroup ↥(linIsometryGroup B) := Subgroup.zpowers y
  let D : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) P
  have hCeq : C = A ⊔ D := centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hAle : A ≤ C := by rw [hCeq]; exact le_sup_left
  have hDle : D ≤ C := by rw [hCeq]; exact le_sup_right
  have hAn : (A.subgroupOf C).Normal :=
    zpowers_normal_in_centralizer hB hBn y hy3 P hPnd hP hfix hP2
  have hDn : (D.subgroupOf C).Normal :=
    pointwiseStab_normal_in_centralizer hB hBn y hy3 P hPnd hP hfix hP2
  have hAD : A.subgroupOf C ≤ Subgroup.centralizer ((D.subgroupOf C) : Set ↥C) :=
    zpowers_le_centralizer_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hAA : ⁅A.subgroupOf C, A.subgroupOf C⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hcomm : ⁅A.subgroupOf C ⊔ D.subgroupOf C,
      A.subgroupOf C ⊔ D.subgroupOf C⁆ ≤ D.subgroupOf C := by
    refine (CFSG.Goldschmidt.Sec82.commutator_sup_le_of_le_centralizer hAD).trans ?_
    rw [hAA, bot_sup_eq]
    exact Subgroup.commutator_le_left _ _
  have hsup : A.subgroupOf C ⊔ D.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAle hDle, ← hCeq]
    simp
  rw [hsup, ← commutator_def] at hcomm
  have hmap := Subgroup.map_mono (f := C.subtype) hcomm
  rw [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hDle] at hmap
  change ⁅C, C⁆ ≤ D
  exact hmap


theorem layer_centralizer_eq_pointwiseStab
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2)
    (hK6 : 6 ≤ Module.finrank (ZMod 2) (B.orthogonal P)) :
    GLALayer (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))) =
        pointwiseStab (linIsometryGroup B) P ∧
      IsComponentOf (pointwiseStab (linIsometryGroup B) P)
        (Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))) := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let D : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) P
  have hDle : D ≤ C := by
    change D ≤ Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
    rw [centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2]
    exact le_sup_right
  have hcomm : ⁅C, C⁆ ≤ D :=
    commutator_centralizer_le_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hq : CFSG.IsQuasisimple ↥D := by
    have hcard : Nat.card (ZMod 2) = 2 := by rw [Nat.card_zmod]
    exact isQuasisimple_pointwiseStab hB hBn hPnd (by omega)
      (Or.inr (Or.inr ⟨hcard, hK6⟩))
  exact CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.glaLayer_eq_of_commutator_le hDle hcomm hq

theorem inf_centralizer_pointwiseStab_eq_zpowers
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ)
    (A : Subgroup ↥(linIsometryGroup B)) (hAe : IsElemAbelian 3 A)
    (y : ↥(linIsometryGroup B)) (hyA : y ∈ A) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2)
    (hV : Module.finrank (ZMod 2) V = 2 * n) :
    A ⊓ Subgroup.centralizer (pointwiseStab (linIsometryGroup B) P : Set
      ↥(linIsometryGroup B)) = Subgroup.zpowers y := by
  classical
  let C : Subgroup ↥(linIsometryGroup B) := Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))
  let D : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) P
  have hCeq : C = Subgroup.zpowers y ⊔ D :=
    centralizer_eq_zpowers_sup_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2
  have hDle : D ≤ C := by rw [hCeq]; exact le_sup_right
  have hAleC : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨y, hyA⟩)
  have hDcenter : Subgroup.center D = ⊥ :=
    center_pointwiseStab_eq_bot hB hBn n P hPnd hV hP2
  refine le_antisymm ?_ ?_
  · intro b hb
    obtain ⟨hbA, hbCen⟩ := Subgroup.mem_inf.mp hb
    have hbC : b ∈ C := hAleC hbA
    obtain ⟨k, hk3, d, hdD, hbd⟩ :=
      exists_zpow_mul_mem_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2 hbC
    have hdEq : d = b * (y ^ k)⁻¹ := by
      rw [hbd]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have hdEq : d = b * (y ^ k)⁻¹ := by
      rw [hbd]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have hdCen : d ∈ Subgroup.centralizer (D : Set ↥(linIsometryGroup B)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhb : h * b = b * h := (Subgroup.mem_centralizer_iff.mp hbCen) h hh
      have hhC : h ∈ C := hDle hh
      have hhy : Commute y h :=
        (commute_iff_eq y h).mpr (Subgroup.mem_centralizer_singleton_iff.mp hhC).symm
      have hhpow : Commute h (y ^ k) := (hhy.zpow_left k).symm
      rw [hdEq]
      calc h * (b * (y ^ k)⁻¹) = (h * b) * (y ^ k)⁻¹ := by group
      _ = (b * h) * (y ^ k)⁻¹ := by rw [hhb]
      _ = b * (h * (y ^ k)⁻¹) := by group
      _ = b * ((y ^ k)⁻¹ * h) := by rw [hhpow.inv_right.eq]
      _ = (b * (y ^ k)⁻¹) * h := by group
    have hdcenter : (⟨d, hdD⟩ : ↥D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hdCen (x : ↥(linIsometryGroup B)) x.2)
    rw [hDcenter, Subgroup.mem_bot] at hdcenter
    have hd1 : d = 1 := congrArg Subtype.val hdcenter
    rw [hbd, hd1, one_mul]
    exact Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) k
  · rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    refine ⟨hyA, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hDle hd)

theorem stdAt_of_oneBlock
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ)
    (A : Subgroup ↥(linIsometryGroup B)) (hAe : IsElemAbelian 3 A)
    (y : ↥(linIsometryGroup B)) (hyA : y ∈ A) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2)
    (hK6 : 6 ≤ Module.finrank (ZMod 2) (B.orthogonal P))
    (hV : Module.finrank (ZMod 2) V = 2 * n) :
    StdAt A y := by
  have hlayer := layer_centralizer_eq_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2 hK6
  refine ⟨?_, ?_⟩
  · rw [hlayer.1]
    exact hlayer.2
  · rw [hlayer.1]
    exact inf_centralizer_pointwiseStab_eq_zpowers hB hBn n A hAe y hyA hy3 P hPnd hP hfix hP2 hV

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
