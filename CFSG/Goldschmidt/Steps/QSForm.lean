module

public import CFSG.Goldschmidt.Statements
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport (mem_sylowCenter_map)

@[expose] def QSFormAt (G : Type*) [Group G] (Q : Subgroup G) : Prop :=
  ∀ β : G → G → ZMod 2,
    (∀ x ∈ Q, ∀ x' ∈ Q, ∀ y ∈ Q, β (x * x') y = β x y + β x' y) →
    (∀ x ∈ Q, ∀ y ∈ Q, ∀ y' ∈ Q, β x (y * y') = β x y + β x y') →
    (∀ z ∈ sylowCenter Q, ∀ y ∈ Q, β z y = 0) →
    (∀ x ∈ Q, ∀ z ∈ sylowCenter Q, β x z = 0) →
    (∀ n ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ Q, ∀ y ∈ Q,
      β (n⁻¹ * x * n) (n⁻¹ * y * n) = β x y) →
    ∀ x ∈ Q, ∀ y ∈ Q, β x y = 0

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem qsFormAt_map (e : G ≃* G') {Q : Subgroup G} (h : QSFormAt G Q) :
    QSFormAt G' (Q.map e.toMonoidHom) := by
  unfold QSFormAt at h ⊢
  intro β h₁ h₂ h₃ h₄ h₅
  have hQ : ∀ {x : G}, x ∈ Q → e x ∈ Q.map e.toMonoidHom := fun hx =>
    Subgroup.mem_map_of_mem e.toMonoidHom hx
  have hZ : ∀ {z : G}, z ∈ sylowCenter Q → e z ∈ sylowCenter (Q.map e.toMonoidHom) :=
    fun hz => (mem_sylowCenter_map e).mpr hz
  have hN : ∀ {n : G}, n ∈ Subgroup.normalizer (Q : Set G) →
      e n ∈ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') := fun hn => by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hn
  have key := h (fun x y => β (e x) (e y))
    (fun x hx x' hx' y hy => by
      simp only [map_mul]
      exact h₁ _ (hQ hx) _ (hQ hx') _ (hQ hy))
    (fun x hx y hy y' hy' => by
      simp only [map_mul]
      exact h₂ _ (hQ hx) _ (hQ hy) _ (hQ hy'))
    (fun z hz y hy => h₃ _ (hZ hz) _ (hQ hy))
    (fun x hx z hz => h₄ _ (hQ hx) _ (hZ hz))
    (fun n hn x hx y hy => by
      simp only [map_mul, map_inv]
      exact h₅ _ (hN hn) _ (hQ hx) _ (hQ hy))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact key x hx y hy

theorem qsFormAt_of_mulEquiv [Finite G] (e : G ≃* G') (h : ∃ Q : Sylow 2 G', QSFormAt G' Q)
    (P : Sylow 2 G) : QSFormAt G P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_equiv G e.toEquiv
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 2 G,
      (P₀ : Subgroup G) = (Q : Subgroup G').map e.symm.toMonoidHom :=
    ⟨Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
      Sylow.coe_mapSurjective e.symm.surjective Q⟩
  have h₀ : QSFormAt G P₀ := by
    rw [hP₀]
    exact qsFormAt_map e.symm hQ
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P₀ P
  rw [Sylow.coe_subgroup_smul]
  exact qsFormAt_map (MulAut.conj g) h₀

end Transport

section Suzuki

open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

theorem qsFormAt_rootSub (m : ℕ) (hm : 0 < m) : QSFormAt (SuzukiMatrixGroup m) (rootSub m) := by
  unfold QSFormAt
  intro β h₁ h₂ h₃ h₄ h₅
  have hS : ∀ a b, root m a b ∈ rootSub m := root_mem m
  have hZ : ∀ b, root m 0 b ∈ sylowCenter (rootSub m) := fun b =>
    (mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩
  have hZl : ∀ a b c, β (root m 0 c) (root m a b) = 0 := fun a b c => h₃ _ (hZ c) _ (hS a b)
  have hZr : ∀ a b c, β (root m a b) (root m 0 c) = 0 := fun a b c => h₄ _ (hS a b) _ (hZ c)
  have hsplit : ∀ a b, root m a b = root m a 0 * root m 0 b := fun a b => by
    rw [root_mul m hm, map_zero, mul_zero, add_zero, zero_add, add_zero]
  have hred : ∀ a b c d, β (root m a b) (root m c d) = β (root m a 0) (root m c 0) := by
    intro a b c d
    rw [hsplit a b, hsplit c d,
      h₁ _ (hS a 0) _ (hS 0 b) _ ((rootSub m).mul_mem (hS c 0) (hS 0 d)),
      h₂ _ (hS a 0) _ (hS c 0) _ (hS 0 d), h₂ _ (hS 0 b) _ (hS c 0) _ (hS 0 d)]
    simp only [hZl, hZr, add_zero]
  have hmul : ∀ a c, root m a 0 * root m c 0 = root m (a + c) (a * tits m c) := fun a c => by
    rw [root_mul m hm, zero_add, zero_add]
  have hcard : 4 < Nat.card (BinaryGaloisField (2 * m + 1)) := by
    rw [GaloisField.card 2 (2 * m + 1) (by omega)]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hf := CFSG.ShultStronglyClosedTI.binaryScalarInvariantBiadditive_eq_zero hcard
    (fun a c => β (root m a 0) (root m c 0))
    (fun a a' c => by
      change β (root m (a + a') 0) (root m c 0) =
        β (root m a 0) (root m c 0) + β (root m a' 0) (root m c 0)
      rw [← h₁ _ (hS a 0) _ (hS a' 0) _ (hS c 0), hmul, hred _ (a * tits m a')])
    (fun a c c' => by
      change β (root m a 0) (root m (c + c') 0) =
        β (root m a 0) (root m c 0) + β (root m a 0) (root m c' 0)
      rw [← h₂ _ (hS a 0) _ (hS c 0) _ (hS c' 0), hmul, hred a 0 _ (c * tits m c')])
    (fun x hx a c => by
      have ht : ∀ a, torus m (Units.mk0 x hx) * root m a 0 * (torus m (Units.mk0 x hx))⁻¹ =
          root m (x * a) 0 := fun a => by
        rw [torus_conj_root, mul_zero, Units.val_mk0]
      have hn : (torus m (Units.mk0 x hx))⁻¹ ∈
          Subgroup.normalizer ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _) :=
        Subgroup.inv_mem _ (torusSub_le_normalizer m (torus_mem m _))
      have h := h₅ _ hn _ (hS a 0) _ (hS c 0)
      rwa [inv_inv, ht, ht] at h)
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hx
  obtain ⟨c, d, rfl⟩ := (mem_rootSub m).mp hy
  exact (hred a b c d).trans (hf a c)

end Suzuki

section Unitary

open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

variable {F : Type} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)

theorem qsFormAt_unitaryCoverRoot {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card F = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    QSFormAt (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryCoverRoot J hJ) := by
  unfold QSFormAt
  intro β hβ₁ hβ₂ hβ₃ hβ₄ hβ₅
  set Q := unitaryCoverRoot J hJ
  set ψ := hermitianUnipotentPSU J hJ
  have hQ (z : hermitianUnipotentCoord J) : ψ z ∈ Q := ⟨z, rfl⟩
  have hcentral (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) :
      ∃ c, ψ c ∈ sylowCenter Q ∧ ψ z = ψ w * ψ c :=
    ⟨w⁻¹ * z, mem_sylowCenter_root_of_fst J hJ (by rw [fst_mul, fst_inv, h, neg_add_cancel]),
      by rw [← map_mul, mul_inv_cancel_left]⟩
  have hleft (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) (a : _) (ha : a ∈ Q) :
      β (ψ z) a = β (ψ w) a := by
    obtain ⟨c, hc, hzc⟩ := hcentral z w h
    rw [hzc, hβ₁ _ (hQ w) _ (hQ c) _ ha, hβ₃ _ hc _ ha, add_zero]
  have hright (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) (a : _) (ha : a ∈ Q) :
      β a (ψ z) = β a (ψ w) := by
    obtain ⟨c, hc, hzc⟩ := hcentral z w h
    rw [hzc, hβ₂ _ ha _ (hQ w) _ (hQ c), hβ₄ _ ha _ hc, add_zero]
  choose s hs using exists_fst_eq J (2 ^ f) hcard hfixed
  let B : F → F → ZMod 2 := fun x y => β (ψ (s x)) (ψ (s y))
  have hB (z w : hermitianUnipotentCoord J) : β (ψ z) (ψ w) = B z.1.1 w.1.1 := by
    rw [hleft z (s z.1.1) (hs _).symm _ (hQ w), hright w (s w.1.1) (hs _).symm _ (hQ _)]
  have hB₁ (x x' y : F) : B (x + x') y = B x y + B x' y := by
    have h := hB (s x * s x') (s y)
    rw [fst_mul, hs, hs, hs] at h
    rw [← h, map_mul, hβ₁ _ (hQ _) _ (hQ _) _ (hQ _)]
  have hB₂ (x y y' : F) : B x (y + y') = B x y + B x y' := by
    have h := hB (s x) (s y * s y')
    rw [fst_mul, hs, hs, hs] at h
    rw [← h, map_mul, hβ₂ _ (hQ _) _ (hQ _) _ (hQ _)]
  have hfst (k : Fˣ) (z : hermitianUnipotentCoord J) :
      (hermitianTorusAction J k z).1.1 = (unitaryCoverScalar J k : F) * z.1.1 := by
    rw [hermitianTorusAction_fst, unitaryCoverScalar_val]
    ring
  have hBinv (h : unitaryCoverScalarImage J) (x y : F) :
      B (((h : Fˣ) : F) * x) (((h : Fˣ) : F) * y) = B x y := by
    obtain ⟨k, hk⟩ := h.2
    have hn : (hermitianTorusPSU J hJ k)⁻¹ ∈ Subgroup.normalizer (Q : Set _) :=
      Subgroup.inv_mem _ (unitaryCoverTorus_le_normalizer J hJ ⟨k, rfl⟩)
    have h₁ := hβ₅ _ hn (ψ (s x)) (hQ _) (ψ (s y)) (hQ _)
    rw [inv_inv, unitaryCoverTorus_conj_root, unitaryCoverTorus_conj_root, hB, hB, hfst, hfst,
      hs, hs, hk] at h₁
    exact h₁
  have hzero := binaryUnitaryTorusInvariantBiadditive_eq_zero f hf hcard
    (unitaryCoverScalarImage J) (unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ) B hB₁
    hB₂ hBinv
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  rw [hB]
  exact hzero _ _

end Unitary

open CFSG.ComponentClassification.AschbacherToolkit.Bender CFSG.BenderSuzuki
  CFSG.BenderSuzuki.MatrixGroups in
theorem N13 : S_N13 := by
  intro K _ _ hK T
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · obtain ⟨S, hS⟩ := SuzukiAut.exists_sylow_eq_rootSub n (by omega)
    exact qsFormAt_of_mulEquiv (e.trans (SuzukiAut.suzukiEquiv n).symm)
      ⟨S, hS ▸ qsFormAt_rootSub n (by omega)⟩ T
  · let k := GaloisField 2 f
    let F := FiniteField.Extension k 2 2
    let J := binaryQuadraticHermitian f (by omega)
    let : CharP F 2 := CharP.of_ringHom_of_ne_zero (algebraMap k F) 2 (by norm_num)
    have hcard : Nat.card F = (2 ^ f) ^ 2 := by
      rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
    have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ f :=
      quadraticBinaryFrobenius_fixed_card f (by omega)
    have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
    let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hcard hfixed).some
    have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
      e₁.trans (MulEquiv.subgroupCongr hmodel)
    obtain ⟨S, hS⟩ := UnitaryAut.exists_sylow_eq_root J f hf hcard hfixed hJ
    exact qsFormAt_of_mulEquiv (e.trans e₂.symm)
      ⟨S, hS ▸ qsFormAt_unitaryCoverRoot J hf hcard hfixed hJ⟩ T

end CFSG.Goldschmidt
