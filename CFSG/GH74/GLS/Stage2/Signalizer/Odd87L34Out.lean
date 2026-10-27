module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Certificate2022
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.Blueprint
open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out

local notation "Perm42" => Equiv.Perm (Fin 42)

@[expose] def NN : Subgroup Perm42 := S ⊔ zpowers g₄

theorem g₄_pow_three : g₄ ^ 3 = 1 := by
  have h : dGL ^ 3 = 1 := by
    apply Units.ext
    decide
  unfold g₄
  rw [← map_pow, h, map_one]

theorem g₅_conj_g₄ : g₅ * g₄ * g₅⁻¹ = g₄⁻¹ := by
  have h := rho_frob (B := dGL) (B' := dGL⁻¹) (by decide) (by decide)
  rw [map_inv] at h
  exact h.symm

theorem g₆_conj_g₄ : g₆ * g₄ * g₆⁻¹ = g₄⁻¹ := by
  have h := rho_invTranspose dGL
  have e : invTranspose dGL = dGL⁻¹ := by
    apply Units.ext
    rw [coe_invTranspose]
    decide
  rw [e, map_inv] at h
  exact h.symm

theorem g₅_comm_g₆ : g₅ * g₆ = g₆ * g₅ := Equiv.ext fun i => by revert i; decide

theorem sq_of_mem_closure_g56 {z : Perm42} (hz : z ∈ closure ({g₅, g₆} : Set Perm42)) :
    z * z = 1 := by
  have key : z * z = 1 ∧ Commute z g₅ ∧ Commute z g₆ := by
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨g₅_mul_g₅, Commute.refl _, g₅_comm_g₆⟩
      · have hx' : x = g₆ := hx
        subst hx'
        exact ⟨g₆_mul_g₆, g₅_comm_g₆.symm, Commute.refl _⟩
    | one => exact ⟨mul_one 1, Commute.one_left _, Commute.one_left _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx2, hx5, hx6⟩ := ihx
      obtain ⟨hy2, hy5, hy6⟩ := ihy
      have hcent : y ∈ centralizer ({x} : Set Perm42) := by
        have hle : closure ({g₅, g₆} : Set Perm42) ≤ centralizer ({x} : Set Perm42) := by
          rw [Subgroup.closure_le]
          intro w hw
          rcases hw with rfl | hw
          · exact mem_centralizer_singleton_iff.mpr hx5.symm.eq
          · have hw' : w = g₆ := hw
            subst hw'
            exact mem_centralizer_singleton_iff.mpr hx6.symm.eq
        exact hle hy
      have hxy : y * x = x * y := mem_centralizer_singleton_iff.mp hcent
      refine ⟨?_, hx5.mul_left hy5, hx6.mul_left hy6⟩
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x hx ihx =>
      obtain ⟨hx2, hx5, hx6⟩ := ihx
      refine ⟨?_, hx5.inv_left, hx6.inv_left⟩
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx2, inv_one]
  exact key.1

section Model


theorem zpowers_g₄_le_normalizer : zpowers g₄ ≤ normalizer (S : Set Perm42) :=
  (zpowers_le).2 (R_le_normalizer g₄_mem_R)

theorem mem_NN_iff {n : Perm42} : n ∈ NN ↔ ∃ s ∈ S, ∃ h ∈ zpowers g₄, s * h = n := by
  have hmul : ((S ⊔ zpowers g₄ : Subgroup Perm42) : Set Perm42) =
      (S : Set Perm42) * (zpowers g₄ : Set Perm42) :=
    coe_mul_of_right_le_normalizer_left S (zpowers g₄) zpowers_g₄_le_normalizer
  have : n ∈ ((S ⊔ zpowers g₄ : Subgroup Perm42) : Set Perm42) ↔
      n ∈ (S : Set Perm42) * (zpowers g₄ : Set Perm42) := by
    rw [hmul]
  simpa [NN, Set.mem_mul] using this

theorem conj_mem_NN {γ : Perm42} (hγ : γ ∈ R) (h4 : γ * g₄ * γ⁻¹ ∈ zpowers g₄) {n : Perm42}
    (hn : n ∈ NN) : γ * n * γ⁻¹ ∈ NN := by
  obtain ⟨s, hs, h, hh, rfl⟩ := mem_NN_iff.mp hn
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have e : γ * (s * g₄ ^ k) * γ⁻¹ = (γ * s * γ⁻¹) * (γ * g₄ * γ⁻¹) ^ k := by
    rw [conj_zpow]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (conj_mem_S hγ hs))
    (Subgroup.mem_sup_right (zpow_mem h4 k))

theorem mem_normalizer_NN {γ : Perm42} (hγ : γ ∈ R) (hγ2 : γ * γ = 1)
    (h4 : γ * g₄ * γ⁻¹ ∈ zpowers g₄) : γ ∈ normalizer (NN : Set Perm42) := by
  rw [mem_normalizer_iff]
  intro n
  refine ⟨fun hn => conj_mem_NN hγ h4 hn, fun hn => ?_⟩
  have hγi : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
  have h := conj_mem_NN hγ h4 hn
  have e : γ * (γ * n * γ⁻¹) * γ⁻¹ = n := by
    rw [hγi]
    calc γ * (γ * n * γ) * γ = (γ * γ) * n * (γ * γ) := by group
      _ = n := by rw [hγ2]; group
  rwa [e] at h

theorem R_le_normalizer_NN : R ≤ normalizer (NN : Set Perm42) := by
  have hS : S ≤ normalizer (NN : Set Perm42) := fun x hx =>
    le_normalizer (Subgroup.mem_sup_left hx : x ∈ NN)
  have h4 : g₄ ∈ NN := Subgroup.mem_sup_right (mem_zpowers g₄)
  have h5 : g₅ ∈ normalizer (NN : Set Perm42) := by
    refine mem_normalizer_NN g₅_mem_R g₅_mul_g₅ ?_
    rw [g₅_conj_g₄]
    exact inv_mem (mem_zpowers g₄)
  have h6 : g₆ ∈ normalizer (NN : Set Perm42) := by
    refine mem_normalizer_NN g₆_mem_R g₆_mul_g₆ ?_
    rw [g₆_conj_g₄]
    exact inv_mem (mem_zpowers g₄)
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hS g₁_mem_S
  · exact hS g₂_mem_S
  · exact hS g₃_mem_S
  · exact le_normalizer h4
  · exact h5
  · exact h6

theorem normalized_NN {r n : Perm42} (hr : r ∈ R) (hn : n ∈ NN) : r * n * r⁻¹ ∈ NN :=
  (mem_normalizer_iff.mp (R_le_normalizer_NN hr) n).mp hn

theorem sq_mem_NN {r : Perm42} (hr : r ∈ R) : r * r ∈ NN := by
  set Z : Subgroup Perm42 := closure ({g₅, g₆} : Set Perm42) with hZ
  have hZR : Z ≤ R := by
    rw [hZ, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact g₅_mem_R
    · have hx' : x = g₆ := hx
      subst hx'
      exact g₆_mem_R
  have hRle : R ≤ Z ⊔ NN := by
    show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left g₁_mem_S : _ ∈ NN)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left g₂_mem_S : _ ∈ NN)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left g₃_mem_S : _ ∈ NN)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (mem_zpowers g₄) : _ ∈ NN)
    · exact Subgroup.mem_sup_left (subset_closure (by simp))
    · exact Subgroup.mem_sup_left (subset_closure (by simp))
  have hmul : ((Z ⊔ NN : Subgroup Perm42) : Set Perm42) = (Z : Set Perm42) * (NN : Set Perm42) :=
    coe_mul_of_left_le_normalizer_right Z NN (fun z hz => R_le_normalizer_NN (hZR hz))
  have hr' : r ∈ ((Z ⊔ NN : Subgroup Perm42) : Set Perm42) := hRle hr
  rw [hmul] at hr'
  obtain ⟨z, hz, n, hn, rfl⟩ := hr'
  have hz2 : z * z = 1 := sq_of_mem_closure_g56 hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h1 := normalized_NN (hZR hz) hn
  rw [hzi] at h1
  have e : z * n * (z * n) = (z * n * z) * n := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 hn

theorem odd_mem_NN {r : Perm42} (hr : r ∈ R) (h3 : r ^ 3 = 1) : r ∈ NN := by
  have h : (r * r) * r = 1 := by rw [← pow_three']; exact h3
  have := eq_inv_of_mul_eq_one_right h
  rw [this]
  exact inv_mem (sq_mem_NN hr)

theorem NN_le_sup_of_not_mem {y : Perm42} (hyN : y ∈ NN) (hyS : y ∉ S) : NN ≤ S ⊔ zpowers y := by
  obtain ⟨s, hs, h, hh, hsh⟩ := mem_NN_iff.mp hyN
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hk : g₄ ^ k = g₄ ^ (k % 3) := by
    have hk3 : k = 3 * (k / 3) + k % 3 := by omega
    conv_lhs => rw [hk3]
    rw [zpow_add, zpow_mul]
    have : g₄ ^ (3 : ℤ) = 1 := by exact_mod_cast g₄_pow_three
    rw [this, one_zpow, one_mul]
  have hys : s⁻¹ * y = g₄ ^ k := by rw [← hsh]; group
  have hmem : s⁻¹ * y ∈ S ⊔ zpowers y :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem hs)) (Subgroup.mem_sup_right (mem_zpowers y))
  have hg4 : g₄ ∈ S ⊔ zpowers y := by
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · exfalso
      apply hyS
      rw [← hsh, hk, h0, zpow_zero, mul_one]
      exact hs
    · rw [hk, h1, zpow_one] at hys
      rwa [← hys]
    · rw [hk, h2] at hys
      have hsq : g₄ ^ (2 : ℤ) ∈ S ⊔ zpowers y := by rwa [← hys]
      have e : g₄ ^ (2 : ℤ) * g₄ ^ (2 : ℤ) = g₄ := by
        calc g₄ ^ (2 : ℤ) * g₄ ^ (2 : ℤ) = g₄ ^ 3 * g₄ := by group
          _ = g₄ := by rw [g₄_pow_three, one_mul]
      rw [← e]
      exact Subgroup.mul_mem _ hsq hsq
  exact sup_le le_sup_left ((zpowers_le).2 hg4)

theorem conj_order_three {g y : Perm42} (hg : g ∈ R) (hy : y ∈ R) (h3 : y ^ 3 = 1) :
    ∃ s ∈ S, ∃ i : ℤ, g * y * g⁻¹ = s * y ^ i := by
  by_cases hyS : y ∈ S
  · exact ⟨g * y * g⁻¹, conj_mem_S hg hyS, 0, by simp⟩
  · have hyN := odd_mem_NN hy h3
    have h1 := normalized_NN hg hyN
    have h2 : g * y * g⁻¹ ∈ S ⊔ zpowers y := NN_le_sup_of_not_mem hyN hyS h1
    have hmul : ((S ⊔ zpowers y : Subgroup Perm42) : Set Perm42) =
        (S : Set Perm42) * (zpowers y : Set Perm42) :=
      coe_mul_of_right_le_normalizer_left S (zpowers y) ((zpowers_le).2 (R_le_normalizer hy))
    have h3' : g * y * g⁻¹ ∈ (S : Set Perm42) * (zpowers y : Set Perm42) := by
      rw [← hmul]
      exact h2
    obtain ⟨s, hs, w, hw, hsw⟩ := h3'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    exact ⟨s, hs, i, hsw.symm⟩

end Model

theorem diag_closure {A : Type} [Group A] (J : Subgroup A) [J.Normal]
    (hJ : LieModel ↥J .PSL 3 2 2) (X : Subgroup A) (hX : Nat.card ↥X = 3) :
    (J ⊔ centralizer (J : Set A) ⊔ X).Normal := by
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hJ
  obtain ⟨eR, -, hinn⟩ := full_automorphism_action
  let Φ : A →* ↥R :=
    eR.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal)
  have hker : ∀ a : A, Φ a = 1 → a ∈ centralizer (J : Set A) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro j hj
    have h0 : eR.symm ((MulAut.congr ψ) (MulAut.conjNormal a)) = 1 := ha
    have h1 : (MulAut.congr ψ) (MulAut.conjNormal a) = 1 := by
      apply eR.symm.injective
      rw [h0, map_one]
    have h2 : (MulAut.conjNormal a : MulAut ↥J) = 1 :=
      (MulAut.congr ψ).injective (by rw [h1, map_one])
    have h3 := congrArg (fun σ : MulAut ↥J => ((σ ⟨j, hj⟩ : ↥J) : A)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc j * a = (a * j * a⁻¹) * a := by rw [h3]
      _ = a * j := by group
  have hS2 : ∀ s : Perm42, s ∈ S → ∃ j ∈ J, ((Φ j : ↥R) : Perm42) = s := by
    intro s hs
    have hmem : eR ⟨s, S_le_R hs⟩ ∈ (MulAut.conj : ↥S →* MulAut ↥S).range := by
      rw [← hinn]
      exact ⟨⟨s, S_le_R hs⟩, mem_subgroupOf.mpr hs, rfl⟩
    obtain ⟨σ, hσ⟩ := hmem
    refine ⟨((ψ.symm σ : ↥J) : A), (ψ.symm σ).2, ?_⟩
    have hΦ : Φ ((ψ.symm σ : ↥J) : A) = ⟨s, S_le_R hs⟩ := by
      apply eR.injective
      show eR (eR.symm ((MulAut.congr ψ) (MulAut.conjNormal ((ψ.symm σ : ↥J) : A)))) = _
      rw [MulEquiv.apply_symm_apply, ← hσ]
      refine MulEquiv.ext fun t => ?_
      have h1 : (MulAut.conjNormal ((ψ.symm σ : ↥J) : A) : MulAut ↥J) (ψ.symm t) =
          ψ.symm σ * ψ.symm t * (ψ.symm σ)⁻¹ := by
        apply Subtype.ext
        simp [MulAut.conjNormal_apply]
      show ψ ((MulAut.conjNormal ((ψ.symm σ : ↥J) : A) : MulAut ↥J) (ψ.symm t)) =
        (MulAut.conj σ) t
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        MulAut.conj_apply]
    exact congrArg Subtype.val hΦ
  have hxcube : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    have h : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    rw [hX] at h
    exact congrArg Subtype.val h
  have hXconj : ∀ a : A, ∀ x ∈ X, a * x * a⁻¹ ∈ J ⊔ centralizer (J : Set A) ⊔ X := by
    intro a x hx
    have hy3 : ((Φ x : ↥R) : Perm42) ^ 3 = 1 := by
      have h := congrArg (fun r : ↥R => (r : Perm42)) (show Φ (x ^ 3) = 1 by rw [hxcube x hx, map_one])
      simpa [map_pow] using h
    obtain ⟨s, hs, i, hsi⟩ := conj_order_three (Φ a).2 (Φ x).2 hy3
    obtain ⟨j, hj, hjs⟩ := hS2 s hs
    have hΦ : Φ (a * x * a⁻¹) = Φ (j * x ^ i) := by
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, map_mul, map_zpow]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      rw [hjs]
      exact hsi
    have hc : (a * x * a⁻¹) * (j * x ^ i)⁻¹ ∈ centralizer (J : Set A) :=
      hker _ (by rw [map_mul, map_inv, hΦ, mul_inv_cancel])
    have e : a * x * a⁻¹ = ((a * x * a⁻¹) * (j * x ^ i)⁻¹) * j * x ^ i := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hc))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hj)))
      (Subgroup.mem_sup_right (zpow_mem hx i))
  refine ⟨fun m hm a => ?_⟩
  have hle : J ⊔ centralizer (J : Set A) ⊔ X ≤
      (J ⊔ centralizer (J : Set A) ⊔ X).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro j hj
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Normal.conj_mem ‹J.Normal› j hj a))
    · intro c hc
      refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
      rw [mem_centralizer_iff] at hc ⊢
      intro j hj
      have hj' : a⁻¹ * j * a ∈ J := by
        simpa using Normal.conj_mem ‹J.Normal› j hj a⁻¹
      have h := hc _ hj'
      show j * (a * c * a⁻¹) = (a * c * a⁻¹) * j
      calc j * (a * c * a⁻¹) = a * ((a⁻¹ * j * a) * c) * a⁻¹ := by group
        _ = a * (c * (a⁻¹ * j * a)) * a⁻¹ := by rw [h]
        _ = (a * c * a⁻¹) * j := by group
    · intro x hx
      exact hXconj a x hx
  exact hle hm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
