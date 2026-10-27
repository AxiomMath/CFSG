module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE3
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1Check
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelGen
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelE1
public meta import CFSG.GH74.GLS.C3.Layer2.L4ModelE3
public import Certificates.Certificate5038
public import Certificates.Certificate5039
public import Certificates.Certificate5041
public import Certificates.Certificate5042
public import Certificates.Certificate5044
public import CFSG.GH74.GLS.C3.Layer2.FinModelClaimCheck

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem e3Claim7 :
    (mkTab 7).claimG ((mkTab 7).e3P (mkTab 7).wActE3 (mkTab 7).wCommE3) = true :=
  Certificates.certificate5044.1

theorem e3Act7 : (mkTab 7).wActOKE3 = true :=
  Certificates.certificate5044.2

theorem vHat_eq_vStdE1_seven
    (α : T0 7 ≃* T0 7) (u : T0 7) (X V : Set (T0 7))
    (hx : α (x0T 7) ≠ x0T 7) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : 7 = 7 →
      ∃ β : ↥(Hgrp 7 ((α (x0T 7) : T0 7) : Amb 7)) ≃* ↥(Hgrp 7 ((α (x0T 7) : T0 7) : Amb 7)),
        ∀ (x : T0 7) (hx : (x : Amb 7) ∈ Hgrp 7 ((α (x0T 7) : T0 7) : Amb 7)),
          ((β ⟨(x : Amb 7), hx⟩ : ↥(Hgrp 7 ((α (x0T 7) : T0 7) : Amb 7))) : Amb 7) =
            ((α x : T0 7) : Amb 7))
    (hX : x0T 7 ∈ X) (hV : x0T 7 * α (x0T 7) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 7, orderOf s = 2 →
      ((∃ g ∈ Fgrp 7, g * (s : Amb 7) * g⁻¹ = (t : Amb 7)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 7, orderOf s = 2 →
      ((∃ g ∈ Fgrp 7, g * (s : Amb 7) * g⁻¹ = (t : Amb 7)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 7, (q : Amb 7).1 = 1 → q ≠ 1 → q ∉ V) :
    ((vHat 7 α : T0 7) : Amb 7) = vStdE1 7 := by
  have hv : (mkTab 7).Valid := Tab.valid_of_validB _ validB7
  obtain ⟨_, -, hP, -, -⟩ := (mkTab 7).facts_of_claimG (Or.inr rfl) hv claimB7 (mkTab 7).e1P1
    e1Claim1_7 α u X V hx hu hsq hext hX hV hdisj hclX hclV hQ
  unfold Tab.e1P1 at hP
  simp only [decide_eq_true_eq] at hP
  obtain ⟨-, -, -, -, hvel, -⟩ := hP
  have hiv := (mkTab 7).iT_vIE1 (Or.inr rfl) hv α _ ((mkTab 7).iT_tabOf (Or.inr rfl) hv α)
  rw [← hiv]
  exact hvel

theorem cover_seven
    (α : T0 7 ≃* T0 7) (hvstd : ((vHat 7 α : T0 7) : Amb 7) = vStdE1 7) :
    ∀ g ∈ Fgrp 7, g * ((vHat 7 α : T0 7) : Amb 7) = ((vHat 7 α : T0 7) : Amb 7) * g →
      ∃ t : T0 7, ∃ j : ℕ, j < 3 ∧ g = (t : Amb 7) * wStdE1 7 ^ j := by
  intro g hgF hgc
  rw [hvstd] at hgc
  have hv : (mkTab 7).Valid := Tab.valid_of_validB _ validB7
  have hg : g ∈ cfListE1 7 := (mem_cfListE1 7 g).2 ⟨hgc, hgF.1, hgF.2⟩
  obtain ⟨i, r, hr, hgr⟩ := (mkTab 7).cfCoverE1_spec e1Cover7 g hg
  have hrep : repListE1 7 = [1, wStdE1 7, wStdE1 7 * wStdE1 7] := by simp [repListE1]
  rw [hrep] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨(mkTab 7).iT (Or.inr rfl) hv i, ?_⟩
  have e1 : (((mkTab 7).iT (Or.inr rfl) hv i : T0 7) : Amb 7) = (mkTab 7).el.get i := rfl
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, by decide, by rw [hgr, e1]; simp⟩
  · exact ⟨1, by decide, by rw [hgr, e1]; simp⟩
  · exact ⟨2, by decide, by rw [hgr, e1, pow_two]⟩

theorem model_E3
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (hn7 : n = 7)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V)
    (E : Subgroup (T0 n))
    (hE : ∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
        (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X)))
    (A : Subgroup (T0 n)) (hA : ∀ t : T0 n, t ∈ A ↔ ∀ e ∈ E, t * e = e * t)
    (b : Fin 4 → T0 n) (hbinj : Function.Injective b)
    (hb1 : ∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧ b i ∉ E)
    (hb2 : ∀ t ∈ A, orderOf t = 2 → t ∈ X → t ∉ E → ∃ i, t = b i) :
    ∃ w : Amb n, w ∈ Fgrp n ∧ orderOf w = 3 ∧ (∀ e ∈ liftT n E, w * e = e * w) ∧
      (∀ g ∈ Fgrp n ⊓ Subgroup.centralizer (liftT n E : Set (Amb n)),
        ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * ((t : T0 n) : Amb n)) ∧
      (∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
        ∃ k : ℤ, g * w * g⁻¹ = w ^ k) ∧
      (∀ t ∈ A, t ∉ E → ((t : T0 n) : Amb n) * w * ((t : T0 n) : Amb n)⁻¹ = w⁻¹) ∧
      (∀ (t y : T0 n) (π₁ π₂ : Equiv.Perm (Fin 4)), t ∉ A → y ∉ A → orderOf t = 2 →
        orderOf y = 2 → t * y = y * t → π₁.IsSwap → π₂.IsSwap → Disjoint π₁ π₂ →
        (∀ i, t * b i * t⁻¹ = b (π₁ i)) → (∀ i, y * b i * y⁻¹ = b (π₂ i)) →
        ((t : T0 n) : Amb n) * w = w * ((t : T0 n) : Amb n)) ∧
      (∃ t y : T0 n, t ∉ A ∧ y ∉ A ∧ orderOf t = 2 ∧ orderOf y = 2 ∧ t * y = y * t ∧
        ∃ π₁ π₂ : Equiv.Perm (Fin 4), π₁.IsSwap ∧ π₂.IsSwap ∧ Disjoint π₁ π₂ ∧
          (∀ i, t * b i * t⁻¹ = b (π₁ i)) ∧ (∀ i, y * b i * y⁻¹ = b (π₂ i))) := by
  subst hn7
  have hv : (mkTab 7).Valid := Tab.valid_of_validB _ validB7
  have hvstd := vHat_eq_vStdE1_seven α u X V hx hu hsq hext hX hV hdisj hclX hclV hQ
  exact model_E3_aux 7 hn rfl (mkTab 7) hv claimB7 e3Claim7 e3Act7 α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ E hE A hA b hbinj hb1 hb2 (cover_seven α hvstd)

end CFSG.GH74.GLS.C3.Layer2.Model
