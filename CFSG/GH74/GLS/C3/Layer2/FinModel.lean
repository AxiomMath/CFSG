module

public import CFSG.GH74.GLS.C3.Layer2.FinModelCentralizer
public import CFSG.GH74.GLS.C3.Layer2.FinModelClaimCheck
public import CFSG.GH74.GLS.C3.Layer2.FinModelAssemble

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2
open scoped Classical

theorem card_Fgrp (n : ℕ) : Nat.card (Fgrp n) = 4 * n.factorial := card_Fgrp_eq n

theorem card_T0
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) : Nat.card (T0 n) = 64 :=
  card_T0_eq n hn

theorem isSylow_T0 (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) :
    ∃ P : Sylow 2 (Fgrp n), (P : Subgroup (Fgrp n)).map (Fgrp n).subtype = T0 n :=
  isSylow_T0_aux n hn

theorem x0_central (n : ℕ) {g : Amb n} (hg : g ∈ Fgrp n) : g * x0 n = x0 n * g :=
  x0_central_aux n hg

theorem fgrp_equiv_centralizer (n : ℕ) (hn : n = 6 ∨ n = 7) (y : alternatingGroup (Fin (n + 4)))
    (hy : orderOf y = 2)
    (h4 : numMoved ((y : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) :
    Nonempty (↥(Fgrp n) ≃* ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))))) :=
  fgrp_equiv_centralizer_aux n hn y hy h4

structure ModelIso (n : ℕ) [NeZero n] (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n)) : Prop where
  data : ∃ (φ : T0 n →* alternatingGroup (Fin (n + 4))) (a₀ : alternatingGroup (Fin (n + 4)))
      (s : T0 n),
    Function.Injective φ ∧ s * α s * u = 1 ∧ a₀ ^ 2 = 1 ∧ a₀ ∉ φ.range ∧
    (∀ t : T0 n, a₀ * φ t * a₀⁻¹ = φ (s * α t * s⁻¹)) ∧
    (∀ t : T0 n, orderOf t = 2 →
      (t ∈ X ∨ t ∈ V) ∧
        (t ∈ X ↔ numMoved ((φ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) ∧
        (t ∈ V ↔ numMoved ((φ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 8)) ∧
    (∀ t : T0 n, orderOf (φ t * a₀) = 2 →
      numMoved (((φ t * a₀ : alternatingGroup (Fin (n + 4)))) : Perm (Fin (n + 4))) = 8) ∧
    (∀ η : ↥(Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀)) →*
        alternatingGroup (Fin (n + 4)),
      Function.Injective η →
      (∀ h : a₀ ∈ Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀),
        η ⟨a₀, h⟩ = φ (x0T n)) →
      (∀ w, η w ∈ φ.range) →
      ∃ w : ↥(Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀)), orderOf w = 2 ∧
        numMoved ((η w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ≠
          (if (w : alternatingGroup (Fin (n + 4))) ∈ φ.range then
            numMoved ((w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) else 4)) ∧
    (∀ w ∈ φ.range ⊔ Subgroup.zpowers a₀, w ∉ φ.range → orderOf w = 2 →
      ∃ t : T0 n, φ t * a₀ * (φ t)⁻¹ = w) ∧
    (∀ y ∈ φ.range ⊔ Subgroup.zpowers a₀, orderOf y = 2 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ Subgroup.zpowers a₀)) = 64 →
      y = φ (x0T n) ∨ y = a₀ * φ (x0T n) * a₀⁻¹)

theorem fin_main
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ t, α (α t) = u * t * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (t : T0 n) (ht : (t : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(t : Amb n), ht⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α t : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ModelIso n α u X V := by
  have hvB : (mkTab n).validB = true := by
    rcases hn with rfl | rfl
    · exact validB6
    · exact validB7
  have hcB : (mkTab n).claimB = true := by
    rcases hn with rfl | rfl
    · exact claimB6
    · exact claimB7
  exact ⟨fin_main_data n hn (mkTab n) (Tab.valid_of_validB _ hvB) hcB (model_facts n hn) α u X V
    hx hu hsq hext hX hV hdisj hclX hclV hQ⟩

end CFSG.GH74.GLS.C3.Layer2.Model
