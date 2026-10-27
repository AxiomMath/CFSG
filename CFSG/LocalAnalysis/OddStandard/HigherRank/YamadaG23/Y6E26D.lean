module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem y6e_of_isElemAbelian_map {Γ : Type} [Group Γ] {V N D : Subgroup Γ}
    [hn : (N.subgroupOf V).Normal] (hDV : D ≤ V)
    (h : IsElemAbelian 2 ((D.subgroupOf V).map (QuotientGroup.mk' (N.subgroupOf V)))) :
    (∀ x ∈ D, x ^ 2 ∈ N) ∧ (∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ N) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx0 : (⟨x, hDV hx⟩ : ↥V) ∈ D.subgroupOf V := hx
    have h1 := h.2 _ (Subgroup.mem_map_of_mem _ hx0)
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · have hx0 : (⟨x⁻¹, hDV (D.inv_mem hx)⟩ : ↥V) ∈ D.subgroupOf V := D.inv_mem hx
    have hy0 : (⟨y⁻¹, hDV (D.inv_mem hy)⟩ : ↥V) ∈ D.subgroupOf V := D.inv_mem hy
    have h1 := h.comm (Subgroup.mem_map_of_mem _ hx0) (Subgroup.mem_map_of_mem _ hy0)
    rw [← map_mul, ← map_mul] at h1
    have h2 : ((⟨y⁻¹, hDV (D.inv_mem hy)⟩ * ⟨x⁻¹, hDV (D.inv_mem hx)⟩ : ↥V) :
        ↥V ⧸ N.subgroupOf V) =
        ((⟨x⁻¹, hDV (D.inv_mem hx)⟩ * ⟨y⁻¹, hDV (D.inv_mem hy)⟩ : ↥V) :
        ↥V ⧸ N.subgroupOf V) := h1.symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    rw [commutatorElement_def]
    convert h2 using 1
    simp [mul_assoc]

theorem y6e_false_of_G23Type_sub {Γ : Type} [Group Γ] [Finite Γ] {S N B W : Subgroup Γ}
    (hBS : B ≤ S) (hWS : W ≤ S) (hNB : N ≤ B) (hNW : N ≤ W) (hBW : B ⊓ W ≤ N)
    (hBsq : ∀ x ∈ B, x ^ 2 ∈ N) (hBc : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ N)
    (hWsq : ∀ x ∈ W, x ^ 2 ∈ N) (hWc : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ N)
    (hBWc : ∀ x ∈ B, ∀ y ∈ W, ⁅x, y⁆ ∈ N)
    (hcB : 4 * Nat.card ↥N ≤ Nat.card ↥B) (hcW : 4 * Nat.card ↥N ≤ Nat.card ↥W)
    {Q : Type} [Group Q] (hQ : HRG23 Q) (S' : Sylow 2 Q) (h3 : CFSG.pRank 2 ↥S' = 3)
    (hsec : SecProp (⊤ : Subgroup ↥S) (N.subgroupOf S) (fun Y _ _ _ => Sec2.IsG23Type Y)) :
    False := by
  have hcard : ∀ {D : Subgroup Γ}, D ≤ S → Nat.card ↥(D.subgroupOf S) = Nat.card ↥D :=
    fun {D} hD => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  refine y6e_false_of_G23Type (V := (⊤ : Subgroup ↥S)) (N := N.subgroupOf S)
    (B := B.subgroupOf S) (W := W.subgroupOf S) le_top le_top (fun x hx => hNB hx)
    (fun x hx => hNW hx) (fun x hx => hBW ⟨hx.1, hx.2⟩) (fun x hx => hBsq _ hx)
    (fun x hx y hy => hBc _ hx _ hy) (fun x hx => hWsq _ hx) (fun x hx y hy => hWc _ hx _ hy)
    (fun x hx y hy => hBWc _ hx _ hy) ?_ ?_ hQ S' h3 hsec
  · rw [hcard (hNB.trans hBS), hcard hBS]
    exact hcB
  · rw [hcard (hNW.trans hWS), hcard hWS]
    exact hcW

theorem y6e_closure_eq {G : Type} [Group G] {X S M : Subgroup G} (hMS : M ≤ S) (hSX : S ≤ X)
    (P : Sylow 2 ↥X) (φ : ↥P ≃* ↥S)
    (hφ : ∀ x : ↥P, ((φ x : ↥S) : G) = (((x : ↥P) : ↥X) : G)) (u v w : ↥P)
    (hcl : Subgroup.closure {((u : ↥P) : ↥X), ((v : ↥P) : ↥X), ((w : ↥P) : ↥X)} =
      M.subgroupOf X) :
    Subgroup.closure {φ u, φ v, φ w} = M.subgroupOf S := by
  have hX : (Subgroup.closure {((u : ↥P) : ↥X), ((v : ↥P) : ↥X), ((w : ↥P) : ↥X)}).map X.subtype =
      M := by
    rw [hcl]
    exact Subgroup.map_subgroupOf_eq_of_le (hMS.trans hSX)
  have hS : (Subgroup.closure {φ u, φ v, φ w}).map S.subtype = M := by
    rw [MonoidHom.map_closure, ← hX, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Subgroup.coe_subtype]
    rw [hφ u, hφ v, hφ w]
  apply Subgroup.map_injective S.subtype_injective
  rw [hS]
  exact (Subgroup.map_subgroupOf_eq_of_le hMS).symm

theorem y6e_omega1_eq {Γ : Type} [Group Γ] [Finite Γ] {S M F : Subgroup Γ} (hFM : F ≤ M)
    (hMS : M ≤ S) (e : ↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))
    (hFsq : ∀ x ∈ F, x ^ 2 = 1) (hFc : Nat.card ↥F = 8) {K : Subgroup ↥S}
    (hK : K = M.subgroupOf S) : omega1 K = F.subgroupOf S := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro y ⟨hyK, hy2⟩
    rw [hK] at hyK
    have hyM : (y : Γ) ∈ M := hyK
    have hy2' : (y : Γ) ^ 2 = 1 := by
      have := congrArg Subtype.val hy2
      simpa using this
    exact y6e_sqone_mem_of_card hFM e hFsq hFc hyM hy2'
  · intro x hx
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [hK]
      exact hFM hx
    · apply Subtype.ext
      simpa using hFsq _ hx

end CFSG.OddStandard.HigherRank.YamadaG23
