module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusExt
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL39

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.gen0_central : ∀ c : SE, c⁻¹ * SE.gen 0 * c = SE.gen 0 := by decide +kernel

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem not_fusN_of_case (L : List ℕ) (hL : ∀ i < L.length, D.FusN i (L.getD i i)) {u j : ℕ}
    (huj : D.FusN u j) (F : List (ℕ × ℕ)) (hF : ∀ p ∈ F, ¬ D.FusN p.1 p.2) (B : List (ℕ × ℕ))
    (hB : ∀ b ∈ B, ∃ p ∈ F,
      ((fun i => if i = u then L.getD j j else L.getD i i) p.1 =
          (fun i => if i = u then L.getD j j else L.getD i i) b.1 ∧
        (fun i => if i = u then L.getD j j else L.getD i i) p.2 =
          (fun i => if i = u then L.getD j j else L.getD i i) b.2) ∨
      ((fun i => if i = u then L.getD j j else L.getD i i) p.1 =
          (fun i => if i = u then L.getD j j else L.getD i i) b.2 ∧
        (fun i => if i = u then L.getD j j else L.getD i i) p.2 =
          (fun i => if i = u then L.getD j j else L.getD i i) b.1)) :
    ∀ b ∈ B, ¬ D.FusN b.1 b.2 := by
  have hL' : ∀ i, D.FusN i (L.getD i i) := by
    intro i
    by_cases hi : i < L.length
    · exact hL i hi
    · rw [List.getD_eq_default _ _ (by omega)]
      exact D.fusN_refl i
  refine Fus.not_bad (R := D.FusN) (fun i j h => D.fusN_symm h)
    (fun i j k h1 h2 => D.fusN_trans h1 h2) (fun i => if i = u then L.getD j j else L.getD i i)
    (fun i => ?_) F hF B hB
  by_cases h : i = u
  · subst h
    simp only [ite_true]
    exact D.fusN_trans huj (hL' j)
  · simp only [h, ite_false]
    exact hL' i

omit [Finite G] in
theorem pred_iff_of_closed {K : Subgroup G} {pred : SE → Prop}
    (hK : ∀ s : SE, D.toG s ∈ K ↔ pred s)
    (hcl : ∀ {g u : G}, g ∈ D.M → u ∈ K → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ K)
    {g : G} (hgz : g⁻¹ * D.z * g = D.z) {s : SE}
    (hs : g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G)) : pred s ↔ pred (D.conjM g s) := by
  have hgM : g ∈ D.M := mem_centralizer_singleton_iff.mpr (by
    calc g * D.z = g * (g⁻¹ * D.z * g) := by rw [hgz]
      _ = D.z * g := by group)
  rw [← hK, ← hK, D.toG_conjM hs]
  constructor
  · intro h
    exact hcl hgM h hs
  · intro h
    have := hcl (inv_mem hgM) h (by
      rw [inv_inv, show g * (g⁻¹ * D.toG s * g) * g⁻¹ = D.toG s by group]
      exact D.toG_mem s)
    rwa [inv_inv, show g * (g⁻¹ * D.toG s * g) * g⁻¹ = D.toG s by group] at this


abbrev y : G := D.toG (SE.invRep 6)

abbrev a1a4 : G := D.toG (SE.invRep 4)

omit [Finite G] in
theorem good_of_rep' {A : Fus.Data} (hA : A.checkM (· * ·) = true) (hcls : SE.clsOk = true)
    {u : G} {v : SE} {g : G} (hsrc : D.toG A.source = u) (htgt : A.target = v)
    (hgu : g⁻¹ * u * g = D.toG v)
    (hC : ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G),
      g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG v} : Set G))
    (hbad : ∀ p ∈ A.badPairs, ¬ D.FusN p.1 p.2)
    (hE : A.useE = true → ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) →
      g⁻¹ * u * g ∈ D.E)
    (hF : A.useF = true → ∀ {g u : G}, g ∈ D.M → u ∈ D.F → g⁻¹ * u * g ∈ (D.S : Subgroup G) →
      g⁻¹ * u * g ∈ D.F) :
    A.good (· * ·) (D.fusQ A g) = true := by
  have hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
    intro s hs
    have hsu : D.toG s ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
      refine mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hsrc, ← map_mul, ← map_mul, hs]
    exact (mem_inf.mp (hC _ hsu)).1
  refine D.fus_good hA hcls (by rw [hsrc, htgt]; exact hgu) hgC hbad
    (fun h hz s hs => D.pred_iff_of_closed (K := D.E) (fun s => D.toG_mem_E_iff) (hE h) hz
      (hgC s hs))
    (fun h hz s hs => D.pred_iff_of_closed (K := D.F) (fun s => D.toG_mem_F_iff) (hF h) hz
      (hgC s hs))

theorem exists_extremal_rep_S2
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {i : Fin 9}
    (hi : ¬ dS2 (SE.invRep i).d) :
    ∃ j : Fin 9, ∃ g : G,
      IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G))
        (centralizer ({D.toG (SE.invRep j)} : Set G)) ∧
      (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5) ∧
      g⁻¹ * D.toG (SE.invRep i) * g = D.toG (SE.invRep j) ∧
      ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G),
        g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G) := by
  have hS : D.toG (SE.invRep i) ∈ (D.S : Subgroup G) := D.toG_mem _
  have hS2 : D.toG (SE.invRep i) ∉ D.S2 := by rw [D.toG_mem_S2_iff]; exact hi
  have hne := D.not_isSylowOf_of_not_mem_S2 hidx hS (D.toG_invRep_mul_self i)
    (D.toG_invRep_ne_one i) hS2
  obtain ⟨j, g, hjext, hlt, hgu, hC⟩ := D.exists_extremal_rep hS (D.toG_invRep_mul_self i)
    (D.toG_invRep_ne_one i) hne
  have h32 := D.card_centralizer_invRep_G i
  rw [h32] at hlt
  have key : ∀ i j : Fin 9, ¬ dS2 (SE.invRep i).d → SE.invRepCent i < SE.invRepCent j →
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by decide
  exact ⟨j, g, hjext, key i j hi hlt, hgu, hC⟩


theorem false_of_extremal_fused {j k : Fin 9}
    (hj : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G))
      (centralizer ({D.toG (SE.invRep j)} : Set G)))
    (hlt : SE.invRepCent j < SE.invRepCent k) (h : D.FusN j k) : False :=
  (D.not_fusN_of_lt hj hlt).1 h

omit [Finite G] in
theorem mem_M_of_fixz {A : Fus.Data} (hA : A.checkM (· * ·) = true) {u : G} {v : SE} {g : G}
    (hsrc : D.toG A.source = u) (htgt : A.target = v) (hgu : g⁻¹ * u * g = D.toG v)
    (hC : ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G),
      g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG v} : Set G))
    {k : ℕ} (hk : k < 32) (hz : A.elt (· * ·) k = SE.gen 0)
    (hfix : A.img (· * ·) (D.fusQ A g) k = SE.gen 0) : g ∈ D.M := by
  have hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
    intro s hs
    have hsu : D.toG s ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
      refine mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hsrc, ← map_mul, ← map_mul, hs]
    exact (mem_inf.mp (hC _ hsu)).1
  have h := D.img_conj hA (by rw [hsrc, htgt]; exact hgu) hgC hk
  rw [hfix, hz] at h
  exact mem_centralizer_singleton_iff.mpr (by
    calc g * D.z = g * (g⁻¹ * D.toG (SE.gen 0) * g) := by rw [← h]
      _ = D.z * g := by group)

end GHSylow

end CFSG.ComponentClassification.GHarris
