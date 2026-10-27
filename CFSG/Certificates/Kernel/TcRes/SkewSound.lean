module

public import CFSG.Certificates.Kernel.TcRes.TransSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK

variable {τ : Tag}

theorem iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = - iform x y := by
  simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem iform_neg_right (x y : Fin τ.rank → ℤ) : iform x (-y) = - iform x y := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem iform_skew {ψ : AddMonoid.End (Fin τ.rank → ℤ)} (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y)
    (hsq : ∀ x, ψ (ψ x) = -x) (x y : Fin τ.rank → ℤ) : iform (ψ x) y = - iform x (ψ y) := by
  rw [← hiso (ψ x) y, hsq, iform_neg_left]

theorem iform_skew_self
    {ψ : AddMonoid.End (Fin τ.rank → ℤ)}
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y) (hsq : ∀ x, ψ (ψ x) = -x)
    (x : Fin τ.rank → ℤ) : iform (ψ x) x = 0 := by
  have h := iform_skew hiso hsq x x
  rw [iform_comm x (ψ x)] at h
  omega

theorem skewOk_tuple
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ)}
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y) (hsq : ∀ x, ψ (ψ x) = -x) {c : ℕ → ℕ}
    (hc : ∀ m < 8, c m < 240 ∧ vec (c m) = ψ (vec m)) :
    ∀ k (hk : k < ((List.range 8).map c).length), 1 ≤ k →
      SkewOk vec (((List.range 8).map c).take k) ((List.range 8).map c)[k] := by
  intro k hk _
  simp only [List.length_map, List.length_range] at hk
  have hlen : (((List.range 8).map c).take k).length = k := by simp; omega
  have hget : ∀ a (ha : a < (((List.range 8).map c).take k).length),
      (((List.range 8).map c).take k)[a] = c a := by
    intro a ha
    simp
  simp only [List.getElem_map, List.getElem_range]
  refine ⟨(hc k hk).1, ?_, ?_⟩
  · rw [hlen, (hc k hk).2]
    exact iform_skew_self hiso hsq _
  · intro a ha
    rw [hlen] at ha
    rw [hlen, hget a (by rw [hlen]; exact ha), (hc k hk).2, (hc a (by omega)).2]
    exact ⟨hiso _ _, iform_skew hiso hsq _ _⟩

theorem exists_conj_of_beta0
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {rt : ℕ → ℕ → ℕ}
    {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {ND T0 tot : ℕ}
    (hD : DatumRaw Tag.E8 240 vec rt adj neg) (hS : SearchRaw vec ND T0 tot)
    (hT0 : fld T0 8 0 < 240) (ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ))
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y) (hsq : ∀ x, ψ (ψ x) = -x)
    (hroot : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (ψ γ)) (hψ0 : ψ (vec 0) = vec (fld T0 8 0)) :
    ∃ h : WeylGroup Tag.E8, ∀ m : Fin Tag.E8.rank, h • ψ (h⁻¹ • vec m) = vec (fld T0 8 m) := by
  have hex : ∀ m, ∃ i, m < 8 → i < 240 ∧ vec i = ψ (vec m) := by
    intro m
    by_cases hm : m < 8
    · obtain ⟨i, hi, hiv⟩ := hD.exists_eq (hroot _ (hD.isRoot m (by omega)))
      exact ⟨i, fun _ => ⟨hi, hiv⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose c hc using hex
  have hc0 : c 0 = fld T0 8 0 := by
    have h := (hc 0 (by norm_num))
    exact hD.inj _ h.1 _ hT0 (h.2.trans hψ0)
  have hr8 : (List.range 8).head? = some 0 := rfl
  obtain ⟨j, hj, hjt, hj8⟩ := hS.mem_search hT0 ((List.range 8).map c)
    (by simp only [List.head?_map, hr8, Option.map_some, hc0])
    (by simp) (skewOk_tuple hiso hsq hc)
  refine hS.leaf j hj (by
    rw [hjt]
    intro a ha
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    exact (hc m (List.mem_range.1 hm)).1) hj8 ψ hiso ?_
  intro m
  rw [hjt]
  have hm : (m : ℕ) < 8 := m.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  exact (hc m hm).2.symm

theorem exists_conj_phi0
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {rt : ℕ → ℕ → ℕ}
    {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {ND T0 tot : ℕ}
    (hD : DatumRaw Tag.E8 240 vec rt adj neg) (hS : SearchRaw vec ND T0 tot)
    (hT0 : fld T0 8 0 < 240)
    (hbt : ∀ g < 240, iform (vec g) (vec 0) = 0 →
      ∃ h : WeylGroup Tag.E8, h • vec 0 = vec 0 ∧ h • vec (fld T0 8 0) = vec g)
    (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ))
    (hiso : ∀ x y, iform (φ x) (φ y) = iform x y) (hsq : ∀ x, φ (φ x) = -x)
    (hroot : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ)) :
    ∃ h : WeylGroup Tag.E8, ∀ m : Fin Tag.E8.rank, h • φ (h⁻¹ • vec m) = vec (fld T0 8 m) := by
  obtain ⟨g, hg, hgv⟩ := hD.exists_eq (hroot _ (hD.isRoot 0 (by norm_num)))
  have hperp : iform (vec g) (vec 0) = 0 := by
    rw [hgv]
    exact iform_skew_self hiso hsq _
  obtain ⟨h1, h10, h1β⟩ := hbt g hg hperp
  let ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ) :=
    { toFun := fun x => h1⁻¹ • φ (h1 • x)
      map_zero' := by simp
      map_add' := fun a b => by simp only [smul_add, map_add] }
  have hψ : ∀ x, ψ x = h1⁻¹ • φ (h1 • x) := fun _ => rfl
  have hiso' : ∀ x y, iform (ψ x) (ψ y) = iform x y := by
    intro x y
    rw [hψ, hψ, iform_smul, hiso, iform_smul]
  have hsq' : ∀ x, ψ (ψ x) = -x := by
    intro x
    rw [hψ, hψ, smul_inv_smul, hsq, smul_neg, inv_smul_smul]
  have hroot' : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (ψ γ) := by
    intro γ hγ
    rw [hψ]
    exact CFSG.LieType.Chevalley.IsRoot.smul (hroot _ (CFSG.LieType.Chevalley.IsRoot.smul hγ h1))
      h1⁻¹
  have hψ0 : ψ (vec 0) = vec (fld T0 8 0) := by
    rw [hψ, h10, ← hgv, ← h1β, inv_smul_smul]
  obtain ⟨h2, hh2⟩ := exists_conj_of_beta0 hD hS hT0 ψ hiso' hsq' hroot' hψ0
  refine ⟨h2 * h1⁻¹, fun m => ?_⟩
  rw [← hh2 m, hψ, mul_inv_rev, inv_inv, mul_smul, mul_smul]

end CFSG.KC.TcRes

end
