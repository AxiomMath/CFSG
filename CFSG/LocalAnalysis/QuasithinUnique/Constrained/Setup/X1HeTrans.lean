module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Sub

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Trans

variable {G : Type*} [Group G] {S : Type*} [Group S]

theorem rank_of_equiv {H : Subgroup G} (Φ : ↥H ≃* MulAut S) {r : ℕ}
    (hr : ∀ B : Subgroup ↥H, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  intro B hcomm hsq
  have h := hr (B.comap Φ.toMonoidHom)
    (fun x hx y hy => Φ.injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy))
    (fun x hx => Φ.injective (by rw [map_mul, map_one]; exact hsq _ hx))
  have hcard : Nat.card (B.comap Φ.toMonoidHom) = Nat.card B :=
    Nat.card_congr (Φ.toEquiv.subtypeEquiv (fun a => Iff.rfl))
  rwa [hcard] at h

theorem gen_of_equiv {H A : Subgroup G} (hAH : A ≤ H) (Φ : ↥H ≃* MulAut S) (θ : S ≃* ↥A)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hAH (θ s).2⟩ = MulAut.conj s) {k : ℕ}
    (hgen : ∀ x ∈ H, x * x = 1 → x ≠ 1 → ∃ gs : List G, gs.length = k ∧ (∀ g ∈ gs, g ∈ A) ∧
      A ≤ Subgroup.closure (conjSet gs {x})) :
    ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ cs : List (MulAut S), cs.length = k ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
      ∀ s : S, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}) := by
  intro ψ hψ2 hψ1
  set xh : ↥H := Φ.symm ψ with hxh
  have hx2 : xh * xh = 1 := by
    apply Φ.injective
    rw [map_mul, hxh, MulEquiv.apply_symm_apply, hψ2, map_one]
  have hx1 : xh ≠ 1 := by
    intro h
    apply hψ1
    rw [← MulEquiv.apply_symm_apply Φ ψ, ← hxh, h, map_one]
  obtain ⟨gs, hlen, hgs, hA⟩ := hgen (xh : G) xh.2 (by simpa using congrArg Subtype.val hx2)
    (fun h => hx1 (Subtype.ext h))
  let cs : List (MulAut S) := gs.attach.map fun g => Φ ⟨g.1, hAH (hgs g.1 g.2)⟩
  have hΦA : ∀ (g : G) (hg : g ∈ A), Φ ⟨g, hAH hg⟩ = MulAut.conj (θ.symm ⟨g, hg⟩) := by
    intro g hg
    rw [← hΦ]
    congr 1
    apply Subtype.ext
    simp
  refine ⟨cs, by simp [cs, hlen], ?_, ?_⟩
  · intro c hc
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨θ.symm ⟨g.1, hgs g.1 g.2⟩, (hΦA g.1 (hgs g.1 g.2)).symm⟩
  · intro s
    set K' : Subgroup (MulAut S) := Subgroup.closure (conjSet cs {ψ}) with hK'
    set Kp : Subgroup G := (K'.comap Φ.toMonoidHom).map H.subtype with hKp
    have hsub : conjSet gs {(xh : G)} ⊆ (Kp : Set G) := by
      rintro _ ⟨g, hg, t, ht, rfl⟩
      have ht' : t = (xh : G) := by simpa using ht
      subst ht'
      have hgA : g ∈ A := hgs g hg
      refine ⟨⟨g, hAH hgA⟩ * xh * ⟨g, hAH hgA⟩⁻¹, ?_, rfl⟩
      show Φ (⟨g, hAH hgA⟩ * xh * ⟨g, hAH hgA⟩⁻¹) ∈ K'
      rw [map_mul, map_mul, map_inv, hxh, MulEquiv.apply_symm_apply]
      refine Subgroup.subset_closure ⟨Φ ⟨g, hAH hgA⟩, ?_, ψ, rfl, rfl⟩
      exact List.mem_map.2 ⟨⟨g, hg⟩, List.mem_attach _ _, rfl⟩
    have hAKp : A ≤ Kp := hA.trans ((Subgroup.closure_le Kp).2 hsub)
    obtain ⟨y, hy, hyθ⟩ := hAKp (θ s).2
    have hy' : y = ⟨(θ s : G), hAH (θ s).2⟩ := Subtype.ext hyθ
    rw [← hΦ s, ← hy']
    exact hy

theorem conj_compat {H A : Subgroup G} (hAH : A ≤ H) (c : ↥H →* MulAut ↥A)
    (hc : ∀ (x : ↥H) (a : ↥A), ((c x a : ↥A) : G) = x * a * x⁻¹) (Φ : ↥H ≃* MulAut S)
    (θ : S ≃* ↥A) (hΦ : ∀ (x : ↥H) (s : S), Φ x s = θ.symm (c x (θ s))) (s : S) :
    Φ ⟨(θ s : G), hAH (θ s).2⟩ = MulAut.conj s := by
  refine MulEquiv.ext fun s' => ?_
  rw [hΦ, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [hc]
  simp [MulAut.conj_apply, map_mul, map_inv]

end Trans

end CFSG.QuasithinUnique.Setup.X1
