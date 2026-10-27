module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecMod

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X7

section Counting

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem two_mul_card_le_of_lt {P Q : Submodule (ZMod 2) V} (h : P < Q) :
    2 * Nat.card ↥P ≤ Nat.card ↥Q := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [natCard_eq_two_pow_finrank ↥P, natCard_eq_two_pow_finrank ↥Q]
  have := Submodule.finrank_lt_finrank_of_lt h
  calc 2 * 2 ^ Module.finrank (ZMod 2) ↥P = 2 ^ (Module.finrank (ZMod 2) ↥P + 1) := by ring
    _ ≤ 2 ^ Module.finrank (ZMod 2) ↥Q := Nat.pow_le_pow_right (by norm_num) this

theorem card_le_of_le {P Q : Submodule (ZMod 2) V} (h : P ≤ Q) : Nat.card ↥P ≤ Nat.card ↥Q :=
  Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le h)

theorem card_sup_le_mul (P Q : Submodule (ZMod 2) V) :
    Nat.card ↥(P ⊔ Q) ≤ Nat.card ↥P * Nat.card ↥Q := by
  have h := natCard_sup_mul_natCard_inf P Q
  have hpos : 0 < Nat.card ↥(P ⊓ Q) := Nat.card_pos
  calc Nat.card ↥(P ⊔ Q) = Nat.card ↥(P ⊔ Q) * 1 := (mul_one _).symm
    _ ≤ Nat.card ↥(P ⊔ Q) * Nat.card ↥(P ⊓ Q) := Nat.mul_le_mul_left _ hpos
    _ = Nat.card ↥P * Nat.card ↥Q := h

theorem card_sup_of_disjoint {U₀ U₁ : Submodule (ZMod 2) V} (hd : Disjoint U₀ U₁) :
    Nat.card ↥(U₀ ⊔ U₁) = Nat.card ↥U₀ * Nat.card ↥U₁ := by
  have h := natCard_sup_mul_natCard_inf U₀ U₁
  rw [disjoint_iff.1 hd] at h
  simpa using h

variable {Γ : Type*} [Group Γ] (τ : Γ →* (V ≃ₗ[ZMod 2] V)) (B : Subgroup Γ)

theorem card_sup_inf_fix_le {U₀ U₁ : Submodule (ZMod 2) V} (hd : Disjoint U₀ U₁)
    (h0 : ∀ b ∈ B, ∀ u ∈ U₀, τ b u ∈ U₀) (h1 : ∀ b ∈ B, ∀ u ∈ U₁, τ b u ∈ U₁) :
    Nat.card ↥((U₀ ⊔ U₁) ⊓ fixSub τ B) ≤
      Nat.card ↥(U₀ ⊓ fixSub τ B) * Nat.card ↥(U₁ ⊓ fixSub τ B) := by
  have hle : (U₀ ⊔ U₁) ⊓ fixSub τ B ≤ (U₀ ⊓ fixSub τ B) ⊔ (U₁ ⊓ fixSub τ B) := by
    rintro x ⟨hx, hfix⟩
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.1 hx
    have key : ∀ b ∈ B, τ b u₀ = u₀ ∧ τ b u₁ = u₁ := by
      intro b hb
      have h : τ b (u₀ + u₁) = u₀ + u₁ := hfix b hb
      rw [map_add] at h
      have hdiff : τ b u₀ - u₀ = -(τ b u₁ - u₁) := by
        calc τ b u₀ - u₀ = (τ b u₀ + τ b u₁) - u₀ - τ b u₁ := by abel
          _ = (u₀ + u₁) - u₀ - τ b u₁ := by rw [h]
          _ = -(τ b u₁ - u₁) := by abel
      have h0' : τ b u₀ - u₀ ∈ U₀ := U₀.sub_mem (h0 b hb u₀ hu₀) hu₀
      have h1' : τ b u₀ - u₀ ∈ U₁ := by
        rw [hdiff]
        exact U₁.neg_mem (U₁.sub_mem (h1 b hb u₁ hu₁) hu₁)
      have hz : τ b u₀ - u₀ = 0 := (Submodule.disjoint_def.1 hd) _ h0' h1'
      have hz' : τ b u₁ - u₁ = 0 := by
        rw [← neg_eq_zero, ← hdiff]
        exact hz
      exact ⟨sub_eq_zero.1 hz, sub_eq_zero.1 hz'⟩
    exact Submodule.add_mem_sup ⟨hu₀, fun b hb => (key b hb).1⟩ ⟨hu₁, fun b hb => (key b hb).2⟩
  exact (card_le_of_le hle).trans (card_sup_le_mul _ _)

omit τ B in
theorem fix_codim_contradiction {X M Fx : Submodule (ZMod 2) V} (hXM : X ≤ M) {P : ℕ} (hP : 0 < P)
    (hM : Nat.card ↥M ≤ 2 * P * Nat.card ↥(M ⊓ Fx))
    (hX : 4 * P * Nat.card ↥(X ⊓ Fx) ≤ Nat.card ↥X) : False := by
  have h := card_fix_le (X := X) (M := M) (Fx := Fx) hXM
  have ha : 0 < Nat.card ↥(X ⊓ Fx) := Nat.card_pos
  have hc : 0 < Nat.card ↥(M ⊓ Fx) := Nat.card_pos
  set a := Nat.card ↥(X ⊓ Fx)
  set c := Nat.card ↥(M ⊓ Fx)
  have h1 : 4 * P * a * c ≤ Nat.card ↥X * c := Nat.mul_le_mul_right c hX
  have h2 : Nat.card ↥M * a ≤ 2 * P * c * a := Nat.mul_le_mul_right a hM
  have hpos : 0 < P * a * c := Nat.mul_pos (Nat.mul_pos hP ha) hc
  nlinarith

end Counting

section DualPair

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

@[expose] def idRep (U : Type) [AddCommGroup U] [Module (ZMod 2) U] :
    Representation (ZMod 2) (U ≃ₗ[ZMod 2] U) U :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := U)

theorem dp_card_bound (G : Subgroup (U ≃ₗ[ZMod 2] U)) [CFSG.IsElementaryAbelian 2 G]
    (hne : G ≠ ⊥)
    (hquad : ∀ g ∈ G, ∀ h ∈ G,
      ((g : U →ₗ[ZMod 2] U) - 1) ∘ₗ ((h : U →ₗ[ZMod 2] U) - 1) = 0)
    {r b : ℕ} (hr : 1 ≤ r) (hb : Nat.card G = 2 ^ b)
    (hrank : ∀ g ∈ G, g ≠ 1 →
      Module.finrank (ZMod 2) (LinearMap.range ((g : U →ₗ[ZMod 2] U) - 1)) = r) :
    2 ^ (b + r) * (Nat.card (fixedSub (idRep U) G) * Nat.card (fixedSub (idRep U).dual G)) ≤
      Nat.card U * Nat.card U := by
  obtain ⟨hmr, hcard, -⟩ := constant_moving_rank_no_dual_pair_offender (ρ := idRep U) (A := G)
    hquad hr hb hne hrank
  rw [Nat.card_prod, natCard_dual_eq, natCard_fixedSub_prod_dual] at hcard
  rw [hcard]
  have h2 : 2 ^ (b + r) ≤ 2 ^ (Module.finrank (ZMod 2) (U ⧸ fixedSub (idRep U) G) +
      Module.finrank (ZMod 2) (commSub (idRep U) G)) := Nat.pow_le_pow_right (by norm_num) hmr
  rw [mul_comm (Nat.card (fixedSub (idRep U) G) * Nat.card (fixedSub (idRep U).dual G))]
  exact Nat.mul_le_mul_right _ h2

end DualPair

section Transfer

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ : Type} [Group Γ]
  (τ : Γ →* (V ≃ₗ[ZMod 2] V))

theorem dual_pair_codim (A₁ : Subgroup Γ) {U₀ U₁ : Submodule (ZMod 2) V}
    (h0 : ∀ g, ∀ u ∈ U₀, τ g u ∈ U₀) (h1 : ∀ g, ∀ u ∈ U₁, τ g u ∈ U₁) (hdis : Disjoint U₀ U₁)
    [CFSG.IsElementaryAbelian 2 ↥(A₁.map (resHom τ U₁ h1))]
    (hne : A₁.map (resHom τ U₁ h1) ≠ ⊥)
    (hquad : ∀ g ∈ A₁.map (resHom τ U₁ h1), ∀ h ∈ A₁.map (resHom τ U₁ h1),
      ((g : U₁ →ₗ[ZMod 2] U₁) - 1) ∘ₗ ((h : U₁ →ₗ[ZMod 2] U₁) - 1) = 0)
    {r b : ℕ} (hr : 2 ≤ r) (hb : Nat.card ↥(A₁.map (resHom τ U₁ h1)) = 2 ^ b)
    (hrank : ∀ g ∈ A₁.map (resHom τ U₁ h1), g ≠ 1 →
      Module.finrank (ZMod 2) (LinearMap.range ((g : U₁ →ₗ[ZMod 2] U₁) - 1)) = r)
    (e : ↥U₀ ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥U₁)
    (he : ∀ γ ∈ A₁, ∀ u : ↥U₀,
      e (resHom τ U₀ h0 γ u) = (idRep ↥U₁).dual (resHom τ U₁ h1 γ) (e u)) :
    4 * 2 ^ b * Nat.card ↥((U₀ ⊔ U₁) ⊓ fixSub τ A₁) ≤ Nat.card ↥(U₀ ⊔ U₁) := by
  classical
  set G := A₁.map (resHom τ U₁ h1) with hG
  have hdp := dp_card_bound G hne hquad (r := r) (by omega) hb hrank
  have hf1 : Nat.card ↥(fixedSub (idRep ↥U₁) G) = Nat.card ↥(U₁ ⊓ fixSub τ A₁) := by
    have : fixedSub (idRep ↥U₁) G = fixSub (MonoidHom.id (↥U₁ ≃ₗ[ZMod 2] ↥U₁)) G :=
      Submodule.ext fun w => Iff.rfl
    rw [this, ← card_fixSub_id_map τ U₁ h1 A₁]
  have hf0 : Nat.card ↥(fixedSub (idRep ↥U₁).dual G) = Nat.card ↥(U₀ ⊓ fixSub τ A₁) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨((e.symm w.1 : ↥U₀) : V), (e.symm w.1).2, fun γ hγ => ?_⟩
        invFun := fun v => ⟨e ⟨v.1, v.2.1⟩, fun g hg => ?_⟩
        left_inv := fun w => ?_
        right_inv := fun v => ?_ }
    · have h2 := he γ hγ (e.symm w.1)
      rw [LinearEquiv.apply_symm_apply] at h2
      have h3 : (idRep ↥U₁).dual (resHom τ U₁ h1 γ) w.1 = w.1 :=
        w.2 _ (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)
      rw [h3] at h2
      have h4 : resHom τ U₀ h0 γ (e.symm w.1) = e.symm w.1 := by
        apply e.injective
        rw [h2, LinearEquiv.apply_symm_apply]
      have h5 := congrArg (fun x : ↥U₀ => (x : V)) h4
      simpa [coe_resHom_apply] using h5
    · obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
      have h2 := he γ hγ ⟨v.1, v.2.1⟩
      have h3 : resHom τ U₀ h0 γ ⟨v.1, v.2.1⟩ = ⟨v.1, v.2.1⟩ := by
        apply Subtype.ext
        simpa [coe_resHom_apply] using v.2.2 γ hγ
      rw [h3] at h2
      exact h2.symm
    · exact Subtype.ext (LinearEquiv.apply_symm_apply e _)
    · exact Subtype.ext (congrArg (fun x : ↥U₀ => (x : V))
        (LinearEquiv.symm_apply_apply e ⟨v.1, v.2.1⟩))
  have hU0 : Nat.card ↥U₀ = Nat.card ↥U₁ := by
    rw [Nat.card_congr e.toEquiv, natCard_dual_eq]
  have hX : Nat.card ↥(U₀ ⊔ U₁) = Nat.card ↥U₁ * Nat.card ↥U₁ := by
    rw [card_sup_of_disjoint hdis, hU0]
  have hfx := card_sup_inf_fix_le τ A₁ hdis (fun b _ => h0 b) (fun b _ => h1 b)
  rw [hf1, hf0] at hdp
  have h4 : 4 * 2 ^ b ≤ 2 ^ (b + r) := by
    calc 4 * 2 ^ b = 2 ^ (b + 2) := by ring
      _ ≤ 2 ^ (b + r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 4 * 2 ^ b * Nat.card ↥((U₀ ⊔ U₁) ⊓ fixSub τ A₁)
      ≤ 4 * 2 ^ b * (Nat.card ↥(U₀ ⊓ fixSub τ A₁) * Nat.card ↥(U₁ ⊓ fixSub τ A₁)) :=
        Nat.mul_le_mul_left _ hfx
    _ ≤ 2 ^ (b + r) * (Nat.card ↥(U₁ ⊓ fixSub τ A₁) * Nat.card ↥(U₀ ⊓ fixSub τ A₁)) := by
        rw [mul_comm (Nat.card ↥(U₁ ⊓ fixSub τ A₁))]
        exact Nat.mul_le_mul_right _ h4
    _ ≤ Nat.card ↥U₁ * Nat.card ↥U₁ := hdp
    _ = Nat.card ↥(U₀ ⊔ U₁) := hX.symm

end Transfer

section Restrict

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {N : Type} [Group N]

theorem offender_of_sub (σ : N →* (V ≃ₗ[ZMod 2] V)) (A : Subgroup N) {M U : Submodule (ZMod 2) V}
    (hMA : Offender.IsInvariant σ A M) (hUA : Offender.IsInvariant σ A U) (hUM : U ≤ M)
    (hker : centSub (σ.comp A.subtype) U = centSub (σ.comp A.subtype) M)
    (hoff : Nat.card ↥M ≤
      weight (MonoidHom.id (↥M ≃ₗ[ZMod 2] ↥M)) (resSub σ A M hMA).range) :
    Nat.card ↥U ≤ weight (MonoidHom.id (↥U ≃ₗ[ZMod 2] ↥U)) (resSub σ A U hUA).range := by
  have hMτ : ∀ g : ↥A, ∀ m ∈ M, (σ.comp A.subtype) g m ∈ M := fun g m hm => hMA g g.2 m hm
  have hUτ : ∀ g : ↥A, ∀ u ∈ U, (σ.comp A.subtype) g u ∈ U := fun g u hu => hUA g g.2 u hu
  have h1 := weightId_range (σ.comp A.subtype) M hMτ
  have h2 := weightId_range (σ.comp A.subtype) U hUτ
  have hcard := card_fix_le (X := U) (M := M) (Fx := fixSub (σ.comp A.subtype) ⊤) hUM
  have hMpos : 0 < Nat.card ↥(M ⊓ fixSub (σ.comp A.subtype) ⊤) := Nat.card_pos
  change Nat.card ↥M ≤ weight _ (resHom (σ.comp A.subtype) M hMτ).range at hoff
  change Nat.card ↥U ≤ weight _ (resHom (σ.comp A.subtype) U hUτ).range
  rw [h1] at hoff
  rw [h2, hker]
  refine Nat.le_of_mul_le_mul_right ?_ hMpos
  calc Nat.card ↥U * Nat.card ↥(M ⊓ fixSub (σ.comp A.subtype) ⊤)
      ≤ Nat.card ↥M * Nat.card ↥(U ⊓ fixSub (σ.comp A.subtype) ⊤) := hcard
    _ ≤ ((centSub (σ.comp A.subtype) M).index *
          Nat.card ↥(M ⊓ fixSub (σ.comp A.subtype) ⊤)) *
          Nat.card ↥(U ⊓ fixSub (σ.comp A.subtype) ⊤) := Nat.mul_le_mul_right _ hoff
    _ = ((centSub (σ.comp A.subtype) M).index * Nat.card ↥(U ⊓ fixSub (σ.comp A.subtype) ⊤)) *
          Nat.card ↥(M ⊓ fixSub (σ.comp A.subtype) ⊤) := by ring

end Restrict

end CFSG.QuasithinUnique.Setup.X7Sec
