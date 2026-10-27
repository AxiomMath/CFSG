module

public import CFSG.CGT.Foote82.T66.CaseIIBasic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev subOne (a : GLV V) : V →ₗ[ZMod 2] V := (a : V →ₗ[ZMod 2] V) - 1

theorem subOne_apply (a : GLV V) (w : V) : subOne a w = a w - w := by
  simp [subOne]

theorem commSpace_zpowers_eq_map {a : GLV V} (ha : a * a = 1) (U : Submodule (ZMod 2) V) :
    commSpace (Subgroup.zpowers a) U = U.map (subOne a) := by
  apply le_antisymm
  · refine commSpace_le_iff.2 fun k hk u hu => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h2 : a ^ (2 : ℕ) = 1 := by rw [pow_two, ha]
    have hn : a ^ n = a ^ (n % 2) := by
      have := zpow_eq_zpow_emod' n h2
      simpa using this
    rw [hn]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0
    · rw [h0, zpow_zero]
      simp
    · rw [h0, zpow_one]
      exact ⟨u, hu, subOne_apply a u⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [subOne_apply]
    exact sub_mem_commSpace (Subgroup.mem_zpowers a) hu

theorem commSpace_zpowers_top_eq_range {a : GLV V} (ha : a * a = 1) :
    commSpace (Subgroup.zpowers a) ⊤ = LinearMap.range (subOne a) := by
  rw [commSpace_zpowers_eq_map ha, Submodule.map_top]

theorem map_subOne_conj (g a : GLV V) (U : Submodule (ZMod 2) V) :
    (U.map (g : V →ₗ[ZMod 2] V)).map (subOne (g * a * g⁻¹)) =
      (U.map (subOne a)).map (g : V →ₗ[ZMod 2] V) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext w
  simp [subOne, mul_assoc]

theorem card_range_subOne_conj (g a : GLV V) :
    Nat.card ↥(LinearMap.range (subOne (g * a * g⁻¹))) =
      Nat.card ↥(LinearMap.range (subOne a)) := by
  have h := map_subOne_conj g a ⊤
  have htop : (⊤ : Submodule (ZMod 2) V).map (g : V →ₗ[ZMod 2] V) = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.2 g.surjective
  rw [htop, Submodule.map_top, Submodule.map_top] at h
  rw [h]
  exact Nat.card_congr ((LinearMap.range (subOne a)).equivMapOfInjective _
    g.injective).toEquiv.symm

theorem card_eq_two_pow_finrank (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have : Fintype W := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]

theorem finrank_eq_of_card_eq {W W' : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W'] (h : Nat.card W = Nat.card W') :
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) W' := by
  rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank] at h
  exact Nat.pow_right_injective le_rfl h

theorem range_eq_sup_of_isCompl {V₀ V₁ : Submodule (ZMod 2) V} (hc : IsCompl V₀ V₁)
    (f : V →ₗ[ZMod 2] V) :
    LinearMap.range f = V₀.map f ⊔ V₁.map f := by
  rw [← Submodule.map_top, ← hc.sup_eq_top, Submodule.map_sup]

theorem map_inf_map_eq_bot_of_isCompl {V₀ V₁ : Submodule (ZMod 2) V} (hc : IsCompl V₀ V₁)
    (f : V →ₗ[ZMod 2] V) (h₀ : V₀.map f ≤ V₀) (h₁ : V₁.map f ≤ V₁) :
    V₀.map f ⊓ V₁.map f = ⊥ :=
  eq_bot_iff.2 fun w hw => hc.inf_eq_bot ▸ ⟨h₀ hw.1, h₁ hw.2⟩

theorem finrank_range_eq_add {V₀ V₁ : Submodule (ZMod 2) V} (hc : IsCompl V₀ V₁)
    (f : V →ₗ[ZMod 2] V) (h₀ : V₀.map f ≤ V₀) (h₁ : V₁.map f ≤ V₁) :
    Module.finrank (ZMod 2) ↥(LinearMap.range f) =
      Module.finrank (ZMod 2) ↥(V₀.map f) + Module.finrank (ZMod 2) ↥(V₁.map f) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (V₀.map f) (V₁.map f)
  rw [map_inf_map_eq_bot_of_isCompl hc f h₀ h₁, finrank_bot, add_zero,
    ← range_eq_sup_of_isCompl hc f] at h
  exact h

theorem beta_mem_range {ι : Type} [Fintype ι] [DecidableEq ι] {W : Submodule (ZMod 2) V}
    (β : ↥W →+ (ι → ZMod 2)) {a : GLV V} (haW : ∀ w ∈ W, a w ∈ W) (M : Matrix ι ι (ZMod 2))
    (he : ∀ w : ↥W, β ⟨a w, haW w w.2⟩ = M.mulVec (β w)) {x : V} (hx : x ∈ W.map (subOne a))
    (hxW : x ∈ W) : β ⟨x, hxW⟩ ∈ LinearMap.range (Matrix.mulVecLin (M - 1)) := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨β ⟨w, hw⟩, ?_⟩
  have e : (⟨subOne a w, hxW⟩ : ↥W) = ⟨a w, haW w hw⟩ - ⟨w, hw⟩ := by
    apply Subtype.ext
    simp [subOne_apply]
  rw [e, map_sub, show β ⟨a w, haW w hw⟩ = M.mulVec (β ⟨w, hw⟩) from he ⟨w, hw⟩,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem map_smul_pi {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {ι : Type*}
    (f : A →+ (ι → ZMod 2)) (c : ZMod 2) (x : A) : f (c • x) = fun i => c * f x i := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, map_zero]
    funext i
    rw [zero_mul]
    rfl
  · rw [one_smul]
    funext i
    rw [one_mul]

theorem finrank_map_subOne_eq {ι : Type} [Fintype ι] [DecidableEq ι] {W : Submodule (ZMod 2) V}
    (β : ↥W →+ (ι → ZMod 2)) (hβ : Function.Bijective β) {a : GLV V}
    (haW : ∀ w ∈ W, a w ∈ W) (M : Matrix ι ι (ZMod 2))
    (he : ∀ w : ↥W, β ⟨a w, haW w w.2⟩ = M.mulVec (β w)) :
    Module.finrank (ZMod 2) ↥(W.map (subOne a)) =
      Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin (M - 1))) := by
  have hle : ∀ x ∈ W.map (subOne a), x ∈ W := by
    rintro _ ⟨w, hw, rfl⟩
    rw [subOne_apply]
    exact W.sub_mem (haW w hw) hw
  let f : ↥(W.map (subOne a)) →ₗ[ZMod 2] ↥(LinearMap.range (Matrix.mulVecLin (M - 1))) :=
    { toFun := fun x => ⟨β ⟨x, hle x x.2⟩, beta_mem_range β haW M he x.2 (hle x x.2)⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [← map_add]
        rfl
      map_smul' := fun c x => by
        apply Subtype.ext
        exact map_smul_pi β c ⟨x, hle x x.2⟩ }
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h1 : β ⟨x, hle x x.2⟩ = β ⟨y, hle y y.2⟩ := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.mk.inj (hβ.1 h1))
    · obtain ⟨t, ht⟩ := y.2
      obtain ⟨w, rfl⟩ := hβ.2 t
      have hx : subOne a w ∈ W.map (subOne a) := ⟨w, w.2, rfl⟩
      refine ⟨⟨subOne a w, hx⟩, Subtype.ext ?_⟩
      show β ⟨subOne a w, _⟩ = y
      have e : (⟨subOne a w, hle _ hx⟩ : ↥W) = ⟨a w, haW w w.2⟩ - w := by
        apply Subtype.ext
        simp [subOne_apply]
      rw [e, map_sub, he, ← ht, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
      rfl
  exact (LinearEquiv.ofBijective f hf).finrank_eq

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem invariant_V₀ : Invariant H₁ (commSpace (HH G L v) ⊤) :=
  invariant_commSpace (fun _ hh _ hx => c.conj_mem_H hh hx) (invariant_top _)

theorem invariant_V₁ : Invariant H₁ (fixedSpace (HH G L v)) :=
  invariant_fixedSpace fun _ hh _ hx => c.conj_mem_H hh hx

theorem map_V₀_le {a : GLV V} (ha : a ∈ H₁) :
    (commSpace (HH G L v) ⊤).map (subOne a) ≤ commSpace (HH G L v) ⊤ := by
  rintro _ ⟨w, hw, rfl⟩
  rw [subOne_apply]
  exact Submodule.sub_mem _ (c.invariant_V₀ a ha w hw) hw

theorem map_V₁_le {a : GLV V} (ha : a ∈ H₁) :
    (fixedSpace (HH G L v)).map (subOne a) ≤ fixedSpace (HH G L v) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [subOne_apply]
  exact Submodule.sub_mem _ (c.invariant_V₁ a ha w hw) hw

theorem map_V₁_eq {a h : GLV V} (hh : h ∈ HH G L v) :
    (fixedSpace (HH G L v)).map (subOne (a * h)) = (fixedSpace (HH G L v)).map (subOne a) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [subOne_apply, hx h hh]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [subOne_apply, hx h hh]

theorem exists_beta (hs : CaseIISplit) :
    ∃ β : ↥(commSpace (HH G L v) ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2),
      Function.Bijective β ∧
      ∀ (h : ↥H₁) (w w' : ↥(commSpace (HH G L v) ⊤)), (w' : V) = (h : GLV V) (w : V) →
        β w' = ((ψ h : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).mulVec (β w) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := c.data.natural
  refine ⟨β, ⟨fun x y hxy => ?_, hβs⟩, hβe⟩
  have hk : x - y ∈ β.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hxy]
    exact sub_eq_zero_of_eq rfl
  rw [hβk] at hk
  have h0 : ((x - y : ↥(commSpace (HH G L v) ⊤)) : V) ∈
      commSpace (HH G L v) ⊤ ⊓ fixedSpace (HH G L v) := ⟨(x - y).2, hk⟩
  rw [(c.split hs).inf_eq_bot, Submodule.mem_bot] at h0
  exact sub_eq_zero.1 (Subtype.ext h0)

theorem finrank_map_V₀ (hs : CaseIISplit) {a : GLV V} (ha : a ∈ H₁) :
    Module.finrank (ZMod 2) ↥((commSpace (HH G L v) ⊤).map (subOne a)) =
      cdim6 (ψ ⟨a, ha⟩) := by
  obtain ⟨β, hβ, hβe⟩ := c.exists_beta hs
  exact finrank_map_subOne_eq β hβ (c.invariant_V₀ a ha) _
    fun w => hβe ⟨a, ha⟩ w ⟨a w, c.invariant_V₀ a ha w w.2⟩ rfl

theorem finrank_range_subOne (hs : CaseIISplit) {a : GLV V} (ha : a ∈ H₁) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (subOne a)) =
      cdim6 (ψ ⟨a, ha⟩) +
        Module.finrank (ZMod 2) ↥((fixedSpace (HH G L v)).map (subOne a)) := by
  rw [finrank_range_eq_add (c.split hs) _ (c.map_V₀_le ha) (c.map_V₁_le ha),
    c.finrank_map_V₀ hs ha]

end Ctx

end CaseII

end CFSG.CGT.Foote82
