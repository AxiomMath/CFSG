module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Stage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1

theorem exists_u3A₁Coords_of_trans {G : Type} [Group G] [Finite G] {A₁ : Subgroup G} {d : G}
    (hcomm : ∀ b ∈ A₁, ∀ b' ∈ A₁, b * b' = b' * b) (hsq : ∀ b ∈ A₁, b ^ 2 = 1)
    (hdA : ∀ b ∈ A₁, d⁻¹ * b * d ∈ A₁)
    (htr : ∀ b ∈ A₁, ∀ b' ∈ A₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    (hne : ∃ b ∈ A₁, b ≠ 1) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
      Fintype.card K = Nat.card A₁ ∧ U3A₁Coords A₁ d v μ ∧
        ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w := by
  classical
  let _ : CommGroup A₁ := { (inferInstance : Group A₁) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hx2 : ∀ x : Additive A₁, 2 • x = 0 := fun x => by
    have h1 : (Additive.toMul x : A₁) ^ 2 = 1 :=
      Subtype.ext (by simpa using hsq _ (Additive.toMul x).2)
    calc 2 • x = Additive.ofMul ((Additive.toMul x) ^ 2) := rfl
      _ = 0 := by rw [h1]; rfl
  let _ : Module (ZMod 2) (Additive A₁) := AddCommGroup.zmodModule (n := 2) hx2
  let φ : A₁ →* A₁ :=
    { toFun := fun b => ⟨d⁻¹ * b * d, hdA b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show d⁻¹ * ((a : G) * b) * d = d⁻¹ * a * d * (d⁻¹ * b * d)
        group) }
  let T : Module.End (ZMod 2) (Additive A₁) := (MonoidHom.toAdditive φ).toZModLinearMap 2
  have hT : ∀ b : A₁, ((Additive.toMul (T (Additive.ofMul b)) : A₁) : G) = d⁻¹ * b * d :=
    fun b => rfl
  have hTpow : ∀ (j : ℕ) (b : A₁),
      ((Additive.toMul ((T ^ j) (Additive.ofMul b)) : A₁) : G) = (d ^ j)⁻¹ * b * d ^ j := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [pow_succ', Module.End.mul_apply]
      have e1 : (T ^ j) (Additive.ofMul b) = Additive.ofMul (Additive.toMul ((T ^ j)
          (Additive.ofMul b))) := rfl
      rw [e1, hT, ih b, pow_succ]
      group
  have htrans : ∀ w w' : Additive A₁, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w' := by
    intro w w' hw hw'
    have hb : ((Additive.toMul w : A₁) : G) ≠ 1 := fun h1 => hw (by
      have : Additive.toMul w = 1 := Subtype.ext h1
      rw [← ofMul_toMul w, this]; rfl)
    have hb' : ((Additive.toMul w' : A₁) : G) ≠ 1 := fun h1 => hw' (by
      have : Additive.toMul w' = 1 := Subtype.ext h1
      rw [← ofMul_toMul w', this]; rfl)
    obtain ⟨n, hn⟩ := htr _ (Additive.toMul w).2 _ (Additive.toMul w').2 hb hb'
    refine ⟨n, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [← ofMul_toMul w, hTpow n]
    exact hn
  obtain ⟨b₀, hb₀, hb₀1⟩ := hne
  have hw₀ : (Additive.ofMul (⟨b₀, hb₀⟩ : A₁)) ≠ 0 := fun h0 => hb₀1 (by
    have h1 := congrArg (fun x : Additive A₁ => ((Additive.toMul x : A₁) : G)) h0
    simpa using h1)
  have : Nontrivial (Additive A₁) := nontrivial_of_ne _ _ hw₀
  have : Finite (Additive A₁) := Finite.of_equiv A₁ Additive.ofMul
  have hF := CFSG.LocalAnalysis.SteinbergBT.isField_adjoin_singleton (F := ZMod 2) htrans
  have hbij := CFSG.LocalAnalysis.SteinbergBT.bijective_apply_adjoin_singleton htrans hw₀
  have hpow := fun (k : Module.End (ZMod 2) (Additive A₁)) =>
    CFSG.LocalAnalysis.SteinbergBT.exists_pow_eq_of_mem_adjoin_singleton htrans (k := k)
  set R := Algebra.adjoin (ZMod 2) ({T} : Set (Module.End (ZMod 2) (Additive A₁))) with hR
  let _ : Field R := hF.toField
  have : Finite (Module.End (ZMod 2) (Additive A₁)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Additive A₁) =>
      (f : Additive A₁ → Additive A₁)) DFunLike.coe_injective
  let _ : Fintype R := Fintype.ofFinite R
  let e : R ≃ Additive A₁ := Equiv.ofBijective _ hbij
  have he : ∀ k : R, e k = (k : Module.End (ZMod 2) (Additive A₁)) (Additive.ofMul ⟨b₀, hb₀⟩) :=
    fun k => rfl
  have he_add : ∀ w w' : Additive A₁, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [Equiv.apply_symm_apply, he, Subalgebra.coe_add, LinearMap.add_apply, ← he, ← he,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let μ : R := ⟨T, Algebra.subset_adjoin (Set.mem_singleton T)⟩
  have he_mul : ∀ w : Additive A₁, e.symm (T w) = μ * e.symm w := by
    intro w
    apply e.injective
    rw [Equiv.apply_symm_apply, he, Subalgebra.coe_mul, Module.End.mul_apply, ← he,
      Equiv.apply_symm_apply]
  let v : G → R := fun g => if hg : g ∈ A₁ then e.symm (Additive.ofMul ⟨g, hg⟩) else 0
  have hv : ∀ b (hb : b ∈ A₁), v b = e.symm (Additive.ofMul ⟨b, hb⟩) := fun b hb => by
    simp [v, hb]
  have h11 : (1 : R) + 1 = 0 := by
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    rw [Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_zero, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.zero_apply, ← two_nsmul]
    exact hx2 x
  have h2R : (2 : R) = 0 := calc (2 : R) = 1 + 1 := one_add_one_eq_two.symm
    _ = 0 := h11
  refine ⟨R, inferInstance, inferInstance, CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2R,
    v, μ, ?_, ⟨fun b hb b' hb' => ?_, fun b hb b' hb' hbb' => ?_, fun c => ?_, hdA,
      fun b hb => ?_⟩, fun w hw => ?_⟩
  · rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_congr Additive.ofMul.symm]
  · rw [hv _ (mul_mem hb hb'), hv b hb, hv b' hb', ← he_add]
    rfl
  · rw [hv b hb, hv b' hb'] at hbb'
    have h1 := congrArg (fun x : Additive A₁ => ((Additive.toMul x : A₁) : G)) (e.symm.injective hbb')
    simpa using h1
  · refine ⟨((Additive.toMul (e c) : A₁) : G), (Additive.toMul (e c)).2, ?_⟩
    rw [hv _ (Additive.toMul (e c)).2]
    have : (Additive.ofMul (⟨((Additive.toMul (e c) : A₁) : G), (Additive.toMul (e c)).2⟩ : A₁))
        = e c := rfl
    rw [this, Equiv.symm_apply_apply]
  · rw [hv _ (hdA b hb), hv b hb, ← he_mul]
    rfl
  · have hw0 : (w : Module.End (ZMod 2) (Additive A₁)) ≠ 0 := fun h0 => hw (Subtype.ext h0)
    obtain ⟨j, hj⟩ := hpow w w.2 hw0
    refine ⟨j, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow]
    exact hj

end U3C1

end CFSG.SeitzReduction.RankOne
