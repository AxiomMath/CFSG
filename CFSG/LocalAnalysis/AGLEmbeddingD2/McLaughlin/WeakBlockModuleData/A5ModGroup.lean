module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModLin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModClass

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix Equiv CFSG.QuasithinUnique

theorem exists_A5_action {Γ W : Type} [Group Γ] [AddCommGroup W] [DistribMulAction Γ W]
    (α₀ : Γ →* A5) (hs : Function.Surjective α₀) (hk : ∀ γ ∈ α₀.ker, ∀ w : W, γ • w = w) :
    ∃ _ : DistribMulAction A5 W, ∀ (γ : Γ) (w : W), α₀ γ • w = γ • w := by
  classical
  have hwd : ∀ (γ γ' : Γ), α₀ γ = α₀ γ' → ∀ w : W, γ • w = γ' • w := by
    intro γ γ' h w
    have hm : γ'⁻¹ * γ ∈ α₀.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have := hk _ hm w
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  choose lift hlift using hs
  have h1 : ∀ w : W, lift 1 • w = w := fun w => by
    have h1 : α₀ (lift 1) = α₀ 1 := by rw [hlift, map_one]
    rw [hwd _ _ h1, one_smul]
  have h2 : ∀ (g h : A5) (w : W), lift (g * h) • w = lift g • lift h • w := fun g h w => by
    have h1 : α₀ (lift (g * h)) = α₀ (lift g * lift h) := by rw [hlift, map_mul, hlift, hlift]
    rw [hwd _ _ h1, mul_smul]
  exact ⟨{ smul := fun g w => lift g • w
           one_smul := h1
           mul_smul := h2
           smul_zero := fun g => smul_zero _
           smul_add := fun g w w' => smul_add _ _ _ }, fun γ w => hwd _ _ (hlift _) w⟩

set_option maxHeartbeats 4000000 in
theorem plumbing {Γ U : Type} [Group Γ] [Group U] [Finite U] [MulDistribMulAction Γ U]
    (hcomm : ∀ a b : U, a * b = b * a) (hexp : ∀ u : U, u * u = 1)
    (Z : Subgroup U) (hZfix : ∀ (γ : Γ), ∀ z ∈ Z, γ • z ∈ Z)
    (α₀ : Γ →* A5) (hs : Function.Surjective α₀)
    (htriv : ∀ γ ∈ α₀.ker, ∀ u : U, γ • u * u⁻¹ ∈ Z)
    (hirr : ∀ K : Subgroup U, Z ≤ K → (∀ (γ : Γ), ∀ k ∈ K, γ • k ∈ K) → K = Z ∨ K = ⊤)
    (hZne : Z ≠ ⊤) (hact : ∃ (γ : Γ) (u : U), γ • u * u⁻¹ ∉ Z) :
    (∃ β : U →* Multiplicative ↥(evenWeight 5), Function.Surjective β ∧ β.ker = Z ∧
      ∀ (γ : Γ) (u : U) (i : Fin 5),
        ((Multiplicative.toAdd (β (γ • u)) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) i =
          ((Multiplicative.toAdd (β u) : ↥(evenWeight 5)) : Fin 5 → ZMod 2)
            (((α₀ γ : Perm (Fin 5))⁻¹) i)) ∨
    (∃ (α₂ : A5 →* SpecialLinearGroup (Fin 2) F4) (β : U →* Multiplicative (Fin 2 → F4)),
      Function.Injective α₂ ∧ Function.Surjective α₂ ∧ Function.Surjective β ∧ β.ker = Z ∧
      ∀ (γ : Γ) (u : U), Multiplicative.toAdd (β (γ • u)) =
        (α₂ (α₀ γ) : Matrix (Fin 2) (Fin 2) F4).mulVec (Multiplicative.toAdd (β u))) := by
  classical
  letI : CommGroup U := { ‹Group U› with mul_comm := hcomm }
  haveI : Z.Normal := Subgroup.normal_of_comm Z
  let φ : Γ → (U ⧸ Z) →* (U ⧸ Z) := fun γ =>
    QuotientGroup.map Z Z (MulDistribMulAction.toMonoidHom U γ) (fun z hz => hZfix γ z hz)
  have hφ : ∀ (γ : Γ) (u : U), φ γ (QuotientGroup.mk u) = QuotientGroup.mk (γ • u) :=
    fun γ u => rfl
  let mkW : U → Additive (U ⧸ Z) := fun u => Additive.ofMul (QuotientGroup.mk u)
  have hmkW_mul : ∀ a b : U, mkW (a * b) = mkW a + mkW b := fun a b => rfl
  have hmkW_one : mkW 1 = 0 := rfl
  have hmkW_inv : ∀ a : U, mkW a⁻¹ = -mkW a := fun a => rfl
  have hmkW_surj : Function.Surjective mkW := fun w => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    exact ⟨u, by simp only [mkW, hu]; rfl⟩
  have hmkW_zero : ∀ u : U, mkW u = 0 ↔ u ∈ Z := fun u => QuotientGroup.eq_one_iff u
  have hmkW_eq : ∀ u u' : U, mkW u = mkW u' ↔ u⁻¹ * u' ∈ Z := fun u u' => QuotientGroup.eq
  letI actΓ : DistribMulAction Γ (Additive (U ⧸ Z)) :=
    { smul := fun γ w => Additive.ofMul (φ γ (Additive.toMul w))
      one_smul := fun w => by
        obtain ⟨u, rfl⟩ := hmkW_surj w
        show mkW ((1 : Γ) • u) = mkW u
        rw [one_smul]
      mul_smul := fun γ γ' w => by
        obtain ⟨u, rfl⟩ := hmkW_surj w
        show mkW ((γ * γ') • u) = mkW (γ • γ' • u)
        rw [mul_smul]
      smul_zero := fun γ => map_one (φ γ)
      smul_add := fun γ w w' => map_mul (φ γ) _ _ }
  have hsm : ∀ (γ : Γ) (u : U), γ • mkW u = mkW (γ • u) := fun γ u => rfl
  have hk : ∀ γ ∈ α₀.ker, ∀ w : Additive (U ⧸ Z), γ • w = w := by
    intro γ hγ w
    obtain ⟨u, rfl⟩ := hmkW_surj w
    rw [hsm, hmkW_eq]
    have := Z.inv_mem (htriv γ hγ u)
    simpa [_root_.mul_inv_rev, hcomm] using this
  obtain ⟨instA, hinstA⟩ := exists_A5_action α₀ hs hk
  letI := instA
  have h2nsmul : ∀ w : Additive (U ⧸ Z), (2 : ℕ) • w = 0 := fun w => by
    obtain ⟨u, rfl⟩ := hmkW_surj w
    rw [two_nsmul, ← hmkW_mul, hexp, hmkW_one]
  letI : Module (ZMod 2) (Additive (U ⧸ Z)) := AddCommGroup.zmodModule h2nsmul
  have hsc : ∀ (g : A5) (c : ZMod 2) (w : Additive (U ⧸ Z)), g • c • w = c • g • w := by
    intro g c w
    have e1 : ∀ x : Additive (U ⧸ Z), c • x = c.val • x := fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) c.val x, ZMod.natCast_zmod_val]
    rw [e1, e1]
    exact ((DistribSMul.toAddMonoidHom (Additive (U ⧸ Z)) g).map_nsmul c.val w)
  haveI : SMulCommClass A5 (ZMod 2) (Additive (U ⧸ Z)) := ⟨hsc⟩
  have hsimple : IsSimpleMod (Additive (U ⧸ Z)) := by
    intro S hS
    let K : Subgroup U :=
      { carrier := {u | mkW u ∈ S}
        one_mem' := by show mkW 1 ∈ S; rw [hmkW_one]; exact S.zero_mem
        mul_mem' := fun {a b} ha hb => by
          show mkW (a * b) ∈ S
          rw [hmkW_mul]; exact S.add_mem ha hb
        inv_mem' := fun {a} ha => by
          show mkW a⁻¹ ∈ S
          rw [hmkW_inv]; exact S.neg_mem ha }
    have hZK : Z ≤ K := fun z hz => by
      show mkW z ∈ S
      rw [(hmkW_zero z).mpr hz]; exact S.zero_mem
    have hKinv : ∀ (γ : Γ), ∀ k ∈ K, γ • k ∈ K := fun γ k hk => by
      show mkW (γ • k) ∈ S
      rw [← hsm, ← hinstA γ]
      exact hS _ _ hk
    rcases hirr K hZK hKinv with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨u, rfl⟩ := hmkW_surj w
      have : u ∈ K := hw
      rw [h] at this
      exact (Submodule.mem_bot _).mpr ((hmkW_zero u).mpr this)
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨u, rfl⟩ := hmkW_surj w
      have : u ∈ K := by rw [h]; exact Subgroup.mem_top u
      exact this
  have hnt : Nontrivial (Additive (U ⧸ Z)) := by
    obtain ⟨u₀, hu₀⟩ : ∃ u, u ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hZne (eq_top_iff.mpr fun u _ => hcon u)
    exact ⟨⟨mkW u₀, 0, fun h => hu₀ ((hmkW_zero u₀).mp h)⟩⟩
  have hact' : ∃ (g : A5) (w : Additive (U ⧸ Z)), g • w ≠ w := by
    obtain ⟨γ, u, hγ⟩ := hact
    refine ⟨α₀ γ, mkW u, fun h => hγ ?_⟩
    rw [hinstA, hsm, hmkW_eq] at h
    have := Z.inv_mem h
    simpa [_root_.mul_inv_rev, hcomm] using this
  have hfin : Finite (Additive (U ⧸ Z)) := inferInstanceAs (Finite (U ⧸ Z))
  let mkβ : ∀ {X : Type} [AddCommGroup X], (Additive (U ⧸ Z) →+ X) → (U →* Multiplicative X) :=
    fun {X} _ f =>
      { toFun := fun u => Multiplicative.ofAdd (f (mkW u))
        map_one' := by simp [hmkW_one]
        map_mul' := fun a b => by simp [hmkW_mul] }
  have hβker : ∀ {X : Type} [AddCommGroup X] (f : Additive (U ⧸ Z) →+ X), Function.Injective f →
      (mkβ f).ker = Z := by
    intro X _ f hf
    ext u
    rw [MonoidHom.mem_ker, ← hmkW_zero]
    constructor
    · intro h
      apply hf
      rw [map_zero]
      exact h
    · intro h
      show Multiplicative.ofAdd (f (mkW u)) = 1
      rw [h, map_zero]
      rfl
  have hβsurj : ∀ {X : Type} [AddCommGroup X] (f : Additive (U ⧸ Z) →+ X), Function.Surjective f →
      Function.Surjective (mkβ f) := by
    intro X _ f hf x
    obtain ⟨w, hw⟩ := hf (Multiplicative.toAdd x)
    obtain ⟨u, rfl⟩ := hmkW_surj w
    exact ⟨u, by show Multiplicative.ofAdd (f (mkW u)) = x; rw [hw]; rfl⟩
  letI instEW : AddCommGroup ↥(evenWeight 5) := AddSubgroup.toAddCommGroup _
  rcases classify hsimple hact' with ⟨φ, hφ⟩ | ⟨ω, hωc, hωs, hωc16⟩
  · left
    refine ⟨mkβ (X := ↥(evenWeight 5)) φ.toAddMonoidHom, hβsurj (X := ↥(evenWeight 5)) _ φ.surjective,
      hβker (X := ↥(evenWeight 5)) _ φ.injective, ?_⟩
    intro γ u i
    show ((φ (mkW (γ • u)) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) i =
      ((φ (mkW u) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) (((α₀ γ : Perm (Fin 5))⁻¹) i)
    rw [← hsm, ← hinstA γ]
    exact hφ (α₀ γ) (mkW u) i
  · right
    obtain ⟨e, α₂, hα₂i, hα₂s, hα₂e⟩ := lin_case ω hωc hωs hωc16 hact'
    refine ⟨α₂, mkβ (X := Fin 2 → F4) e.toAddMonoidHom, hα₂i, hα₂s,
      hβsurj (X := Fin 2 → F4) _ e.surjective, hβker (X := Fin 2 → F4) _ e.injective, ?_⟩
    intro γ u
    show e (mkW (γ • u)) = (α₂ (α₀ γ) : Matrix (Fin 2) (Fin 2) F4).mulVec (e (mkW u))
    rw [← hsm, ← hinstA γ]
    exact hα₂e (α₀ γ) (mkW u)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
