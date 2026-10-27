module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl

namespace FormCore

section Scalar

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]

theorem scalar_of_nilpotent_sub (R : Module.End F V) (l : F) (e : ℕ)
    (hN : (R - algebraMap F (Module.End F V) l) ^ (2 ^ e) = 0) (m : ℕ) (hm : Odd m)
    (hRm : R ^ m = 1) : ∃ c : F, R = algebraMap F (Module.End F V) c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hinj : Function.Injective (algebraMap F (Module.End F V)) := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := congrArg (fun f : Module.End F V => f v) hab
    simp only [Module.algebraMap_end_apply] at this
    exact smul_left_injective F hv this
  haveI : CharP (Module.End F V) 2 := charP_of_injective_algebraMap hinj 2
  have hcomm : Commute (algebraMap F (Module.End F V) l)
      (R - algebraMap F (Module.End F V) l) := Algebra.commutes l _
  have hpow : R ^ 2 ^ e = algebraMap F (Module.End F V) (l ^ 2 ^ e) := by
    have h := add_pow_char_pow_of_commute 2 e hcomm
    rw [add_sub_cancel, hN, add_zero, ← map_pow] at h
    exact h
  have hcop : Nat.Coprime (2 ^ e) (orderOf R) := by
    refine Nat.Coprime.pow_left e ?_
    have hdvd : orderOf R ∣ m := orderOf_dvd_of_pow_eq_one hRm
    refine Nat.Coprime.coprime_dvd_right hdvd ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm.not_two_dvd_nat
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [hpow, ← map_pow] at hk
  exact ⟨(l ^ 2 ^ e) ^ k, hk.symm⟩

end Scalar

section Ctx

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

structure Ctx (Φ : ReflForm F V) (r : Equiv.Perm V) (σ : F ≃+* F) : Prop where
  add : ∀ u v, r (u + v) = r u + r v
  smul : ∀ (c : F) (v : V), r (c • v) = σ c • r v
  iso : ∀ u v, Φ.β (r u) (r v) = σ (Φ.β u v)

variable {Φ : ReflForm F V} {r : Equiv.Perm V} {σ : F ≃+* F}

theorem Ctx.map_sub (h : Ctx Φ r σ) (u v : V) : r (u - v) = r u - r v := by
  have := h.add (u - v) v
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem exists_ctx (Φ : ReflForm F V) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (hΦ : SemiIso Φ r) (hne : ∃ u v, Φ.β u v ≠ 0) : ∃ σ : F ≃+* F, Ctx Φ r σ := by
  obtain ⟨hadd, σ, hσ⟩ := hr
  obtain ⟨τ, hτ⟩ := hΦ
  obtain ⟨u, v, huv⟩ := hne
  have hτ0 : τ (Φ.β u v) ≠ 0 := fun h => huv ((map_eq_zero_iff τ τ.injective).1 h)
  have hτσ : ∀ c, τ c = σ c := by
    intro c
    have h1 : Φ.β (r u) (r (c • v)) = τ c * τ (Φ.β u v) := by
      rw [hτ, Φ.smul_right, map_mul]
    have h2 : Φ.β (r u) (r (c • v)) = σ c * τ (Φ.β u v) := by
      rw [hσ, Φ.smul_right, hτ]
    exact mul_right_cancel₀ hτ0 (h1.symm.trans h2)
  exact ⟨σ, ⟨hadd, hσ, fun a b => by rw [hτ, hτσ]⟩⟩

theorem Ctx.star (h : Ctx Φ r σ) {x v₀ y : V} {l c : F} (hxl : r x = l • x) (hv₀ : Φ.β x v₀ = 1)
    (hE : ∀ v, r (v + Φ.β x v • (y + c • x) - Φ.β y v • x) =
      r v + Φ.β x (r v) • (y + c • x) - Φ.β y (r v) • x) :
    ∃ b : F, r y = Φ.β x (r v₀) • y + b • x := by
  have h1 := hE v₀
  rw [hv₀, one_smul, h.map_sub, h.add, h.add, h.smul, h.smul, hxl, smul_smul, smul_smul] at h1
  refine ⟨Φ.β x (r v₀) * c - Φ.β y (r v₀) - σ c * l + σ (Φ.β y v₀) * l, ?_⟩
  linear_combination (norm := module) h1

theorem Ctx.value (h : Ctx Φ r σ) {x v₀ : V} {l : F} (hxl : r x = l • x) (hv₀ : Φ.β x v₀ = 1) :
    Φ.σ l * Φ.β x (r v₀) = 1 := by
  have := h.iso x v₀
  rw [hxl, Φ.smul_left, hv₀, map_one] at this
  exact this

theorem eq_zero_of_smul_eq_smul {x y : V} (hy : y ∉ Submodule.span F {x}) {p q : F}
    (h : p • y = q • x) : p = 0 := by
  by_contra hp
  apply hy
  have : y = (p⁻¹ * q) • x := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

theorem Ctx.sigma_id (h : Ctx Φ r σ) {x y : V} {a : F} (ha : a ≠ 0)
    (hy : y ∉ Submodule.span F {x}) (h1 : ∃ b : F, r y = a • y + b • x)
    (h2 : ∀ s : F, ∃ b : F, r (s • y) = a • (s • y) + b • x) (s : F) : σ s = s := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨b', hb'⟩ := h2 s
  rw [h.smul, hb] at hb'
  have hmain : (σ s * a - a * s) • y = (b' - σ s * b) • x := by
    linear_combination (norm := module) hb'
  have h0 := eq_zero_of_smul_eq_smul hy hmain
  have : σ s * a = s * a := by rw [mul_comm s a]; exact sub_eq_zero.1 h0
  exact mul_right_cancel₀ ha this

theorem Ctx.const (h : Ctx Φ r σ) (hσ : ∀ s, σ s = s) {W : Submodule F V} {x₀ : V} (hx₀ : x₀ ∈ W)
    (hx₀0 : x₀ ≠ 0) {l : F} (hxl : r x₀ = l • x₀)
    (hline : ∀ x ∈ W, x ≠ 0 → ∃ c : F, r x = c • x) : ∀ w ∈ W, r w = l • w := by
  intro w hw
  by_cases hws : w ∈ Submodule.span F {x₀}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hws
    rw [h.smul, hσ, hxl, smul_smul, smul_smul, mul_comm]
  · have hw0 : w ≠ 0 := fun h0 => hws (h0 ▸ Submodule.zero_mem _)
    have hwx : w + x₀ ≠ 0 := by
      intro h0
      apply hws
      have : w = (-1 : F) • x₀ := by
        rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_left h0
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₀)
    obtain ⟨c₁, hc₁⟩ := hline w hw hw0
    obtain ⟨c₂, hc₂⟩ := hline (w + x₀) (add_mem hw hx₀) hwx
    rw [h.add, hc₁, hxl, smul_add] at hc₂
    have hmain : (c₁ - c₂) • w = (c₂ - l) • x₀ := by
      linear_combination (norm := module) hc₂
    have h0 := eq_zero_of_smul_eq_smul hws hmain
    have hc12 : c₁ = c₂ := sub_eq_zero.1 h0
    rw [hc12] at hmain
    rw [hc₁, hc12]
    have : (c₂ - l) • x₀ = 0 := by rw [← hmain, sub_self, zero_smul]
    rcases smul_eq_zero.1 this with h3 | h3
    · rw [sub_eq_zero.1 h3]
    · exact absurd h3 hx₀0

theorem Ctx.a_eq_l [FiniteDimensional F V] (h : Ctx Φ r σ) (hσ : ∀ s, σ s = s)
    (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c) (hdim : 4 ≤ Module.finrank F V) {W : Submodule F V}
    (hWi : Φ.IsTotallyIsotropic W) {x₀ v₀ : V} (hx₀ : x₀ ∈ W) (hx₀0 : x₀ ≠ 0) {l : F}
    (hxl : r x₀ = l • x₀) (hv₀ : Φ.β x₀ v₀ = 1) (hlW : ∀ w ∈ W, r w = l • w)
    (hstar : ∀ y ∈ Φ.perp W, ∃ b : F, r y = Φ.β x₀ (r v₀) • y + b • x₀) :
    Φ.β x₀ (r v₀) = l := by
  set a := Φ.β x₀ (r v₀) with ha
  have hval : Φ.σ l * a = 1 := h.value hxl hv₀
  by_cases hW2 : ∃ y ∈ W, y ∉ Submodule.span F {x₀}
  · obtain ⟨y, hyW, hy⟩ := hW2
    obtain ⟨b, hb⟩ := hstar y (hWi hyW)
    have e : l • y = a • y + b • x₀ := (hlW y hyW).symm.trans hb
    have hmain : (l - a) • y = b • x₀ := by linear_combination (norm := module) e
    have h0 := eq_zero_of_smul_eq_smul hy hmain
    exact (sub_eq_zero.1 h0).symm
  · push Not at hW2
    have hWle : W ≤ Submodule.span F {x₀} := hW2
    have hrankW : Module.finrank F W ≤ 1 := by
      calc Module.finrank F W ≤ Module.finrank F (Submodule.span F {x₀}) :=
            Submodule.finrank_mono hWle
        _ = 1 := finrank_span_singleton hx₀0
    have hperp := Φ.finrank_perp W
    have hnti : ¬ Φ.perp W ≤ Φ.perp (Φ.perp W) := by
      intro hti
      rw [Φ.perp_perp] at hti
      have := Submodule.finrank_mono hti
      omega
    obtain ⟨y, hyP, hyN⟩ := SetLike.not_le_iff_exists.1 hnti
    have : ∃ y' ∈ Φ.perp W, Φ.β y' y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hyN (Φ.mem_perp.2 hcon)
    obtain ⟨y', hy'P, hy'y⟩ := this
    obtain ⟨b₁, hb₁⟩ := hstar y hyP
    obtain ⟨b₂, hb₂⟩ := hstar y' hy'P
    have hiso := h.iso y' y
    rw [hb₂, hb₁, hσ] at hiso
    have hx₀y' : Φ.β y' x₀ = 0 := Φ.refl _ _ (Φ.mem_perp.1 hy'P x₀ hx₀)
    have hx₀y : Φ.β x₀ y = 0 := Φ.mem_perp.1 hyP x₀ hx₀
    have hx₀x₀ : Φ.β x₀ x₀ = 0 := Φ.mem_perp.1 (hWi hx₀) x₀ hx₀
    rw [Φ.add_left, Φ.add_right, Φ.add_right, Φ.smul_left, Φ.smul_left, Φ.smul_left, Φ.smul_left,
      Φ.smul_right, Φ.smul_right, Φ.smul_right, Φ.smul_right, hx₀y', hx₀y, hx₀x₀] at hiso
    have hσa : Φ.σ a * a = 1 := by
      have : (Φ.σ a * a) * Φ.β y' y = 1 * Φ.β y' y := by
        rw [one_mul]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hiso
      exact mul_right_cancel₀ hy'y this
    have hσa0 : Φ.σ a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hσa; exact zero_ne_one hσa
    have h2 : l * Φ.σ a = 1 := by
      have := congrArg Φ.σ hval
      rwa [map_mul, hσΦ, map_one] at this
    have : l * Φ.σ a = a * Φ.σ a := by rw [h2, mul_comm, hσa]
    exact (mul_right_cancel₀ hσa0 this).symm

end Ctx

section Main

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem rigid_form_core (Φ : ReflForm F V) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hdim : 4 ≤ Module.finrank F V) (W : Submodule F V) (hW0 : W ≠ ⊥)
    (hWi : Φ.IsTotallyIsotropic W) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (hΦ : SemiIso Φ r) (m : ℕ) (hm : Odd m) (hrm : r ^ m = 1)
    (hline : ∀ x ∈ W, x ≠ 0 → ∃ c : F, r x = c • x)
    (hE : ∀ x ∈ W, x ≠ 0 → ∀ y ∈ Φ.perp W, ∃ c : F, ∀ v,
      r (v + Φ.β x v • (y + c • x) - Φ.β y v • x) =
        r v + Φ.β x (r v) • (y + c • x) - Φ.β y (r v) • x) :
    ∃ c : F, ∀ v, r v = c • v := by
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨v₁, hv₁⟩ : ∃ v, Φ.β x₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀0 (Φ.nondeg x₀ hcon)
  set v₀ : V := (Φ.β x₀ v₁)⁻¹ • v₁ with hv₀def
  have hv₀ : Φ.β x₀ v₀ = 1 := by rw [hv₀def, Φ.smul_right, inv_mul_cancel₀ hv₁]
  obtain ⟨σ, hC⟩ := exists_ctx Φ r hr hΦ ⟨x₀, v₁, hv₁⟩
  obtain ⟨l, hxl⟩ := hline x₀ hx₀ hx₀0
  have hperp := Φ.finrank_perp W
  have hWperp : W ≤ Φ.perp W := hWi
  have hfr : 2 ≤ Module.finrank F (Φ.perp W) := by
    have := Submodule.finrank_mono hWperp
    omega
  have hnle : ¬ Φ.perp W ≤ Submodule.span F {x₀} := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hx₀0] at this
    omega
  obtain ⟨y₁, hy₁P, hy₁⟩ := SetLike.not_le_iff_exists.1 hnle
  have hstar : ∀ y ∈ Φ.perp W, ∃ b : F, r y = Φ.β x₀ (r v₀) • y + b • x₀ := by
    intro y hy
    obtain ⟨c, hc⟩ := hE x₀ hx₀ hx₀0 y hy
    exact hC.star hxl hv₀ hc
  have hval := hC.value hxl hv₀
  have ha0 : Φ.β x₀ (r v₀) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hval
    exact zero_ne_one hval
  have hσ : ∀ s, σ s = s := fun s => hC.sigma_id ha0 hy₁ (hstar y₁ hy₁P)
    (fun s' => hstar (s' • y₁) (Submodule.smul_mem _ _ hy₁P)) s
  have hlW := hC.const hσ hx₀ hx₀0 hxl hline
  have hal := hC.a_eq_l hσ hσΦ hdim hWi hx₀ hx₀0 hxl hv₀ hlW hstar
  have hll : Φ.σ l * l = 1 := by
    have := hval
    rwa [hal] at this
  have h7 : ∀ v, r v - l • v ∈ Φ.perp W := by
    intro v
    rw [Φ.mem_perp]
    intro w hw
    have h1 := hC.iso w v
    rw [hlW w hw, Φ.smul_left, hσ] at h1
    rw [Φ.β_sub_right, Φ.smul_right]
    have : Φ.β w (r v) = l * Φ.β w v := by
      have hll' : l * Φ.σ l = 1 := by rw [mul_comm]; exact hll
      calc Φ.β w (r v) = (l * Φ.σ l) * Φ.β w (r v) := by rw [hll', one_mul]
        _ = l * (Φ.σ l * Φ.β w (r v)) := by ring
        _ = l * Φ.β w v := by rw [h1]
    rw [this, sub_self]
  have h8 : ∀ y ∈ Φ.perp W, r y - l • y ∈ W := by
    intro y hy
    obtain ⟨b, hb⟩ := hstar y hy
    rw [hal] at hb
    rw [hb, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hx₀
  let R : Module.End F V :=
    { toFun := r
      map_add' := hC.add
      map_smul' := fun c v => by rw [hC.smul, hσ]; rfl }
  have hRapp : ∀ v, R v = r v := fun v => rfl
  have hN : ∀ v, (R - algebraMap F (Module.End F V) l) v = r v - l • v := fun v => by
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hRapp]
  have hN3 : ∀ v, (R - algebraMap F (Module.End F V) l)
      ((R - algebraMap F (Module.End F V) l) ((R - algebraMap F (Module.End F V) l) v)) = 0 := by
    intro v
    rw [hN, hN, hN]
    have h1 := h8 _ (h7 v)
    rw [hlW _ h1, sub_self]
  have hN4 : (R - algebraMap F (Module.End F V) l) ^ (2 ^ 2) = 0 := by
    ext v
    have : ((R - algebraMap F (Module.End F V) l) ^ (2 ^ 2)) v =
        (R - algebraMap F (Module.End F V) l)
          ((R - algebraMap F (Module.End F V) l) ((R - algebraMap F (Module.End F V) l)
            ((R - algebraMap F (Module.End F V) l) v))) := by
      simp [pow_succ, Module.End.mul_apply]
    rw [this, hN3]
    simp
  have hRpow : ∀ k v, (R ^ k) v = (r ^ k) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', Module.End.mul_apply, Equiv.Perm.mul_apply, ih]; rfl
  have hRm : R ^ m = 1 := by
    ext v
    rw [hRpow, hrm]
    simp
  obtain ⟨c, hc⟩ := scalar_of_nilpotent_sub R l 2 hN4 m hm hRm
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun f : Module.End F V => f v) hc
  simpa [hRapp] using this

end Main

section Lines

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Φ : ReflForm F V}
  {r : Equiv.Perm V} {σ : F ≃+* F}

theorem Ctx.line_of_transvection (h : Ctx Φ r σ) {x v₀ : V} (hv₀ : Φ.β x v₀ = 1)
    (hT : ∀ v, r (v + Φ.β x v • x) = r v + Φ.β x (r v) • x) : ∃ c : F, r x = c • x := by
  have h1 := hT v₀
  rw [hv₀, one_smul, h.add] at h1
  exact ⟨Φ.β x (r v₀), add_left_cancel h1⟩

theorem exists_perp_one (Φ : ReflForm F V) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c) {x y : V} (hx0 : x ≠ 0)
    (hy : y ∉ Submodule.span F {x}) : ∃ v', Φ.β x v' = 0 ∧ Φ.β y v' = 1 := by
  obtain ⟨va, hva⟩ : ∃ v, Φ.β x v = 1 := by
    obtain ⟨v₁, hv₁⟩ : ∃ v, Φ.β x v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (Φ.nondeg x hcon)
    exact ⟨(Φ.β x v₁)⁻¹ • v₁, by rw [Φ.smul_right, inv_mul_cancel₀ hv₁]⟩
  by_contra hcon
  push Not at hcon
  have hzero : ∀ v', Φ.β x v' = 0 → Φ.β y v' = 0 := by
    intro v' hv'
    by_contra hne
    exact hcon ((Φ.β y v')⁻¹ • v') (by rw [Φ.smul_right, hv', mul_zero])
      (by rw [Φ.smul_right, inv_mul_cancel₀ hne])
  have hall : ∀ v, Φ.β y v = Φ.β x v * Φ.β y va := by
    intro v
    have h1 : Φ.β x (v - Φ.β x v • va) = 0 := by
      rw [Φ.β_sub_right, Φ.smul_right, hva, mul_one, sub_self]
    have h2 := hzero _ h1
    rw [Φ.β_sub_right, Φ.smul_right, sub_eq_zero] at h2
    exact h2
  apply hy
  have : y = Φ.σ (Φ.β y va) • x := by
    refine sub_eq_zero.1 (Φ.nondeg _ fun v => ?_)
    rw [Φ.β_sub_left, Φ.smul_left, hσΦ, hall v, mul_comm (Φ.β x v), sub_self]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

theorem Ctx.line_mem (h : Ctx Φ r σ) {x y : V} {c : F} {v' : V} (hv'x : Φ.β x v' = 0)
    (hv'y : Φ.β y v' = 1)
    (hE : ∀ v, r (v + Φ.β x v • (y + c • x) - Φ.β y v • x) =
      r v + Φ.β x (r v) • (y + c • x) - Φ.β y (r v) • x) :
    ∃ α γ : F, r x = α • y + γ • x := by
  have h1 := hE v'
  rw [hv'x, hv'y, zero_smul, add_zero, one_smul, h.map_sub] at h1
  exact ⟨-Φ.β x (r v'), Φ.β y (r v') - Φ.β x (r v') * c, by
    linear_combination (norm := module) (-1 : F) • h1⟩

theorem Ctx.line_of_eichler (h : Ctx Φ r σ) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c) {x y₁ y₂ : V}
    (hx0 : x ≠ 0) (hy₁ : y₁ ∉ Submodule.span F {x})
    (hy₂ : y₂ ∉ Submodule.span F ({x, y₁} : Set V))
    (hE₁ : ∃ c : F, ∀ v, r (v + Φ.β x v • (y₁ + c • x) - Φ.β y₁ v • x) =
      r v + Φ.β x (r v) • (y₁ + c • x) - Φ.β y₁ (r v) • x)
    (hE₂ : ∃ c : F, ∀ v, r (v + Φ.β x v • (y₂ + c • x) - Φ.β y₂ v • x) =
      r v + Φ.β x (r v) • (y₂ + c • x) - Φ.β y₂ (r v) • x) : ∃ c : F, r x = c • x := by
  have hy₂' : y₂ ∉ Submodule.span F {x} := fun hmem =>
    hy₂ (Submodule.span_mono (by simp) hmem)
  obtain ⟨c₁, hc₁⟩ := hE₁
  obtain ⟨c₂, hc₂⟩ := hE₂
  obtain ⟨v₁, hv₁x, hv₁y⟩ := exists_perp_one Φ hσΦ hx0 hy₁
  obtain ⟨v₂, hv₂x, hv₂y⟩ := exists_perp_one Φ hσΦ hx0 hy₂'
  obtain ⟨α₁, γ₁, e₁⟩ := h.line_mem hv₁x hv₁y hc₁
  obtain ⟨α₂, γ₂, e₂⟩ := h.line_mem hv₂x hv₂y hc₂
  by_cases hα : α₂ = 0
  · exact ⟨γ₂, by rw [e₂, hα, zero_smul, zero_add]⟩
  · exfalso
    apply hy₂
    have : y₂ = α₂⁻¹ • (α₁ • y₁ + (γ₁ - γ₂) • x) := by
      have h3 : α₂ • y₂ = α₁ • y₁ + (γ₁ - γ₂) • x := by
        linear_combination (norm := module) e₁.symm.trans e₂ |>.symm
      rw [← h3, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_))
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

end Lines

end FormCore

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
