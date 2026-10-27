module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Smith1980Orth

@[expose] def cubePerm {α : Type*} (f : α → α) (hf : ∀ x, f (f (f x)) = x) : Equiv.Perm α where
  toFun := f
  invFun x := f (f x)
  left_inv x := hf x
  right_inv x := hf x

theorem cubePerm_pow_three {α : Type*} (f : α → α) (hf : ∀ x, f (f (f x)) = x) :
    cubePerm f hf ^ 3 = 1 := by
  ext x
  rw [Equiv.Perm.coe_pow]
  exact hf x

theorem exists_fixed_of_pow_three {α : Type*} [Finite α] (σ : Equiv.Perm α) (hσ : σ ^ 3 = 1)
    (h3 : ¬ 3 ∣ Nat.card α) : ∃ a, σ a = a := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card] at h3
  have hσ' : σ ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hσ
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) h3 hσ'

theorem conj_cube_eq {G : Type*} [Group G] {θ : G} (hθ : θ ^ 3 = 1) (z : G) :
    θ * (θ * (θ * z * θ⁻¹) * θ⁻¹) * θ⁻¹ = z := by
  have h3 : θ * θ * θ = 1 := (pow_three' θ).symm.trans hθ
  calc θ * (θ * (θ * z * θ⁻¹) * θ⁻¹) * θ⁻¹ = (θ * θ * θ) * z * (θ * θ * θ)⁻¹ := by group
    _ = z := by rw [h3]; simp

theorem exists_fixed_mem_coset {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (hH : IsPGroup 2 H) {θ : G} (hθ : θ ^ 3 = 1) (hθH : ∀ h ∈ H, θ * h * θ⁻¹ ∈ H) {g : G}
    (hg : g⁻¹ * (θ * g * θ⁻¹) ∈ H) : ∃ h ∈ H, θ * (g * h) * θ⁻¹ = g * h := by
  let f : H → H := fun h => ⟨g⁻¹ * (θ * (g * (h : G)) * θ⁻¹), by
    have e : g⁻¹ * (θ * (g * (h : G)) * θ⁻¹) = (g⁻¹ * (θ * g * θ⁻¹)) * (θ * (h : G) * θ⁻¹) := by
      group
    rw [e]
    exact H.mul_mem hg (hθH h h.2)⟩
  have hA : ∀ k : H, g * ((f k : H) : G) = θ * (g * (k : G)) * θ⁻¹ := fun k => by
    show g * (g⁻¹ * (θ * (g * (k : G)) * θ⁻¹)) = θ * (g * (k : G)) * θ⁻¹
    group
  have hf : ∀ k : H, f (f (f k)) = k := by
    intro k
    apply Subtype.ext
    have e1 : g * ((f (f k) : H) : G) = θ * (g * ((f k : H) : G)) * θ⁻¹ := hA (f k)
    have e2 : g * ((f k : H) : G) = θ * (g * (k : G)) * θ⁻¹ := hA k
    show g⁻¹ * (θ * (g * ((f (f k) : H) : G)) * θ⁻¹) = (k : G)
    rw [e1, e2, conj_cube_eq hθ (g * (k : G))]
    group
  have h3 : ¬ 3 ∣ Nat.card H := by
    obtain ⟨n, hn⟩ := hH.exists_card_dvd_pow
    intro h
    have h2 : 3 ∣ 2 ^ n := h.trans hn
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  obtain ⟨a, ha⟩ := exists_fixed_of_pow_three (cubePerm f hf) (cubePerm_pow_three f hf) h3
  have hfa : g⁻¹ * (θ * (g * (a : G)) * θ⁻¹) = (a : G) := congrArg Subtype.val ha
  refine ⟨a, a.2, ?_⟩
  calc θ * (g * (a : G)) * θ⁻¹ = g * (g⁻¹ * (θ * (g * (a : G)) * θ⁻¹)) := by group
    _ = g * (a : G) := by rw [hfa]

theorem exists_unique_fixed_of_orbit {G : Type*} [Group G] {Q : Subgroup G} [Finite Q]
    (hQ : IsPGroup 2 Q) {θ x y : G} (hθ : θ ^ 3 = 1) (hθQ : ∀ q ∈ Q, θ * q * θ⁻¹ ∈ Q)
    (hθy : ∃ q ∈ Q, θ * y * θ⁻¹ = q * y * q⁻¹)
    (hC : ∀ q ∈ Q, θ * q * θ⁻¹ = q → ∀ q' ∈ Q, θ * (q' * y * q'⁻¹) * θ⁻¹ = q' * y * q'⁻¹ →
      q * (q' * y * q'⁻¹) * q⁻¹ = q' * y * q'⁻¹)
    (hxθ : x * θ * x⁻¹ = θ⁻¹) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hxy : ∃ q ∈ Q, x * y * x⁻¹ = q * y * q⁻¹) :
    ∃ q ∈ Q, θ * (q * y * q⁻¹) * θ⁻¹ = q * y * q⁻¹ ∧ x * (q * y * q⁻¹) * x⁻¹ = q * y * q⁻¹ := by
  obtain ⟨qθ, hqθ, hθy'⟩ := hθy
  obtain ⟨qx, hqx, hxy'⟩ := hxy
  letI : MulAction Q G :=
    { smul := fun q z => (q : G) * z * (q : G)⁻¹
      one_smul := fun z => by
        show ((1 : Q) : G) * z * ((1 : Q) : G)⁻¹ = z
        simp
      mul_smul := fun a b z => by
        show ((a * b : Q) : G) * z * ((a * b : Q) : G)⁻¹
          = (a : G) * ((b : G) * z * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have memS : ∀ s : G, s ∈ MulAction.orbit Q y ↔ ∃ q ∈ Q, s = q * y * q⁻¹ := by
    intro s
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q : G), q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  haveI hSfin : Finite (MulAction.orbit Q y) :=
    (Set.finite_range fun q : Q => q • y).to_subtype
  have h3S : ¬ 3 ∣ Nat.card (MulAction.orbit Q y) := by
    obtain ⟨n, hn⟩ := hQ.card_orbit y
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hθS : ∀ s ∈ MulAction.orbit Q y, θ * s * θ⁻¹ ∈ MulAction.orbit Q y := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := (memS s).1 hs
    rw [memS]
    refine ⟨θ * q * θ⁻¹ * qθ, Q.mul_mem (hθQ q hq) hqθ, ?_⟩
    calc θ * (q * y * q⁻¹) * θ⁻¹ = (θ * q * θ⁻¹) * (θ * y * θ⁻¹) * (θ * q * θ⁻¹)⁻¹ := by group
      _ = (θ * q * θ⁻¹ * qθ) * y * (θ * q * θ⁻¹ * qθ)⁻¹ := by rw [hθy']; group
  let f : MulAction.orbit Q y → MulAction.orbit Q y :=
    fun s => ⟨θ * (s : G) * θ⁻¹, hθS _ s.2⟩
  have hf3 : ∀ s : MulAction.orbit Q y, f (f (f s)) = s := by
    intro s
    apply Subtype.ext
    exact conj_cube_eq hθ (s : G)
  obtain ⟨v₀, hv₀⟩ := exists_fixed_of_pow_three (cubePerm f hf3) (cubePerm_pow_three f hf3) h3S
  have hθv₀ : θ * (v₀ : G) * θ⁻¹ = (v₀ : G) := congrArg Subtype.val hv₀
  obtain ⟨v, hvS, hθv⟩ : ∃ v ∈ MulAction.orbit Q y, θ * v * θ⁻¹ = v := ⟨v₀, v₀.2, hθv₀⟩
  obtain ⟨q₀, hq₀, hv⟩ := (memS v).1 hvS
  have hθv' : θ⁻¹ * v * θ = v := by
    calc θ⁻¹ * v * θ = θ⁻¹ * (θ * v * θ⁻¹) * θ := by rw [hθv]
      _ = v := by group
  have hθv₁ : θ * (q₀ * y * q₀⁻¹) * θ⁻¹ = q₀ * y * q₀⁻¹ := by
    rw [← hv]
    exact hθv
  have uniq : ∀ q ∈ Q, θ * (q * v * q⁻¹) * θ⁻¹ = q * v * q⁻¹ → q * v * q⁻¹ = v := by
    intro q hq hfix
    let C : Subgroup G :=
      { carrier := {c | c ∈ Q ∧ c * v * c⁻¹ = v}
        mul_mem' := fun {a b} ha hb => by
          refine ⟨Q.mul_mem ha.1 hb.1, ?_⟩
          calc a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group
            _ = v := by rw [hb.2, ha.2]
        one_mem' := by
          refine ⟨Q.one_mem, ?_⟩
          simp
        inv_mem' := fun {a} ha => by
          refine ⟨Q.inv_mem ha.1, ?_⟩
          have hav : a * v = v * a := by
            calc a * v = a * v * a⁻¹ * a := by group
              _ = v * a := by rw [ha.2]
          calc a⁻¹ * v * a⁻¹⁻¹ = a⁻¹ * (v * a) := by group
            _ = a⁻¹ * (a * v) := by rw [hav]
            _ = v := by group }
    have hθC : ∀ c ∈ C, θ * c * θ⁻¹ ∈ C := by
      intro c hc
      refine ⟨hθQ c hc.1, ?_⟩
      calc θ * c * θ⁻¹ * v * (θ * c * θ⁻¹)⁻¹ = θ * (c * (θ⁻¹ * v * θ) * c⁻¹) * θ⁻¹ := by group
        _ = θ * (c * v * c⁻¹) * θ⁻¹ := by rw [hθv']
        _ = θ * v * θ⁻¹ := by rw [hc.2]
        _ = v := hθv
    have hu : q⁻¹ * (θ * q * θ⁻¹) ∈ C := by
      refine ⟨Q.mul_mem (Q.inv_mem hq) (hθQ q hq), ?_⟩
      calc q⁻¹ * (θ * q * θ⁻¹) * v * (q⁻¹ * (θ * q * θ⁻¹))⁻¹
          = q⁻¹ * (θ * q * (θ⁻¹ * v * θ) * q⁻¹ * θ⁻¹) * q := by group
        _ = q⁻¹ * (θ * (q * v * q⁻¹) * θ⁻¹) * q := by rw [hθv']; group
        _ = q⁻¹ * (q * v * q⁻¹) * q := by rw [hfix]
        _ = v := by group
    haveI hCfin : Finite C := by
      refine Finite.of_injective (fun c : C => (⟨c.1, c.2.1⟩ : Q)) ?_
      intro a b hab
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      exact h
    have hC2 : IsPGroup 2 C := by
      intro c
      obtain ⟨k, hk⟩ := hQ ⟨c.1, c.2.1⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨c, hcC, hcfix⟩ := exists_fixed_mem_coset hC2 hθ hθC (g := q) hu
    have hq'Q : q * c ∈ Q := Q.mul_mem hq hcC.1
    have hfinal := hC (q * c) hq'Q hcfix q₀ hq₀ hθv₁
    rw [← hv] at hfinal
    calc q * v * q⁻¹ = q * (c * v * c⁻¹) * q⁻¹ := by rw [hcC.2]
      _ = q * c * v * (q * c)⁻¹ := by group
      _ = v := hfinal
  have hθx : θ * x = x * θ⁻¹ := by
    have h1 : x * θ⁻¹ * x⁻¹ = θ := by
      calc x * θ⁻¹ * x⁻¹ = (x * θ * x⁻¹)⁻¹ := by group
        _ = θ := by rw [hxθ, inv_inv]
    calc θ * x = x * θ⁻¹ * x⁻¹ * x := by rw [h1]
      _ = x * θ⁻¹ := by group
  have hx1 : x⁻¹ * θ⁻¹ = θ * x⁻¹ := by
    calc x⁻¹ * θ⁻¹ = x⁻¹ * (x * θ * x⁻¹) := by rw [hxθ]
      _ = θ * x⁻¹ := by group
  have hxθv : θ * (x * v * x⁻¹) * θ⁻¹ = x * v * x⁻¹ := by
    calc θ * (x * v * x⁻¹) * θ⁻¹ = (θ * x) * v * (x⁻¹ * θ⁻¹) := by group
      _ = (x * θ⁻¹) * v * (θ * x⁻¹) := by rw [hθx, hx1]
      _ = x * (θ⁻¹ * v * θ) * x⁻¹ := by group
      _ = x * v * x⁻¹ := by rw [hθv']
  obtain ⟨qw, hqw, hxw⟩ : ∃ q ∈ Q, x * v * x⁻¹ = q * v * q⁻¹ := by
    refine ⟨x * q₀ * x⁻¹ * qx * q₀⁻¹, Q.mul_mem (Q.mul_mem (hxQ q₀ hq₀) hqx) (Q.inv_mem hq₀), ?_⟩
    rw [hv]
    calc x * (q₀ * y * q₀⁻¹) * x⁻¹
        = (x * q₀ * x⁻¹) * (x * y * x⁻¹) * (x * q₀ * x⁻¹)⁻¹ := by group
      _ = (x * q₀ * x⁻¹) * (qx * y * qx⁻¹) * (x * q₀ * x⁻¹)⁻¹ := by rw [hxy']
      _ = (x * q₀ * x⁻¹ * qx * q₀⁻¹) * (q₀ * y * q₀⁻¹) * (x * q₀ * x⁻¹ * qx * q₀⁻¹)⁻¹ := by
        group
  have hθw : θ * (qw * v * qw⁻¹) * θ⁻¹ = qw * v * qw⁻¹ := by
    rw [← hxw]
    exact hxθv
  have hxv : x * v * x⁻¹ = v := hxw.trans (uniq qw hqw hθw)
  exact ⟨q₀, hq₀, hθv₁, by rw [← hv]; exact hxv⟩

end CFSG.GF2Type.Smith1980Orth
