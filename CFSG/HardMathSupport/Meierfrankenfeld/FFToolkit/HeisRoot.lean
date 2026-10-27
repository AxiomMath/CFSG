module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.LiftOrbitRel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

section Count

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def heisFun (lK : K →+ ZMod p) (lV : V →+ ZMod p)
    (β : V →ₗ[K] V →ₗ[K] K) (k : Kˣ) (A : V →+ V) (v : V) : K × V →+ ZMod p where
  toFun x := lK ((k : K) * x.1) + (lK (β (A x.2) v) + lV (A x.2))
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add, LinearMap.add_apply]
    ring

theorem heisFun_apply (lK : K →+ ZMod p) (lV : V →+ ZMod p) (β : V →ₗ[K] V →ₗ[K] K) (k : Kˣ)
    (A : V →+ V) (v : V) (x : K × V) :
    heisFun lK lV β k A v x = lK ((k : K) * x.1) + (lK (β (A x.2) v) + lV (A x.2)) := rfl

theorem heisFun_inl (lK : K →+ ZMod p) (lV : V →+ ZMod p) (β : V →ₗ[K] V →ₗ[K] K) (k : Kˣ)
    (A : V →+ V) (v : V) (c : K) : heisFun lK lV β k A v (c, 0) = lK ((k : K) * c) := by
  simp [heisFun_apply]

theorem heisFun_inr (lK : K →+ ZMod p) (lV : V →+ ZMod p) (β : V →ₗ[K] V →ₗ[K] K) (k : Kˣ)
    (A : V →+ V) (v : V) (u : V) :
    heisFun lK lV β k A v (0, u) = lK (β (A u) v) + lV (A u) := by
  simp [heisFun_apply]

theorem eq_zero_of_map_mul_eq_zero (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0) {ξ : K}
    (h : ∀ r, lK (ξ * r) = 0) : ξ = 0 := by
  by_contra hξ
  obtain ⟨b, hb⟩ := hlK
  apply hb
  have := h (ξ⁻¹ * b)
  rwa [mul_inv_cancel_left₀ hξ] at this

theorem eq_zero_of_map_bilin_eq_zero (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0) {x : V}
    (h : ∀ w, lK (β w x) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨u, hu⟩ := hβ x hx
  obtain ⟨b, hb⟩ := hlK
  apply hb
  have := h ((b / β u x) • u)
  rwa [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hu] at this

theorem heisFun_ne_zero (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0) (lV : V →+ ZMod p)
    (β : V →ₗ[K] V →ₗ[K] K) (k : Kˣ) (A : V →+ V) (v : V) : heisFun lK lV β k A v ≠ 0 := by
  intro h0
  obtain ⟨b, hb⟩ := hlK
  apply hb
  have := DFunLike.congr_fun h0 ((k : K)⁻¹ * b, 0)
  rw [heisFun_inl, AddMonoidHom.zero_apply, mul_inv_cancel_left₀ k.ne_zero] at this
  exact this

theorem heisFun_inj (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0) (lV : V →+ ZMod p)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0) (R : Subgroup Kˣ)
    (A : R → V →+ V) (hA : ∀ k, Function.Surjective (A k)) {x y : R × V}
    (h : ∀ w, heisFun lK lV β x.1 (A x.1) x.2 w = heisFun lK lV β y.1 (A y.1) y.2 w) :
    x = y := by
  obtain ⟨k, v⟩ := x
  obtain ⟨k', v'⟩ := y
  have hk : k = k' := by
    have h1 : ((k : Kˣ) : K) - ((k' : Kˣ) : K) = 0 := by
      refine eq_zero_of_map_mul_eq_zero lK hlK fun r => ?_
      have := h (r, 0)
      simp only [heisFun_inl] at this
      rw [sub_mul, map_sub, this]
      exact sub_self _
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h1))
  subst hk
  have hv : v = v' := by
    have h2 : v - v' = 0 := by
      refine eq_zero_of_map_bilin_eq_zero lK hlK β hβ fun w => ?_
      obtain ⟨u, rfl⟩ := hA k w
      have := h (0, u)
      simp only [heisFun_inr] at this
      have h3 : lK (β (A k u) v) = lK (β (A k u) v') := add_right_cancel this
      rw [map_sub, map_sub, h3]
      exact sub_self _
    exact sub_eq_zero.1 h2
  rw [hv]

variable [Fintype K] [Fintype V]

open scoped Classical

theorem card_fiber_heis_le (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0) (lV : V →+ ZMod p)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0) (R : Subgroup Kˣ)
    (A : R → V →+ V) (hA : ∀ k, Function.Surjective (A k)) (x₀ : R × V) :
    (Finset.univ.filter (fun x : R × V =>
      (heisFun lK lV β x.1 (A x.1) x.2).ker = (heisFun lK lV β x₀.1 (A x₀.1) x₀.2).ker)).card ≤
      p - 1 := by
  set F : R × V → (K × V →+ ZMod p) := fun x => heisFun lK lV β x.1 (A x.1) x.2 with hF
  have hF0 : ∀ x, F x ≠ 0 := fun x => heisFun_ne_zero lK hlK lV β _ _ _
  have hprop : ∀ x : R × V, (F x).ker = (F x₀).ker → ∃ k : ZMod p, ∀ y, F x y = k * F x₀ y := by
    intro x hx
    refine exists_smul_of_ker_eq_addHom (F x₀) (F x) (hF0 x₀) fun y => ?_
    have := SetLike.ext_iff.1 hx y
    simpa [AddMonoidHom.mem_ker] using this.symm
  choose! ε hε using hprop
  have hεne : ∀ x : R × V, (F x).ker = (F x₀).ker → ε x ≠ 0 := by
    intro x hx h0
    apply hF0 x
    ext y
    rw [hε x hx y, h0, zero_mul, AddMonoidHom.zero_apply]
  have hinj : Set.InjOn ε ↑(Finset.univ.filter (fun x : R × V => (F x).ker = (F x₀).ker)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    exact heisFun_inj lK hlK lV β hβ R A hA fun w => by
      show F x w = F y w
      rw [hε x hx' w, hε y hy' w, hxy]
  calc (Finset.univ.filter (fun x : R × V => (F x).ker = (F x₀).ker)).card
      ≤ ((Finset.univ : Finset (ZMod p)).erase 0).card :=
        Finset.card_le_card_of_injOn ε (fun x hx => Finset.mem_erase.2
          ⟨hεne x (Finset.mem_filter.1 hx).2, Finset.mem_univ _⟩) hinj
    _ = p - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

theorem card_params_le_mul_card_image_heis (lK : K →+ ZMod p) (hlK : ∃ a, lK a ≠ 0)
    (lV : V →+ ZMod p) (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (R : Subgroup Kˣ) (A : R → V →+ V) (hA : ∀ k, Function.Surjective (A k)) :
    Nat.card R * Nat.card V ≤ (p - 1) *
      ((Finset.univ : Finset (R × V)).image
        (fun x => (heisFun lK lV β x.1 (A x.1) x.2).ker)).card := by
  have h := Finset.card_le_mul_card_image (Finset.univ : Finset (R × V))
    (f := fun x => (heisFun lK lV β x.1 (A x.1) x.2).ker) (p - 1) (fun a ha => by
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 ha
      exact card_fiber_heis_le lK hlK lV β hβ R A hA x₀)
  rwa [Finset.card_univ, Fintype.card_prod, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h

end Count

section Main

open scoped Classical

theorem two_pow_le_card_of_heis_root {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K V : Type} [Field K] [Finite K] [CharP K p] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hinj : ∀ (c : K) (u : V), z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u) = 1 →
      c = 0 ∧ u = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) *
      (b v)⁻¹ =
        a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    {T : Type} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ = a (Multiplicative.ofAdd u')) :
    2 ^ (orderOf (2 : ZMod p) * (Nat.card χ.range * Nat.card V / (p - 1))) ≤ Nat.card W := by
  have : Finite S := Finite.of_surjective π hπ
  have : Finite V := Module.finite_of_finite K
  have : Fintype K := Fintype.ofFinite K
  have : Fintype V := Fintype.ofFinite V
  have ha0 : ∀ u : V, a (Multiplicative.ofAdd u) = 1 → u = 0 := by
    intro u h
    refine (hinj 0 u ?_).2
    rw [ofAdd_zero, map_one, one_mul]
    exact h
  have haI : ∀ x y : V, a (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd y) → x = y := by
    intro x y h
    refine sub_eq_zero.1 (ha0 _ ?_)
    rw [ofAdd_sub, map_div, h]
    exact div_self' _
  have hkey : ∀ (c1 c2 : Multiplicative K) (u1 u2 : Multiplicative V),
      z c1 * z c2 * (a u1 * a u2) = z c1 * a u1 * (z c2 * a u2) := by
    intro c1 c2 u1 u2
    calc z c1 * z c2 * (a u1 * a u2) = z c1 * (z c2 * a u1) * a u2 := by simp only [mul_assoc]
      _ = z c1 * (a u1 * z c2) * a u2 := by rw [hza c2 u1]
      _ = z c1 * a u1 * (z c2 * a u2) := by simp only [mul_assoc]
  let φ : Multiplicative (K × V) →* S :=
    { toFun := fun x => z (Multiplicative.ofAdd x.toAdd.1) * a (Multiplicative.ofAdd x.toAdd.2)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
        exact hkey _ _ _ _ }
  have hφ : ∀ (c : K) (u : V), φ (Multiplicative.ofAdd (c, u)) =
      z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u) := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h := hinj x.toAdd.1 x.toAdd.2 hx
    apply Multiplicative.toAdd.injective
    exact Prod.ext h.1 h.2
  have hUc : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow]
    have : y ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      refine Prod.ext ?_ ?_
      · show p • y.toAdd.1 = 0
        rw [← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero, zero_smul]
      · show p • y.toAdd.2 = 0
        rw [← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero, zero_smul]
    rw [this, map_one]
  have hZU : z.range ≤ φ.range := by
    rintro _ ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd (c.toAdd, 0), ?_⟩
    show z (Multiplicative.ofAdd c.toAdd) * a (Multiplicative.ofAdd 0) = z c
    rw [ofAdd_zero, map_one a, mul_one]
    rfl
  have hZne : z.range ≠ ⊥ := by
    intro h
    have hm : z (Multiplicative.ofAdd (1 : K)) ∈ z.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hm
    have := (hinj 1 0 (by rw [ofAdd_zero, map_one a, mul_one]; exact hm)).1
    exact one_ne_zero this
  have hAex : ∀ s : T, ∃ A : V →+ V,
      (∀ u, t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ = a (Multiplicative.ofAdd (A u))) ∧
        Function.Surjective A := by
    intro s
    choose f hf using hta s
    have hfadd : ∀ u v, f (u + v) = f u + f v := by
      intro u v
      apply haI
      rw [← hf, ofAdd_add, map_mul, ofAdd_add, map_mul, ← hf, ← hf]
      group
    let A : V →+ V := AddMonoidHom.mk' f hfadd
    refine ⟨A, hf, ?_⟩
    have hAinj : Function.Injective A := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      apply ha0
      have h1 := hf u
      have h2 : f u = 0 := hu
      rw [h2, ofAdd_zero, map_one] at h1
      calc a (Multiplicative.ofAdd u)
          = (t s)⁻¹ * (t s * a (Multiplicative.ofAdd u) * (t s)⁻¹) * t s := by group
        _ = 1 := by rw [h1]; group
    exact Finite.injective_iff_surjective.1 hAinj
  choose Am hAm hAsurj using hAex
  have hconjT : ∀ (s : T) (c : K) (u : V), t s * φ (Multiplicative.ofAdd (c, u)) * (t s)⁻¹ =
      φ (Multiplicative.ofAdd ((χ s : K) * c, Am s u)) := by
    intro s c u
    show t s * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)) * a (Multiplicative.ofAdd (Am s u))
    rw [← htz s c, ← hAm s u]
    group
  have hconjB : ∀ (v : V) (c : K) (u : V),
      b v * φ (Multiplicative.ofAdd (c, u)) *
        (b v)⁻¹ = φ (Multiplicative.ofAdd (c + β u v, u)) := by
    intro v c u
    show b v * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) *
        (b v)⁻¹ =
      z (Multiplicative.ofAdd (c + β u v)) * a (Multiplicative.ofAdd u)
    calc b v * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) *
          (b v)⁻¹
        = (b v * z (Multiplicative.ofAdd c)) * a (Multiplicative.ofAdd u) *
          (b v)⁻¹ := by simp only [mul_assoc]
      _ = (z (Multiplicative.ofAdd c) * b v) * a (Multiplicative.ofAdd u) *
          (b v)⁻¹ := by rw [hbz]
      _ = z (Multiplicative.ofAdd c) * (b v * a (Multiplicative.ofAdd u) *
          (b v)⁻¹) := by simp only [mul_assoc]
      _ = z (Multiplicative.ofAdd c) * (a (Multiplicative.ofAdd u) *
          z (Multiplicative.ofAdd (β u v))) := by rw [hab]
      _ = z (Multiplicative.ofAdd c) * (z (Multiplicative.ofAdd (β u v)) *
          a (Multiplicative.ofAdd u)) := by rw [hza]
      _ = z (Multiplicative.ofAdd (c + β u v)) * a (Multiplicative.ofAdd u) := by
          rw [ofAdd_add, map_mul, mul_assoc]
  have hnorm : ∀ g : S, (∀ x, ∃ y, g * φ x * g⁻¹ = φ y) →
      g ∈ Subgroup.normalizer (φ.range : Set S) := by
    intro g h1
    choose f hf using h1
    have hfinj : Function.Injective f := by
      intro x y hxy
      apply hφinj
      have h2 : g * φ x * g⁻¹ = g * φ y * g⁻¹ := by rw [hf x, hf y, hxy]
      exact mul_left_cancel (mul_right_cancel h2)
    have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, (hf x).symm⟩
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hfsurj x'
      refine ⟨x, ?_⟩
      have h2 : g * y * g⁻¹ = g * φ x * g⁻¹ := by rw [← hx', hf x]
      exact (mul_left_cancel (mul_right_cancel h2)).symm
  have hN_t : ∀ s : T, t s ∈ Subgroup.normalizer (φ.range : Set S) := fun s =>
    hnorm _ fun x => ⟨_, hconjT s x.toAdd.1 x.toAdd.2⟩
  have hN_b : ∀ v : V, b v ∈ Subgroup.normalizer (φ.range : Set S) := fun v =>
    hnorm _ fun x => ⟨_, hconjB v x.toAdd.1 x.toAdd.2⟩
  have horb : ∀ D₀ : Subgroup S, D₀ ≤ φ.range → D₀.relIndex φ.range = p → ¬ z.range ≤ D₀ →
      Nat.card χ.range * Nat.card V / (p - 1) ≤
        (Subgroup.normalizer (φ.range : Set S) ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex
          (Subgroup.normalizer (φ.range : Set S)) := by
    intro D₀ hD₀U hrel hZD
    have hDidx : (D₀.comap φ).index = p := by
      rw [Subgroup.index_comap]
      exact hrel
    have hDaidx : (AddSubgroup.toSubgroup.symm (D₀.comap φ)).index = p := by
      rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]
      exact hDidx
    obtain ⟨l, hl⟩ := exists_hom_of_index_eq_prime _ hDaidx
    have hlD : ∀ x : K × V, l x = 0 ↔ φ (Multiplicative.ofAdd x) ∈ D₀ := fun x =>
      (hl x).trans (mem_toSubgroup_symm _ x)
    set lK : K →+ ZMod p := l.comp (AddMonoidHom.inl K V) with hlKdef
    set lV : V →+ ZMod p := l.comp (AddMonoidHom.inr K V) with hlVdef
    have hlsplit : ∀ c u, l (c, u) = lK c + lV u := by
      intro c u
      have : ((c, u) : K × V) = (c, 0) + (0, u) := Prod.ext (by simp) (by simp)
      rw [this, map_add]
      rfl
    have hlK : ∃ x, lK x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hZD
      rintro _ ⟨c, rfl⟩
      have h0 : l (c.toAdd, 0) = 0 := hcon c.toAdd
      have := (hlD (c.toAdd, 0)).1 h0
      have e : φ (Multiplicative.ofAdd (c.toAdd, 0)) = z c := by
        show z (Multiplicative.ofAdd c.toAdd) * a (Multiplicative.ofAdd 0) = z c
        rw [ofAdd_zero, map_one a, mul_one]
        rfl
      rwa [e] at this
    obtain ⟨sec, hsec⟩ : ∃ sec : χ.range → T, ∀ k, χ (sec k) = (k : Kˣ) :=
      ⟨fun k => (MonoidHom.mem_range.1 k.2).choose,
        fun k => (MonoidHom.mem_range.1 k.2).choose_spec⟩
    let g : χ.range × V → S := fun x => b x.2 * t (sec x.1)
    have hg : ∀ x, g x ∈ Subgroup.normalizer (φ.range : Set S) := fun x =>
      Subgroup.mul_mem _ (hN_b x.2) (hN_t (sec x.1))
    have hgconj : ∀ (x : χ.range × V) (c : K) (u : V),
        g x * φ (Multiplicative.ofAdd (c, u)) * (g x)⁻¹ =
          φ (Multiplicative.ofAdd (((x.1 : Kˣ) : K) * c + β (Am (sec x.1) u) x.2,
            Am (sec x.1) u)) := by
      intro x c u
      have e1 := hconjT (sec x.1) c u
      have e2 := hconjB x.2 ((χ (sec x.1) : K) * c) (Am (sec x.1) u)
      rw [hsec x.1] at e1 e2
      calc g x * φ (Multiplicative.ofAdd (c, u)) * (g x)⁻¹
          = b x.2 * (t (sec x.1) * φ (Multiplicative.ofAdd (c, u)) *
            (t (sec x.1))⁻¹) * (b x.2)⁻¹ := by
            simp only [g, mul_inv_rev, mul_assoc]
        _ = _ := by rw [e1, e2]
    have hker' : ∀ (x : χ.range × V) (w : K × V),
        heisFun lK lV β x.1 (Am (sec x.1)) x.2 w = 0 ↔
          φ (Multiplicative.ofAdd w) ∈ conjSub (g x)⁻¹ D₀ := by
      intro x w
      obtain ⟨c, u⟩ := w
      rw [mem_conjSub, inv_inv, hgconj x c u, ← hlD, hlsplit, heisFun_apply, map_add]
      show _ + (_ + _) = 0 ↔ _ + _ + _ = 0
      rw [add_assoc]
    let s : Finset S := Finset.univ.image (fun x : χ.range × V => (g x)⁻¹)
    have hs : ∀ y ∈ s, y ∈ Subgroup.normalizer (φ.range : Set S) := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
      exact Subgroup.inv_mem _ (hg x)
    have h1 := card_image_conj_le_relIndex (Subgroup.normalizer (φ.range : Set S)) D₀ s hs
    let G : Subgroup S → AddSubgroup (K × V) := fun C => AddSubgroup.toSubgroup.symm (C.comap φ)
    have hkerG : ∀ x : χ.range × V,
        (heisFun lK lV β x.1 (Am (sec x.1)) x.2).ker = G (conjSub (g x)⁻¹ D₀) := by
      intro x
      ext w
      rw [AddMonoidHom.mem_ker, hker' x w]
      exact (mem_toSubgroup_symm ((conjSub (g x)⁻¹ D₀).comap φ) w).symm
    have hcomp : ((Finset.univ : Finset (χ.range × V)).image
        (fun x => (heisFun lK lV β x.1 (Am (sec x.1)) x.2).ker)) =
          (s.image fun y => conjSub y D₀).image G := by
      simp only [s, Finset.image_image]
      congr 1
      funext x
      exact hkerG x
    have h2 : ((Finset.univ : Finset (χ.range × V)).image
        (fun x => (heisFun lK lV β x.1 (Am (sec x.1)) x.2).ker)).card ≤
          (s.image fun y => conjSub y D₀).card := by
      rw [hcomp]
      exact Finset.card_image_le
    have h3 := card_params_le_mul_card_image_heis lK hlK lV β hβ χ.range (fun k => Am (sec k))
      (fun k => hAsurj _)
    exact Nat.div_le_of_le_mul (h3.trans (Nat.mul_le_mul_left _ (h2.trans h1)))
  have h := two_pow_le_card_of_lift_orbit_rel hW hp2 π hπ hker hZ hZU hZne hUc hUp le_rfl horb
  rwa [mul_comm] at h

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
