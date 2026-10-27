module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped commutatorElement

section Lift

variable {H : Type*} [Group H]

theorem exists_lift_threePow [Finite H] (Z : Subgroup H) {x₀ : H} (h : x₀ ^ 3 ∈ Z) :
    ∃ (x : H) (j : ℕ), x ^ (3 ^ j) = 1 ∧ x₀⁻¹ * x ∈ Z := by
  have ho : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  obtain ⟨w, hw⟩ : ∃ w : ℕ, b * w % 3 = 1 := by
    have : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases this with h1 | h1
    · exact ⟨1, by simpa using h1⟩
    · exact ⟨2, by omega⟩
  refine ⟨x₀ ^ (b * w), a, ?_, ?_⟩
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hab]
    exact ⟨w, by ring⟩
  · obtain ⟨q, hq⟩ : ∃ q, b * w = 3 * q + 1 := ⟨b * w / 3, by omega⟩
    have : x₀⁻¹ * x₀ ^ (b * w) = (x₀ ^ 3) ^ q := by
      rw [hq, pow_succ, pow_mul]
      group
    rw [this]
    exact Subgroup.pow_mem _ h q

end Lift

section LiftCommute

variable {H : Type*} [Group H]

theorem commute_of_central_commutator {x t : H} (ht : t * t = 1) {j : ℕ} (hx : x ^ (3 ^ j) = 1)
    (hz : ∀ y : H, (x * t * x⁻¹ * t⁻¹) * y = y * (x * t * x⁻¹ * t⁻¹)) : x * t = t * x := by
  set ζ : H := x * t * x⁻¹ * t⁻¹ with hζ
  have hxt : x * t * x⁻¹ = ζ * t := by rw [hζ]; group
  have hsq : ζ ^ 2 = 1 := by
    have h1 : x * (t * t) * x⁻¹ = (ζ * t) * (ζ * t) := by
      rw [← hxt]; group
    have h2 : (ζ * t) * (ζ * t) = ζ * ζ * (t * t) := by
      calc (ζ * t) * (ζ * t) = ζ * (t * ζ) * t := by group
        _ = ζ * (ζ * t) * t := by rw [hz t]
        _ = ζ * ζ * (t * t) := by group
    rw [ht] at h1 h2
    simp only [mul_one] at h1 h2
    have : ζ * ζ = 1 := by rw [← h2, ← h1]; group
    rwa [sq]
  have hpow : ∀ n : ℕ, x ^ n * t * (x ^ n)⁻¹ = ζ ^ n * t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : x ^ (n + 1) * t * (x ^ (n + 1))⁻¹ = x * (x ^ n * t * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih]
      have e2 : x * (ζ ^ n * t) * x⁻¹ = ζ ^ n * (x * t * x⁻¹) := by
        have hc : x * ζ ^ n = ζ ^ n * x := by
          have := Commute.pow_left (show Commute ζ x from hz x) n
          exact this.symm.eq
        calc x * (ζ ^ n * t) * x⁻¹ = (x * ζ ^ n) * t * x⁻¹ := by group
          _ = (ζ ^ n * x) * t * x⁻¹ := by rw [hc]
          _ = ζ ^ n * (x * t * x⁻¹) := by group
      rw [e2, hxt, pow_succ]
      group
  have hζn : ζ ^ (3 ^ j) = 1 := by
    have := hpow (3 ^ j)
    rw [hx] at this
    simp only [inv_one, mul_one, one_mul] at this
    have h3 : ζ ^ (3 ^ j) * t = t := this.symm
    exact mul_eq_right.mp h3
  have hord : orderOf ζ ∣ Nat.gcd 2 (3 ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hζn)
  have hcop : Nat.gcd 2 (3 ^ j) = 1 := by
    apply Nat.Coprime.pow_right
    norm_num
  rw [hcop] at hord
  have hζ1 : ζ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  have : x * t * x⁻¹ * t⁻¹ = 1 := hζ1
  calc x * t = (x * t * x⁻¹ * t⁻¹) * (t * x) := by group
    _ = t * x := by rw [this, one_mul]

end LiftCommute

section Induced

@[expose] noncomputable def inducedAutCenter (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem inducedAutCenter_mk {H : Type*} [Group H] (φ : MulAut H) (x : H) :
    inducedAutCenter H φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

end Induced

section Main

variable {G : Type} [Group G]

@[expose] def Rigid3 (P : Type) [Group P] (τ : P) : Prop :=
  ∃ S : Set P, (∀ s ∈ S, s ^ 3 = 1 ∧ s * τ = τ * s) ∧
    ∀ α : MulAut P, (∃ k : ℕ, α ^ (3 ^ k) = 1) → (∀ s ∈ S, α s = s) → α = 1

theorem model1520_of_rigid3 [Finite G] {X : Subgroup G} {t : G} (htX : t ∈ X) (ht : t * t = 1)
    {P : Type} [Group P] (hP : Group.IsPerfect P) (e : ↥X ⧸ Subgroup.center ↥X ≃* P) {τ : P}
    (hτ : e (QuotientGroup.mk ⟨t, htX⟩) = τ) (hR : Rigid3 P τ) : Model1520 X t := by
  intro A hA3 hAN hAD
  obtain ⟨S, hS, hrig⟩ := hR
  have : Finite ↥X := Subtype.finite
  intro a ha
  set t' : ↥X := ⟨t, htX⟩ with ht'
  let q : ↥X →* P := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hq : ∀ x, q x = e (QuotientGroup.mk x) := fun x => rfl
  have hqsurj : Function.Surjective q := fun p => by
    obtain ⟨y, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, rfl⟩
  have hqker : ∀ x, q x = 1 ↔ x ∈ Subgroup.center ↥X := fun x => by
    rw [hq, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hqt : q t' = τ := hτ
  set na : Subgroup.normalizer (X : Set G) := ⟨a, hAN ha⟩ with hna
  let ν : MulAut ↥X := X.normalizerMonoidHom na
  have hν : ∀ x : ↥X, ((ν x : ↥X) : G) = a * x * a⁻¹ := fun x => rfl
  let α : MulAut P := (MulAut.congr e) (inducedAutCenter ↥X ν)
  have hα : ∀ x : ↥X, α (q x) = q (ν x) := fun x => by
    simp [α, hq, MulAut.congr_apply, inducedAutCenter_mk]
  have hαord : ∃ k : ℕ, α ^ (3 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hA3 ⟨a, ha⟩
    refine ⟨k, ?_⟩
    let Φ : Subgroup.normalizer (X : Set G) →* MulAut P :=
      (MulAut.congr e).toMonoidHom.comp ((inducedAutCenter ↥X).comp X.normalizerMonoidHom)
    have h1 : na ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg (fun y : ↥A => (y : G)) hk
      simpa [hna] using this
    have h2 : α ^ (3 ^ k) = Φ (na ^ (3 ^ k)) := by
      rw [map_pow]; rfl
    rw [h2, h1, map_one]
  have hfix : ∀ x : ↥X, x * t' = t' * x → ν x = x := by
    intro x hx
    apply Subtype.ext
    have hmem : (x : G) ∈ (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg (fun y : ↥X => (y : G)) hx
      simpa [ht'] using this
    have := Subgroup.mem_centralizer_iff.mp (hAD ha) (x : G) hmem
    rw [hν]
    calc a * (x : G) * a⁻¹ = (x : G) * a * a⁻¹ := by rw [← this]
      _ = x := by group
  have hαS : ∀ s ∈ S, α s = s := by
    intro s hs
    obtain ⟨hs3, hsτ⟩ := hS s hs
    obtain ⟨x₀, rfl⟩ := hqsurj s
    have hx₀ : x₀ ^ 3 ∈ Subgroup.center ↥X := by
      rw [← hqker, map_pow]; exact hs3
    obtain ⟨x, j, hxj, hxz⟩ := exists_lift_threePow (Subgroup.center ↥X) hx₀
    have hqx : q x = q x₀ := by
      have : q (x₀⁻¹ * x) = 1 := (hqker _).mpr hxz
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hcomm : x * t' = t' * x := by
      apply commute_of_central_commutator (by apply Subtype.ext; simpa [ht'] using ht) hxj
      intro y
      have hz : x * t' * x⁻¹ * t'⁻¹ ∈ Subgroup.center ↥X := by
        rw [← hqker, map_mul, map_mul, map_mul, map_inv, map_inv, hqt, hqx]
        calc q x₀ * τ * (q x₀)⁻¹ * τ⁻¹ = (τ * q x₀) * (q x₀)⁻¹ * τ⁻¹ := by rw [hsτ]
          _ = 1 := by group
      exact (Subgroup.mem_center_iff.mp hz y).symm
    rw [← hqx, hα, hfix x hcomm]
  have hα1 : α = 1 := hrig α hαord hαS
  have hcen : ∀ x : ↥X, ν x * x⁻¹ ∈ Subgroup.center ↥X := by
    intro x
    rw [← hqker, map_mul, map_inv, ← hα, hα1]
    simp
  let c : ↥X →* Subgroup.center ↥X :=
    { toFun := fun x => ⟨ν x * x⁻¹, hcen x⟩
      map_one' := by refine Subtype.ext ?_; simp
      map_mul' := fun x y => by
        refine Subtype.ext ?_
        have hc := Subgroup.mem_center_iff.mp (hcen y) x⁻¹
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        calc ν x * ν y * (y⁻¹ * x⁻¹) = ν x * ((ν y * y⁻¹) * x⁻¹) := by group
          _ = ν x * (x⁻¹ * (ν y * y⁻¹)) := by rw [← hc]
          _ = ν x * x⁻¹ * (ν y * y⁻¹) := by group }
  have hcZ : ∀ z ∈ Subgroup.center ↥X, c z = 1 := by
    intro z hz
    have : ν z = z := hfix z (Subgroup.mem_center_iff.mp hz t').symm
    apply Subtype.ext
    simp [c, this]
  have hcomm_ker : commutator ↥X ≤ c.ker := Abelianization.commutator_subset_ker c
  have := hP
  have htop : (commutator ↥X).map q = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective q hqsurj]
    have h := Group.IsPerfect.commutator_eq_top (G := P)
    rwa [commutator_def] at h
  have hc1 : ∀ x : ↥X, c x = 1 := by
    intro x
    have hx : q x ∈ (commutator ↥X).map q := by rw [htop]; trivial
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hz : y⁻¹ * x ∈ Subgroup.center ↥X := by
      rw [← hqker, map_mul, map_inv, hyx]; simp
    have : x = y * (y⁻¹ * x) := by group
    rw [this, map_mul, hcZ _ hz, mul_one]
    exact hcomm_ker hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : ν ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ = 1 := by
    have := congrArg (fun z : Subgroup.center ↥X => (z : ↥X)) (hc1 ⟨x, hx⟩)
    simpa [c] using this
  have h2 : ν ⟨x, hx⟩ = ⟨x, hx⟩ := mul_inv_eq_one.mp h1
  have h3 := congrArg (fun z : ↥X => (z : G)) h2
  simp only [hν] at h3
  calc x * a = a * x * a⁻¹ * a := by rw [h3]
    _ = a * x := by group

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
