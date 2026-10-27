module

public import CFSG.GH74.GLS.Bg.TwoGroups.Basic

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup
open scoped commutatorElement

theorem abstract_fix {V : Type} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a * a = 1) (σ : V →* V) (hσ : ∀ v, σ (σ v) = v)
    (hcard : Nat.card {v : V // σ v = v} ^ 2 = Nat.card V) :
    ∀ v : V, σ v = v → ∃ w : V, w * σ w = v := by
  classical
  let δ : V →* V := MonoidHom.mk' (fun w => w * σ w) (by
    intro a b
    simp only [map_mul]
    calc a * b * (σ a * σ b) = a * (b * σ a) * σ b := by group
      _ = a * (σ a * b) * σ b := by rw [hcomm b (σ a)]
      _ = a * σ a * (b * σ b) := by group)
  have hδ : ∀ w, δ w = w * σ w := fun w => rfl
  let Fx : Subgroup V := MonoidHom.eqLocus σ (MonoidHom.id V)
  have hFx : ∀ v, v ∈ Fx ↔ σ v = v := fun v => Iff.rfl
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hker : δ.ker = Fx := by
    ext w
    rw [MonoidHom.mem_ker, hδ, hFx]
    constructor
    · intro h
      have : σ w = w⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, hinv]
    · intro h
      rw [h]; exact hsq w
  have hrange : δ.range ≤ Fx := by
    rintro _ ⟨w, rfl⟩
    rw [hFx, hδ]
    simp only [map_mul, hσ]
    exact hcomm _ _
  have hFxcard : Nat.card Fx = Nat.card {v : V // σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hFx)
  have hcardk : Nat.card δ.ker = Nat.card {v : V // σ v = v} := by
    rw [hker]; exact hFxcard
  have h1 : Nat.card V = Nat.card (V ⧸ δ.ker) * Nat.card δ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  have h2 : Nat.card (V ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have hposF : 0 < Nat.card {v : V // σ v = v} := by
    rw [← hFxcard]; exact Nat.card_pos
  have h3 : Nat.card δ.range = Nat.card Fx := by
    rw [hFxcard]
    have : Nat.card δ.range * Nat.card {v : V // σ v = v}
        = Nat.card {v : V // σ v = v} * Nat.card {v : V // σ v = v} := by
      calc Nat.card δ.range * Nat.card {v : V // σ v = v}
          = Nat.card (V ⧸ δ.ker) * Nat.card δ.ker := by rw [h2, hcardk]
        _ = Nat.card V := h1.symm
        _ = Nat.card {v : V // σ v = v} ^ 2 := hcard.symm
        _ = Nat.card {v : V // σ v = v} * Nat.card {v : V // σ v = v} := sq _
    exact Nat.eq_of_mul_eq_mul_right hposF this
  have heq : δ.range = Fx := Subgroup.eq_of_le_of_card_ge hrange (by rw [h3])
  intro v hv
  have : v ∈ δ.range := by rw [heq]; exact (hFx v).mpr hv
  obtain ⟨w, hw⟩ := this
  exact ⟨w, hw⟩

theorem key_step {G : Type} [Group G] [Finite G] (x : G) (hx : x * x = 1) (N M : Subgroup G)
    (hNM : N ≤ M) (hcomm : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) (hsq : ∀ a ∈ M, a ^ 2 ∈ N)
    (hxN : ∀ g ∈ N, x * g * x⁻¹ ∈ N) (hxM : ∀ g ∈ M, x * g * x⁻¹ ∈ M)
    (hcard : Nat.card {m : G // m ∈ M ∧ m⁻¹ * (x * m * x⁻¹) ∈ N} ^ 2 = Nat.card M * Nat.card N)
    (m : G) (hm : m ∈ M) (hm2 : m * (x * m * x⁻¹) ∈ N) :
    ∃ c ∈ M, c⁻¹ * m * (x * c * x⁻¹) ∈ N := by
  classical
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hNnorm : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hcomm g hg n (hNM hn)) hn
  let Nn : Subgroup M := N.subgroupOf M
  have hmemNn : ∀ a : M, a ∈ Nn ↔ (a : G) ∈ N := fun a => Iff.rfl
  have hnormal : Nn.Normal := ⟨by
    intro n hn g
    rw [hmemNn] at hn ⊢
    exact hNnorm g g.2 n hn⟩
  let V := M ⧸ Nn
  let cx : M →* M :=
    { toFun := fun a => ⟨x * a * x⁻¹, hxM a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc] }
  have hcx : ∀ a : M, ((cx a : M) : G) = x * a * x⁻¹ := fun a => rfl
  have hcxNn : Nn ≤ Nn.comap cx := by
    intro n hn
    rw [Subgroup.mem_comap, hmemNn, hcx]
    exact hxN n hn
  let σ : V →* V := QuotientGroup.map Nn Nn cx hcxNn
  have hσmk : ∀ a : M, σ (a : V) = ((cx a : M) : V) := fun a => rfl
  have hσσ : ∀ v : V, σ (σ v) = v := by
    intro v
    induction v using QuotientGroup.induction_on with
    | _ a =>
      rw [hσmk, hσmk]
      congr 1
      apply Subtype.ext
      rw [hcx, hcx]
      have : x * (x * (a : G) * x⁻¹) * x⁻¹ = (a : G) := by
        calc x * (x * (a : G) * x⁻¹) * x⁻¹ = (x * x) * (a : G) * (x⁻¹ * x⁻¹) := by group
          _ = (a : G) := by rw [hx, ← mul_inv_rev, hx]; simp
      exact this
  have hVcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.mpr
        rw [hmemNn]
        have : (((a * b)⁻¹ * (b * a) : M) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv]; group
        rw [this]
        exact hcomm _ (inv_mem b.2) _ (inv_mem a.2)
  have hVsq : ∀ a : V, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | _ a =>
      rw [← QuotientGroup.mk_mul]
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [hmemNn]
      have : (((a * a : M)) : G) = (a : G) ^ 2 := by simp [pow_two]
      rw [this]
      exact hsq a a.2
  let Fx : Subgroup V := MonoidHom.eqLocus σ (MonoidHom.id V)
  have hFx : ∀ v, v ∈ Fx ↔ σ v = v := fun v => Iff.rfl
  have hfix : ∀ a : M, σ (a : V) = (a : V) ↔ (a : G)⁻¹ * (x * a * x⁻¹) ∈ N := by
    intro a
    rw [hσmk, eq_comm, QuotientGroup.eq, hmemNn]
    simp [hcx]
  let f : M →* V := QuotientGroup.mk' Nn
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective Nn
  have hfker : f.ker = Nn := QuotientGroup.ker_mk' Nn
  have hNnN : Nat.card Nn = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hMcard : Nat.card M = Nat.card V * Nat.card Nn :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Nn
  let e : {m : G // m ∈ M ∧ m⁻¹ * (x * m * x⁻¹) ∈ N} ≃ ↥(Fx.comap f) :=
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, (hFx _).mpr ((hfix ⟨p.1, p.2.1⟩).mpr p.2.2)⟩
      invFun := fun q => ⟨(q.1 : M), q.1.2, (hfix q.1).mp ((hFx _).mp q.2)⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hcm : Nat.card (Fx.comap f) = Nat.card Fx * Nat.card Nn := by
    have := card_comap_of_surjective f hfsurj Fx
    rw [hfker] at this; exact this
  have hFxcard : Nat.card Fx = Nat.card {v : V // σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hFx)
  have hVcard : Nat.card {v : V // σ v = v} ^ 2 = Nat.card V := by
    have h1 := hcard
    rw [Nat.card_congr e, hcm, hMcard, hNnN.symm] at h1
    rw [← hFxcard] at *
    have hpos : 0 < Nat.card Nn := Nat.card_pos
    have : (Nat.card Fx) ^ 2 * (Nat.card Nn * Nat.card Nn)
        = Nat.card V * (Nat.card Nn * Nat.card Nn) := by
      calc (Nat.card Fx) ^ 2 * (Nat.card Nn * Nat.card Nn) = (Nat.card Fx * Nat.card Nn) ^ 2 := by
            ring
        _ = Nat.card V * Nat.card Nn * Nat.card Nn := h1
        _ = Nat.card V * (Nat.card Nn * Nat.card Nn) := by ring
    have hpos2 : 0 < Nat.card Nn * Nat.card Nn := Nat.mul_pos hpos hpos
    exact Nat.eq_of_mul_eq_mul_right hpos2 this
  have hmv : σ ((⟨m, hm⟩ : M) : V) = ((⟨m, hm⟩ : M) : V) := by
    have h1 : ((⟨m, hm⟩ : M) : V) * σ ((⟨m, hm⟩ : M) : V) = 1 := by
      rw [hσmk, ← QuotientGroup.mk_mul]
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [hmemNn]
      exact hm2
    have h2 : σ ((⟨m, hm⟩ : M) : V) = (((⟨m, hm⟩ : M) : V))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (hVsq _)
  obtain ⟨w, hw⟩ := abstract_fix hVcomm hVsq σ hσσ hVcard _ hmv
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨(c : G), c.2, ?_⟩
  rw [hσmk, ← QuotientGroup.mk_mul] at hw
  have hw' := QuotientGroup.eq.mp hw
  rw [hmemNn] at hw'
  have hw'' : ((c : G) * (x * (c : G) * x⁻¹))⁻¹ * m ∈ N := by simpa [hcx] using hw'
  set s : G := x * (c : G) * x⁻¹ with hs
  have hsM : s ∈ M := hxM c c.2
  have hrw : (c : G)⁻¹ * m * s = (s * (((c : G) * s)⁻¹ * m) * s⁻¹) * (s * s) := by
    group
  rw [hrw]
  exact mul_mem (hNnorm s hsM _ hw'') (by simpa [pow_two] using hsq s hsM)

theorem chain_two {G : Type} [Group G] [Finite G] (x : G) (hx : x * x = 1) :
    ∀ (n : ℕ) (P : ℕ → Subgroup G), P 0 = ⊥ → (∀ i < n, FreeSec2 x (P i) (P (i + 1))) →
      ∀ y : G, y * x⁻¹ ∈ P n → y ^ 2 = 1 → ∃ c ∈ P n, c * x * c⁻¹ = y := by
  intro n
  induction n with
  | zero =>
    intro P hP0 _ y hy _
    rw [hP0] at hy
    have : y * x⁻¹ = 1 := hy
    refine ⟨1, one_mem _, ?_⟩
    have h : y = x := by
      have := congrArg (fun t => t * x) this
      simpa using this
    rw [h]; simp
  | succ n ih =>
    intro P hP0 hP y hy hy2
    obtain ⟨hNM, hcomm, hsq, hxN, hxM, hcard⟩ := hP n (Nat.lt_succ_self n)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    set m : G := y * x⁻¹ with hm
    have hmM : m ∈ P (n + 1) := hy
    have hm2 : m * (x * m * x⁻¹) ∈ P n := by
      have h1 : m * (x * m * x⁻¹) = y ^ 2 := by
        have : y = m * x := by rw [hm]; group
        rw [this, pow_two]
        calc m * (x * m * x⁻¹) = m * (x * m * x⁻¹) * (x * x) := by rw [hx, mul_one]
          _ = m * x * (m * x) := by group
      rw [h1, hy2]
      exact one_mem _
    obtain ⟨c, hcM, hc⟩ := key_step x hx (P n) (P (n + 1)) hNM hcomm hsq hxN hxM hcard m hmM hm2
    have hy1 : (c⁻¹ * y * c) * x⁻¹ ∈ P n := by
      have : (c⁻¹ * y * c) * x⁻¹ = c⁻¹ * m * (x * c * x⁻¹) := by
        rw [hm]; group
      rw [this]; exact hc
    have hy12 : (c⁻¹ * y * c) ^ 2 = 1 := by
      have : (c⁻¹ * y * c) ^ 2 = c⁻¹ * y ^ 2 * c := by
        rw [pow_two, pow_two]; group
      rw [this, hy2]; group
    obtain ⟨c₁, hc₁, hc₁'⟩ :=
      ih P hP0 (fun i hi => hP i (Nat.lt_succ_of_lt hi)) (c⁻¹ * y * c) hy1 hy12
    refine ⟨c * c₁, mul_mem hcM (hNM hc₁), ?_⟩
    calc c * c₁ * x * (c * c₁)⁻¹ = c * (c₁ * x * c₁⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * y * c) * c⁻¹ := by rw [hc₁']
      _ = y := by group

theorem zpowers_of_sq_eq_one {X : Type*} [Group X] (x : X) (hx : x * x = 1) :
    ∀ h ∈ zpowers x, h = 1 ∨ h = x := by
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    simp [hx2]
  rw [this]
  have : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases this with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  have := pow_orderOf_eq_one x
  rw [hx, pow_two] at this
  exact this

theorem ig_10_31 : IG_10_31 := by
  intro G _ _ P x n Pi hx _ hP0 hPn hfree y hy hy2
  have hx2 := mul_self_eq_one_of_orderOf_eq_two hx
  have := chain_two x hx2 n Pi hP0 hfree y (by rw [hPn]; exact hy) hy2
  rw [hPn] at this
  exact this

theorem mem_sup_of_commute' {G : Type*} [Group G] {Q₁ Q₂ : Subgroup G}
    (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a) {g : G} (hg : g ∈ Q₁ ⊔ Q₂) :
    ∃ a ∈ Q₁, ∃ b ∈ Q₂, a * b = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ Q₁, ∃ b ∈ Q₂, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have := hcomm a' ha' b hb
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [this]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have := hcomm a ha b hb
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [this] }
  have : Q₁ ⊔ Q₂ ≤ S := by
    apply sup_le
    · intro a ha; exact ⟨a, ha, 1, one_mem _, by simp⟩
    · intro b hb; exact ⟨1, one_mem _, b, hb, by simp⟩
  exact this hg

end CFSG.GH74.GLS.Bg.TwoGroups
