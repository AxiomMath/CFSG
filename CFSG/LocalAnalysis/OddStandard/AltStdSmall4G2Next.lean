module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Scalar

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

@[expose] def StepCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (k : ℕ)
    (A P A' : Subgroup G), StepData θ c.hn8 z k A P A' →
      ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ KA L z A', ∀ v : Fin 3 → ZMod 2,
        g * epsV θ c.hn8 v * g⁻¹ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)

section Comm

variable {G : Type} [Group G]

theorem commutator_mul_left' (x x' y : G) :
    x * x' * y * (x * x')⁻¹ * y⁻¹ =
      x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group

theorem commutator_mul_right' (x y y' : G) :
    x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group

theorem commutator_conj' (κ x y : G) :
    κ * x * κ⁻¹ * (κ * y * κ⁻¹) * (κ * x * κ⁻¹)⁻¹ * (κ * y * κ⁻¹)⁻¹ =
      κ * (x * y * x⁻¹ * y⁻¹) * κ⁻¹ := by group

end Comm

namespace StepData

section Basic

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n} {z : G} {k : ℕ} {A P A' : Subgroup G}
  (hs : StepData θ hn z k A P A')
include hs

theorem A'_le_P : A' ≤ P := by
  rw [hs.A'_eq]
  exact inf_le_left

theorem A'_le_centralizer : A' ≤ centralizer (A : Set G) := by
  rw [hs.A'_eq]
  exact inf_le_right

theorem A'_le_RA : A' ≤ RA θ hn z A := hs.A'_le_P.trans hs.P_le

theorem isPGroup_A' : IsPGroup 2 A' := hs.P_two.to_le hs.A'_le_P

theorem A_le_A' : A ≤ A' := by
  rw [hs.A'_eq]
  exact le_inf (le_sup_left.trans hs.le_P) fun a ha =>
    mem_centralizer_iff.2 fun b hb => hs.datum.comm hb ha

theorem z_mem_P : z ∈ P := hs.le_P (mem_sup_right (mem_zpowers z))

theorem z_not_mem_A' : z ∉ A' := fun h' =>
  hs.datum.z_not_mem_centralizer (hs.A'_le_centralizer h')

theorem comm_of_mem_A {a x : G} (ha : a ∈ A) (hx : x ∈ A') : a * x = x * a :=
  (mem_centralizer_iff.1 (hs.A'_le_centralizer hx) a ha)

end Basic

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {k : ℕ} {A P A' : Subgroup G}
  (c : Config G L Q n θ z) (hs : StepData θ c.hn8 z k A P A')
include c hs

theorem conj_mem_A' {x : G} (hx : x ∈ A') : z * x * z⁻¹ ∈ A' := by
  have hzi := z_inv c
  rw [hs.A'_eq] at hx ⊢
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hs.z_mem_P hxP) (inv_mem hs.z_mem_P), ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : z⁻¹ * a * z ∈ A := by
    have := hs.datum.conj_z_mem ha
    rwa [hzi] at this ⊢
  have := mem_centralizer_iff.1 hxC _ ha'
  calc a * (z * x * z⁻¹) = z * ((z⁻¹ * a * z) * x) * z⁻¹ := by group
    _ = z * (x * (z⁻¹ * a * z)) * z⁻¹ := by rw [this]
    _ = z * x * z⁻¹ * a := by group

theorem betaHat_mul' {x y : G} (hx : x ∈ A') (hy : y ∈ A') :
    betaHat k z (x * y) = betaHat k z x * betaHat k z y :=
  betaHat_mul c hs.datum (hs.A'_le_RA hx) (hs.A'_le_RA hy)

theorem betaHat_inv' {x : G} (hx : x ∈ A') : betaHat k z x⁻¹ = (betaHat k z x)⁻¹ :=
  betaHat_inv c hs.datum (hs.A'_le_RA hx)

theorem betaHat_mem_E' {x : G} (hx : x ∈ A') : betaHat k z x ∈ E θ c.hn8 :=
  betaHat_mem_E c hs.datum (hs.A'_le_RA hx)

theorem inv_mul_mem_A {x x' : G} (hx : x ∈ A') (hx' : x' ∈ A')
    (h : betaHat k z x = betaHat k z x') : x⁻¹ * x' ∈ A := by
  refine hs.ker _ (mul_mem (inv_mem hx) hx') ?_
  rw [betaHat_mul' c hs (inv_mem hx) hx', betaHat_inv' c hs hx, h, inv_mul_cancel]

theorem commutator_mem_A {x y : G} (hx : x ∈ A') (hy : y ∈ A') :
    x * y * x⁻¹ * y⁻¹ ∈ A := by
  refine hs.ker _ (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
  rw [betaHat_mul' c hs (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    betaHat_mul' c hs (mul_mem hx hy) (inv_mem hx), betaHat_mul' c hs hx hy, betaHat_inv' c hs hx,
    betaHat_inv' c hs hy, E_comm θ c.hn8 (betaHat_mem_E' c hs hx) (betaHat_mem_E' c hs hy)]
  group

theorem exists_conj_z_eq {x : G} (hx : x ∈ A') : ∃ b ∈ A, z * x * z⁻¹ = b * x := by
  have hβ := beta_mem c hs.datum (hs.A'_le_RA hx)
  refine ⟨(x * z * x⁻¹ * z⁻¹)⁻¹, inv_mem hβ, ?_⟩
  group

theorem commutator_eq_of_betaHat_left {x x' y : G} (hx : x ∈ A') (hx' : x' ∈ A') (hy : y ∈ A')
    (h : betaHat k z x = betaHat k z x') :
    x * y * x⁻¹ * y⁻¹ = x' * y * x'⁻¹ * y⁻¹ := by
  set a := x⁻¹ * x' with ha
  have haA : a ∈ A := inv_mul_mem_A c hs hx hx' h
  have hx'a : x' = x * a := by rw [ha, mul_inv_cancel_left]
  have hay : a * y * a⁻¹ * y⁻¹ = 1 := by
    rw [hs.comm_of_mem_A haA hy, mul_inv_cancel_right, mul_inv_cancel]
  rw [hx'a, commutator_mul_left', hay, mul_one, mul_inv_cancel, one_mul]

theorem commutator_eq_of_betaHat_right {x y y' : G} (hx : x ∈ A') (hy : y ∈ A') (hy' : y' ∈ A')
    (h : betaHat k z y = betaHat k z y') :
    x * y * x⁻¹ * y⁻¹ = x * y' * x⁻¹ * y'⁻¹ := by
  set b := y⁻¹ * y' with hb
  have hbA : b ∈ A := inv_mul_mem_A c hs hy hy' h
  have hy'b : y' = y * b := by rw [hb, mul_inv_cancel_left]
  have hxb : x * b * x⁻¹ * b⁻¹ = 1 := by
    rw [← hs.comm_of_mem_A hbA hx, mul_inv_cancel_right, mul_inv_cancel]
  rw [hy'b, commutator_mul_right', hxb, mul_one, mul_inv_cancel, mul_one]

theorem commutator_mem_E {x y : G} (hx : x ∈ A') (hy : y ∈ A') :
    x * y * x⁻¹ * y⁻¹ ∈ E θ c.hn8 := by
  have hc := commutator_mem_A c hs hx hy
  refine hs.datum.mem_E_of_conj_eq hc ?_
  obtain ⟨b, hb, hbx⟩ := exists_conj_z_eq c hs hx
  obtain ⟨b', hb', hby⟩ := exists_conj_z_eq c hs hy
  have e : z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ =
      (z * x * z⁻¹) * (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ * (z * y * z⁻¹)⁻¹ := by group
  rw [e, hbx, hby]
  have h1 : b * x * (b' * y) * (b * x)⁻¹ * (b' * y)⁻¹ =
      (b * b' * b⁻¹ * b'⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
    have hbx' := hs.comm_of_mem_A hb hx
    have hby' := hs.comm_of_mem_A hb hy
    have hb'x := hs.comm_of_mem_A hb' hx
    have hb'y := hs.comm_of_mem_A hb' hy
    calc b * x * (b' * y) * (b * x)⁻¹ * (b' * y)⁻¹
        = b * (x * b') * y * x⁻¹ * b⁻¹ * y⁻¹ * b'⁻¹ := by group
      _ = b * (b' * x) * y * x⁻¹ * b⁻¹ * y⁻¹ * b'⁻¹ := by rw [hb'x]
      _ = b * b' * (x * y * x⁻¹) * (b⁻¹ * y⁻¹) * b'⁻¹ := by group
      _ = b * b' * (x * y * x⁻¹) * (y⁻¹ * b⁻¹) * b'⁻¹ := by
          rw [show b⁻¹ * y⁻¹ = y⁻¹ * b⁻¹ by
            rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hby']]
      _ = b * b' * ((x * y * x⁻¹ * y⁻¹) * b⁻¹) * b'⁻¹ := by group
      _ = b * b' * (b⁻¹ * (x * y * x⁻¹ * y⁻¹)) * b'⁻¹ := by
          rw [(hs.comm_of_mem_A (inv_mem hb)
            (hs.A_le_A' hc)).symm]
      _ = b * b' * b⁻¹ * ((x * y * x⁻¹ * y⁻¹) * b'⁻¹) := by group
      _ = b * b' * b⁻¹ * (b'⁻¹ * (x * y * x⁻¹ * y⁻¹)) := by
          rw [(hs.comm_of_mem_A (inv_mem hb') (hs.A_le_A' hc)).symm]
      _ = (b * b' * b⁻¹ * b'⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
  rw [h1, hs.datum.comm hb hb', mul_assoc b', mul_inv_cancel, mul_one, mul_inv_cancel, one_mul]

variable (hcov : ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ KA L z A', ∀ v : Fin 3 → ZMod 2,
  g * epsV θ c.hn8 v * g⁻¹ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
include hcov

theorem comm {x y : G} (hx : x ∈ A') (hy : y ∈ A') : x * y = y * x := by
  classical
  choose X hXA hXβ using fun v : Fin 3 → ZMod 2 =>
    hs.onto (epsV θ c.hn8 v) (epsV_mem_E θ c.hn8 v)
  choose cf hcf using fun v w : Fin 3 → ZMod 2 =>
    (mem_E_iff_epsV θ c.hn8 _).1 (commutator_mem_E c hs (hXA v) (hXA w))
  have hcentral : ∀ a ∈ A, ∀ x ∈ A', x * a * x⁻¹ = a := fun a ha x hx => by
    rw [← hs.comm_of_mem_A ha hx, mul_inv_cancel_right]
  have hβprod : ∀ u v, betaHat k z (X u * X v) = betaHat k z (X (u + v)) := fun u v => by
    rw [betaHat_mul' c hs (hXA u) (hXA v), hXβ, hXβ, hXβ, epsV_add]
  have hl : ∀ u v w, cf (u + v) w = cf u w + cf v w := by
    intro u v w
    apply epsV_injective θ c.hn8
    rw [hcf, ← commutator_eq_of_betaHat_left c hs (mul_mem (hXA u) (hXA v)) (hXA (u + v)) (hXA w)
      (hβprod u v), commutator_mul_left',
      hcentral _ (commutator_mem_A c hs (hXA v) (hXA w)) _ (hXA u), epsV_add, hcf, hcf]
    exact E_comm θ c.hn8 (commutator_mem_E c hs (hXA v) (hXA w))
      (commutator_mem_E c hs (hXA u) (hXA w))
  have hr : ∀ u v w, cf u (v + w) = cf u v + cf u w := by
    intro u v w
    apply epsV_injective θ c.hn8
    rw [hcf, ← commutator_eq_of_betaHat_right c hs (hXA u) (mul_mem (hXA v) (hXA w)) (hXA (v + w))
      (hβprod v w), commutator_mul_right',
      hcentral _ (commutator_mem_A c hs (hXA u) (hXA w)) _ (hXA v), epsV_add, hcf, hcf]
  have ha : ∀ v, cf v v = 0 := by
    intro v
    apply epsV_injective θ c.hn8
    rw [hcf, epsV_zero, mul_inv_cancel_right, mul_inv_cancel]
  have heqv : ∀ M : GL (Fin 3) (ZMod 2), ∀ v w,
      cf ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
        (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ cf v w := by
    intro M v w
    obtain ⟨κ, hκ, hκv⟩ := hcov M
    have hκN := KA_le_normalizer hκ
    have hκz : κ * z = z * κ := mem_centralizer_singleton_iff.1 (KA_le_centralizer hκ)
    have hκx : ∀ u, κ * X u * κ⁻¹ ∈ A' := fun u => (mem_normalizer_iff.1 hκN _).1 (hXA u)
    have hκβ : ∀ u, betaHat k z (κ * X u * κ⁻¹) =
        betaHat k z (X ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u)) := fun u => by
      rw [betaHat_conj_of_comm hκz, hXβ, hκv, hXβ]
    apply epsV_injective θ c.hn8
    rw [hcf, ← hκv, hcf, ← commutator_conj',
      ← commutator_eq_of_betaHat_left c hs (hκx v) (hXA _) (hXA _) (hκβ v),
      ← commutator_eq_of_betaHat_right c hs (hκx v) (hκx w) (hXA _) (hκβ w)]
  have h0 := M3 cf hl hr ha (heqv x2G) (heqv y2G)
  obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ c.hn8 _).1 (betaHat_mem_E' c hs hx)
  obtain ⟨w, hw⟩ := (mem_E_iff_epsV θ c.hn8 _).1 (betaHat_mem_E' c hs hy)
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [commutator_eq_of_betaHat_left c hs hx (hXA v) hy (by rw [hXβ, hv]),
      commutator_eq_of_betaHat_right c hs (hXA v) hy (hXA w) (by rw [hXβ, hw]), ← hcf, h0,
      epsV_zero]
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem gamma_mem_E {x : G} (hx : x ∈ A') : x * (z * x * z⁻¹) ∈ E θ c.hn8 := by
  have hzx := conj_mem_A' c hs hx
  have hΓA : x * (z * x * z⁻¹) ∈ A' := mul_mem hx hzx
  have hzz := z_mul_self c
  have hzi := z_inv c
  have hΓz : x * (z * x * z⁻¹) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hcomm := comm c hs hcov hx hzx
    calc x * (z * x * z⁻¹) * z = x * z * x := by group
      _ = (z * z) * x * z⁻¹ * x := by rw [hzz, one_mul, hzi]
      _ = z * ((z * x * z⁻¹) * x) := by group
      _ = z * (x * (z * x * z⁻¹)) := by rw [hcomm]
  obtain ⟨j, hj⟩ := hs.isPGroup_A' ⟨_, hΓA⟩
  have hj' : (x * (z * x * z⁻¹)) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hB := mem_of_two_pow_RA c (hs.A'_le_RA hΓA) hΓz hj'
  obtain ⟨i, hi | hi⟩ := (N0.mem_B0_iff c.hn8 c _).1 hB
  · rw [hi]
    exact N0.eps_mem_E θ c.hn8 i
  · exfalso
    apply hs.z_not_mem_A'
    have he : N0.eps θ c.hn8 i ∈ A' := hs.A_le_A' (hs.datum.E_le (N0.eps_mem_E θ c.hn8 i))
    rw [show z = (z * N0.eps θ c.hn8 i) * (N0.eps θ c.hn8 i)⁻¹ by group, ← hi]
    exact mul_mem hΓA (inv_mem he)

theorem betaHat_eq_pow {x : G} (hx : x ∈ A') : betaHat k z x = x ^ 2 ^ k := by
  have hk := hs.datum.two_le
  have hzx := conj_mem_A' c hs hx
  set γ := x * (z * x * z⁻¹) with hγ
  have hγE : γ ∈ E θ c.hn8 := gamma_mem_E c hs hcov hx
  have hγA' : γ ∈ A' := mul_mem hx hzx
  have hγ2 : γ * γ = 1 := by rw [← sq]; exact sq_eq_one_of_mem_E θ c.hn8 hγE
  have hβ : x * z * x⁻¹ * z⁻¹ = x ^ 2 * γ := by
    have hzx' : z * x⁻¹ * z⁻¹ = γ⁻¹ * x := by rw [hγ]; group
    have hcγ : Commute x γ⁻¹ := comm c hs hcov hx (inv_mem hγA')
    rw [show x * z * x⁻¹ * z⁻¹ = x * (z * x⁻¹ * z⁻¹) by group, hzx', ← mul_assoc,
      hcγ.eq, mul_assoc, ← sq, inv_eq_of_mul_eq_one_right hγ2]
    exact (comm c hs hcov hγA' (pow_mem hx 2))
  rw [betaHat, hβ, (Commute.mul_pow (comm c hs hcov (pow_mem hx 2) hγA') _), ← pow_mul,
    ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 1 := ⟨k - 2, by omega⟩
  rw [hj, pow_succ', pow_mul, sq, hγ2, one_pow, mul_one]

theorem sq_mem_A {x : G} (hx : x ∈ A') : x ^ 2 ∈ A := by
  refine hs.ker _ (pow_mem hx 2) ?_
  rw [sq, betaHat_mul' c hs hx hx, ← sq]
  exact sq_eq_one_of_mem_E θ c.hn8 (betaHat_mem_E' c hs hx)

theorem exists_sq_eq {a : G} (ha : a ∈ A) : ∃ x ∈ A', x ^ 2 = a := by
  have hk := hs.datum.two_le
  let f : A' →* A' := MonoidHom.mk' (fun x => x ^ 2) fun x y => by
    have hxy : Commute x y := Subtype.ext (comm c hs hcov x.2 y.2)
    exact hxy.mul_pow 2
  have hker : ∀ x : A', x ∈ f.ker → (x : G) ∈ E θ c.hn8 := by
    intro x hx
    have hx2 : (x : G) ^ 2 = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [f] using this
    have hxA : (x : G) ∈ A := by
      refine hs.ker _ x.2 ?_
      rw [betaHat_eq_pow c hs hcov x.2]
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hj, pow_succ', pow_mul, hx2, one_pow]
    exact (hs.datum.mem_E_iff_sq_eq_one hxA).2 hx2
  have hcardker : Nat.card f.ker ≤ 8 := by
    have hinj : Function.Injective (fun x : f.ker => (⟨(x : A'), hker x x.2⟩ : E θ c.hn8)) := by
      intro x y hxy
      have h1 : ((x : A') : G) = ((y : A') : G) := congrArg (fun e : E θ c.hn8 => (e : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [card_E] at this
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hs.card_A'] at hcard
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hrange : Nat.card A ≤ Nat.card f.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card f.ker * Nat.card f.range < 8 * Nat.card A := by
      calc Nat.card f.ker * Nat.card f.range ≤ 8 * Nat.card f.range :=
            Nat.mul_le_mul_right _ hcardker
        _ < 8 * Nat.card A := by omega
    omega
  set B := f.range.map A'.subtype with hB
  have hBA : B ≤ A := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact sq_mem_A c hs hcov x.2
  have hBc : Nat.card B = Nat.card f.range := card_map_of_injective A'.subtype_injective
  have hBeq : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hBc]; exact hrange)
  rw [← hBeq] at ha
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := ha
  exact ⟨x, x.2, rfl⟩

theorem levelDatum_succ : LevelDatum θ c.hn8 z (k + 1) A' := by
  have hk := hs.datum.two_le
  obtain ⟨ι, hι⟩ := hs.datum.exists_ecoords
  obtain ⟨ι', hι'⟩ := coords_of_sq hι (fun x hx y hy => comm c hs hcov hx hy)
    (fun a ha => exists_sq_eq c hs hcov ha) hs.card_A'
  have hcov' : ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ normalizer (A' : Set G) ⊓
      centralizer ({z} : Set G), ∀ v, g * epsV θ c.hn8 v * g⁻¹ =
        epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := fun M => by
    obtain ⟨g, hg, hgv⟩ := hcov M
    exact ⟨g, (Subgroup.mem_inf.1 hg).1, hgv⟩
  have hzact := zact_of_M1 hι' (fun x hx => conj_mem_A' c hs hx)
    (fun x hx => gamma_mem_E c hs hcov hx)
    (x2 := x2G) (y2 := y2G) M1 hcov'
  refine ⟨by omega, hs.datum.E_le.trans hs.A_le_A', ⟨ι', hι'.toAdd_eps⟩, ?_, hcov⟩
  rcases hzact with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by omega, h1⟩

end StepData

theorem g2Step_of_cover (hcov : StepCover) : G2Step := by
  intro G _ _ L Q n θ z c k A h hT
  obtain ⟨P, A', hs⟩ := exists_stepData c h hT
  refine ⟨A', StepData.levelDatum_succ c hs (hcov G L Q n θ z c k A P A' hs), ?_⟩
  rw [hs.card_A']
  have : 0 < Nat.card A := Nat.card_pos
  omega

end CFSG.OddStandard.AltStdSmall4.G2
