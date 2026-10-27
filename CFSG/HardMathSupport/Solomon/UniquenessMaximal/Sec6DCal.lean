module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DHeis

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremB

variable {Q : Type*} [Group Q]

structure Class2 (R C : Subgroup Q) : Prop where
  le : C ≤ R
  central : ∀ c ∈ C, ∀ r ∈ R, c * r = r * c
  comm_mem : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ C

namespace Class2

variable {R C : Subgroup Q} (h : Class2 R C)
include h

theorem comm_comm {x y x' y' : Q} (hx : x ∈ R) (hy : y ∈ R) (hx' : x' ∈ R) (hy' : y' ∈ R) :
    ⁅x, y⁆ * ⁅x', y'⁆ = ⁅x', y'⁆ * ⁅x, y⁆ :=
  h.central _ (h.comm_mem x hx y hy) _ (h.le (h.comm_mem x' hx' y' hy'))

theorem conj_comm {x y z : Q} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
    z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
  have := h.central _ (h.comm_mem x hx y hy) z hz
  calc z * ⁅x, y⁆ * z⁻¹ = (z * ⁅x, y⁆) * z⁻¹ := rfl
    _ = (⁅x, y⁆ * z) * z⁻¹ := by rw [← this]
    _ = ⁅x, y⁆ := by group

theorem mul_left {x y z : Q} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have e : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, h.conj_comm hy hz hx]
  exact h.comm_comm hy hz hx hz

theorem mul_right {x y z : Q} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, h.conj_comm hx hz hy]

theorem inv_left {x z : Q} (hx : x ∈ R) (hz : z ∈ R) : ⁅x⁻¹, z⁆ = ⁅x, z⁆⁻¹ := by
  have := h.mul_left hx (R.inv_mem hx) hz
  rw [mul_inv_cancel] at this
  have h1 : ⁅(1 : Q), z⁆ = 1 := by simp [commutatorElement_def]
  rw [h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem inv_right {x z : Q} (hx : x ∈ R) (hz : z ∈ R) : ⁅x, z⁻¹⁆ = ⁅x, z⁆⁻¹ := by
  have := h.mul_right hx hz (R.inv_mem hz)
  rw [mul_inv_cancel] at this
  have h1 : ⁅x, (1 : Q)⁆ = 1 := by simp [commutatorElement_def]
  rw [h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem pow_left {x z : Q} (hx : x ∈ R) (hz : z ∈ R) (n : ℕ) : ⁅x ^ n, z⁆ = ⁅x, z⁆ ^ n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ n ih =>
    rw [pow_succ, h.mul_left (R.pow_mem hx n) hx hz, ih, pow_succ]

theorem pow_right {x z : Q} (hx : x ∈ R) (hz : z ∈ R) (n : ℕ) : ⁅x, z ^ n⁆ = ⁅x, z⁆ ^ n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ n ih =>
    rw [pow_succ, h.mul_right hx (R.pow_mem hz n) hz, ih, pow_succ]

theorem zpow_left {x z : Q} (hx : x ∈ R) (hz : z ∈ R) (n : ℤ) : ⁅x ^ n, z⁆ = ⁅x, z⁆ ^ n := by
  cases n with
  | ofNat n => simpa using h.pow_left hx hz n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, h.inv_left (R.pow_mem hx _) hz, h.pow_left hx hz]

theorem zpow_right {x z : Q} (hx : x ∈ R) (hz : z ∈ R) (n : ℤ) : ⁅x, z ^ n⁆ = ⁅x, z⁆ ^ n := by
  cases n with
  | ofNat n => simpa using h.pow_right hx hz n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, h.inv_right hx (R.pow_mem hz _), h.pow_right hx hz]

end Class2

theorem commutatorElement_inv' {x y : Q} : ⁅x, y⁆⁻¹ = ⁅y, x⁆ := by
  simp only [commutatorElement_def]; group

@[expose] def cj (σ : Q) (R : Subgroup Q) : Subgroup Q := R.map (MulAut.conj σ).toMonoidHom

theorem mem_cj {σ : Q} {R : Subgroup Q} {y : Q} : y ∈ cj σ R ↔ σ⁻¹ * y * σ ∈ R := by
  unfold cj
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : σ⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj σ)) x * σ = x := by
      simp [MulAut.conj_apply]; group
    rw [e]; exact hx
  · intro h
    exact ⟨σ⁻¹ * y * σ, h, by simp [MulAut.conj_apply]; group⟩

theorem conj_mem_cj {σ : Q} {R : Subgroup Q} {x : Q} (hx : x ∈ R) : σ * x * σ⁻¹ ∈ cj σ R := by
  rw [mem_cj]
  have e : σ⁻¹ * (σ * x * σ⁻¹) * σ = x := by group
  rw [e]; exact hx

theorem card_cj (σ : Q) (R : Subgroup Q) : Nat.card (cj σ R) = Nat.card R :=
  Subgroup.card_map_of_injective (MulAut.conj σ).injective

theorem Zc_cj (σ : Q) (R : Subgroup Q) : Zc (cj σ R) = cj σ (Zc R) := by
  ext z
  simp only [mem_Zc, mem_cj]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun r hr => ?_⟩
    have := hc (σ * r * σ⁻¹) (by
      have e : σ⁻¹ * (σ * r * σ⁻¹) * σ = r := by group
      rw [e]; exact hr)
    have h2 : σ⁻¹ * z * σ * r = r * (σ⁻¹ * z * σ) := by
      calc σ⁻¹ * z * σ * r = σ⁻¹ * (z * (σ * r * σ⁻¹)) * σ := by group
        _ = σ⁻¹ * ((σ * r * σ⁻¹) * z) * σ := by rw [this]
        _ = r * (σ⁻¹ * z * σ) := by group
    exact h2
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun r hr => ?_⟩
    have := hc (σ⁻¹ * r * σ) hr
    calc z * r = σ * (σ⁻¹ * z * σ * (σ⁻¹ * r * σ)) * σ⁻¹ := by group
      _ = σ * ((σ⁻¹ * r * σ) * (σ⁻¹ * z * σ)) * σ⁻¹ := by rw [this]
      _ = r * z := by group

theorem IsThreeOnePlusTwo.cj {σ : Q} {R : Subgroup Q} (h : IsThreeOnePlusTwo R) :
    IsThreeOnePlusTwo (cj σ R) := by
  obtain ⟨⟨r, hr, s, hs, hne⟩, hcard, hexp⟩ := h
  refine ⟨⟨σ * r * σ⁻¹, conj_mem_cj hr, σ * s * σ⁻¹, conj_mem_cj hs, ?_⟩, by rw [card_cj, hcard], ?_⟩
  · intro h2
    apply hne
    have : σ * (r * s) * σ⁻¹ = σ * (s * r) * σ⁻¹ := by
      calc σ * (r * s) * σ⁻¹ = σ * r * σ⁻¹ * (σ * s * σ⁻¹) := by group
        _ = σ * s * σ⁻¹ * (σ * r * σ⁻¹) := h2
        _ = σ * (s * r) * σ⁻¹ := by group
    simpa using this
  · intro g hg
    rw [mem_cj] at hg
    have := hexp _ hg
    have h3 : (σ⁻¹ * g * σ) ^ 3 = σ⁻¹ * g ^ 3 * σ := by
      have := conj_pow (a := σ⁻¹) (b := g) (i := 3)
      simpa using this
    rw [h3] at this
    have h4 : g ^ 3 = σ * (σ⁻¹ * g ^ 3 * σ) * σ⁻¹ := by group
    rw [h4, this]; group


structure Comm3 (R₁ R₂ R₃ : Subgroup Q) : Prop where
  c12 : ∀ r ∈ R₁, ∀ s ∈ R₂, r * s = s * r
  c13 : ∀ r ∈ R₁, ∀ s ∈ R₃, r * s = s * r
  c23 : ∀ r ∈ R₂, ∀ s ∈ R₃, r * s = s * r

namespace Comm3

variable {R₁ R₂ R₃ : Subgroup Q} (h : Comm3 R₁ R₂ R₃)
include h

@[expose] def prod3 : (↥R₁ × ↥R₂ × ↥R₃) →* Q where
  toFun p := (p.1 : Q) * (p.2.1 : Q) * (p.2.2 : Q)
  map_one' := by simp
  map_mul' p q := by
    obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩⟩ := p
    obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩⟩ := q
    have e1 : y₁ * x₂ = x₂ * y₁ := (h.c12 y₁ hy₁ x₂ hx₂)
    have e2 : y₁ * x₃ = x₃ * y₁ := (h.c13 y₁ hy₁ x₃ hx₃)
    have e3 : y₂ * x₃ = x₃ * y₂ := (h.c23 y₂ hy₂ x₃ hx₃)
    show x₁ * y₁ * (x₂ * y₂) * (x₃ * y₃) = x₁ * x₂ * x₃ * (y₁ * y₂ * y₃)
    calc x₁ * y₁ * (x₂ * y₂) * (x₃ * y₃)
        = x₁ * (y₁ * x₂) * (y₂ * x₃) * y₃ := by group
      _ = x₁ * (x₂ * y₁) * (x₃ * y₂) * y₃ := by rw [e1, e3]
      _ = x₁ * x₂ * (y₁ * x₃) * y₂ * y₃ := by group
      _ = x₁ * x₂ * (x₃ * y₁) * y₂ * y₃ := by rw [e2]
      _ = x₁ * x₂ * x₃ * (y₁ * y₂ * y₃) := by group

theorem comm_prod3 {x₁ y₁ x₂ y₂ x₃ y₃ : Q} (hx₁ : x₁ ∈ R₁) (hy₁ : y₁ ∈ R₁) (hx₂ : x₂ ∈ R₂)
    (hy₂ : y₂ ∈ R₂) (hx₃ : x₃ ∈ R₃) (hy₃ : y₃ ∈ R₃) :
    ⁅x₁ * x₂ * x₃, y₁ * y₂ * y₃⁆ = ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * ⁅x₃, y₃⁆ := by
  have := map_commutatorElement h.prod3 (⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩)
    (⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩)
  simpa [prod3, commutatorElement_def] using this.symm

theorem mem_sup3 {g : Q} (hg : g ∈ R₁ ⊔ R₂ ⊔ R₃) :
    ∃ g₁ ∈ R₁, ∃ g₂ ∈ R₂, ∃ g₃ ∈ R₃, g = g₁ * g₂ * g₃ := by
  have h12 : R₁ ≤ Subgroup.centralizer (R₂ : Set Q) := fun r hr s hs => (h.c12 r hr s hs).symm
  have h123 : R₁ ⊔ R₂ ≤ Subgroup.centralizer (R₃ : Set Q) := by
    refine sup_le (fun r hr s hs => (h.c13 r hr s hs).symm) (fun r hr s hs => (h.c23 r hr s hs).symm)
  obtain ⟨u, hu, g₃, hg₃, rfl⟩ := exists_mul_of_mem_sup h123 hg
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_mul_of_mem_sup h12 hu
  exact ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, rfl⟩

theorem prod_eq_one {t₁ t₂ t₃ : Q} (ht₁ : t₁ ∈ R₁) (ht₂ : t₂ ∈ R₂) (ht₃ : t₃ ∈ R₃)
    (hprod : t₁ * t₂ * t₃ = 1) : t₁ ∈ Zc R₁ ∧ t₂ ∈ Zc R₂ ∧ t₃ ∈ Zc R₃ := by
  have e1 : t₁ = (t₂ * t₃)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← mul_assoc]; exact hprod
  have e2 : t₂ = t₁⁻¹ * t₃⁻¹ := by
    calc t₂ = t₁⁻¹ * (t₁ * t₂ * t₃) * t₃⁻¹ := by group
      _ = t₁⁻¹ * t₃⁻¹ := by rw [hprod]; group
  have e3 : t₃ = (t₁ * t₂)⁻¹ := by
    calc t₃ = (t₁ * t₂)⁻¹ * (t₁ * t₂ * t₃) := by group
      _ = (t₁ * t₂)⁻¹ := by rw [hprod]; group
  refine ⟨mem_Zc.2 ⟨ht₁, fun r hr => ?_⟩, mem_Zc.2 ⟨ht₂, fun r hr => ?_⟩,
    mem_Zc.2 ⟨ht₃, fun r hr => ?_⟩⟩
  · have hu : Commute (t₂ * t₃) r :=
      Commute.mul_left (h.c12 r hr t₂ ht₂).symm (h.c13 r hr t₃ ht₃).symm
    rw [e1]
    exact hu.inv_left.eq
  · have hu : Commute (t₁⁻¹ * t₃⁻¹) r :=
      Commute.mul_left (Commute.inv_left (show Commute t₁ r from h.c12 t₁ ht₁ r hr))
        (Commute.inv_left (show Commute t₃ r from (h.c23 r hr t₃ ht₃).symm))
    rw [e2]
    exact hu.eq
  · have hu : Commute (t₁ * t₂) r :=
      Commute.mul_left (h.c13 t₁ ht₁ r hr : Commute t₁ r) (h.c23 t₂ ht₂ r hr : Commute t₂ r)
    rw [e3]
    exact hu.inv_left.eq

theorem unique_decomp {x₁ x₂ x₃ y₁ y₂ y₃ : Q} (hx₁ : x₁ ∈ R₁) (hx₂ : x₂ ∈ R₂) (hx₃ : x₃ ∈ R₃)
    (hy₁ : y₁ ∈ R₁) (hy₂ : y₂ ∈ R₂) (hy₃ : y₃ ∈ R₃) (heq : x₁ * x₂ * x₃ = y₁ * y₂ * y₃) :
    x₁⁻¹ * y₁ ∈ Zc R₁ ∧ x₂⁻¹ * y₂ ∈ Zc R₂ ∧ x₃⁻¹ * y₃ ∈ Zc R₃ := by
  have hp := h.prod3.map_mul
  have key : (x₁⁻¹ * y₁) * (x₂⁻¹ * y₂) * (x₃⁻¹ * y₃) = 1 := by
    have := h.prod3.map_mul (⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩)⁻¹ (⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩)
    rw [map_inv] at this
    have h1 : h.prod3 (⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩) = h.prod3 (⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩) := heq
    rw [h1, inv_mul_cancel] at this
    simpa [prod3] using this
  exact h.prod_eq_one (R₁.mul_mem (R₁.inv_mem hx₁) hy₁) (R₂.mul_mem (R₂.inv_mem hx₂) hy₂)
    (R₃.mul_mem (R₃.inv_mem hx₃) hy₃) key

end Comm3


theorem cj_cj_cj {σ : Q} (h3 : σ ^ 3 = 1) (R : Subgroup Q) : cj σ (cj σ (cj σ R)) = R := by
  ext y
  simp only [mem_cj]
  have e : σ⁻¹ * (σ⁻¹ * (σ⁻¹ * y * σ) * σ) * σ = y := by
    have h3' : σ⁻¹ * σ⁻¹ * σ⁻¹ = 1 := by
      have : σ * σ * σ = 1 := by simpa [pow_succ] using h3
      calc σ⁻¹ * σ⁻¹ * σ⁻¹ = (σ * σ * σ)⁻¹ := by group
        _ = 1 := by rw [this]; simp
    calc σ⁻¹ * (σ⁻¹ * (σ⁻¹ * y * σ) * σ) * σ = (σ⁻¹ * σ⁻¹ * σ⁻¹) * y * (σ * σ * σ) := by group
      _ = y := by
        have : σ * σ * σ = 1 := by simpa [pow_succ] using h3
        rw [h3', this]; simp
  rw [e]

theorem commute_cj {σ : Q} {A B : Subgroup Q} (h : ∀ r ∈ A, ∀ s ∈ B, r * s = s * r) :
    ∀ r ∈ cj σ A, ∀ s ∈ cj σ B, r * s = s * r := by
  intro r hr s hs
  rw [mem_cj] at hr hs
  have := h _ hr _ hs
  calc r * s = σ * ((σ⁻¹ * r * σ) * (σ⁻¹ * s * σ)) * σ⁻¹ := by group
    _ = σ * ((σ⁻¹ * s * σ) * (σ⁻¹ * r * σ)) * σ⁻¹ := by rw [this]
    _ = s * r := by group

theorem commute_of_mul_commute {a u r : Q} (hu : Commute u r) (h : Commute (a * u) r) :
    Commute a r := by
  have := h.mul_left hu.inv_left
  simpa using this

structure Triple (σ : Q) (R₁ : Subgroup Q) : Prop where
  heis : IsThreeOnePlusTwo R₁
  pow3 : σ ^ 3 = 1
  c12 : ∀ r ∈ R₁, ∀ s ∈ cj σ R₁, r * s = s * r

namespace Triple

variable {σ : Q} {R₁ : Subgroup Q} (h : Triple σ R₁)
include h

theorem comm3 : Comm3 R₁ (cj σ R₁) (cj σ (cj σ R₁)) := by
  have c23 := commute_cj (σ := σ) h.c12
  refine ⟨h.c12, ?_, c23⟩
  have c31 := commute_cj (σ := σ) c23
  rw [cj_cj_cj h.pow3] at c31
  intro r hr s hs
  exact (c31 s hs r hr).symm

theorem heis₂ : IsThreeOnePlusTwo (cj σ R₁) := h.heis.cj
theorem heis₃ : IsThreeOnePlusTwo (cj σ (cj σ R₁)) := h.heis.cj.cj

@[expose] def R (σ : Q) (R₁ : Subgroup Q) : Subgroup Q := R₁ ⊔ cj σ R₁ ⊔ cj σ (cj σ R₁)

@[expose] def W (σ : Q) (R₁ : Subgroup Q) : Subgroup Q :=
  Zc R₁ ⊔ Zc (cj σ R₁) ⊔ Zc (cj σ (cj σ R₁))

omit h in
theorem centralizes_R {z : Q} (hA : ∀ y ∈ R₁, z * y = y * z) (hB : ∀ y ∈ cj σ R₁, z * y = y * z)
    (hC : ∀ y ∈ cj σ (cj σ R₁), z * y = y * z) : ∀ y ∈ R σ R₁, z * y = y * z := by
  have : R σ R₁ ≤ Subgroup.centralizer ({z} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]; exact (hA y hy).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]; exact (hB y hy).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]; exact (hC y hy).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm

theorem W_central : ∀ c ∈ W σ R₁, ∀ r ∈ R σ R₁, c * r = r * c := by
  have hc := h.comm3
  have key : ∀ (S : Subgroup Q), (∀ z ∈ S, ∀ y ∈ R σ R₁, z * y = y * z) →
      ∀ c ∈ S, ∀ r ∈ R σ R₁, c * r = r * c := fun S hS => hS
  have h1 : ∀ z ∈ Zc R₁, ∀ y ∈ R σ R₁, z * y = y * z := fun z hz => by
    have hz' := mem_Zc.1 hz
    exact centralizes_R (σ := σ) (R₁ := R₁) hz'.2 (fun y hy => hc.c12 z hz'.1 y hy) (fun y hy => hc.c13 z hz'.1 y hy)
  have h2 : ∀ z ∈ Zc (cj σ R₁), ∀ y ∈ R σ R₁, z * y = y * z := fun z hz => by
    have hz' := mem_Zc.1 hz
    exact centralizes_R (σ := σ) (R₁ := R₁) (fun y hy => (hc.c12 y hy z hz'.1).symm) hz'.2
      (fun y hy => hc.c23 z hz'.1 y hy)
  have h3 : ∀ z ∈ Zc (cj σ (cj σ R₁)), ∀ y ∈ R σ R₁, z * y = y * z := fun z hz => by
    have hz' := mem_Zc.1 hz
    exact centralizes_R (σ := σ) (R₁ := R₁) (fun y hy => (hc.c13 y hy z hz'.1).symm)
      (fun y hy => (hc.c23 y hy z hz'.1).symm) hz'.2
  have hW : W σ R₁ ≤ Subgroup.centralizer ((R σ R₁ : Subgroup Q) : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro z hz; rw [Subgroup.mem_centralizer_iff]; intro r hr; exact (h1 z hz r hr).symm
    · intro z hz; rw [Subgroup.mem_centralizer_iff]; intro r hr; exact (h2 z hz r hr).symm
    · intro z hz; rw [Subgroup.mem_centralizer_iff]; intro r hr; exact (h3 z hz r hr).symm
  intro c hc' r hr
  exact (Subgroup.mem_centralizer_iff.1 (hW hc') r hr).symm

omit h in
theorem W_le_R : W σ R₁ ≤ R σ R₁ :=
  sup_le_sup (sup_le_sup (Zc_le _) (Zc_le _)) (Zc_le _)

theorem class2 : Class2 (R σ R₁) (W σ R₁) := by
  have hc := h.comm3
  refine ⟨(W_le_R (σ := σ) (R₁ := R₁)), h.W_central, ?_⟩
  intro x hx y hy
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, rfl⟩ := hc.mem_sup3 hx
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, rfl⟩ := hc.mem_sup3 hy
  rw [hc.comm_prod3 hx₁ hy₁ hx₂ hy₂ hx₃ hy₃]
  have m1 : ⁅x₁, y₁⁆ ∈ W σ R₁ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (h.heis.comm_mem_Zc hx₁ hy₁))
  have m2 : ⁅x₂, y₂⁆ ∈ W σ R₁ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (h.heis₂.comm_mem_Zc hx₂ hy₂))
  have m3 : ⁅x₃, y₃⁆ ∈ W σ R₁ := Subgroup.mem_sup_right (h.heis₃.comm_mem_Zc hx₃ hy₃)
  exact (W σ R₁).mul_mem ((W σ R₁).mul_mem m1 m2) m3

theorem Zc_R : Zc (R σ R₁) = W σ R₁ := by
  have hc := h.comm3
  apply le_antisymm
  · intro z hz
    obtain ⟨hzR, hzc⟩ := mem_Zc.1 hz
    obtain ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, rfl⟩ := hc.mem_sup3 hzR
    have cz12 : Commute z₁ z₂ := hc.c12 z₁ hz₁ z₂ hz₂
    have cz13 : Commute z₁ z₃ := hc.c13 z₁ hz₁ z₃ hz₃
    have cz23 : Commute z₂ z₃ := hc.c23 z₂ hz₂ z₃ hz₃
    have in1 : z₁ ∈ Zc R₁ := by
      refine mem_Zc.2 ⟨hz₁, fun r hr => ?_⟩
      have hu : Commute (z₂ * z₃) r :=
        Commute.mul_left (hc.c12 r hr z₂ hz₂).symm (hc.c13 r hr z₃ hz₃).symm
      have h0 : Commute (z₁ * z₂ * z₃) r :=
        hzc r (Subgroup.mem_sup_left (Subgroup.mem_sup_left hr))
      have h1 : Commute (z₁ * (z₂ * z₃)) r := by rwa [← mul_assoc]
      exact (commute_of_mul_commute hu h1).eq
    have in2 : z₂ ∈ Zc (cj σ R₁) := by
      refine mem_Zc.2 ⟨hz₂, fun r hr => ?_⟩
      have hu : Commute (z₁ * z₃) r :=
        Commute.mul_left (hc.c12 z₁ hz₁ r hr) (hc.c23 r hr z₃ hz₃).symm
      have h0 : Commute (z₁ * z₂ * z₃) r :=
        hzc r (Subgroup.mem_sup_left (Subgroup.mem_sup_right hr))
      have h1 : Commute (z₂ * (z₁ * z₃)) r := by
        have : z₂ * (z₁ * z₃) = z₁ * z₂ * z₃ := by
          rw [← mul_assoc, ← cz12.eq]
        rw [this]; exact h0
      exact (commute_of_mul_commute hu h1).eq
    have in3 : z₃ ∈ Zc (cj σ (cj σ R₁)) := by
      refine mem_Zc.2 ⟨hz₃, fun r hr => ?_⟩
      have hu : Commute (z₁ * z₂) r :=
        Commute.mul_left (hc.c13 z₁ hz₁ r hr) (hc.c23 z₂ hz₂ r hr)
      have h0 : Commute (z₁ * z₂ * z₃) r :=
        hzc r (Subgroup.mem_sup_right hr)
      have h1 : Commute (z₃ * (z₁ * z₂)) r := by
        have : z₃ * (z₁ * z₂) = z₁ * z₂ * z₃ := (cz13.mul_left cz23).eq.symm
        rw [this]; exact h0
      exact (commute_of_mul_commute hu h1).eq
    exact (W σ R₁).mul_mem ((W σ R₁).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left in1))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right in2))) (Subgroup.mem_sup_right in3)
  · intro z hz
    exact mem_Zc.2 ⟨(W_le_R (σ := σ) (R₁ := R₁)) hz, fun r hr => (h.W_central z hz r hr)⟩

end Triple

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
