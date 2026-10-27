module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Class2
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Retract
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPart

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix
open scoped commutatorElement

section Torus

variable {K : Type} [Field K] [Finite K]

theorem exists_unit_pow_three_ne_one (h5 : 5 ≤ Nat.card K) : ∃ t : Kˣ, t ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun h3 => ?_⟩
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = Nat.card K - 1 := CFSG.SectionRank.OddCover.card_units_eq
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
  omega

end Torus

section Extension

variable {K : Type} [Field K] {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin 3) K}

@[expose] def Yhat (π : E →* SpecialLinearGroup (Fin 3) K) : Subgroup E := (Zsl K).comap π

@[expose] def Uhat (π : E →* SpecialLinearGroup (Fin 3) K) : Subgroup E := (Usl K).comap π

theorem mem_Yhat {y : E} : y ∈ Yhat π ↔ ∃ b : K, π y = uSL 0 b 0 := Iff.rfl

theorem mem_Uhat {g : E} : g ∈ Uhat π ↔ ∃ a b c : K, π g = uSL a b c := Iff.rfl

theorem commute_uSL_Zsl (a b c β : K) : Commute (uSL a b c) (uSL 0 β 0) := by
  change uSL a b c * uSL 0 β 0 = uSL 0 β 0 * uSL a b c
  rw [uSL_mul, uSL_mul]
  congr 1 <;> ring

theorem comm_Yhat_eq_one (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {s : E} (hs : π s ∈ Usl K) {t : Kˣ × Kˣ} (htc : tSL t * π s = π s * tSL t)
    (hν : (t.1 : K) ^ 2 * t.2 ≠ 1) : ∀ y ∈ Yhat π, ⁅s, y⁆ = 1 := by
  obtain ⟨h, hh⟩ := hπ (tSL t)
  obtain ⟨a, b, c, hsabc⟩ := hs
  have hconj : ∀ (y : E) (β : K), π y = uSL 0 β 0 →
      π (h * y * h⁻¹) = uSL 0 (((t.1 : K) ^ 2 * t.2) * β) 0 := by
    intro y β hy
    rw [map_mul, map_mul, map_inv, hh, hy, tSL_conj_uSL]
    simp
  refine comm_eq_one_of_conj_surj (s := s) (h := h) (Y := Yhat π) ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨β, hβ⟩ := hy
    refine comm_mem_center_of_commute_map hcen ?_
    rw [hsabc, hβ]
    exact commute_uSL_Zsl a b c β
  · intro y hy
    obtain ⟨β, hβ⟩ := hy
    exact ⟨_, hconj y β hβ⟩
  · refine comm_mem_center_of_commute_map hcen ?_
    change π h * π s = π s * π h
    rw [hh]
    exact htc
  · intro y hy
    obtain ⟨β, hβ⟩ := hy
    have hν1 : (t.1 : K) ^ 2 * t.2 - 1 ≠ 0 := sub_ne_zero.2 hν
    obtain ⟨y₁, hy₁⟩ := hπ (uSL 0 (β / ((t.1 : K) ^ 2 * t.2 - 1)) 0)
    have hv : π (h * y₁ * h⁻¹ * y₁⁻¹) = uSL 0 β 0 := by
      rw [map_mul, hconj y₁ _ hy₁, map_inv, hy₁, uSL_inv, uSL_mul]
      congr 1
      · simp
      · field_simp
        ring
      · simp
    have hw : y * (h * y₁ * h⁻¹ * y₁⁻¹)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hv, hβ, mul_inv_cancel]
    refine ⟨y₁, ⟨_, hy₁⟩, y * (h * y₁ * h⁻¹ * y₁⁻¹)⁻¹, ?_, by group⟩
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (hcen hw) s)

theorem commute_tSL_uSL_left (t₀ : Kˣ) (a : K) :
    tSL (t₀, t₀) * uSL a 0 0 = uSL a 0 0 * tSL (t₀, t₀) := by
  rw [tSL_mul_uSL]
  simp

theorem commute_tSL_uSL_right (t₀ : Kˣ) (c : K) :
    tSL (t₀⁻¹ ^ 2, t₀) * uSL 0 0 c = uSL 0 0 c * tSL (t₀⁻¹ ^ 2, t₀) := by
  rw [tSL_mul_uSL]
  simp

theorem Yhat_central [Finite K] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h5 : 5 ≤ Nat.card K) : ∀ y ∈ Yhat π, ∀ g ∈ Uhat π, ⁅g, y⁆ = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_three_ne_one h5
  have hne : (t₀ : K) ^ 3 ≠ 1 := fun h => ht₀ (Units.ext (by simpa using h))
  have h12 : ∀ (s : E) (a : K), π s = uSL a 0 0 → ∀ y ∈ Yhat π, ⁅s, y⁆ = 1 := by
    intro s a hs
    refine comm_Yhat_eq_one hπ hcen (t := (t₀, t₀)) (by rw [hs]; exact uSL_mem_Usl _ _ _)
      (by rw [hs]; exact commute_tSL_uSL_left t₀ a) ?_
    show (t₀ : K) ^ 2 * (t₀ : K) ≠ 1
    rw [show (t₀ : K) ^ 2 * (t₀ : K) = (t₀ : K) ^ 3 by ring]
    exact hne
  have h23 : ∀ (s : E) (c : K), π s = uSL 0 0 c → ∀ y ∈ Yhat π, ⁅s, y⁆ = 1 := by
    intro s c hs
    refine comm_Yhat_eq_one hπ hcen (t := (t₀⁻¹ ^ 2, t₀)) (by rw [hs]; exact uSL_mem_Usl _ _ _)
      (by rw [hs]; exact commute_tSL_uSL_right t₀ c) ?_
    have h0 : (t₀ : K) ≠ 0 := t₀.ne_zero
    show (((t₀⁻¹ ^ 2 : Kˣ) : K)) ^ 2 * (t₀ : K) ≠ 1
    rw [show (((t₀⁻¹ ^ 2 : Kˣ) : K)) ^ 2 * (t₀ : K) = ((t₀ : K) ^ 3)⁻¹ by
      simp; field_simp]
    exact fun h => hne (inv_eq_one.1 h)
  have hYY : ∀ y' ∈ Yhat π, ∀ y ∈ Yhat π, y * y' = y' * y := by
    intro y' hy' y hy
    obtain ⟨β', hβ'⟩ := hy'
    obtain ⟨σ₁, hσ₁⟩ := hπ (uSL β' 0 0)
    obtain ⟨σ₂, hσ₂⟩ := hπ (uSL 0 0 1)
    have hk : (⁅σ₁, σ₂⁆)⁻¹ * y' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, hσ₁, hσ₂, uSL_comm, hβ']
      simp
    have hy1 : Commute y σ₁ := (commutatorElement_eq_one_iff_mul_comm.1 (h12 σ₁ β' hσ₁ y hy)).symm
    have hy2 : Commute y σ₂ := (commutatorElement_eq_one_iff_mul_comm.1 (h23 σ₂ 1 hσ₂ y hy)).symm
    have hyc : Commute y ⁅σ₁, σ₂⁆ := by
      rw [commutatorElement_def]
      exact ((hy1.mul_right hy2).mul_right hy1.inv_right).mul_right hy2.inv_right
    have hyk : Commute y ((⁅σ₁, σ₂⁆)⁻¹ * y') := Subgroup.mem_center_iff.1 (hcen hk) y
    have hy' : y' = ⁅σ₁, σ₂⁆ * ((⁅σ₁, σ₂⁆)⁻¹ * y') := by group
    rw [hy']
    exact (hyc.mul_right hyk).eq
  intro y hy g hg
  obtain ⟨a, b, c, hg⟩ := hg
  obtain ⟨σ₁, hσ₁⟩ := hπ (uSL a 0 0)
  obtain ⟨σ₂, hσ₂⟩ := hπ (uSL 0 0 c)
  have hg₃ : (σ₁ * σ₂)⁻¹ * g ∈ Yhat π := by
    refine ⟨b - a * c, ?_⟩
    rw [map_mul, map_inv, map_mul, hσ₁, hσ₂, hg, uSL_mul, uSL_inv, uSL_mul]
    congr 1
    · ring
    · ring
    · ring
  have hy1 : Commute σ₁ y := commutatorElement_eq_one_iff_mul_comm.1 (h12 σ₁ a hσ₁ y hy)
  have hy2 : Commute σ₂ y := commutatorElement_eq_one_iff_mul_comm.1 (h23 σ₂ c hσ₂ y hy)
  have hy3 : Commute ((σ₁ * σ₂)⁻¹ * g) y := (hYY _ hg₃ y hy).symm
  have hgg : g = σ₁ * σ₂ * ((σ₁ * σ₂)⁻¹ * g) := by group
  rw [hgg]
  exact commutatorElement_eq_one_iff_mul_comm.2 ((hy1.mul_left hy2).mul_left hy3 |>.eq)

theorem Yhat_le_Uhat : Yhat π ≤ Uhat π := fun _ hy => Zsl_le_Usl hy

theorem ker_le_Yhat : π.ker ≤ Yhat π := fun c hc =>
  ⟨0, by rw [MonoidHom.mem_ker.1 hc, uSL_zero]⟩

theorem commutator_mem_Yhat {g h : E} (hg : g ∈ Uhat π) (hh : h ∈ Uhat π) :
    ⁅g, h⁆ ∈ Yhat π := by
  obtain ⟨a, b, c, hg⟩ := hg
  obtain ⟨a', b', c', hh⟩ := hh
  exact ⟨a * c' - a' * c, by rw [map_commutatorElement, hg, hh, uSL_comm]⟩

theorem conj_mem_Yhat {g y : E} {t : Kˣ × Kˣ} (hg : π g = tSL t) (hy : y ∈ Yhat π) :
    g * y * g⁻¹ ∈ Yhat π := by
  obtain ⟨β, hβ⟩ : ∃ β : K, π y = uSL 0 β 0 := hy
  refine ⟨((t.1 : K) ^ 2 * t.2) * β, ?_⟩
  rw [map_mul, map_mul, map_inv, hg, hβ, tSL_conj_uSL]
  simp

theorem exists_kappa [Finite K] [Finite E] {p f : ℕ} [hp : Fact p.Prime]
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    ∃ κ : E → E, (∀ y ∈ Yhat π, κ y ∈ π.ker) ∧
      (∀ y ∈ Yhat π, ∀ y' ∈ Yhat π, κ (y * y') = κ y * κ y') ∧ (∀ c ∈ π.ker, κ c = c) ∧
      ∀ (t : Kˣ × Kˣ) (g : E), π g = tSL t → ∀ y ∈ Yhat π, κ (g * y * g⁻¹) = κ y := by
  classical
  have := Fintype.ofFinite K
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_three_ne_one h5
  set ν : K := (t₀ : K) ^ 3 with hν
  have hν0 : ν ≠ 0 := pow_ne_zero 3 t₀.ne_zero
  have hν1 : ν ≠ 1 := fun h => ht₀ (Units.ext (by simpa [hν] using h))
  obtain ⟨z, hz⟩ := hπ (tSL (t₀, t₀))
  set m := Nat.card K - 1 with hm
  have hmK : Nat.Coprime m (Nat.card π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
    rw [hk]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_))
    intro hdvd
    have hpq : p ∣ Nat.card K := by rw [hK]; exact dvd_pow_self p (by omega)
    have := Nat.dvd_sub hpq hdvd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hconjpow : ∀ (i : ℕ) (y : E) (β : K), π y = uSL 0 β 0 →
      π (z ^ i * y * (z ^ i)⁻¹) = uSL 0 (ν ^ i * β) 0 := by
    intro i y β hy
    rw [map_mul, map_mul, map_inv, map_pow, hz, ← map_pow, hy, tSL_conj_uSL]
    simp only [Prod.pow_mk, Units.val_pow_eq_pow_val, mul_zero, hν]
    congr 1
    ring
  have hnorm : ∀ (n : ℕ) (y : E) (β : K), π y = uSL 0 β 0 →
      π (normSum z y n) = uSL 0 ((∑ i ∈ Finset.range n, ν ^ i) * β) 0 := by
    intro n y β hy
    induction n with
    | zero => simp [uSL_zero]
    | succ n ih =>
      rw [normSum_succ, map_mul, ih, hconjpow n y β hy, uSL_mul, Finset.sum_range_succ]
      congr 1 <;> ring
  have hgeom : ∑ i ∈ Finset.range m, ν ^ i = 0 := by
    have h1 := geom_sum_mul ν m
    have h2 : ν ^ m = 1 := by
      rw [hm, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one ν hν0
    rw [h2, sub_self] at h1
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hν1)
  have hN : ∀ y ∈ Yhat π, normSum z y m ∈ π.ker := by
    rintro y ⟨β, hβ⟩
    rw [MonoidHom.mem_ker, hnorm m y β hβ, hgeom, zero_mul, uSL_zero]
  have hYc : ∀ a ∈ Yhat π, ∀ b ∈ Yhat π, a * b = b * a := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.1
      (Yhat_central hπ hcen h5 b hb a (Yhat_le_Uhat ha))
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_retraction_fun (Y := Yhat π) (K := π.ker)
    ker_le_Yhat hcen hYc (z := z) (fun y hy => conj_mem_Yhat hz hy)
    (fun y hy => by
      simpa using conj_mem_Yhat (g := z⁻¹) (t := (t₀, t₀)⁻¹) (by rw [map_inv, hz, map_inv]) hy)
    hmK hN
  refine ⟨κ, hκK, hκmul, hκid, fun t g hg y hy => ?_⟩
  refine hκinv g (fun y hy => conj_mem_Yhat hg hy) (fun y _ => ?_) y hy
  refine conj_conj_comm_of_comm_mem_center (comm_mem_center_of_commute_map hcen ?_) y
  change π g * π z = π z * π g
  rw [hg, hz, ← map_mul, ← map_mul, mul_comm]

theorem commutator_Uhat_inf_ker_eq_bot [Finite K] [Finite E] {p f : ℕ} [Fact p.Prime]
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    ⁅Uhat π, Uhat π⁆ ⊓ π.ker = ⊥ := by
  classical
  obtain ⟨κ, hκK, hκmul, hκid, hκtor⟩ := exists_kappa hπ hcen hK hf h5 hker
  have hlift : ∀ v : K × K, ∃ g : E, π g = uSL v.1 0 v.2 := fun v => hπ _
  choose ℓ hℓ using hlift
  have hgood := exists_good_scalar h5
  refine commutator_inf_eq_bot_of_fun (Y := Yhat π) (fun g hg h hh => commutator_mem_Yhat hg hh)
    hκmul hκid ?_
  refine kappa_comm_eq_one (E := E) (G := Uhat π) (Y := Yhat π) Yhat_le_Uhat
    (Yhat_central hπ hcen h5) (fun g hg h hh => commutator_mem_Yhat hg hh) hκmul
    (fun y hy => hcen (hκK y hy)) (F := K) (V := K × K) hgood ℓ
    (fun v => ⟨v.1, 0, v.2, hℓ v⟩) ?_ ?_ ?_
  · rintro g ⟨a, b, c, hg⟩
    refine ⟨(a, c), (ℓ (a, c))⁻¹ * g, ⟨b, ?_⟩, by group⟩
    rw [map_mul, map_inv, hℓ, hg, uSL_inv, uSL_mul]
    congr 1 <;> ring
  · intro v w
    refine ⟨(ℓ v * ℓ w)⁻¹ * ℓ (v + w), ⟨-(v.1 * w.2), ?_⟩, by group⟩
    rw [map_mul, map_inv, map_mul, hℓ, hℓ, hℓ, uSL_mul, uSL_inv, uSL_mul]
    congr 1 <;> simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · intro a ha
    obtain ⟨g, hg⟩ := hπ (tSL (Units.mk0 a ha, 1))
    refine ⟨g, fun y hy => hκtor _ g hg y hy, fun v => ?_⟩
    refine ⟨(ℓ (a • v))⁻¹ * (g * ℓ v * g⁻¹), ?_, by group⟩
    have hk : (ℓ (a • v))⁻¹ * (g * ℓ v * g⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hg, hℓ, hℓ,
        tSL_conj_uSL]
      simp
    exact hcen hk

theorem sl3_ker_eq_bot_of_isPGroup [Finite K] [Finite E] [Group.IsPerfect E] {p f : ℕ}
    [Fact p.Prime] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    π.ker = ⊥ :=
  ker_eq_bot_of_commutator_inf_eq_bot π hπ hcen hker (isPGroup_Usl hK) (not_dvd_index_Usl hK hf)
    (commutator_Uhat_inf_ker_eq_bot hπ hcen hK hf h5 hker)

end Extension

end CFSG.ClassicalInvolution.ModelFacts.OddCover
