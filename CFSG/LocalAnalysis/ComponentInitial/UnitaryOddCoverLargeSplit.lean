module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLargeRadical

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

@[expose] def conjCommSubgroup (g : G) (T : Subgroup G) (hg : ∀ y ∈ T, g * y * g⁻¹ ∈ T)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : Subgroup G where
  carrier := {x | ∃ y ∈ T, x = g * y * g⁻¹ * y⁻¹}
  one_mem' := ⟨1, one_mem _, by group⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y * y', mul_mem hy hy', ?_⟩
    have h1 := hT (g * y' * g⁻¹) (hg y' hy') y⁻¹ (inv_mem hy)
    have h2 := hT y hy y' hy'
    calc g * y * g⁻¹ * y⁻¹ * (g * y' * g⁻¹ * y'⁻¹)
        = g * y * g⁻¹ * (y⁻¹ * (g * y' * g⁻¹)) * y'⁻¹ := by group
      _ = g * y * g⁻¹ * ((g * y' * g⁻¹) * y⁻¹) * y'⁻¹ := by rw [h1]
      _ = g * (y * y') * g⁻¹ * (y' * y)⁻¹ := by group
      _ = g * (y * y') * g⁻¹ * (y * y')⁻¹ := by rw [h2]
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, inv_mem hy, ?_⟩
    have h1 := hT y hy (g * y⁻¹ * g⁻¹) (hg y⁻¹ (inv_mem hy))
    calc (g * y * g⁻¹ * y⁻¹)⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
      _ = g * y⁻¹ * g⁻¹ * y := h1
      _ = g * y⁻¹ * g⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]

theorem conjCommSubgroup_le {g : G} {T : Subgroup G} {hg : ∀ y ∈ T, g * y * g⁻¹ ∈ T}
    {hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x} : conjCommSubgroup g T hg hT ≤ T := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (hg y hy) (inv_mem hy)

theorem eq_one_of_conj_mul_inv_of_odd' {X : Type*} [Group X] {θ : G →* X}
    (hC : θ.ker ≤ Subgroup.center G) (h2 : IsPGroup 2 θ.ker) {g₀ : G} {m : ℕ} (hm : Odd m)
    (hg₀m : θ (g₀ ^ m) = 1) {y : G} (hy : θ (g₀ * y * g₀⁻¹ * y⁻¹) = 1) :
    g₀ * y * g₀⁻¹ * y⁻¹ = 1 := by
  have hconj : g₀ * y * g₀⁻¹ = (g₀ * y * g₀⁻¹ * y⁻¹) * y := by group
  generalize hxdef : g₀ * y * g₀⁻¹ * y⁻¹ = x at hy hconj ⊢
  have hcx : ∀ g : G, g * x = x * g := fun g => Subgroup.mem_center_iff.mp (hC hy) g
  have hk : ∀ k : ℕ, g₀ ^ k * y * (g₀ ^ k)⁻¹ = x ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g₀ ^ (k + 1) * y * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * y * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
            group
        _ = g₀ * (x ^ k * y) * g₀⁻¹ := by rw [ih]
        _ = x ^ k * (g₀ * y * g₀⁻¹) := by
            rw [show g₀ * (x ^ k * y) * g₀⁻¹ = (g₀ * x ^ k) * y * g₀⁻¹ by group,
              (Commute.pow_right (hcx g₀) k).eq]
            group
        _ = x ^ (k + 1) * y := by rw [hconj, pow_succ, mul_assoc]
  have hgmc : ∀ g : G, g * g₀ ^ m = g₀ ^ m * g := fun g =>
    Subgroup.mem_center_iff.mp (hC hg₀m) g
  have hxm : x ^ m = 1 := by
    have h' := hk m
    rw [← hgmc y, mul_inv_cancel_right] at h'
    exact mul_eq_right.mp h'.symm
  obtain ⟨n, hn⟩ := h2 ⟨x, hy⟩
  have hn' : x ^ 2 ^ n = 1 := by
    simpa using congrArg (fun w : θ.ker => (w : G)) hn
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  have hord : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hxm)
  exact orderOf_eq_one_iff.mp hord

end Group

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
variable (θ) in
structure IsLeviComplement (Vt : Subgroup E) : Prop where
  le : Vt ≤ preV θ
  inj : ∀ v ∈ Vt, θ v = 1 → v = 1
  dec : ∀ t ∈ preV θ, ∃ c v, θ c = 1 ∧ v ∈ Vt ∧ t = c * v
  conj : ∀ (A : GL (Fin r) K) (g : E), θ g = hypProj h r 1 (lHom h r A) →
    ∀ v ∈ Vt, g * v * g⁻¹ ∈ Vt

omit [CharP K 2] in
theorem conj_mem_preV_of_lift_even {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {t : E} (ht : t ∈ preV θ) :
    g * t * g⁻¹ ∈ preV θ := by
  obtain ⟨B, hB⟩ := mem_preV.mp ht
  exact (hB.conj A hg).mem

omit [CharP K 2] in
theorem conj_mem_preN_of_lift_even {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {y : E} (hy : y ∈ preN θ) :
    g * y * g⁻¹ ∈ preN θ := by
  obtain ⟨x, hx⟩ := mem_preN.mp hy
  exact (hx.conj A hg).mem

omit [CharP K 2] in
theorem lHom_scalar_commute (s : Kˣ) (A : GL (Fin r) K) :
    lHom h r (hTorusGL fun _ => s) * lHom h r A = lHom h r A * lHom h r (hTorusGL fun _ => s) := by
  rw [← map_mul, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hTorusGL_coe]
  ext i j
  rw [diagonal_mul, mul_diagonal, mul_comm]

omit [CharP K 2] in
theorem diagonal_const_congr {s : K} (hs : h.bar s = s) (B : Matrix (Fin r) (Fin r) K) :
    diagonal (fun _ => s) * B * ((diagonal fun _ => s).map h.bar)ᵀ = (s ^ 2) • B := by
  rw [diagonal_map (map_zero _), diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul, hs]
  ring

omit [CharP K 2] in
theorem IsN.conj_scalar {s : Kˣ} (hs : h.bar (s : K) = s) {x : Fin r → K} {m g : E}
    (hm : IsN θ x m) (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL fun _ => s))) :
    IsN θ ((s : K) • x) (g * m * g⁻¹) := by
  refine (hm.conj _ hg).congr ?_
  rw [dval_hTorusGL_of_fixed fun _ => hs, inv_one, one_smul, hTorusGL_coe]
  ext i
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

include hθ hC in
theorem exists_levi_complement [Finite E] (hf : 2 ≤ f) (h2 : IsPGroup 2 θ.ker) :
    ∃ Vt : Subgroup E, IsLeviComplement θ Vt := by
  have := h.finite
  obtain ⟨σ, hσ, hσ1⟩ := UnitaryEvenCover.exists_fixed_unit (h := h) hf
  set A₀ : GL (Fin r) K := hTorusGL fun _ => σ with hA₀
  obtain ⟨g₀, hg₀⟩ := hθ (hypProj h r 1 (lHom h r A₀))
  have hT : ∀ x ∈ preV θ, ∀ y ∈ preV θ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_preV_even hθ hC hx hy
  have hg₀T : ∀ y ∈ preV θ, g₀ * y * g₀⁻¹ ∈ preV θ := fun y hy => conj_mem_preV_of_lift_even hg₀ hy
  set Vt := conjCommSubgroup g₀ (preV θ) hg₀T hT with hVt
  have := Fintype.ofFinite K
  have hm : Odd (Nat.card Kˣ) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one
  have hg₀m : θ (g₀ ^ Nat.card Kˣ) = 1 := by
    rw [map_pow, hg₀, ← map_pow, ← map_pow]
    have : A₀ ^ Nat.card Kˣ = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, hA₀, hTorusGL_coe, diagonal_pow, Units.val_one,
        ← diagonal_one]
      congr 1
      funext i
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
    rw [this, map_one, map_one]
  have hsurj : ∀ {B : Matrix (Fin r) (Fin r) K}, IsRad h 0 B → ∃ v ∈ Vt, IsV θ B v := by
    intro B hB
    have hσ2 : (σ : K) ^ 2 - 1 ≠ 0 :=
      sub_ne_zero.mpr (UnitaryEvenCover.sq_ne_one_of_ne_one' hσ1)
    set c := ((σ : K) ^ 2 - 1)⁻¹ with hc
    have hcF : h.bar c = c := by rw [hc, map_inv₀, map_sub, map_pow, hσ, map_one]
    have hB' : IsRad h 0 (c • B) := by
      rw [isRad_zero_iff_isHerm] at hB ⊢
      unfold UnitaryEvenCover.IsHerm at hB ⊢
      have e : ((c • B).map h.bar)ᵀ = c • (B.map h.bar)ᵀ := by
        ext i j
        simp only [transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcF]
      rw [e, ← smul_add, hB, smul_zero]
    obtain ⟨t, ht⟩ := exists_isV hθ hB'
    refine ⟨_, ⟨t, ht.mem, rfl⟩, ((ht.conj A₀ hg₀).mul ht.inv).congr ?_⟩
    rw [hA₀, hTorusGL_coe, diagonal_const_congr hσ, smul_smul, ← sub_eq_add_neg, ← sub_smul,
      show (σ : K) ^ 2 * c - c = 1 by rw [← sub_one_mul, hc, mul_inv_cancel₀ hσ2], one_smul]
  refine ⟨Vt, ⟨conjCommSubgroup_le, ?_, fun t ht => ?_, fun A g hg v hv => ?_⟩⟩
  · rintro _ ⟨y, -, rfl⟩ hx
    exact eq_one_of_conj_mul_inv_of_odd' hC h2 hm hg₀m hx
  · obtain ⟨B, hB⟩ := mem_preV.mp ht
    obtain ⟨v, hv, hvB⟩ := hsurj hB.1
    refine ⟨t * v⁻¹, v, ?_, hv, by group⟩
    rw [map_mul, map_inv, IsV.map_eq_even hB hvB, mul_inv_cancel]
  · obtain ⟨y, hy, rfl⟩ := hv
    set c := g * g₀ * g⁻¹ * g₀⁻¹ with hcdef
    have hsc := lHom_scalar_commute (h := h) σ A
    rw [← hA₀] at hsc
    have hcomm : θ g * θ g₀ = θ g₀ * θ g := by
      rw [hg, hg₀, ← map_mul (hypProj h r 1), ← map_mul (hypProj h r 1), hsc]
    have hc : c ∈ Subgroup.center E := hC (by
      rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group)
    have hgg₀ : g * g₀ * g⁻¹ = c * g₀ := by rw [hcdef]; group
    refine ⟨g * y * g⁻¹, conj_mem_preV_of_lift_even hg hy, ?_⟩
    calc g * (g₀ * y * g₀⁻¹ * y⁻¹) * g⁻¹
        = (g * g₀ * g⁻¹) * (g * y * g⁻¹) * (g * g₀ * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      _ = (c * g₀) * (g * y * g⁻¹) * (c * g₀)⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hgg₀]
      _ = c * (g₀ * (g * y * g⁻¹) * g₀⁻¹) * c⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      _ = g₀ * (g * y * g⁻¹) * g₀⁻¹ * (g * y * g⁻¹)⁻¹ := by
          rw [conj_eq_of_mem_center hc]

section Commutator

variable {Vt : Subgroup E} (hVt : IsLeviComplement θ Vt)

omit [CharP K 2] in
include hC hVt in
theorem IsLeviComplement.conj_mul_inv_mem {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {t : E} (ht : t ∈ preV θ) :
    g * t * g⁻¹ * t⁻¹ ∈ Vt := by
  obtain ⟨c, v, hc, hv, rfl⟩ := hVt.dec t ht
  have hcc : c ∈ Subgroup.center E := hC hc
  have e : g * (c * v) * g⁻¹ * (c * v)⁻¹ = g * v * g⁻¹ * v⁻¹ :=
    calc g * (c * v) * g⁻¹ * (c * v)⁻¹ = (g * c * g⁻¹) * (g * v * g⁻¹ * v⁻¹) * c⁻¹ := by group
      _ = c * (g * v * g⁻¹ * v⁻¹) * c⁻¹ := by rw [conj_central hcc]
      _ = g * v * g⁻¹ * v⁻¹ := conj_eq_of_mem_center hcc _
  rw [e]
  exact mul_mem (hVt.conj A g hg v hv) (inv_mem hv)

include hθ hC in
theorem conj_preV_of_mem_preN_even (hf : 2 ≤ f) (hr : 2 ≤ r) {τ m : E} (hτ : τ ∈ preV θ)
    (hm : m ∈ preN θ) : m * τ * m⁻¹ = τ := by
  rw [← mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr hτ hm, mul_inv_cancel_right]

include hθ hC in
theorem commutatorElement_mul_left_preN_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m₁ m₂ m' : E}
    (hm₁ : m₁ ∈ preN θ) (hm₂ : m₂ ∈ preN θ) (hm' : m' ∈ preN θ) :
    ⁅m₁ * m₂, m'⁆ = ⁅m₁, m'⁆ * ⁅m₂, m'⁆ := by
  rw [commutatorElement_mul_left', conj_preV_of_mem_preN_even hθ hC hf hr
    (commutatorElement_mem_preV hm₂ hm') hm₁]
  exact mul_comm_of_mem_preV_even hθ hC (commutatorElement_mem_preV hm₂ hm')
    (commutatorElement_mem_preV hm₁ hm')

include hθ hC in
theorem commutatorElement_mul_right_preN_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m m'₁ m'₂ : E}
    (hm : m ∈ preN θ) (hm'₁ : m'₁ ∈ preN θ) (hm'₂ : m'₂ ∈ preN θ) :
    ⁅m, m'₁ * m'₂⁆ = ⁅m, m'₁⁆ * ⁅m, m'₂⁆ := by
  rw [commutatorElement_mul_right', conj_preV_of_mem_preN_even hθ hC hf hr
    (commutatorElement_mem_preV hm hm'₂) hm'₁]

include hθ hC in
theorem commutatorElement_eq_of_isN_left_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m m₁ m' : E}
    {x : Fin r → K} (hm : IsN θ x m) (hm₁ : IsN θ x m₁) (hm' : m' ∈ preN θ) :
    ⁅m, m'⁆ = ⁅m₁, m'⁆ := by
  have hτ := hm.inv_mul_mem hm₁
  rw [show m₁ = m * (m⁻¹ * m₁) by group, commutatorElement_mul_left_preN_even hθ hC hf hr hm.mem
    (preV_le_preN hτ) hm', commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr hτ hm'), mul_one]

include hθ hC in
theorem commutatorElement_mul_preV_right_preN_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m m' τ : E}
    (hm : m ∈ preN θ) (hm' : m' ∈ preN θ) (hτ : τ ∈ preV θ) : ⁅m, m' * τ⁆ = ⁅m, m'⁆ := by
  rw [commutatorElement_mul_right_preN_even hθ hC hf hr hm hm' (preV_le_preN hτ),
    show ⁅m, τ⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr hτ hm).symm, mul_one]

include hθ hC in
theorem commutatorElement_eq_of_isN_right_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m m' m'₁ : E}
    {y : Fin r → K} (hm : m ∈ preN θ) (hm' : IsN θ y m') (hm'₁ : IsN θ y m'₁) :
    ⁅m, m'⁆ = ⁅m, m'₁⁆ := by
  rw [show m'₁ = m' * (m'⁻¹ * m'₁) by group,
    commutatorElement_mul_preV_right_preN_even hθ hC hf hr hm hm'.mem (hm'.inv_mul_mem hm'₁)]

include hθ hC hVt in
theorem commutatorElement_mem_of_weight_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m' : E}
    (hm' : m' ∈ preN θ) {ψ : K → Fin r → K} (hψ : ∀ s s', ψ (s + s') = ψ s + ψ s')
    {A : GL (Fin r) K} {g : E} (hg : θ g = hypProj h r 1 (lHom h r A)) {ζ : K} (hζ : ζ ≠ 1)
    (hgm' : m'⁻¹ * (g * m' * g⁻¹) ∈ preV θ)
    (hgψ : ∀ s m, IsN θ (ψ s) m → IsN θ (ψ (ζ * s)) (g * m * g⁻¹)) {s : K} {m : E}
    (hm : IsN θ (ψ s) m) : ⁅m, m'⁆ ∈ Vt := by
  choose ℓ hℓ using fun s => exists_isN hθ (ψ s)
  have hF : ∀ s, ⁅ℓ s, m'⁆ ∈ preV θ := fun s => commutatorElement_mem_preV (hℓ s).mem hm'
  have hadd : ∀ s s', ⁅ℓ (s + s'), m'⁆ = ⁅ℓ s, m'⁆ * ⁅ℓ s', m'⁆ := fun s s' => by
    rw [commutatorElement_eq_of_isN_left_even hθ hC hf hr (hℓ (s + s'))
      (((hℓ s).mul (hℓ s')).congr (hψ s s').symm) hm',
      commutatorElement_mul_left_preN_even hθ hC hf hr (hℓ s).mem (hℓ s').mem hm']
  have hconj : ∀ s, g * ⁅ℓ s, m'⁆ * g⁻¹ = ⁅ℓ (ζ * s), m'⁆ := fun s => by
    rw [conjugate_commutatorElement, show g * m' * g⁻¹ = m' * (m'⁻¹ * (g * m' * g⁻¹)) by group,
      commutatorElement_mul_preV_right_preN_even hθ hC hf hr (hgψ s _ (hℓ s)).mem hm' hgm',
      commutatorElement_eq_of_isN_left_even hθ hC hf hr (hgψ s _ (hℓ s)) (hℓ (ζ * s)) hm']
  have hmem : ∀ u, ⁅ℓ ((ζ - 1) * u), m'⁆ ∈ Vt := fun u => by
    have h1 := hVt.conj_mul_inv_mem hC hg (hF u)
    rw [hconj, show ζ * u = (ζ - 1) * u + u by ring, hadd, mul_inv_cancel_right] at h1
    exact h1
  have hζ' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  rw [commutatorElement_eq_of_isN_left_even hθ hC hf hr hm (hℓ s) hm',
    show s = (ζ - 1) * ((ζ - 1)⁻¹ * s) by field_simp]
  exact hmem _

include hθ hC hVt in
theorem commutatorElement_mem_of_ne_even (hf : 2 ≤ f) (hr : 2 ≤ r) {i j : Fin r} (hij : i ≠ j)
    {a b : K} {m m' : E} (hm : IsN θ (Pi.single i a) m) (hm' : IsN θ (Pi.single j b) m') :
    ⁅m, m'⁆ ∈ Vt := by
  obtain ⟨σ, hσ, hσ1⟩ := UnitaryEvenCover.exists_fixed_unit (h := h) hf
  have hdF := UnitaryEvenCover.mulSingle_fixed hσ i
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL (Pi.mulSingle i σ))))
  refine commutatorElement_mem_of_weight_even hθ hC hVt hf hr hm'.mem
    (ψ := fun s : K => (Pi.single i s : Fin r → K)) (fun s s' => by rw [Pi.single_add]) hg
    (ζ := (σ : K)) hσ1 ?_ ?_ hm
  · refine hm'.inv_mul_mem ((hm'.conj_hTorusGL (dval_hTorusGL_of_fixed hdF) hg).congr ?_)
    rw [UnitaryEvenCover.mulSingle_val, ite_eq_right (Ne.symm hij), one_mul]
  · intro s m hm
    refine (hm.conj_hTorusGL (dval_hTorusGL_of_fixed hdF) hg).congr ?_
    rw [UnitaryEvenCover.mulSingle_val, ite_eq_left rfl]

include hθ hC hVt in
theorem commutatorElement_mem_of_eq_even (hf : 2 ≤ f) (hr : 2 ≤ r) {k : Fin r} {a b : K}
    {ν ν' : E} (hν : IsN θ (Pi.single k a) ν) (hν' : IsN θ (Pi.single k b) ν') :
    ⁅ν, ν'⁆ ∈ Vt := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨i, hik⟩ := exists_ne k
  have hki : k ≠ i := Ne.symm hik
  obtain ⟨μ, hμ⟩ := exists_isN hθ (Pi.single i a)
  obtain ⟨μ', hμ'⟩ := exists_isN hθ (Pi.single i b)
  set A : GL (Fin r) K := hElemGL hki 1 with hA
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r A))
  have hact : ∀ (c : K) (n : E), IsN θ (Pi.single i c) n →
      IsN θ (Pi.single k c) (n⁻¹ * (g * n * g⁻¹)) := fun c n hn => by
    have h1 := hn.conj A hg
    rw [dval_of_det_eq_one (by rw [hA]; exact hElemGL_det hki 1), inv_one, one_smul, hA,
      hElemGL_coe, hElem_mulVec, Pi.single_eq_same, one_mul] at h1
    exact (hn.inv.mul h1).congr (by abel)
  set ν₀ := μ⁻¹ * (g * μ * g⁻¹) with hν₀
  set ν₀' := μ'⁻¹ * (g * μ' * g⁻¹) with hν₀'
  have h₀ := hact a μ hμ
  have h₀' := hact b μ' hμ'
  have hX : g * ⁅μ, μ'⁆ * g⁻¹ = ⁅μ, μ'⁆ * ⁅μ, ν₀'⁆ * (⁅ν₀, μ'⁆ * ⁅ν₀, ν₀'⁆) := by
    rw [conjugate_commutatorElement, show g * μ * g⁻¹ = μ * ν₀ by rw [hν₀]; group,
      show g * μ' * g⁻¹ = μ' * ν₀' by rw [hν₀']; group,
      commutatorElement_mul_left_preN_even hθ hC hf hr hμ.mem h₀.mem (mul_mem hμ'.mem h₀'.mem),
      commutatorElement_mul_right_preN_even hθ hC hf hr hμ.mem hμ'.mem h₀'.mem,
      commutatorElement_mul_right_preN_even hθ hC hf hr h₀.mem hμ'.mem h₀'.mem]
  have hP := hVt.conj_mul_inv_mem hC hg (commutatorElement_mem_preV hμ.mem hμ'.mem)
  have hQ := commutatorElement_mem_of_ne_even hθ hC hVt hf hr hik hμ h₀'
  have hR := commutatorElement_mem_of_ne_even hθ hC hVt hf hr hki h₀ hμ'
  rw [commutatorElement_eq_of_isN_left_even hθ hC hf hr hν h₀ hν'.mem,
    commutatorElement_eq_of_isN_right_even hθ hC hf hr h₀.mem hν' h₀']
  have hcomm : ⁅μ, μ'⁆⁻¹ * (g * ⁅μ, μ'⁆ * g⁻¹) = g * ⁅μ, μ'⁆ * g⁻¹ * ⁅μ, μ'⁆⁻¹ :=
    mul_comm_of_mem_preV_even hθ hC (inv_mem (commutatorElement_mem_preV hμ.mem hμ'.mem))
      (conj_mem_preV_of_lift_even hg (commutatorElement_mem_preV hμ.mem hμ'.mem))
  have e : ⁅ν₀, ν₀'⁆ = ⁅ν₀, μ'⁆⁻¹ * ⁅μ, ν₀'⁆⁻¹ * (⁅μ, μ'⁆⁻¹ * (g * ⁅μ, μ'⁆ * g⁻¹)) := by
    rw [hX]
    group
  rw [e, hcomm]
  exact mul_mem (mul_mem (inv_mem hR) (inv_mem hQ)) hP

include hθ hC in
theorem commutatorElement_mem_of_single_left_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m' : E}
    (hm' : m' ∈ preN θ)
    (hgen : ∀ (k : Fin r) (a : K) (m : E), IsN θ (Pi.single k a) m → ⁅m, m'⁆ ∈ Vt) {m : E}
    (hm : m ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {x | ∀ m, IsN θ x m → ⁅m, m'⁆ ∈ Vt}
      zero_mem' := fun m hm => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr (isN_zero_iff.mp hm) hm')]
        exact one_mem _
      add_mem' := by
        intro x y hx hy m hm
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m) := (hm₁.inv.mul hm).congr (by abel)
        rw [show m = m₁ * (m₁⁻¹ * m) by group,
          commutatorElement_mul_left_preN_even hθ hC hf hr hm₁.mem hm₂.mem hm']
        exact mul_mem (hx m₁ hm₁) (hy _ hm₂)
      neg_mem' := by
        intro x hx m hm
        have hm₁ : IsN θ x m⁻¹ := hm.inv.congr (neg_neg x)
        have h1 := commutatorElement_mul_left_preN_even hθ hC hf hr hm.mem hm₁.mem hm'
        rw [mul_inv_cancel, commutatorElement_one_left] at h1
        rw [eq_inv_of_mul_eq_one_left h1.symm]
        exact inv_mem (hx _ hm₁) }
  obtain ⟨x, hx⟩ := mem_preN.mp hm
  have hxS : x ∈ S := by
    rw [← Finset.univ_sum_single x]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (x k)
  exact hxS m hx

include hθ hC in
theorem commutatorElement_mem_of_single_right_even (hf : 2 ≤ f) (hr : 2 ≤ r) {m : E}
    (hm : m ∈ preN θ)
    (hgen : ∀ (k : Fin r) (b : K) (m' : E), IsN θ (Pi.single k b) m' → ⁅m, m'⁆ ∈ Vt) {m' : E}
    (hm' : m' ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {y | ∀ m', IsN θ y m' → ⁅m, m'⁆ ∈ Vt}
      zero_mem' := fun m' hm' => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr (isN_zero_iff.mp hm') hm).symm]
        exact one_mem _
      add_mem' := by
        intro x y hx hy m' hm'
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m') := (hm₁.inv.mul hm').congr (by abel)
        rw [show m' = m₁ * (m₁⁻¹ * m') by group,
          commutatorElement_mul_right_preN_even hθ hC hf hr hm hm₁.mem hm₂.mem]
        exact mul_mem (hx m₁ hm₁) (hy _ hm₂)
      neg_mem' := by
        intro x hx m' hm'
        have hm₁ : IsN θ x m'⁻¹ := hm'.inv.congr (neg_neg x)
        have h1 := commutatorElement_mul_right_preN_even hθ hC hf hr hm hm'.mem hm₁.mem
        rw [mul_inv_cancel, commutatorElement_one_right] at h1
        rw [eq_inv_of_mul_eq_one_left h1.symm]
        exact inv_mem (hx _ hm₁) }
  obtain ⟨y, hy⟩ := mem_preN.mp hm'
  have hyS : y ∈ S := by
    rw [← Finset.univ_sum_single y]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (y k)
  exact hyS m' hy

include hθ hC hVt in
theorem commutatorElement_mem_levi_complement (hf : 2 ≤ f) (hr : 2 ≤ r) {m m' : E}
    (hm : m ∈ preN θ) (hm' : m' ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  refine commutatorElement_mem_of_single_right_even hθ hC hf hr hm (fun k b m'₀ hm'₀ => ?_) hm'
  refine commutatorElement_mem_of_single_left_even hθ hC hf hr hm'₀.mem
    (fun k' a m₀ hm₀ => ?_) hm
  by_cases hk : k' = k
  · subst hk
    exact commutatorElement_mem_of_eq_even hθ hC hVt hf hr hm₀ hm'₀
  · exact commutatorElement_mem_of_ne_even hθ hC hVt hf hr hk hm₀ hm'₀

end Commutator

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
