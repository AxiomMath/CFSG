module

public import CFSG.GH74.Uniqueness.Section164Q
public import CFSG.GH74.Uniqueness.Bender.FixedLinear

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

@[expose] def conjAut {F : Subgroup X} {a : X} (ha : a ∈ normalizer (F : Set X)) : MulAut ↥F where
  toFun f := ⟨a * f * a⁻¹, (mem_normalizer_iff.mp ha f).mp f.2⟩
  invFun f := ⟨a⁻¹ * f * a, by
    have := (mem_normalizer_iff.mp (inv_mem ha) f).mp f.2
    simpa using this⟩
  left_inv f := Subtype.ext (by simp [mul_assoc])
  right_inv f := Subtype.ext (by simp [mul_assoc])
  map_mul' f g := Subtype.ext (by
    change a * ((f : X) * g) * a⁻¹ = (a * f * a⁻¹) * (a * g * a⁻¹)
    group)

omit [Finite X] in
@[simp]
theorem conjAut_apply {F : Subgroup X} {a : X} (ha : a ∈ normalizer (F : Set X)) (f : ↥F) :
    ((conjAut ha f : ↥F) : X) = a * f * a⁻¹ := rfl

omit [Finite X] in
theorem conjAut_mul_self {F : Subgroup X} {a : X} (ha : a ∈ normalizer (F : Set X))
    (ha2 : a * a = 1) : conjAut ha * conjAut ha = 1 := by
  ext f
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  change a * (a * (f : X) * a⁻¹) * a⁻¹ = f
  rw [hai]
  calc a * (a * (f : X) * a) * a = (a * a) * f * (a * a) := by group
    _ = f := by rw [ha2]; group

omit [Finite X] in
theorem conjAut_fix {F : Subgroup X} {a : X} (ha : a ∈ normalizer (F : Set X)) {f : ↥F}
    (hf : a * f = f * a) : conjAut ha f = f := by
  apply Subtype.ext
  rw [conjAut_apply, hf, mul_inv_cancel_right]

theorem not_inner_conjAut (S : ZDSetup X Z M) {F : Subgroup X} {m i e : ℕ}
    (hF : Bender.BenderType ↥F m i e) (hinv : ∀ y ∈ F, orderOf y = 2 → y ∈ Z) {z t a : X}
    (hz : z ∈ Z) (hzM : z ∈ M) (hzF : z ∈ F) (htM : t ∉ M) (htF : t ∈ F)
    (ha : a ∈ normalizer (F : Set X)) (ha2 : a * a = 1) (haz : a * z = z * a)
    (hat : a * t = t * a) (haF : a ∉ centralizer (F : Set X)) :
    ¬ ∃ g : ↥F, ∀ x : ↥F, conjAut ha x = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g, hg⟩
  have hg2 : g * g = 1 := by
    have hc : g * g ∈ center ↥F := by
      rw [mem_center_iff]
      intro x
      have h1 := congrArg (fun σ : MulAut ↥F => σ x) (conjAut_mul_self ha ha2)
      simp only [MulAut.mul_apply, MulAut.one_apply, hg] at h1
      calc x * (g * g) = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = g * g * x := by group
    rw [hF.center_eq_bot, mem_bot] at hc
    exact hc
  have hgz : (g : X) * z = z * g := by
    have h1 := hg ⟨z, hzF⟩
    rw [conjAut_fix ha (f := ⟨z, hzF⟩) haz] at h1
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul, coe_inv] at h2
    calc (g : X) * z = (g * z * (g : X)⁻¹) * g := by group
      _ = z * g := by rw [← h2]
  have hgt : (g : X) * t = t * g := by
    have h1 := hg ⟨t, htF⟩
    rw [conjAut_fix ha (f := ⟨t, htF⟩) hat] at h1
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul, coe_inv] at h2
    calc (g : X) * t = (g * t * (g : X)⁻¹) * g := by group
      _ = t * g := by rw [← h2]
  by_cases hg1 : g = 1
  · apply haF
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := congrArg Subtype.val (hg ⟨f, hf⟩)
    rw [hg1] at h1
    simp only [conjAut_apply, one_mul, inv_one, mul_one] at h1
    calc f * a = (a * f * a⁻¹) * a := by rw [h1]
      _ = a * f := by group
  · have hgo : orderOf (g : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hg2) hg1
    have hgZ : (g : X) ∈ Z := hinv _ g.2 hgo
    have hgM : (g : X) ∈ M :=
      S.prodDisc.centralizer_le_of_mem hz hzM (mem_centralizer_singleton_iff.mpr hgz)
    apply htM
    refine S.prodDisc.mem_of_conj_mem hgZ hgM (g := t) ?_
    have e : t⁻¹ * (g : X) * t = g := by
      calc t⁻¹ * (g : X) * t = t⁻¹ * ((g : X) * t) := by group
        _ = t⁻¹ * (t * g) := by rw [hgt]
        _ = g := by group
    rw [e]
    exact hgM

theorem B0_structure
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e)
    (hu164 : ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 → y = c.u) {v : X}
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvu : v ≠ c.u)
    (huv : c.u * v = v * c.u) (hvt : v * c.t = c.t * v) (hvz : v * c.z = c.z * v) :
    ∃ hvN : v ∈ normalizer (c.B0 : Set X),
      c.Bzero = c.B0 ∧ ∃ k : ℕ, 1 ≤ k ∧ Bender.BenderType ↥c.B0 (2 * k) 1 1 ∧
        (¬ ∃ g : ↥c.B0, ∀ x : ↥c.B0, conjAut hvN x = g * x * g⁻¹) ∧
        Nonempty (Bender.autFixed (conjAut hvN) ≃* CFSG.Theory.Comparator.PSL2Model k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvB : v ∈ c.B := mem_centralizer_singleton_iff.mpr huv.symm
  have hvN : v ∈ normalizer (c.B0 : Set X) := le_normalizer_zHull S.invariant _ hvB
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hvC : v ∉ centralizer (c.Bzero : Set X) := fun h =>
    hvu (hu164 v (mem_inf.mpr ⟨hvB, h⟩) hvo)
  have hfix : ∀ x : ↥c.B0, (x : X) = c.z ∨ (x : X) = c.t → conjAut hvN x = x := by
    rintro x (hx | hx)
    · exact conjAut_fix hvN (by rw [hx]; exact hvz)
    · exact conjAut_fix hvN (by rw [hx]; exact hvt)
  obtain ⟨m, hm, ⟨hF, hBT⟩ | ⟨-, -, -, hb3⟩⟩ := Sec164.lemma162_B0 S h162 c
  swap
  · exfalso
    apply hvC
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ fZero Z M c.B0 c.t := by rw [Sec164.fZero_B0]; exact hx
    have h1 := congrArg Subtype.val (hb3 (conjAut hvN) (conjAut_mul_self hvN hv2) hfix
      ⟨x, Sec164.Bzero_le_B0 c hx⟩ hx')
    rw [conjAut_apply] at h1
    calc x * v = (v * x * v⁻¹) * v := by rw [h1]
      _ = v * x := by group
  rw [Sec164.fZero_B0] at hF
  have hvC0 : v ∉ centralizer (c.B0 : Set X) := fun h =>
    hvC (centralizer_le (Sec164.Bzero_le_B0 c) h)
  refine ⟨hvN, hF, ?_⟩
  rcases hBT with hL | hSz
  · have hni := not_inner_conjAut S hL hB.invol c.hz c.hzM (Sec164.z_mem_B0 c) c.htM
      (Sec164.t_mem_B0 c) hvN hv2 hvz hvt hvC0
    obtain ⟨k, hmk, hiso, -⟩ := hL.fixed_linear (conjAut hvN) (conjAut_mul_self hvN hv2) hni
    exact ⟨k, by omega, hmk ▸ hL, hni, hiso⟩
  · exfalso
    obtain ⟨g, -, hg⟩ := hSz.exists_inner_of_sq_eq_one_suzuki (conjAut hvN)
      (conjAut_mul_self hvN hv2)
    exact not_inner_conjAut S hSz hB.invol c.hz c.hzM (Sec164.z_mem_B0 c) c.htM
      (Sec164.t_mem_B0 c) hvN hv2 hvz hvt hvC0 ⟨g, hg⟩

end Sec165

end CFSG.GH74.Uniqueness
