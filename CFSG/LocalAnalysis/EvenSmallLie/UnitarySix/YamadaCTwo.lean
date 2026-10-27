module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCTwoCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)

@[expose] def yamadaC2 {G : Type} [Group G] {L : Subgroup G} (D : ToddParabolic L) (t : G) :
    Subgroup G :=
  (CFSG.pCore 2 (normalizer (toddE D t : Set G))).map (normalizer (toddE D t : Set G)).subtype

section G

variable {G : Type} [Group G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem yamadaC2_le : yamadaC2 D t ≤ normalizer (toddE D t : Set G) := map_subtype_le _

theorem isPGroup_yamadaC2 : IsPGroup 2 (yamadaC2 D t) := CFSG.pCore_isPGroup.map _

theorem conj_mem_yamadaC2 {x c : G} (hx : x ∈ normalizer (toddE D t : Set G))
    (hc : c ∈ yamadaC2 D t) : x * c * x⁻¹ ∈ yamadaC2 D t := by
  obtain ⟨c, hc, rfl⟩ := hc
  exact ⟨⟨x, hx⟩ * c * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem c hc ⟨x, hx⟩, rfl⟩

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

private theorem t_mul_t (h : Setting G L D t) : t * t = 1 := by rw [← sq, h.t_sq]

private theorem t_inv (h : Setting G L D t) : t⁻¹ = t := inv_eq_of_mul_eq_one_left h.t_mul_t

theorem conj_t_mul_t_mem (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) {x : G}
    (hx : x ∈ normalizer (toddE D t : Set G)) : x * t * x⁻¹ * t ∈ toddA D := by
  have h1 : x * t * x⁻¹ ∈ omegaSet D t := conj_mem_conjOrbit' hx t_mem_omega
  rw [hΩ] at h1
  obtain ⟨a, ha, e⟩ := h1
  rw [e, mul_assoc, h.t_mul_t, mul_one]
  exact ha

omit [Finite G] in
theorem conj_mem_inf_centralizer_toddA (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    {x c : G} (hx : x ∈ normalizer (toddE D t : Set G))
    (hc : c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G)) :
    x * c * x⁻¹ ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) := by
  refine mem_inf.2 ⟨mul_mem (mul_mem hx hc.1) (inv_mem hx), mem_centralizer_iff.2 fun a ha => ?_⟩
  have hxa : x⁻¹ * a * x ∈ toddA D := by
    have := (mem_normalizer_iff.1 (normalizer_le_of_omega hΩ (inv_mem hx)) a).1 ha
    rwa [inv_inv] at this
  have hca := mem_centralizer_iff.1 hc.2 _ hxa
  calc a * (x * c * x⁻¹) = x * ((x⁻¹ * a * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * a * x)) * x⁻¹ := by rw [hca]
    _ = x * c * x⁻¹ * a := by group

theorem toddE_le_inf_centralizer_toddA (h : Setting G L D t) :
    toddE D t ≤ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) :=
  le_inf le_normalizer fun _ he => mem_centralizer_iff.2 fun _ ha =>
    mul_comm_of_sq_eq_one h.toddE_sq (toddA_le_toddE D t ha) he

theorem conj_t_mul_t_mul (h : Setting G L D t) (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    {c d : G} (hc : c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G))
    (hd : d ∈ normalizer (toddE D t : Set G)) :
    c * d * t * (c * d)⁻¹ * t = (c * t * c⁻¹ * t) * (d * t * d⁻¹ * t) := by
  have ha := h.conj_t_mul_t_mem hΩ hd
  have hcA : (d * t * d⁻¹ * t) * c = c * (d * t * d⁻¹ * t) := mem_centralizer_iff.1 hc.2 _ ha
  calc c * d * t * (c * d)⁻¹ * t = c * (d * t * d⁻¹ * t) * t⁻¹ * c⁻¹ * t := by group
    _ = (d * t * d⁻¹ * t) * (c * t⁻¹ * c⁻¹ * t) := by rw [← hcA]; group
    _ = (d * t * d⁻¹ * t) * (c * t * c⁻¹ * t) := by rw [h.t_inv]
    _ = (c * t * c⁻¹ * t) * (d * t * d⁻¹ * t) :=
      toddA_comm D ha (h.conj_t_mul_t_mem hΩ hc.1)

theorem conj_t_mul_t_eq_one_iff (h : Setting G L D t) {c : G}
    (hc : c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G)) :
    c * t * c⁻¹ * t = 1 ↔ c ∈ toddE D t := by
  constructor
  · intro h1
    refine h.mem_toddE_of_comm (fun a ha => ?_) ?_
    · rw [← mem_centralizer_iff.1 hc.2 a ha, mul_inv_cancel_right]
    · calc c * t * c⁻¹ = c * t * c⁻¹ * t * t := by rw [mul_assoc _ t t, h.t_mul_t, mul_one]
        _ = t := by rw [h1, one_mul]
  · intro hcE
    rw [mem_centralizer_singleton_iff.1 (h.toddE_le_H hcE), mul_inv_cancel_right, h.t_mul_t]

theorem pow_four_eq_one_of_omega (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) {c : G}
    (hc : c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G)) : c ^ 4 = 1 := by
  have h1 : c * c * t * (c * c)⁻¹ * t = 1 := by
    rw [h.conj_t_mul_t_mul hΩ hc hc.1, ← sq, toddA_sq D _ (h.conj_t_mul_t_mem hΩ hc.1)]
  have h2 := h.toddE_sq _ ((h.conj_t_mul_t_eq_one_iff (mul_mem hc hc)).1 h1)
  rw [← sq, ← pow_mul] at h2
  exact h2

theorem exists_conj_t_mul_t_eq (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    (hc : ∃ c ∈ normalizer (toddE D t : Set G), (∀ a ∈ toddA D, c * a = a * c) ∧ c * t ≠ t * c)
    {a : G} (ha : a ∈ toddA D) :
    ∃ c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G),
      c * t * c⁻¹ * t = a := by
  set C := normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) with hC
  let φ : C →* G := MonoidHom.mk' (fun c => (c : G) * t * (c : G)⁻¹ * t)
    (fun c d => h.conj_t_mul_t_mul hΩ c.2 d.2.1)
  have hφ : ∀ c : C, φ c = (c : G) * t * (c : G)⁻¹ * t := fun c => rfl
  have hle : φ.range ≤ toddA D := by
    rintro _ ⟨c, rfl⟩
    exact h.conj_t_mul_t_mem hΩ c.2.1
  have hK : ∀ k ∈ toddK D, ∀ b ∈ φ.range, k * b * k⁻¹ ∈ φ.range := by
    rintro k hk _ ⟨c, rfl⟩
    refine ⟨⟨k * c * k⁻¹, conj_mem_inf_centralizer_toddA hΩ (h.toddK_le_X hk) c.2⟩, ?_⟩
    rw [hφ, hφ]
    have e : k * t * k⁻¹ = t := by rw [h.comm_toddK hk, mul_inv_cancel_right]
    calc k * c * k⁻¹ * t * (k * c * k⁻¹)⁻¹ * t =
        k * c * k⁻¹ * (k * t * k⁻¹) * (k * c * k⁻¹)⁻¹ * (k * t * k⁻¹) := by rw [e]
      _ = k * ((c : G) * t * (c : G)⁻¹ * t) * k⁻¹ := by group
  have h1 : φ.range ≠ ⊥ := by
    obtain ⟨c, hcX, hcA, hct⟩ := hc
    have hcC : c ∈ C := mem_inf.2 ⟨hcX, mem_centralizer_iff.2 fun a ha => (hcA a ha).symm⟩
    intro h0
    have hmem : φ ⟨c, hcC⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [h0, mem_bot, hφ] at hmem
    exact hct (mem_centralizer_singleton_iff.1
      (h.toddE_le_H ((h.conj_t_mul_t_eq_one_iff hcC).1 hmem)))
  rw [← h.eq_toddA_of_invariant hle hK h1] at ha
  obtain ⟨c, rfl⟩ := ha
  exact ⟨c, c.2, rfl⟩

theorem exists_mul_eq_of_omega (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    (hc : ∃ c ∈ normalizer (toddE D t : Set G), (∀ a ∈ toddA D, c * a = a * c) ∧ c * t ≠ t * c)
    {x : G} (hx : x ∈ normalizer (toddE D t : Set G)) :
    ∃ y ∈ normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G),
      ∃ c ∈ normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G), x = y * c := by
  have h1 : x⁻¹ * t * x ∈ omegaSet D t := ⟨x, hx, rfl⟩
  rw [hΩ] at h1
  obtain ⟨a, ha, hat⟩ := h1
  obtain ⟨d, hd, hda⟩ := h.exists_conj_t_mul_t_eq hΩ hc ha
  have hdt : d * t * d⁻¹ = a * t := by rw [← hda, mul_assoc _ t t, h.t_mul_t, mul_one]
  refine ⟨x * d, ?_, d⁻¹, inv_mem hd, by group⟩
  rw [← h.normalizer_toddE_inf]
  refine mem_inf.2 ⟨mul_mem hx hd.1, mem_centralizer_singleton_iff.2 ?_⟩
  have e : x * d * t * (x * d)⁻¹ = t := by
    calc x * d * t * (x * d)⁻¹ = x * (d * t * d⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [hdt, hat]
      _ = t := by group
  calc x * d * t = x * d * t * (x * d)⁻¹ * (x * d) := by group
    _ = t * (x * d) := by rw [e]

theorem le_yamadaC2 (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) ≤ yamadaC2 D t := by
  set X := normalizer (toddE D t : Set G) with hX
  set C := X ⊓ centralizer (toddA D : Set G) with hC
  have hn : (C.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact conj_mem_inf_centralizer_toddA hΩ g.2 hn⟩
  have hp : IsPGroup 2 (C.subgroupOf X) := fun g => ⟨2, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using h.pow_four_eq_one_of_omega hΩ (mem_subgroupOf.1 g.2)⟩
  have hle : C.subgroupOf X ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  have := map_mono (f := X.subtype) hle
  rwa [subgroupOf_map_subtype, inf_of_le_left inf_le_left] at this

theorem yamadaC2_eq (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    (hc : ∃ c ∈ normalizer (toddE D t : Set G), (∀ a ∈ toddA D, c * a = a * c) ∧ c * t ≠ t * c) :
    yamadaC2 D t = normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) := by
  have hCle := h.le_yamadaC2 hΩ
  refine le_antisymm (fun x hx => ?_) hCle
  have hKN : toddK D ≤ normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) :=
    le_inf (toddK_le_normalizer D) h.toddK_le_H
  have hQ : yamadaC2 D t ⊓ (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G)) ≤
      toddE D t :=
    h.le_toddE_of_isPGroup inf_le_right (isPGroup_yamadaC2.to_le inf_le_left)
      fun k hk q hq => mem_inf.2 ⟨conj_mem_yamadaC2 (h.toddK_le_X hk) hq.1,
        mul_mem (mul_mem (hKN hk) hq.2) (inv_mem (hKN hk))⟩
  obtain ⟨y, hy, c, hcC, rfl⟩ := h.exists_mul_eq_of_omega hΩ hc (yamadaC2_le hx)
  have hyC2 : y ∈ yamadaC2 D t := by
    have := mul_mem hx (inv_mem (hCle hcC))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (h.toddE_le_inf_centralizer_toddA (hQ (mem_inf.2 ⟨hyC2, hy⟩))) hcC

end Setting

theorem Setting.yamada_4_3_of {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {D : ToddParabolic L} {t : G} (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t})
    (hc : ∃ c ∈ normalizer (toddE D t : Set G), (∀ a ∈ toddA D, c * a = a * c) ∧ c * t ≠ t * c) :
    (∀ x ∈ normalizer (toddE D t : Set G), ∃ y ∈ normalizer (toddA D : Set G) ⊓
        centralizer ({t} : Set G), ∃ c ∈ yamadaC2 D t, x = y * c) ∧
      centralizer ({t} : Set G) ⊓ yamadaC2 D t = toddE D t ∧
      (center (yamadaC2 D t)).map (yamadaC2 D t).subtype = toddA D ∧
      (∀ c ∈ yamadaC2 D t, c * t * c⁻¹ * t ∈ toddA D) ∧
      (∀ c ∈ yamadaC2 D t, ∀ d ∈ yamadaC2 D t,
        c * d * t * (c * d)⁻¹ * t = (c * t * c⁻¹ * t) * (d * t * d⁻¹ * t)) ∧
      (∀ a ∈ toddA D, ∃ c ∈ yamadaC2 D t, c * t * c⁻¹ * t = a) ∧
      (∀ c ∈ yamadaC2 D t, c * t * c⁻¹ * t = 1 ↔ c ∈ toddE D t) := by
  rw [h.yamadaC2_eq hΩ hc]
  refine ⟨fun x hx => h.exists_mul_eq_of_omega hΩ hc hx, ?_, ?_,
    fun c hc => h.conj_t_mul_t_mem hΩ hc.1, fun c hc d hd => h.conj_t_mul_t_mul hΩ hc hd.1,
    fun a ha => h.exists_conj_t_mul_t_eq hΩ hc ha, fun c hc => h.conj_t_mul_t_eq_one_iff hc⟩
  · refine le_antisymm (fun c hc => (h.conj_t_mul_t_eq_one_iff hc.2).1 ?_)
      (le_inf h.toddE_le_H h.toddE_le_inf_centralizer_toddA)
    rw [mem_centralizer_singleton_iff.1 hc.1, mul_inv_cancel_right, ← sq, h.t_sq]
  · set C := normalizer (toddE D t : Set G) ⊓ centralizer (toddA D : Set G) with hC
    have htC : t ∈ C := h.toddE_le_inf_centralizer_toddA (t_mem_toddE D t)
    obtain ⟨c₀, hc₀X, hc₀A, hc₀t⟩ := hc
    have hc₀C : c₀ ∈ C := mem_inf.2 ⟨hc₀X, mem_centralizer_iff.2 fun a ha => (hc₀A a ha).symm⟩
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff] at hz
      have hzt : (z : G) * t = t * z := (congrArg Subtype.val (hz ⟨t, htC⟩)).symm
      have hzE : (z : G) ∈ toddE D t := (h.conj_t_mul_t_eq_one_iff z.2).1 (by
        rw [hzt, mul_inv_cancel_right, ← sq, h.t_sq])
      obtain ⟨a, ha, hza | hza⟩ := h.eq_or_eq_mul_of_mem_toddE hzE
      · show (z : G) ∈ toddA D
        rw [hza]
        exact ha
      · exfalso
        apply hc₀t
        have h1 : c₀ * (a * t) = a * t * c₀ := by
          rw [← hza]
          exact congrArg Subtype.val (hz ⟨c₀, hc₀C⟩)
        refine mul_left_cancel (a := a) ?_
        calc a * (c₀ * t) = c₀ * a * t := by rw [← mul_assoc, hc₀A a ha]
          _ = c₀ * (a * t) := by rw [mul_assoc]
          _ = a * t * c₀ := h1
          _ = a * (t * c₀) := by rw [mul_assoc]
    · intro hz
      refine ⟨⟨z, h.toddE_le_inf_centralizer_toddA (toddA_le_toddE D t hz)⟩,
        mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact (mem_centralizer_iff.1 (mem_inf.1 g.2).2 z hz).symm

end CFSG.EvenSmallLie.UnitarySix.Yamada
