module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

theorem exists_mul_inv_map_eq_of_norm {A : Type*} [CommGroup A] (φ : A →* A)
    (hcop : Nat.Coprime (Nat.card A) 3) (a : A) (ha : a * φ a * φ (φ a) = 1) :
    ∃ t : A, t * (φ t)⁻¹ = a := by
  have hφ2 : φ (φ a) = (a * φ a)⁻¹ := eq_inv_of_mul_eq_one_right ha
  obtain ⟨t, ht⟩ := (powCoprime hcop).surjective (a ^ 2 * φ a)
  have ht3 : t ^ 3 = a ^ 2 * φ a := ht
  refine ⟨t, (powCoprime hcop).injective ?_⟩
  show (t * (φ t)⁻¹) ^ 3 = a ^ 3
  have h1 : (t * (φ t)⁻¹) ^ 3 = t ^ 3 * (φ (t ^ 3))⁻¹ := by
    rw [mul_pow, inv_pow, map_pow]
  rw [h1, ht3, map_mul, map_pow, hφ2]
  simp only [mul_inv_rev, inv_inv]
  simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

theorem exists_lift_mem_centralizer {N : Type*} [Group N] (T : Subgroup N) [T.Normal]
    (hT : ∀ t ∈ T, ∀ u ∈ T, t * u = u * t) (hcop : Nat.Coprime 3 (Nat.card T)) (s : N)
    (hs : s ^ 3 = 1) (c : N)
    (hc : (QuotientGroup.mk c : N ⧸ T) ∈
      Subgroup.centralizer ({(QuotientGroup.mk s : N ⧸ T)} : Set (N ⧸ T))) :
    ∃ c' ∈ Subgroup.centralizer ({s} : Set N),
      (QuotientGroup.mk c' : N ⧸ T) = QuotientGroup.mk c := by
  let _ : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun a b => Subtype.ext (hT _ a.2 _ b.2) }
  let σ : T →* T :=
    { toFun := fun t => ⟨s * t * s⁻¹, ‹T.Normal›.conj_mem t t.2 s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show s * ((a : N) * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹)
        group) }
  have hσ : ∀ t : T, ((σ t : T) : N) = s * t * s⁻¹ := fun t => rfl
  set κ : N := c * s * c⁻¹ * s⁻¹ with hκdef
  have hcomm : (QuotientGroup.mk c : N ⧸ T) * QuotientGroup.mk s =
      QuotientGroup.mk s * QuotientGroup.mk c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hκ : κ ∈ T := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [hκdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm]
    group
  have hcs : c * s = κ * s * c := by rw [hκdef]; group
  have hcube : κ * s * κ * s * κ * s = 1 := by
    have h1 : (κ * s) ^ 3 = 1 := by
      have : κ * s = c * s * c⁻¹ := by rw [hκdef]; group
      rw [this, conj_pow, hs]
      group
    simpa [pow_succ, mul_assoc] using h1
  set kT : T := ⟨κ, hκ⟩ with hkT
  have hnorm : kT * σ kT * σ (σ kT) = 1 := by
    apply Subtype.ext
    show κ * (s * κ * s⁻¹) * (s * (s * κ * s⁻¹) * s⁻¹) = 1
    calc κ * (s * κ * s⁻¹) * (s * (s * κ * s⁻¹) * s⁻¹)
        = (κ * s * κ * s * κ * s) * (s ^ 3)⁻¹ := by group
      _ = 1 := by rw [hcube, hs]; simp
  have hnorm' : kT⁻¹ * σ kT⁻¹ * σ (σ kT⁻¹) = 1 := by
    simp only [map_inv]
    rw [← mul_inv, ← mul_inv, hnorm, inv_one]
  obtain ⟨t, ht⟩ := exists_mul_inv_map_eq_of_norm σ hcop.symm kT⁻¹ hnorm'
  have ht' : (t : N) * (s * t * s⁻¹)⁻¹ = κ⁻¹ := by
    have := congrArg Subtype.val ht
    simpa [hσ] using this
  have ht2 : (t : N) = κ⁻¹ * (s * t * s⁻¹) := mul_inv_eq_iff_eq_mul.mp ht'
  have hκt : κ * t = s * t * s⁻¹ :=
    (congrArg (κ * ·) ht2).trans (by group)
  refine ⟨t * c, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * c * s = t * (c * s) := by group
      _ = t * (κ * s * c) := by rw [hcs]
      _ = (t * κ) * s * c := by group
      _ = (s * t * s⁻¹) * s * c := by rw [hT _ t.2 _ hκ, hκt]
      _ = s * (t * c) := by group
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (t : N)).mpr t.2, one_mul]

theorem card_centralizer_quotient_dvd {N : Type*} [Group N] [Finite N] (T : Subgroup N)
    [T.Normal] (hT : ∀ t ∈ T, ∀ u ∈ T, t * u = u * t) (hcop : Nat.Coprime 3 (Nat.card T))
    (s : N) (hs : s ^ 3 = 1) :
    Nat.card (Subgroup.centralizer ({(QuotientGroup.mk s : N ⧸ T)} : Set (N ⧸ T))) ∣
      Nat.card (Subgroup.centralizer ({s} : Set N)) := by
  let f : Subgroup.centralizer ({s} : Set N) →* N ⧸ T :=
    (QuotientGroup.mk' T).comp (Subgroup.centralizer ({s} : Set N)).subtype
  have hrange : f.range =
      Subgroup.centralizer ({(QuotientGroup.mk s : N ⧸ T)} : Set (N ⧸ T)) := by
    ext x
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (QuotientGroup.mk c : N ⧸ T) * QuotientGroup.mk s =
        QuotientGroup.mk s * QuotientGroup.mk c
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    · intro hx
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨c', hc', hc'c⟩ := exists_lift_mem_centralizer T hT hcop s hs c hx
      exact ⟨⟨c', hc'⟩, hc'c⟩
  have := Subgroup.card_ker_mul_card_range f
  rw [hrange] at this
  exact Dvd.intro_left _ this

theorem eightyOne_dvd_of_quotient {N : Type*} [Group N] [Finite N] (T : Subgroup N)
    [T.Normal] (hT : ∀ t ∈ T, ∀ u ∈ T, t * u = u * t) (hcop : Nat.Coprime 3 (Nat.card T))
    (s : N) (hs : s ^ 3 = 1)
    (h : 81 ∣ Nat.card (Subgroup.centralizer ({(QuotientGroup.mk s : N ⧸ T)} : Set (N ⧸ T)))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set N)) :=
  h.trans (card_centralizer_quotient_dvd T hT hcop s hs)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
