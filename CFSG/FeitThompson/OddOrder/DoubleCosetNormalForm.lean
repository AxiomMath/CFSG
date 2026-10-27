module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
import CFSG.FeitThompson.OddOrder.PrimeLineFactorsProductOne

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Pointwise

variable {G : Type*} [Group G] {F : Type*} [Field F] {p q : ℕ}

variable {Pe : Multiplicative F →* G} {Ue : normOneUnits F →* G}

theorem primeLine_eq_map (Pe : Multiplicative F →* G) :
    primeLine Pe = (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup).map Pe := by
  ext g
  rw [mem_primeLine, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨ofAdd c, hc, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨toAdd x, hx, by simp⟩

theorem natCard_primeLine (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hPe : Function.Injective Pe) : Nat.card (primeLine Pe) = p := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : Fintype F := Fintype.ofFinite F
  rw [primeLine_eq_map]
  exact natCard_map_primeSubfield hp (by rwa [← Nat.card_eq_fintype_card]) Pe hPe

instance isMulCommutative_primeLine : IsMulCommutative (primeLine Pe) :=
  (primeLine_eq_map Pe) ▸ isMulCommutative_map _ _

theorem range_le_normalizer_range
    (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u)⁻¹ * Pe (ofAdd z) * Ue u = Pe (ofAdd (z * ((u : Fˣ) : F)))) :
    Ue.range ≤ Subgroup.normalizer Pe.range := by
  have hA : ∀ (u : normOneUnits F) (x : Multiplicative F),
      (Ue u)⁻¹ * Pe x * Ue u ∈ Pe.range := fun u x =>
    ⟨ofAdd (toAdd x * ((u : Fˣ) : F)), by rw [← hact (toAdd x) u]; simp⟩
  rintro g ⟨u, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨x, rfl⟩ := hw
    have h := hA u⁻¹ x
    rwa [map_inv, inv_inv] at h
  · obtain ⟨x, hx⟩ := hw
    have h := hA u x
    rw [hx] at h
    have e : (Ue u)⁻¹ * (Ue u * w * (Ue u)⁻¹) * Ue u = w := by group
    rwa [e] at h

theorem coe_range_sup_range (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u)⁻¹ * Pe (ofAdd z) * Ue u = Pe (ofAdd (z * ((u : Fˣ) : F)))) :
    ((Pe.range ⊔ Ue.range : Subgroup G) : Set G) = (Pe.range : Set G) * (Ue.range : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (range_le_normalizer_range hact)

theorem exists_mul_primeLine_mul_eq_map_ofAdd_mul (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u)⁻¹ * Pe (ofAdd z) * Ue u = Pe (ofAdd (z * ((u : Fˣ) : F))))
    (z : F) {b : G} (hb : b ∈ Ue.range) :
    ∃ u ∈ Ue.range, ∃ r ∈ primeLine Pe, ∃ v ∈ Ue.range, Pe (ofAdd z) * b = u * r * v := by
  by_cases hz : z = 0
  · exact ⟨1, one_mem _, Pe (ofAdd z), apply_ofAdd_mem_primeLine Pe (hz ▸ zero_mem _), b, hb,
      by rw [one_mul]⟩
  · obtain ⟨⟨c, w⟩, hcw, -⟩ := existsUnique_units_mul_eq hp hcard hcop (Units.mk0 z hz)
    have hz' : ((c : Fˣ) : F) * ((w : Fˣ) : F) = z := by
      simpa using congrArg Units.val hcw
    refine ⟨Ue w⁻¹, ⟨w⁻¹, rfl⟩, Pe (ofAdd ((c : Fˣ) : F)),
      apply_ofAdd_mem_primeLine Pe (mem_botSubfieldUnits.1 c.2), Ue w * b,
      mul_mem ⟨w, rfl⟩ hb, ?_⟩
    have h1 := hact ((c : Fˣ) : F) w
    rw [← hz', ← h1, map_inv]
    group

theorem exists_mul_primeLine_mul (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u)⁻¹ * Pe (ofAdd z) * Ue u = Pe (ofAdd (z * ((u : Fˣ) : F))))
    {h : G} (hh : h ∈ Pe.range ⊔ Ue.range) :
    ∃ u ∈ Ue.range, ∃ r ∈ primeLine Pe, ∃ v ∈ Ue.range, h = u * r * v := by
  rw [← SetLike.mem_coe, coe_range_sup_range hact] at hh
  obtain ⟨a, ⟨x, rfl⟩, b, hb, rfl⟩ := hh
  have hx : Pe x = Pe (ofAdd (toAdd x)) := by simp
  rw [hx]
  exact exists_mul_primeLine_mul_eq_map_ofAdd_mul hp hcard hcop hact (toAdd x) hb

theorem coe_range_sup_range_eq_mul_primeLine_mul (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u)⁻¹ * Pe (ofAdd z) * Ue u = Pe (ofAdd (z * ((u : Fˣ) : F)))) :
    ((Pe.range ⊔ Ue.range : Subgroup G) : Set G)
      = (Ue.range : Set G) * (primeLine Pe : Set G) * (Ue.range : Set G) := by
  refine Set.Subset.antisymm (fun h hh => ?_) ?_
  · obtain ⟨u, hu, r, hr, v, hv, rfl⟩ := exists_mul_primeLine_mul hp hcard hcop hact hh
    exact ⟨u * r, ⟨u, hu, r, hr, rfl⟩, v, hv, rfl⟩
  · rintro g ⟨-, ⟨u, hu, r, hr, rfl⟩, v, hv, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hu)
      (Subgroup.mem_sup_left (primeLine_le_range Pe hr))) (Subgroup.mem_sup_right hv)

theorem range_subtype_comp {P : Subgroup G} {A : Type*} [Group A] (e : A ≃* P) :
    (P.subtype.comp (e : A →* P)).range = P := by
  ext g
  refine ⟨?_, fun hg => ⟨e.symm ⟨g, hg⟩, by simp⟩⟩
  rintro ⟨a, rfl⟩
  exact (e a).2

theorem exists_mul_primeLine_mul_of_appendixC (hp : p.Prime) (_hq : q.Prime) (_hqp : q < p)
    (hcard : Nat.card F = p ^ q) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U)
    (_hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (u : normOneUnits F),
      (Ue u : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue u : G)
        = (Pe (ofAdd (z * ((u : Fˣ) : F))) : G))
    {Q : Subgroup G} (_hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x)
    (_hQp : Nat.Coprime (Nat.card Q) p)
    (_hQnorm : primeLine (P.subtype.comp (Pe : Multiplicative F →* P))
      ≤ Subgroup.normalizer Q)
    {y : G} (_hy : y ∈ Q)
    (_hP₁ : (primeLine (P.subtype.comp (Pe : Multiplicative F →* P))).map
      (MulAut.conj y⁻¹).toMonoidHom ≤ Subgroup.normalizer U)
    {h : G} (hh : h ∈ P ⊔ U) :
    ∃ u ∈ U, ∃ r ∈ primeLine (P.subtype.comp (Pe : Multiplicative F →* P)), ∃ v ∈ U,
      h = u * r * v := by
  have hP := range_subtype_comp Pe
  have hU := range_subtype_comp Ue
  rw [← hP, ← hU] at hh
  obtain ⟨u, hu, r, hr, v, hv, hEq⟩ := exists_mul_primeLine_mul hp hcard hcop hact hh
  exact ⟨u, hU ▸ hu, r, hr, v, hU ▸ hv, hEq⟩

end

end CFSG.FeitThompson
