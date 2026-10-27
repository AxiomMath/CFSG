module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex
import Mathlib.Tactic.Group

open MulAction Subgroup Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {L : Type*} [Group L] {H E : Subgroup L}

theorem exists_mem_conj_eq_mul_of_inf_centralizer_eq_bot [H.Normal] [Finite H] {e : L}
    (hCe : H ⊓ centralizer ({e} : Set L) = ⊥) {h : L} (hh : h ∈ H) :
    ∃ k ∈ H, k * e * k⁻¹ = h * e := by
  set Hc : Subgroup (ConjAct L) := H.map (ConjAct.toConjAct : L ≃* ConjAct L).toMonoidHom with hHc
  have hmem : ∀ x : ConjAct L, x ∈ Hc ↔ ConjAct.ofConjAct x ∈ H := by
    intro x; rw [hHc, Subgroup.mem_map_equiv]; rfl
  have hact : ∀ x : (Hc : Type _), x • e = ConjAct.ofConjAct (x : ConjAct L) * e *
      (ConjAct.ofConjAct (x : ConjAct L))⁻¹ := fun x => by
    rw [Subgroup.smul_def, ConjAct.smul_def]
  have hcardHc : Nat.card (Hc : Type _) = Nat.card H :=
    Nat.card_congr (H.equivMapOfInjective _
      (ConjAct.toConjAct : L ≃* ConjAct L).injective).symm.toEquiv
  have : Finite (Hc : Type _) :=
    Nat.finite_of_card_ne_zero (by rw [hcardHc]; exact Nat.card_pos.ne')
  have hstab : stabilizer (Hc : Type _) e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_stabilizer_iff, hact] at hx
    have hx' : ConjAct.ofConjAct (x : ConjAct L) ∈ H ⊓ centralizer ({e} : Set L) := by
      refine ⟨(hmem _).1 x.2, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at hx
      exact hx
    rw [hCe, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  have hcard : Nat.card (orbit (Hc : Type _) e) = Nat.card H := by
    have h := natCard_orbit_mul_natCard_stabilizer (G := (Hc : Type _)) (X := L) e
    rw [hstab] at h
    simpa [hcardHc] using h
  have hsub : orbit (Hc : Type _) e ⊆ (fun k : L => k * e) '' (H : Set L) := by
    rintro y ⟨x, rfl⟩
    refine ⟨ConjAct.ofConjAct (x : ConjAct L) * e * (ConjAct.ofConjAct (x : ConjAct L))⁻¹ * e⁻¹,
      ?_, ?_⟩
    · have h1 : ConjAct.ofConjAct (x : ConjAct L) ∈ H := (hmem _).1 x.2
      have h2 : e * (ConjAct.ofConjAct (x : ConjAct L))⁻¹ * e⁻¹ ∈ H := by
        simpa using (Subgroup.Normal.conj_mem ‹H.Normal› _ (H.inv_mem h1) e)
      simpa [mul_assoc] using H.mul_mem h1 h2
    · change ConjAct.ofConjAct (x : ConjAct L) * e * (ConjAct.ofConjAct (x : ConjAct L))⁻¹ * e⁻¹ * e
        = x • e
      rw [hact]; group
  have hcardim : (((fun k : L => k * e) '' (H : Set L))).ncard = Nat.card H := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective e), ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.refl _)
  have heq : orbit (Hc : Type _) e = (fun k : L => k * e) '' (H : Set L) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hcardim, ← Nat.card_coe_set_eq, hcard]
  have hmemorb : h * e ∈ orbit (Hc : Type _) e := by rw [heq]; exact ⟨h, hh, rfl⟩
  obtain ⟨x, hx⟩ := hmemorb
  exact ⟨ConjAct.ofConjAct (x : ConjAct L), (hmem _).1 x.2, by rw [← hact]; exact hx⟩

theorem inf_centralizer_singleton_eq_bot_of_notMem [H.Normal] [Finite H]
    (hHE : H.IsComplement' E) (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set L) = ⊥)
    {y : L} (hy : y ∉ H) : H ⊓ centralizer ({y} : Set L) = ⊥ := by
  have hmul : (H : Set L) * (E : Set L) = Set.univ := hHE.mul_eq
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 (hmul.symm ▸ Set.mem_univ y)
  subst hab
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hy (by simpa using ha)
  obtain ⟨k, hk, hkeq⟩ := exists_mem_conj_eq_mul_of_inf_centralizer_eq_bot (H := H) (hC b hb hb1) ha
  rw [eq_bot_iff]
  rintro z ⟨hzH, hzc⟩
  have hzc' : z * (k * b * k⁻¹) = (k * b * k⁻¹) * z := by
    rw [hkeq]; exact mem_centralizer_singleton_iff.1 hzc
  have hcomm : (k⁻¹ * z * k) * b = b * (k⁻¹ * z * k) :=
    calc (k⁻¹ * z * k) * b = k⁻¹ * (z * (k * b * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * b * k⁻¹) * z) * k := by rw [hzc']
      _ = b * (k⁻¹ * z * k) := by group
  have hz1 : k⁻¹ * z * k ∈ H ⊓ centralizer ({b} : Set L) :=
    ⟨by simpa using ‹H.Normal›.conj_mem z hzH k⁻¹, mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [hC b hb hb1, Subgroup.mem_bot] at hz1
  rw [Subgroup.mem_bot]
  have hzeq : z = k * (k⁻¹ * z * k) * k⁻¹ := by group
  rw [hzeq, hz1]; group

theorem centralizer_singleton_le_of_mem_of_ne_one [H.Normal] [Finite H]
    (hHE : H.IsComplement' E) (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set L) = ⊥)
    {h : L} (hh : h ∈ H) (hh1 : h ≠ 1) : centralizer ({h} : Set L) ≤ H := by
  intro y hy
  by_contra hyH
  have hmem : h ∈ H ⊓ centralizer ({y} : Set L) :=
    ⟨hh, mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.1 hy).symm⟩
  rw [inf_centralizer_singleton_eq_bot_of_notMem hHE hC hyH, Subgroup.mem_bot] at hmem
  exact hh1 hmem

theorem inf_centralizer_singleton_eq_centralizer_singleton_of_mem_of_ne_one [H.Normal] [Finite H]
    (hHE : H.IsComplement' E) (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set L) = ⊥)
    {h : L} (hh : h ∈ H) (hh1 : h ≠ 1) :
    H ⊓ centralizer ({h} : Set L) = centralizer ({h} : Set L) :=
  inf_eq_right.mpr (centralizer_singleton_le_of_mem_of_ne_one hHE hC hh hh1)

end

end CFSG.FeitThompson
