module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

@[expose] def gmsN₁ (L T : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ normalizer (gmsV L T : Set G) ∧ n ∈ normalizer (gmsA L T : Set G) ∧
    ∀ v ∈ gmsV L T, n * v * n⁻¹ * v⁻¹ ∈ gmsA L T}
  one_mem' := ⟨one_mem _, one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro n m ⟨hnV, hnA, hn⟩ ⟨hmV, hmA, hm⟩
    refine ⟨mul_mem hnV hmV, mul_mem hnA hmA, fun v hv => ?_⟩
    have h1 : n * (m * v * m⁻¹ * v⁻¹) * n⁻¹ ∈ gmsA L T :=
      (mem_normalizer_iff.mp hnA _).mp (hm v hv)
    have : n * m * v * (n * m)⁻¹ * v⁻¹ =
        n * (m * v * m⁻¹ * v⁻¹) * n⁻¹ * (n * v * n⁻¹ * v⁻¹) := by group
    rw [this]
    exact mul_mem h1 (hn v hv)
  inv_mem' := by
    rintro n ⟨hnV, hnA, hn⟩
    refine ⟨inv_mem hnV, inv_mem hnA, fun v hv => ?_⟩
    have h1 : n⁻¹ * (n * v * n⁻¹ * v⁻¹)⁻¹ * n⁻¹⁻¹ ∈ gmsA L T :=
      (mem_normalizer_iff.mp (inv_mem hnA) _).mp (inv_mem (hn v hv))
    have : n⁻¹ * v * n⁻¹⁻¹ * v⁻¹ = n⁻¹ * (n * v * n⁻¹ * v⁻¹)⁻¹ * n⁻¹⁻¹ := by group
    rw [this]
    exact h1

@[expose] def gmsTrans (L T : Subgroup G) : Subgroup G :=
  gmsN₁ L T ⊓ centralizer (gmsA L T : Set G)

@[expose] def deltaPerm (L T : Subgroup G) :
    normalizer (gmsV L T : Set G) →* Equiv.Perm (gmsDelta L T) where
  toFun n :=
    { toFun := fun Q => ⟨rightConjugate Q (n : G)⁻¹,
        Sec3.rightConjugate_mem_delta Q.2 (inv_mem n.2)⟩
      invFun := fun Q => ⟨rightConjugate Q n, Sec3.rightConjugate_mem_delta Q.2 n.2⟩
      left_inv := fun Q => Subtype.ext (by
        simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one])
      right_inv := fun Q => Subtype.ext (by
        simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]) }
  map_one' := Equiv.ext fun Q => Subtype.ext (by simp [rightConjugate_one])
  map_mul' n m := Equiv.ext fun Q => Subtype.ext (by
    simp [rightConjugate_mul, mul_inv_rev])

variable {L T : Subgroup G}

omit [Finite G] in
theorem mem_gmsN₁ {n : G} : n ∈ gmsN₁ L T ↔ n ∈ normalizer (gmsV L T : Set G) ∧
    n ∈ normalizer (gmsA L T : Set G) ∧ ∀ v ∈ gmsV L T, n * v * n⁻¹ * v⁻¹ ∈ gmsA L T :=
  Iff.rfl

omit [Finite G] in
theorem deltaPerm_apply (n : normalizer (gmsV L T : Set G)) (Q : gmsDelta L T) :
    ((deltaPerm L T n Q : gmsDelta L T) : Subgroup G) = rightConjugate Q (n : G)⁻¹ :=
  rfl

omit [Finite G] in
theorem deltaPerm_apply_eq_iff (n : normalizer (gmsV L T : Set G)) (Q : gmsDelta L T) :
    deltaPerm L T n Q = Q ↔ (n : G) ∈ normalizer ((Q : Subgroup G) : Set G) := by
  rw [Subtype.ext_iff, deltaPerm_apply, rightConjugate_eq_self_iff, inv_mem_iff]

omit [Finite G] in
theorem deltaPerm_eq_one_of_commute {n : normalizer (gmsV L T : Set G)}
    (hn : ∀ v ∈ gmsV L T, (n : G) * v = v * n) : deltaPerm L T n = 1 := by
  refine Equiv.ext fun Q => ?_
  rw [Equiv.Perm.one_apply, deltaPerm_apply_eq_iff]
  exact Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun d hd => (hn d (Q.2.2 hd)).symm)

omit [Finite G] in
theorem gmsA_le_normalizer :
    gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun a ha => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ ht =>
    (mem_centralizer_iff.mp (mem_inf.mp ht).2 a (mem_inf.mp (mem_inf.mp ha).1).2).symm)

omit [Finite G] in
theorem commute_gmsV {x : G} (hA : ∀ a ∈ gmsA L T, x * a = a * x)
    (hT : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t = t * x) :
    ∀ v ∈ gmsV L T, x * v = v * x := by
  intro v hv
  obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer gmsA_le_normalizer hv
  rw [← mul_assoc, hA a ha, mul_assoc, hT t ht, mul_assoc]

omit [Finite G] in
theorem conj_mem_centralizer {g : G} (hg : g ∈ normalizer (gmsV L T : Set G)) {c : G}
    (hc : c ∈ centralizer (gmsV L T : Set G)) : g * c * g⁻¹ ∈ centralizer (gmsV L T : Set G) := by
  refine mem_centralizer_iff.mpr fun v hv => ?_
  have hv' : g⁻¹ * v * g ∈ gmsV L T := by
    simpa using (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
  have h1 : g⁻¹ * v * g * c = c * (g⁻¹ * v * g) := mem_centralizer_iff.mp hc _ hv'
  calc v * (g * c * g⁻¹) = g * (g⁻¹ * v * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

namespace Sec3

variable {q : ℕ}

omit [Finite G] in
theorem conj_mem_gmsN₁ (h313 : Lemma313 L T q) {g : G} (hg : g ∈ normalizer (gmsV L T : Set G))
    {n : G} (hn : n ∈ gmsN₁ L T) : g * n * g⁻¹ ∈ gmsN₁ L T := by
  obtain ⟨hnV, hnA, hn⟩ := hn
  have hgA := h313.normalizer_le hg
  refine ⟨mul_mem (mul_mem hg hnV) (inv_mem hg), mul_mem (mul_mem hgA hnA) (inv_mem hgA),
    fun v hv => ?_⟩
  have hv' : g⁻¹ * v * g ∈ gmsV L T := by
    simpa using (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
  have h1 := (mem_normalizer_iff.mp hgA _).mp (hn _ hv')
  have : g * n * g⁻¹ * v * (g * n * g⁻¹)⁻¹ * v⁻¹ =
      g * (n * (g⁻¹ * v * g) * n⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ := by group
  rw [this]
  exact h1

omit [Finite G] in
theorem conj_mem_gmsTrans (h313 : Lemma313 L T q) {g : G} (hg : g ∈ normalizer (gmsV L T : Set G))
    {u : G} (hu : u ∈ gmsTrans L T) : g * u * g⁻¹ ∈ gmsTrans L T := by
  obtain ⟨huN, huC⟩ := mem_inf.mp hu
  have hgA := h313.normalizer_le hg
  refine mem_inf.mpr ⟨conj_mem_gmsN₁ h313 hg huN, mem_centralizer_iff.mpr fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g ∈ gmsA L T := by
    simpa using (mem_normalizer_iff.mp (inv_mem hgA) a).mp ha
  have h1 : g⁻¹ * a * g * u = u * (g⁻¹ * a * g) := mem_centralizer_iff.mp huC _ ha'
  calc a * (g * u * g⁻¹) = g * (g⁻¹ * a * g * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = g * u * g⁻¹ * a := by group

omit [Finite G] in
theorem IsTorus.mem_gmsN₁ {y : G} (hy : IsTorus L T y) : y ∈ gmsN₁ L T := by
  refine ⟨hy.mem_normalizer, hy.mem_normalizer_gmsA, fun v hv => ?_⟩
  obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer gmsA_le_normalizer hv
  have hyt : y * t = t * y := hy.commute ht
  have : y * (a * t) * y⁻¹ * (a * t)⁻¹ = y * a * y⁻¹ * a⁻¹ := by
    calc y * (a * t) * y⁻¹ * (a * t)⁻¹ = y * a * (y⁻¹ * (y * t) * y⁻¹ * t⁻¹) * a⁻¹ := by group
      _ = y * a * y⁻¹ * a⁻¹ := by rw [hyt]; group
  rw [this]
  exact mul_mem ((mem_normalizer_iff.mp hy.mem_normalizer_gmsA a).mp ha) (inv_mem ha)

omit [Finite G] in
theorem conj_eq_of_mem_gmsN₁ (h313 : Lemma313 L T q) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T)
    {n : G} (hn : n ∈ gmsN₁ L T) (hnQ : n ∈ normalizer (Q : Set G)) {d : G} (hd : d ∈ Q) :
    n * d * n⁻¹ = d := by
  have h1 : n * d * n⁻¹ * d⁻¹ ∈ Q ⊓ gmsA L T :=
    mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hnQ d).mp hd) (inv_mem hd), hn.2.2 d (hQ.2 hd)⟩
  rw [h313.inf_gmsA_eq_bot hQ, mem_bot, mul_inv_eq_one] at h1
  exact h1

end Sec3

end CFSG.ComponentClassification.GMS78
