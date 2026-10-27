module

public import CFSG.Certificates.ExtraspecialNormalForm

public section

namespace CFSG.EvenSporadicStandard.ThStd

variable {G : Type*} [Group G]

@[expose] def prodBits (g : Fin 4 → G) (e : Fin 4 → ZMod 2) : G :=
  g 0 ^ (e 0).val * g 1 ^ (e 1).val * g 2 ^ (e 2).val * g 3 ^ (e 3).val

theorem closure_range_comm (g : Fin 4 → G) (hcomm : ∀ i j, g i * g j = g j * g i) :
    ∀ x ∈ Subgroup.closure (Set.range g), ∀ y ∈ Subgroup.closure (Set.range g), x * y = y * x := by
  have h : ∀ x ∈ Subgroup.closure (Set.range g), ∀ y ∈ Subgroup.closure (Set.range g),
      x * y = y * x := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => ∀ y ∈ Subgroup.closure (Set.range g),
      x * y = y * x) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩ y hy
      refine Subgroup.closure_induction (p := fun y _ => g i * y = y * g i) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, rfl⟩
        exact hcomm i j
      · simp
      · intro a b _ _ ha hb
        rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
      · intro a _ ha
        calc g i * a⁻¹ = a⁻¹ * (a * g i) * a⁻¹ := by group
          _ = a⁻¹ * (g i * a) * a⁻¹ := by rw [ha]
          _ = a⁻¹ * g i := by group
    · intro y _
      simp
    · intro a b _ _ ha hb y hy
      rw [mul_assoc, hb y hy, ← mul_assoc, ha y hy, mul_assoc]
    · intro a _ ha y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha y hy]
        _ = y * a⁻¹ := by group
  exact h

theorem mul4_distrib {M : Type*} [CommMonoid M] (x0 y0 x1 y1 x2 y2 x3 y3 : M) :
    x0 * y0 * (x1 * y1) * (x2 * y2) * (x3 * y3) = (x0 * x1 * x2 * x3) * (y0 * y1 * y2 * y3) := by
  rw [mul_mul_mul_comm x0 y0 x1 y1, mul_mul_mul_comm (x0 * x1) (y0 * y1) x2 y2,
    mul_mul_mul_comm (x0 * x1 * x2) (y0 * y1 * y2) x3 y3]

section Card

variable (g : Fin 4 → G) (A : Subgroup G)

theorem sq_mem_of_closure (hcomm : ∀ i j, g i * g j = g j * g i) (hsq : ∀ i, g i * g i ∈ A) :
    ∀ x ∈ Subgroup.closure (Set.range g), x * x ∈ A := by
  have hHc := closure_range_comm g hcomm
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x * x ∈ A) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact hsq i
  · simp
  · intro a b ha hb haA hbA
    have e : (a * b) * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hHc a ha b hb]
        _ = a * a * (b * b) := by group
    rw [e]
    exact A.mul_mem haA hbA
  · intro a _ haA
    have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [e]
    exact A.inv_mem haA

theorem card_closure_four (hcomm : ∀ i j, g i * g j = g j * g i) (hsq : ∀ i, g i * g i ∈ A)
    (hA : A ≤ Subgroup.closure (Set.range g))
    (hindep : ∀ e : Fin 4 → ZMod 2, e ≠ 0 → prodBits g e ∉ A) :
    Nat.card (Subgroup.closure (Set.range g)) = Nat.card A * 16 := by
  classical
  set H := Subgroup.closure (Set.range g) with hH
  have hHc := closure_range_comm g hcomm
  have hsqH := sq_mem_of_closure g A hcomm hsq
  let _ : CommGroup ↥H :=
    { (inferInstance : Group ↥H) with mul_comm := fun a b => Subtype.ext (hHc a a.2 b b.2) }
  let N : Subgroup ↥H := A.subgroupOf H
  let gH : Fin 4 → ↥H := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let gb : Fin 4 → ↥H ⧸ N := fun i => QuotientGroup.mk (gH i)
  have hgb : ∀ i, gb i * gb i = 1 := fun i => by
    show QuotientGroup.mk (gH i) * QuotientGroup.mk (gH i) = 1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (hsq i)
  have hq2 : ∀ x : ↥H ⧸ N, x * x = 1 := fun x => by
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 (hsqH x x.2)
  have hmemP : ∀ e : Fin 4 → ZMod 2, prodBits g e ∈ H := fun e => by
    unfold prodBits
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.pow_mem (Subgroup.subset_closure ⟨0, rfl⟩) _)
      (H.pow_mem (Subgroup.subset_closure ⟨1, rfl⟩) _))
      (H.pow_mem (Subgroup.subset_closure ⟨2, rfl⟩) _))
      (H.pow_mem (Subgroup.subset_closure ⟨3, rfl⟩) _)
  let Φ : Multiplicative (Fin 4 → ZMod 2) →* ↥H ⧸ N :=
    MonoidHom.mk' (fun e => gb 0 ^ (e.toAdd 0).val * gb 1 ^ (e.toAdd 1).val *
      gb 2 ^ (e.toAdd 2).val * gb 3 ^ (e.toAdd 3).val) (fun a b => by
      simp only [toAdd_mul, Pi.add_apply]
      rw [CFSG.Certificates.ExtraspecialNF.pow_val_add (hgb 0),
        CFSG.Certificates.ExtraspecialNF.pow_val_add (hgb 1),
        CFSG.Certificates.ExtraspecialNF.pow_val_add (hgb 2),
        CFSG.Certificates.ExtraspecialNF.pow_val_add (hgb 3)]
      exact mul4_distrib _ _ _ _ _ _ _ _)
  have hΦ : ∀ e : Fin 4 → ZMod 2, Φ (Multiplicative.ofAdd e) =
      QuotientGroup.mk (⟨prodBits g e, hmemP e⟩ : ↥H) := fun e => by
    have : (⟨prodBits g e, hmemP e⟩ : ↥H) =
        gH 0 ^ (e 0).val * gH 1 ^ (e 1).val * gH 2 ^ (e 2).val * gH 3 ^ (e 3).val :=
      Subtype.ext (by simp [prodBits, gH])
    rw [this]
    simp [Φ, gb, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    obtain ⟨e', rfl⟩ : ∃ e' : Fin 4 → ZMod 2, Multiplicative.ofAdd e' = e := ⟨e.toAdd, rfl⟩
    rw [hΦ, QuotientGroup.eq_one_iff] at he
    have hP : prodBits g e' ∈ A := Subgroup.mem_subgroupOf.1 he
    by_contra hne
    exact hindep e' (fun h => hne (by rw [h]; rfl)) hP
  have hsurj : Function.Surjective Φ := by
    have hgen : Subgroup.closure (((↑) : H → G) ⁻¹' Set.range g) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ Subgroup.closure (((↑) : H → G) ⁻¹' Set.range g) := by
        rw [hgen]
        exact Subgroup.mem_top x
      refine Subgroup.closure_induction (p := fun x _ => QuotientGroup.mk x ∈ Φ.range)
        ?_ ?_ ?_ ?_ hx
      · rintro y ⟨i, hi⟩
        have hy : y = gH i := Subtype.ext hi.symm
        rw [hy]
        refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
        fin_cases i <;> simp [Φ, gb, CFSG.Certificates.ExtraspecialNF.val_one_two]
      · exact ⟨1, by simp⟩
      · intro a b _ _ ha hb
        rw [QuotientGroup.mk_mul]
        exact Φ.range.mul_mem ha hb
      · intro a _ ha
        rw [QuotientGroup.mk_inv]
        exact Φ.range.inv_mem ha
  have hΦcard : Nat.card (↥H ⧸ N) = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)]
    simp [Nat.card_eq_fintype_card]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hΦcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h1
  rw [h1, mul_comm]

end Card

end CFSG.EvenSporadicStandard.ThStd
