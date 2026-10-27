module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineDelta
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3L3 Equiv

section Fixc

variable {Γ : Type} [Group Γ] (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]

@[expose] def fixc (x y : Γ) : ℕ :=
  (Finset.univ.filter fun p : X => x • p = p ∧ y • p = p).card

theorem fixc_conj (l x y : Γ) : fixc X (l * x * l⁻¹) (l * y * l⁻¹) = fixc X x y := by
  unfold fixc
  refine Finset.card_nbij' (fun p => l⁻¹ • p) (fun p => l • p) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := congrArg (fun q => l⁻¹ • q) h1
      simpa [mul_smul] using this
    · have := congrArg (fun q => l⁻¹ • q) h2
      simpa [mul_smul] using this
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := congrArg (fun q => l • q) h1
      simpa [mul_smul] using this
    · have := congrArg (fun q => l • q) h2
      simpa [mul_smul] using this
  · intro p _
    simp
  · intro p _
    simp

theorem fixc_comm (x y : Γ) : fixc X x y = fixc X y x := by
  unfold fixc
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

theorem fixc_shear (x y : Γ) : fixc X x (x * y) = fixc X x y := by
  unfold fixc
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mul_smul] at h2
    exact smul_left_cancel x (h2.trans h1.symm)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mul_smul, h2, h1]

end Fixc

section Fibre

variable {Γ : Type} [Group Γ] (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]

theorem add_self_V5 (w : V5) : w + w = 0 := by
  apply Subtype.ext
  funext i
  exact CharTwo.add_self_eq_zero (w.1 i)

theorem vact_eq_zero_iff (σ : Perm (Fin 5)) (w : V5) : vact σ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have := congrArg (vact σ⁻¹) h
    rw [← vact_mul, inv_mul_cancel, vact_one] at this
    rw [this]
    exact Subtype.ext (funext fun i => by simp [vact, pact])
  · rintro rfl
    exact Subtype.ext (funext fun i => by simp [vact, pact])

theorem vact_injective (σ : Perm (Fin 5)) : Function.Injective (vact σ) := by
  intro u w h
  have := congrArg (vact σ⁻¹) h
  rwa [← vact_mul, ← vact_mul, inv_mul_cancel, vact_one, vact_one] at this

theorem actP_mem {σ : Perm (Fin 5)} {p : V5 × V5} (hp : p ∈ pairs5) : actP σ p ∈ pairs5 := by
  simp only [pairs5, Finset.mem_filter, Finset.mem_univ, true_and, actP] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact h1 ((vact_eq_zero_iff σ p.1).1 h)
  · intro h
    exact h2 ((vact_eq_zero_iff σ p.2).1 h)
  · intro h
    exact h3 (vact_injective σ h)

theorem swp_mem {p : V5 × V5} (hp : p ∈ pairs5) : swp p ∈ pairs5 := by
  simp only [pairs5, Finset.mem_filter, Finset.mem_univ, true_and, swp] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨h2, h1, fun h => h3 h.symm⟩

theorem shr_mem {p : V5 × V5} (hp : p ∈ pairs5) : shr p ∈ pairs5 := by
  simp only [pairs5, Finset.mem_filter, Finset.mem_univ, true_and, shr] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, ?_, ?_⟩
  · intro h
    apply h3
    have h4 : p.1 + (p.1 + p.2) = p.1 + 0 := by rw [h]
    rw [← add_assoc, add_self_V5, zero_add, add_zero] at h4
    exact h4.symm
  · intro h
    apply h2
    have h4 : p.1 + p.1 = p.1 + (p.1 + p.2) := by rw [← h]
    rw [add_self_V5, ← add_assoc, add_self_V5, zero_add] at h4
    exact h4.symm

variable {E : Subgroup Γ} (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

@[expose] def fibre5 (v : ℕ) : Finset (V5 × V5) :=
  pairs5.filter fun p => fixc X (pt β p.1) (pt β p.2) = v

theorem closed5_fibre (h : Delta5Norm E β) (v : ℕ) : Closed5 (fibre5 X β v) where
  sub := Finset.filter_subset _ _
  act := by
    intro σ hσ p hp
    simp only [fibre5, Finset.mem_filter] at hp ⊢
    obtain ⟨l, hl, hact⟩ := h σ hσ
    refine ⟨actP_mem hp.1, ?_⟩
    have e1 := pt_vact β hl hact p.1
    have e2 := pt_vact β hl hact p.2
    simp only [actP]
    rw [e1, e2, fixc_conj]
    exact hp.2
  swp := by
    intro p hp
    simp only [fibre5, Finset.mem_filter] at hp ⊢
    refine ⟨swp_mem hp.1, ?_⟩
    simp only [swp]
    rw [fixc_comm]
    exact hp.2
  shr := by
    intro p hp
    simp only [fibre5, Finset.mem_filter] at hp ⊢
    refine ⟨shr_mem hp.1, ?_⟩
    simp only [shr]
    rw [pt_add, fixc_shear]
    exact hp.2

theorem delta5Norm_fibre_card (h : Delta5Norm E β) (v : ℕ) :
    (fibre5 X β v).card = 0 ∨ (fibre5 X β v).card = 60 ∨ (fibre5 X β v).card = 90 ∨
      (fibre5 X β v).card = 120 ∨ (fibre5 X β v).card = 150 ∨ (fibre5 X β v).card = 210 :=
  pairs5_fiber (closed5_fibre X β h v)

end Fibre

section PairCount

variable {Γ : Type} [Group Γ] (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]

@[expose] noncomputable def pairCount (E : Subgroup Γ) (v : ℕ) : ℕ :=
  {p : Γ × Γ | p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2 ∧ fixc X p.1 p.2 = v}.ncard

@[expose] def PairFibersAllowed (E : Subgroup Γ) : Prop :=
  ∀ v : ℕ, pairCount X E v = 0 ∨ pairCount X E v = 60 ∨ pairCount X E v = 90 ∨
    pairCount X E v = 120 ∨ pairCount X E v = 150 ∨ pairCount X E v = 210

theorem pt_injective' {E : Subgroup Γ} (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) :
    Function.Injective (pt β : V5 → Γ) := by
  intro u w h
  have h1 : β.symm (Multiplicative.ofAdd u) = β.symm (Multiplicative.ofAdd w) := Subtype.ext h
  exact Multiplicative.ofAdd.injective (β.symm.injective h1)

theorem pt_toAdd {E : Subgroup Γ} (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) (x : ↥E) :
    pt β (Multiplicative.toAdd (β x)) = (x : Γ) := by
  simp [pt]

theorem pairCount_eq_card_fibre5 {E : Subgroup Γ} (β : ↥E ≃* Multiplicative ↥(evenWeight 5))
    (v : ℕ) : pairCount X E v = (fibre5 X β v).card := by
  unfold pairCount
  have hset : {p : Γ × Γ | p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2 ∧
      fixc X p.1 p.2 = v} =
      (fun q : V5 × V5 => (pt β q.1, pt β q.2)) '' ((fibre5 X β v : Finset (V5 × V5)) :
        Set (V5 × V5)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, fibre5, Finset.mem_filter,
      pairs5, Finset.mem_univ, true_and, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hx, hy, hx1, hy1, hxy, hv⟩
      have hxe : pt β (Multiplicative.toAdd (β ⟨x, hx⟩)) = x := pt_toAdd β ⟨x, hx⟩
      have hye : pt β (Multiplicative.toAdd (β ⟨y, hy⟩)) = y := pt_toAdd β ⟨y, hy⟩
      refine ⟨Multiplicative.toAdd (β ⟨x, hx⟩), Multiplicative.toAdd (β ⟨y, hy⟩),
        ⟨⟨?_, ?_, ?_⟩, ?_⟩, hxe, hye⟩
      · intro h0
        apply hx1
        rw [← hxe, h0, pt_zero β]
      · intro h0
        apply hy1
        rw [← hye, h0, pt_zero β]
      · intro h0
        apply hxy
        rw [← hxe, ← hye, h0]
      · rw [hxe, hye]
        exact hv
    · rintro ⟨u, w, ⟨⟨hu, hw, huw⟩, hv⟩, rfl, rfl⟩
      refine ⟨pt_mem β u, pt_mem β w, ?_, ?_, ?_, hv⟩
      · intro h
        apply hu
        exact pt_injective' β (h.trans (pt_zero β).symm)
      · intro h
        apply hw
        exact pt_injective' β (h.trans (pt_zero β).symm)
      · intro h
        apply huw
        exact pt_injective' β h
  rw [hset, Set.ncard_image_of_injective, Set.ncard_coe_finset]
  intro q q' h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (pt_injective' β h.1) (pt_injective' β h.2)

theorem delta5Norm_pairFibersAllowed {E : Subgroup Γ}
    {β : ↥E ≃* Multiplicative ↥(evenWeight 5)} (h : Delta5Norm E β) :
    PairFibersAllowed X E := by
  intro v
  rw [pairCount_eq_card_fibre5 X β v]
  exact delta5Norm_fibre_card X β h v

end PairCount

section Basis

variable {Γ : Type} [Group Γ] (f : Fin 4 → Γ)

@[expose] def gE (a : ℕ) : Γ :=
  (if a.testBit 0 then f 0 else 1) * (if a.testBit 1 then f 1 else 1) *
    (if a.testBit 2 then f 2 else 1) * (if a.testBit 3 then f 3 else 1)

@[expose] def E4 : Subgroup Γ := Subgroup.closure (Set.range f)

theorem E4_comm (hc : ∀ s t, f s * f t = f t * f s) :
    ∀ x ∈ E4 f, ∀ y ∈ E4 f, x * y = y * x := by
  have h1 : E4 f ≤ Subgroup.centralizer (Set.range f) := by
    rw [E4, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    exact (hc t s)
  intro x hx y hy
  have h2 : ∀ z ∈ Set.range f, z * x = x * z := fun z hz =>
    Subgroup.mem_centralizer_iff.1 (h1 hx) z hz
  have h3 : E4 f ≤ Subgroup.centralizer {x} := by
    rw [E4, Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact (h2 z hz).symm
  exact Subgroup.mem_centralizer_iff.1 (h3 hy) x rfl

theorem gE_mem (a : ℕ) : gE f a ∈ E4 f := by
  have hf : ∀ t, f t ∈ E4 f := fun t => Subgroup.subset_closure ⟨t, rfl⟩
  unfold gE
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;> split_ifs <;>
    first | exact one_mem _ | exact hf _

theorem gE_zero : gE f 0 = 1 := by simp [gE]

theorem gE_two_pow_0 : gE f 1 = f 0 := by simp [gE, Nat.testBit]

theorem gE_two_pow_1 : gE f 2 = f 1 := by simp [gE, Nat.testBit]

theorem gE_two_pow_2 : gE f 4 = f 2 := by simp [gE, Nat.testBit]

theorem gE_two_pow_3 : gE f 8 = f 3 := by simp [gE, Nat.testBit]

@[expose, instance_reducible] noncomputable def e4CommGroup (hc : ∀ s t, f s * f t = f t * f s) :
    CommGroup ↥(E4 f) :=
  { (inferInstance : Group ↥(E4 f)) with
    mul_comm := fun x y => Subtype.ext (E4_comm f hc x.1 x.2 y.1 y.2) }

theorem ite_testBit_xor {M : Type*} [Monoid M] (t : ℕ) (u : M) (hu : u * u = 1) (a b : ℕ) :
    (if (a ^^^ b).testBit t then u else 1) =
      (if a.testBit t then u else 1) * (if b.testBit t then u else 1) := by
  simp only [Nat.testBit_xor]
  cases a.testBit t <;> cases b.testBit t <;> simp [hu]

theorem gE_xor (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s) (a b : ℕ) :
    gE f (a ^^^ b) = gE f a * gE f b := by
  let _ : CommGroup ↥(E4 f) := e4CommGroup f hc
  let f' : Fin 4 → ↥(E4 f) := fun t => ⟨f t, Subgroup.subset_closure ⟨t, rfl⟩⟩
  have hsq' : ∀ t, f' t * f' t = 1 := fun t => Subtype.ext (hsq t)
  have key : ∀ a, gE f a = (((if a.testBit 0 then f' 0 else 1) * (if a.testBit 1 then f' 1 else 1) *
      (if a.testBit 2 then f' 2 else 1) * (if a.testBit 3 then f' 3 else 1) : ↥(E4 f)) : Γ) := by
    intro a
    simp only [gE, f', Subgroup.coe_mul]
    split_ifs <;> simp
  rw [key, key, key, ← Subgroup.coe_mul]
  congr 1
  rw [ite_testBit_xor 0 (f' 0) (hsq' 0), ite_testBit_xor 1 (f' 1) (hsq' 1),
    ite_testBit_xor 2 (f' 2) (hsq' 2), ite_testBit_xor 3 (f' 3) (hsq' 3)]
  ac_rfl

theorem xor_lt_16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 := by
  have := Nat.xor_lt_two_pow (n := 4) (x := a) (y := b) (by simpa using ha) (by simpa using hb)
  simpa using this

theorem gE_self_mul (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s) (a : ℕ) :
    gE f a * gE f a = 1 := by
  rw [← gE_xor f hsq hc, Nat.xor_self, gE_zero]

theorem exists_gE (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s) :
    ∀ x ∈ E4 f, ∃ a, a < 16 ∧ gE f a = x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    fin_cases t
    · exact ⟨1, by norm_num, gE_two_pow_0 f⟩
    · exact ⟨2, by norm_num, gE_two_pow_1 f⟩
    · exact ⟨4, by norm_num, gE_two_pow_2 f⟩
    · exact ⟨8, by norm_num, gE_two_pow_3 f⟩
  | one => exact ⟨0, by norm_num, gE_zero f⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, rfl⟩ := ihx
    obtain ⟨b, hb, rfl⟩ := ihy
    exact ⟨a ^^^ b, xor_lt_16 ha hb, gE_xor f hsq hc a b⟩
  | inv x _ ih =>
    obtain ⟨a, ha, rfl⟩ := ih
    exact ⟨a, ha, (inv_eq_of_mul_eq_one_right (gE_self_mul f hsq hc a)).symm⟩

theorem gE_inj (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s)
    (hcard : Nat.card (E4 f) = 16) : ∀ a < 16, ∀ b < 16, gE f a = gE f b → a = b := by
  have hfin : Finite ↥(E4 f) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ : Fintype ↥(E4 f) := Fintype.ofFinite _
  let L : Fin 16 → ↥(E4 f) := fun a => ⟨gE f a, gE_mem f a⟩
  have hsurj : Function.Surjective L := by
    intro x
    obtain ⟨a, ha, hx⟩ := exists_gE f hsq hc x.1 x.2
    exact ⟨⟨a, ha⟩, Subtype.ext hx⟩
  have hbij : Function.Bijective L := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨hsurj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  intro a ha b hb hab
  have := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hab)
  simpa using this

@[expose] def pairs4 : Finset (ℕ × ℕ) :=
  (Finset.range 16 ×ˢ Finset.range 16).filter fun p => 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2

theorem mem_pairs4 {p : ℕ × ℕ} :
    p ∈ pairs4 ↔ (p.1 < 16 ∧ p.2 < 16) ∧ 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2 := by
  simp only [pairs4, Finset.mem_filter, Finset.mem_product, Finset.mem_range]

theorem pairCount_eq_of_basis (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]
    (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s)
    (hcard : Nat.card (E4 f) = 16) (v : ℕ) :
    pairCount X (E4 f) v =
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card := by
  unfold pairCount
  have hinj := gE_inj f hsq hc hcard
  have hset : {p : Γ × Γ | p.1 ∈ E4 f ∧ p.2 ∈ E4 f ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2 ∧
      fixc X p.1 p.2 = v} =
      (fun q : ℕ × ℕ => (gE f q.1, gE f q.2)) ''
        ((pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter, pairs4,
      Finset.mem_product, Finset.mem_range, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hx, hy, hx1, hy1, hxy, hv⟩
      obtain ⟨a, ha, rfl⟩ := exists_gE f hsq hc x hx
      obtain ⟨b, hb, rfl⟩ := exists_gE f hsq hc y hy
      refine ⟨a, b, ⟨⟨⟨ha, hb⟩, ?_, ?_, ?_⟩, hv⟩, rfl, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h0 | h0
        · exact absurd (by rw [h0, gE_zero]) hx1
        · exact h0
      · rcases Nat.eq_zero_or_pos b with h0 | h0
        · exact absurd (by rw [h0, gE_zero]) hy1
        · exact h0
      · intro h
        exact hxy (by rw [h])
    · rintro ⟨a, b, ⟨⟨⟨ha, hb⟩, ha0, hb0, hab⟩, hv⟩, rfl, rfl⟩
      refine ⟨gE_mem f a, gE_mem f b, ?_, ?_, ?_, hv⟩
      · intro h
        have := hinj a ha 0 (by norm_num) (by rw [h, gE_zero])
        omega
      · intro h
        have := hinj b hb 0 (by norm_num) (by rw [h, gE_zero])
        omega
      · intro h
        exact hab (hinj a ha b hb h)
  rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro q hq q' hq' h
  have h1 := mem_pairs4.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).1
  have h2 := mem_pairs4.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).1
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (hinj _ h1.1.1 _ h2.1.1 h.1) (hinj _ h1.1.2 _ h2.1.2 h.2)

theorem not_pairFibersAllowed_of_basis (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]
    (hsq : ∀ t, f t * f t = 1) (hc : ∀ s t, f s * f t = f t * f s)
    (hcard : Nat.card (E4 f) = 16) (v : ℕ)
    (hbad : ¬ ((pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 0 ∨
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 60 ∨
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 90 ∨
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 120 ∨
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 150 ∨
      (pairs4.filter fun p => fixc X (gE f p.1) (gE f p.2) = v).card = 210)) :
    ¬ PairFibersAllowed X (E4 f) := by
  intro h
  apply hbad
  have := h v
  rwa [pairCount_eq_of_basis f X hsq hc hcard] at this

end Basis

end CFSG.QuasithinUnique.A5.Kc3SporLine
