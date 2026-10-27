module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Centralizer

variable {S : Type} [Group S]

theorem mem_centralizer_of_cj_fix {E : Subgroup S} (hN : E.Normal) (u : S)
    (h : ∀ x : E, cj hN u x = x) : u ∈ Subgroup.centralizer (E : Set S) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hx : cj hN u ⟨g, hg⟩ = ⟨g, hg⟩ := h ⟨g, hg⟩
  have hx' : u * g * u⁻¹ = g := congrArg Subtype.val hx
  calc g * u = u * g * u⁻¹ * u := by rw [hx']
    _ = u * g := by group

theorem cj_of_mem_centralizer {E : Subgroup S} (hN : E.Normal) (z : S)
    (hz : z ∈ Subgroup.centralizer (E : Set S)) (w : E) : cj hN z w = w := by
  apply Subtype.ext
  have h : z * (w : S) = (w : S) * z := ((Subgroup.mem_centralizer_iff.mp hz) (w : S) w.2).symm
  show z * (w : S) * z⁻¹ = (w : S)
  rw [h, mul_inv_cancel_right]

end Centralizer

section Frame

variable {S : Type} [Group S]

open Classical in
noncomputable def Frame.codeC {E : Subgroup S} (F : Frame E) (s : S) : Bool × Bool × Bool :=
  (decide (cj F.hN s F.b = F.b),
    decide (cj F.hN s F.c = F.b * F.c ∨ cj F.hN s F.c = F.a * (F.b * F.c)),
    decide (cj F.hN s F.c = F.a * F.c ∨ cj F.hN s F.c = F.a * (F.b * F.c)))

theorem Frame.codeC_eq {E : Subgroup S} (F : Frame E) (s t : S)
    (h : F.codeC s = F.codeC t) :
    cj F.hN s F.b = cj F.hN t F.b ∧ cj F.hN s F.c = cj F.hN t F.c := by
  simp only [Frame.codeC, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := decide_eq_decide.mp h1
  have e2 := decide_eq_decide.mp h2
  have e3 := decide_eq_decide.mp h3
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := F.four_ne
  have hb : cj F.hN s F.b = cj F.hN t F.b := by
    rcases F.hblk s with hs | hs <;> rcases F.hblk t with ht | ht
    · rw [hs, ht]
    · exact absurd ((e1.mp hs).symm.trans ht).symm F.ab_ne_b
    · exact absurd ((e1.mpr ht).symm.trans hs).symm F.ab_ne_b
    · rw [hs, ht]
  have hc : cj F.hN s F.c = cj F.hN t F.c := by
    have hsym1 := d1.symm
    have hsym2 := d2.symm
    have hsym3 := d3.symm
    have hsym4 := d4.symm
    have hsym5 := d5.symm
    have hsym6 := d6.symm
    rcases F.c_form s with hs | hs | hs | hs <;> rcases F.c_form t with ht | ht | ht | ht <;>
      rw [hs, ht] at e2 e3 ⊢ <;>
      simp only [d1, d2, d3, d4, d5, d6, hsym1, hsym2, hsym3, hsym4, hsym5, hsym6, true_or,
        or_true, or_false, false_or, iff_self, iff_true, true_iff, false_iff, not_true_eq_false,
        eq_self_iff_true, and_self, and_true, true_and] at e2 e3 <;>
      simp_all
  exact ⟨hb, hc⟩

theorem Frame.codeC_inj_of' {E : Subgroup S} (F : Frame E)
    (r : S ⧸ Subgroup.centralizer (E : Set S) → S)
    (hr : ∀ q, ((r q : S) : S ⧸ Subgroup.centralizer (E : Set S)) = q) :
    Function.Injective (fun q => F.codeC (r q)) := by
  intro q q' h
  have h' : F.codeC (r q) = F.codeC (r q') := h
  obtain ⟨h1, h2⟩ := F.codeC_eq _ _ h'
  have hub : cj F.hN ((r q)⁻¹ * r q') F.b = F.b := by
    rw [cj_mul_apply, ← h1, cj_inv_cancel]
  have huc : cj F.hN ((r q)⁻¹ * r q') F.c = F.c := by
    rw [cj_mul_apply, ← h2, cj_inv_cancel]
  have hu : (r q)⁻¹ * r q' ∈ Subgroup.centralizer (E : Set S) :=
    mem_centralizer_of_cj_fix F.hN _ (fun z => F.cj_fix _ (F.ha _) hub huc z)
  rw [← hr q, ← hr q']
  exact QuotientGroup.eq.mpr hu

theorem Frame.exists_codeC' {E : Subgroup S} (F : Frame E)
    (hcard : Nat.card (S ⧸ Subgroup.centralizer (E : Set S)) = 8)
    (τ : Bool × Bool × Bool) : ∃ s : S, F.codeC s = τ := by
  obtain ⟨r, hr⟩ : ∃ r : S ⧸ Subgroup.centralizer (E : Set S) → S,
      ∀ q, ((r q : S) : S ⧸ Subgroup.centralizer (E : Set S)) = q :=
    ⟨fun q => Function.surjInv
        (QuotientGroup.mk_surjective (s := Subgroup.centralizer (E : Set S))) q,
      fun q => Function.surjInv_eq _ q⟩
  have hinj := F.codeC_inj_of' r hr
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij := (Nat.bijective_iff_injective_and_card (fun q => F.codeC (r q))).mpr
    ⟨hinj, by rw [hcard, h8]⟩
  obtain ⟨q, hq⟩ := hbij.2 τ
  exact ⟨r q, hq⟩

theorem Frame.card_quot_le' {E : Subgroup S} (F : Frame E) :
    Nat.card (S ⧸ Subgroup.centralizer (E : Set S)) ≤ 8 := by
  obtain ⟨r, hr⟩ : ∃ r : S ⧸ Subgroup.centralizer (E : Set S) → S,
      ∀ q, ((r q : S) : S ⧸ Subgroup.centralizer (E : Set S)) = q :=
    ⟨fun q => Function.surjInv
        (QuotientGroup.mk_surjective (s := Subgroup.centralizer (E : Set S))) q,
      fun q => Function.surjInv_eq _ q⟩
  have hinj := F.codeC_inj_of' r hr
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [← h8]
  exact Nat.card_le_card_of_injective _ hinj

theorem Frame.exists_comm_not_mem' {E : Subgroup S} (F : Frame E)
    (hcard : Nat.card (S ⧸ Subgroup.centralizer (E : Set S)) = 8) :
    ∃ s t : S, s * t * s⁻¹ * t⁻¹ ∉ Subgroup.centralizer (E : Set S) := by
  classical
  obtain ⟨s₁, hs₁⟩ := F.exists_codeC' hcard (false, false, false)
  obtain ⟨s₂, hs₂⟩ := F.exists_codeC' hcard (true, true, false)
  refine ⟨s₁, s₂, fun hz => ?_⟩
  have h1 : decide (cj F.hN s₁ F.b = F.b) = false := congrArg Prod.fst hs₁
  have h2 : decide (cj F.hN s₁ F.c = F.b * F.c ∨ cj F.hN s₁ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.1) hs₁
  have h3 : decide (cj F.hN s₁ F.c = F.a * F.c ∨ cj F.hN s₁ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.2) hs₁
  have g1 : cj F.hN s₁ F.b = F.a * F.b := by
    rcases F.hblk s₁ with h | h
    · exact (decide_eq_false_iff_not.mp h1 h).elim
    · exact h
  have g2 := not_or.mp (decide_eq_false_iff_not.mp h2)
  have g3 := not_or.mp (decide_eq_false_iff_not.mp h3)
  have hc1' : cj F.hN s₁ F.c = F.c := by
    rcases F.c_form s₁ with h | h | h | h
    · exact h
    · exact (g3.1 h).elim
    · exact (g2.1 h).elim
    · exact (g2.2 h).elim
  have k2 : decide (cj F.hN s₂ F.c = F.b * F.c ∨ cj F.hN s₂ F.c = F.a * (F.b * F.c)) = true :=
    congrArg (fun p => p.2.1) hs₂
  have k3 : decide (cj F.hN s₂ F.c = F.a * F.c ∨ cj F.hN s₂ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.2) hs₂
  have l3 := not_or.mp (decide_eq_false_iff_not.mp k3)
  have hc2' : cj F.hN s₂ F.c = F.b * F.c := by
    rcases decide_eq_true_iff.mp k2 with h | h
    · exact h
    · exact (l3.2 h).elim
  have L : cj F.hN (s₁ * s₂) F.c = F.a * F.b * F.c := by
    rw [cj_mul_apply, hc2', cj_mul, g1, hc1']
  have R : cj F.hN (s₂ * s₁) F.c = F.b * F.c := by
    rw [cj_mul_apply, hc1', hc2']
  have hzs : s₁ * s₂ = (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * (s₂ * s₁) := by group
  have key : cj F.hN (s₁ * s₂) F.c = cj F.hN (s₂ * s₁) F.c := by
    rw [hzs, cj_mul_apply F.hN (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) (s₂ * s₁) F.c,
      cj_of_mem_centralizer F.hN _ hz]
  rw [L, R] at key
  exact F.ab_ne_b (mul_right_cancel key)

end Frame

theorem index_centralizer_le_eight {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {E : Subgroup S} (hEn : E.Normal) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) :
    (Subgroup.centralizer (E : Set S)).index ≤ 8 := by
  have hAc : ∀ x y : E, x * y = y * x := fun x y => hEa.1.is_comm.comm x y
  have hexp : ∀ x : E, x * x = 1 := fun x => Subtype.ext (by
    show (x : S) * x = 1
    rw [← pow_two]
    exact hEa.2 x x.2)
  obtain ⟨F⟩ := exists_frame hS hEn hAc hexp hE8
  rw [Subgroup.index_eq_card]
  exact F.card_quot_le'

theorem exists_comm_not_mem_centralizer {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {E : Subgroup S} (hEn : E.Normal) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (h8 : (Subgroup.centralizer (E : Set S)).index = 8) :
    ∃ s t : S, s * t * s⁻¹ * t⁻¹ ∉ Subgroup.centralizer (E : Set S) := by
  have hAc : ∀ x y : E, x * y = y * x := fun x y => hEa.1.is_comm.comm x y
  have hexp : ∀ x : E, x * x = 1 := fun x => Subtype.ext (by
    show (x : S) * x = 1
    rw [← pow_two]
    exact hEa.2 x x.2)
  obtain ⟨F⟩ := exists_frame hS hEn hAc hexp hE8
  refine F.exists_comm_not_mem' ?_
  rw [← Subgroup.index_eq_card]
  exact h8

end CFSG.EvenSporadicStandard.Fin76b
