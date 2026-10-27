module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.AltStdSec

@[expose] noncomputable def prodCnt {H : Type*} [Group H] (Ω : Set H) (g : H) : ℕ :=
  Nat.card {t : H × H × H // t.1 ∈ Ω ∧ t.2.1 ∈ Ω ∧ t.2.2 ∈ Ω ∧ t.1 * t.2.1 * t.2.2 = g}

@[expose] noncomputable def tripleCnt {R : Type*} [Group R] (T : Set R) (p : R) : ℕ :=
  Nat.card {qs : R × R // qs.1 ∈ T ∧ qs.2 ∈ T ∧ qs.1 * qs.2 * p ∈ T}

theorem tripleCnt_map {R : Type*} [Group R] (φ : R ≃* R) {T : Set R}
    (hT : ∀ r, φ r ∈ T ↔ r ∈ T) (p : R) : tripleCnt T (φ p) = tripleCnt T p := by
  unfold tripleCnt
  symm
  refine Nat.card_congr ((Equiv.prodCongr φ.toEquiv φ.toEquiv).subtypeEquiv (fun qs => ?_))
  simp only [Equiv.prodCongr_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Prod.map_fst,
    Prod.map_snd, hT]
  rw [← map_mul, ← map_mul, hT]

theorem prodCnt_inj {H H' : Type*} [Group H] [Group H'] (ψ : H →* H')
    (hψ : Function.Injective ψ) {Ω : Set H} {Ω' : Set H'} (hΩ : ∀ h, ψ h ∈ Ω' ↔ h ∈ Ω)
    (hΩ' : ∀ x ∈ Ω', ∃ h, ψ h = x) (g : H) : prodCnt Ω' (ψ g) = prodCnt Ω g := by
  unfold prodCnt
  symm
  refine Nat.card_eq_of_bijective
    (fun t => ⟨(ψ t.1.1, ψ t.1.2.1, ψ t.1.2.2), (hΩ _).2 t.2.1, (hΩ _).2 t.2.2.1,
      (hΩ _).2 t.2.2.2.1, by simp only [← map_mul, t.2.2.2.2]⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a, b, c⟩, ha⟩ ⟨⟨a', b', c'⟩, ha'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact Subtype.ext (by simp only [hψ h1, hψ h2, hψ h3])
  · rintro ⟨⟨x, y, z⟩, hx, hy, hz, hxyz⟩
    obtain ⟨a, rfl⟩ := hΩ' x hx
    obtain ⟨b, rfl⟩ := hΩ' y hy
    obtain ⟨c, rfl⟩ := hΩ' z hz
    have habc : a * b * c = g := hψ (by simpa only [map_mul] using hxyz)
    exact ⟨⟨(a, b, c), (hΩ a).1 hx, (hΩ b).1 hy, (hΩ c).1 hz, habc⟩, rfl⟩

theorem tripleCnt_eq_prodCnt {R : Type*} [Group R] {z : R} (hz2 : z * z = 1)
    (hzc : ∀ r : R, r * z = z * r) {Ω : Set R} (hΩ2 : ∀ w ∈ Ω, w * w = 1) (p₀ : R) :
    tripleCnt {t | ∃ w ∈ Ω, t = z * w} (z * p₀) = prodCnt Ω p₀ := by
  have hcomm : ∀ x y : R, x * (z * y) = z * (x * y) := by
    intro x y
    rw [← mul_assoc, hzc x, mul_assoc]
  have hzz : ∀ x y : R, z * x * (z * y) = x * y := by
    intro x y
    rw [mul_assoc, hcomm x y, ← mul_assoc, hz2, one_mul]
  have hsq : ∀ a b c : R, a * a = 1 → b * b = 1 → a * b * c = p₀ → c = b * a * p₀ := by
    intro a b c ha hb h
    rw [← h]
    symm
    calc b * a * (a * b * c) = b * (a * a) * (b * c) := by simp only [mul_assoc]
      _ = c := by rw [ha, mul_one, ← mul_assoc, hb, one_mul]
  have hprod : ∀ a b c : R, c = b * a * p₀ → z * b * (z * a) * (z * p₀) = z * c := by
    intro a b c h
    rw [hzz, hcomm, h]
  unfold tripleCnt prodCnt
  symm
  refine Nat.card_eq_of_bijective
    (fun t => ⟨(z * t.1.2.1, z * t.1.1), ⟨_, t.2.2.1, rfl⟩, ⟨_, t.2.1, rfl⟩,
      ⟨t.1.2.2, t.2.2.2.1, hprod t.1.1 t.1.2.1 t.1.2.2
        (hsq _ _ _ (hΩ2 _ t.2.1) (hΩ2 _ t.2.2.1) t.2.2.2.2)⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a, b, c⟩, ha, hb, hc, habc⟩ ⟨⟨a', b', c'⟩, ha', hb', hc', habc'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : b = b' := mul_left_cancel h1
    have e2 : a = a' := mul_left_cancel h2
    subst e1 e2
    have e3 : c = c' := (hsq _ _ _ (hΩ2 _ ha) (hΩ2 _ hb) habc).trans
      (hsq _ _ _ (hΩ2 _ ha) (hΩ2 _ hb) habc').symm
    subst e3
    rfl
  · rintro ⟨⟨q, s⟩, ⟨w₁, hw₁, h1⟩, ⟨w₂, hw₂, h2⟩, ⟨w', hw', hqs⟩⟩
    change q = z * w₁ at h1
    change s = z * w₂ at h2
    change q * s * (z * p₀) = z * w' at hqs
    subst h1 h2
    have hw : w' = w₁ * w₂ * p₀ := by
      rw [hzz, hcomm] at hqs
      exact (mul_left_cancel hqs).symm
    refine ⟨⟨(w₂, w₁, w'), hw₂, hw₁, hw', ?_⟩, rfl⟩
    rw [hw]
    calc w₂ * w₁ * (w₁ * w₂ * p₀) = w₂ * (w₁ * w₁) * w₂ * p₀ := by simp only [mul_assoc]
      _ = p₀ := by rw [hΩ2 _ hw₁, mul_one, hΩ2 _ hw₂, one_mul]

theorem prodCnt_eq_ncard {H : Type*} [Group H] (Ω : Set H) (g : H) :
    prodCnt Ω g =
      {t : H × H × H | t.1 ∈ Ω ∧ t.2.1 ∈ Ω ∧ t.2.2 ∈ Ω ∧ t.1 * t.2.1 * t.2.2 = g}.ncard :=
  rfl

theorem prodCnt_one_le {H : Type*} [Group H] [Finite H] {F : Set H} (hF2 : ∀ w ∈ F, w * w = 1)
    (hF1 : (1 : H) ∉ F) :
    prodCnt (insert (1 : H) F) 1 ≤ 1 + 3 * Nat.card F + prodCnt F 1 := by
  rw [prodCnt_eq_ncard, prodCnt_eq_ncard]
  set B : Set (H × H × H) :=
    {t | t.1 ∈ F ∧ t.2.1 ∈ F ∧ t.2.2 ∈ F ∧ t.1 * t.2.1 * t.2.2 = 1} with hB
  set S0 : Set (H × H × H) := {(1, 1, 1)} with hS0
  set I0 : Set (H × H × H) := (fun w : H => ((1 : H), w, w)) '' F with hI0
  set I1 : Set (H × H × H) := (fun w : H => (w, (1 : H), w)) '' F with hI1
  set I2 : Set (H × H × H) := (fun w : H => (w, w, (1 : H))) '' F with hI2
  have hinv : ∀ x y : H, x ∈ F → x * y = 1 → y = x := fun x y hx h =>
    mul_left_cancel (h.trans (hF2 x hx).symm)
  have hcover : {t : H × H × H | t.1 ∈ insert (1 : H) F ∧ t.2.1 ∈ insert (1 : H) F ∧
      t.2.2 ∈ insert (1 : H) F ∧ t.1 * t.2.1 * t.2.2 = 1} ⊆ S0 ∪ I0 ∪ I1 ∪ I2 ∪ B := by
    rintro ⟨a, b, c⟩ ⟨ha, hb, hc, habc⟩
    simp only [Set.mem_insert_iff] at ha hb hc
    simp only [Set.mem_union, hS0, hI0, hI1, hI2, hB, Set.mem_singleton_iff, Set.mem_image,
      Prod.mk.injEq]
    rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)))
    · have h : c = 1 := by simpa using habc
      exact absurd (h ▸ hc) hF1
    · have h : b = 1 := by simpa using habc
      exact absurd (h ▸ hb) hF1
    · have hbc : b * c = 1 := by simpa using habc
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨b, hb, rfl, rfl, (hinv b c hb hbc).symm⟩)))
    · have h : a = 1 := by simpa using habc
      exact absurd (h ▸ ha) hF1
    · have hac : a * c = 1 := by simpa using habc
      exact Or.inl (Or.inl (Or.inr ⟨a, ha, rfl, rfl, (hinv a c ha hac).symm⟩))
    · have hab : a * b = 1 := by simpa using habc
      exact Or.inl (Or.inr ⟨a, ha, rfl, (hinv a b ha hab).symm, rfl⟩)
    · exact Or.inr ⟨ha, hb, hc, habc⟩
  have e0 : S0.ncard = 1 := Set.ncard_singleton _
  have e1 : I0.ncard ≤ F.ncard := Set.ncard_image_le
  have e2 : I1.ncard ≤ F.ncard := Set.ncard_image_le
  have e3 : I2.ncard ≤ F.ncard := Set.ncard_image_le
  have h0 := Set.ncard_le_ncard hcover
  have h1 := Set.ncard_union_le (S0 ∪ I0 ∪ I1 ∪ I2) B
  have h2 := Set.ncard_union_le (S0 ∪ I0 ∪ I1) I2
  have h3 := Set.ncard_union_le (S0 ∪ I0) I1
  have h4 := Set.ncard_union_le S0 I0
  have hF : Nat.card F = F.ncard := rfl
  omega

theorem prodCnt_ge {H : Type*} [Group H] [Finite H] {F : Set H} (hF1 : (1 : H) ∉ F) {c : H}
    (hc : c ∈ F) : 3 + prodCnt F c ≤ prodCnt (insert (1 : H) F) c := by
  rw [prodCnt_eq_ncard, prodCnt_eq_ncard]
  set B : Set (H × H × H) :=
    {t | t.1 ∈ F ∧ t.2.1 ∈ F ∧ t.2.2 ∈ F ∧ t.1 * t.2.1 * t.2.2 = c} with hB
  set T3 : Set (H × H × H) := {(1, 1, c), (1, c, 1), (c, 1, 1)} with hT3
  have hc1 : c ≠ 1 := fun h => hF1 (h ▸ hc)
  have d12 : ((1 : H), (1 : H), c) ≠ (1, c, 1) := fun h => hc1 (congrArg (fun t => t.2.1) h).symm
  have d13 : ((1 : H), (1 : H), c) ≠ (c, 1, 1) := fun h => hc1 (congrArg (fun t => t.1) h).symm
  have d23 : ((1 : H), c, (1 : H)) ≠ (c, 1, 1) := fun h => hc1 (congrArg (fun t => t.1) h).symm
  have hT3card : T3.ncard = 3 :=
    Set.ncard_eq_three.2 ⟨(1, 1, c), (1, c, 1), (c, 1, 1), d12, d13, d23, rfl⟩
  have hdisj : Disjoint T3 B := by
    rw [Set.disjoint_left]
    rintro t (rfl | rfl | rfl) ⟨hFa, hFb, hFd, -⟩
    · exact hF1 hFa
    · exact hF1 hFa
    · exact hF1 hFb
  have hsub : T3 ∪ B ⊆ {t : H × H × H | t.1 ∈ insert (1 : H) F ∧ t.2.1 ∈ insert (1 : H) F ∧
      t.2.2 ∈ insert (1 : H) F ∧ t.1 * t.2.1 * t.2.2 = c} := by
    rintro t (ht | ht)
    · rcases ht with rfl | rfl | rfl
      · exact ⟨Set.mem_insert _ _, Set.mem_insert _ _, Set.mem_insert_of_mem _ hc, by simp⟩
      · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ hc, Set.mem_insert _ _, by simp⟩
      · exact ⟨Set.mem_insert_of_mem _ hc, Set.mem_insert _ _, Set.mem_insert _ _, by simp⟩
    · exact ⟨Set.mem_insert_of_mem _ ht.1, Set.mem_insert_of_mem _ ht.2.1,
        Set.mem_insert_of_mem _ ht.2.2.1, ht.2.2.2⟩
  calc 3 + B.ncard = T3.ncard + B.ncard := by rw [hT3card]
    _ = (T3 ∪ B).ncard := (Set.ncard_union_eq hdisj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

theorem prodCnt_prod {D E : Type*} [Group D] [Group E] (X : Set D) (X' : Set E) (g : D) (g' : E) :
    prodCnt (X ×ˢ X') (g, g') = prodCnt X g * prodCnt X' g' := by
  unfold prodCnt
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun t => (⟨(t.1.1.1, t.1.2.1.1, t.1.2.2.1), t.2.1.1, t.2.2.1.1, t.2.2.2.1.1,
          congrArg Prod.fst t.2.2.2.2⟩,
        ⟨(t.1.1.2, t.1.2.1.2, t.1.2.2.2), t.2.1.2, t.2.2.1.2, t.2.2.2.1.2,
          congrArg Prod.snd t.2.2.2.2⟩)
      invFun := fun p => ⟨((p.1.1.1, p.2.1.1), (p.1.1.2.1, p.2.1.2.1), (p.1.1.2.2, p.2.1.2.2)),
          ⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2.1, p.2.2.2.1⟩, ⟨p.1.2.2.2.1, p.2.2.2.2.1⟩,
          Prod.ext p.1.2.2.2.2 p.2.2.2.2.2⟩
      left_inv := fun t => rfl
      right_inv := fun p => rfl }

end CFSG.OddStandard.AltStdSec
