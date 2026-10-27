module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

open Subgroup

variable {G : Type*} [Group G]

private theorem zpow_of_mul_self_eq_one {t : G} (ht : t * t = 1) (n : ℤ) :
    (Even n → t ^ n = 1) ∧ (Odd n → t ^ n = t) := by
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  constructor
  · rintro ⟨r, rfl⟩
    rw [← two_mul, zpow_mul, ht2, one_zpow]
  · rintro ⟨r, rfl⟩
    rw [zpow_add_one, zpow_mul, ht2, one_zpow, one_mul]

private theorem mem_zpowers_iff_eq_or_of_sq {t x : G} (ht : t * t = 1) :
    x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl ((zpow_of_mul_self_eq_one ht k).1 hk)
    · exact Or.inr ((zpow_of_mul_self_eq_one ht k).2 hk)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

private theorem commute_zpowers_right {x y z : G} (h : x * y = y * x)
    (hz : z ∈ Subgroup.zpowers y) : x * z = z * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_right (show Commute x y from h) k).eq

private theorem mem_sup_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B h, Set.mem_mul]
  simp only [SetLike.mem_coe]

private theorem le_normalizer_of_comm {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : B ≤ Subgroup.normalizer (A : Set G) :=
  le_trans (fun b hb => (Subgroup.mem_centralizer_iff).2 (fun a ha => h a ha b hb))
    (Subgroup.centralizer_le_normalizer (A : Set G))

private theorem mem_sup_zpowers_of_sq {s t w : G} (hs : s * s = 1) (ht : t * t = 1)
    (hab : s * t = t * s) :
    w ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers t ↔
      w = 1 ∨ w = s ∨ w = t ∨ w = s * t := by
  have hcomm : ∀ y ∈ Subgroup.zpowers s, ∀ z ∈ Subgroup.zpowers t, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((show Commute s t from hab).zpow_zpow i j).eq
  rw [mem_sup_of_le_normalizer (A := Subgroup.zpowers s) (B := Subgroup.zpowers t)
    (le_normalizer_of_comm hcomm)]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases (mem_zpowers_iff_eq_or_of_sq hs).1 hy with rfl | rfl <;>
      rcases (mem_zpowers_iff_eq_or_of_sq ht).1 hz with rfl | rfl <;>
      simp
  · rintro (h | h | h | h)
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [h]; simp⟩
    · exact ⟨s, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, 1, Subgroup.one_mem _,
        by rw [h]; simp⟩
    · exact ⟨1, Subgroup.one_mem _, t, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩,
        by rw [h]; simp⟩
    · exact ⟨s, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, t,
        Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, by rw [h]⟩

private theorem commute_sup_of_comm {A B : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hnorm : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_comm hAB
  intro x hx y hy
  rw [mem_sup_of_le_normalizer hnorm] at hx hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
  have h1 : b₁ * a₂ = a₂ * b₁ := (hAB a₂ ha₂ b₁ hb₁).symm
  have h2 : a₁ * b₂ = b₂ * a₁ := hAB a₁ ha₁ b₂ hb₂
  have h3 : a₁ * a₂ = a₂ * a₁ := hA a₁ ha₁ a₂ ha₂
  have h4 : b₁ * b₂ = b₂ * b₁ := hB b₁ hb₁ b₂ hb₂
  calc (a₁ * b₁) * (a₂ * b₂)
      = a₁ * (b₁ * (a₂ * b₂)) := by group
    _ = a₁ * ((b₁ * a₂) * b₂) := by group
    _ = a₁ * ((a₂ * b₁) * b₂) := by rw [h1]
    _ = a₁ * (a₂ * (b₁ * b₂)) := by group
    _ = a₁ * (a₂ * (b₂ * b₁)) := by rw [h4]
    _ = (a₁ * a₂) * (b₂ * b₁) := by group
    _ = (a₂ * a₁) * (b₂ * b₁) := by rw [h3]
    _ = a₂ * (a₁ * (b₂ * b₁)) := by group
    _ = a₂ * ((a₁ * b₂) * b₁) := by group
    _ = a₂ * ((b₂ * a₁) * b₁) := by rw [h2]
    _ = a₂ * (b₂ * (a₁ * b₁)) := by group
    _ = (a₂ * b₂) * (a₁ * b₁) := by group

private theorem sq_sup_of_sq {A B : Subgroup G}
    (hA : ∀ x ∈ A, x * x = 1) (hB : ∀ x ∈ B, x * x = 1)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, x * x = 1 := by
  have hnorm : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_comm hAB
  intro x hx
  rw [mem_sup_of_le_normalizer hnorm] at hx
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
  have hab : a₁ * b₁ = b₁ * a₁ := hAB a₁ ha₁ b₁ hb₁
  calc (a₁ * b₁) * (a₁ * b₁)
      = a₁ * (b₁ * (a₁ * b₁)) := by group
    _ = a₁ * ((b₁ * a₁) * b₁) := by group
    _ = a₁ * ((a₁ * b₁) * b₁) := by rw [hab]
    _ = a₁ * (a₁ * (b₁ * b₁)) := by group
    _ = (a₁ * a₁) * (b₁ * b₁) := by group
    _ = 1 := by rw [hA a₁ ha₁, hB b₁ hb₁]; group

theorem exists_elemAbelian_eight [Finite G] {a v₁ v₂ : G} (ha : orderOf a = 2)
    (h1 : orderOf v₁ = 2) (h2 : orderOf v₂ = 2) (h12 : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ v₂)
    (ha1 : a * v₁ = v₁ * a) (ha2 : a * v₂ = v₂ * a) (hav₁ : a ≠ v₁) (hav₂ : a ≠ v₂)
    (hav : a ≠ v₁ * v₂) :
    ∃ P : Subgroup G, a ∈ P ∧ v₁ ∈ P ∧ v₂ ∈ P ∧ Nat.card P = 8 ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x * x = 1) ∧
      ∀ H : Subgroup G, a ∈ H → v₁ ∈ H → v₂ ∈ H → P ≤ H := by
  have hv1sq : v₁ * v₁ = 1 := by rw [← pow_two, ← h1]; exact pow_orderOf_eq_one v₁
  have hv2sq : v₂ * v₂ = 1 := by rw [← pow_two, ← h2]; exact pow_orderOf_eq_one v₂
  have hasq : a * a = 1 := by rw [← pow_two, ← ha]; exact pow_orderOf_eq_one a
  let V : Subgroup G := Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂
  let P : Subgroup G := V ⊔ Subgroup.zpowers a
  have hVeq : V = Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ := rfl
  have hPeq : P = V ⊔ Subgroup.zpowers a := rfl
  have hV1comm : ∀ x ∈ Subgroup.zpowers v₁, ∀ y ∈ Subgroup.zpowers v₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl v₁).zpow_zpow i j).eq
  have hV2comm : ∀ x ∈ Subgroup.zpowers v₂, ∀ y ∈ Subgroup.zpowers v₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl v₂).zpow_zpow i j).eq
  have hV12comm : ∀ x ∈ Subgroup.zpowers v₁, ∀ y ∈ Subgroup.zpowers v₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute v₁ v₂ from h12).zpow_zpow i j).eq
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    exact commute_sup_of_comm hV1comm hV2comm hV12comm x hx y hy
  have hV1sq : ∀ x ∈ Subgroup.zpowers v₁, x * x = 1 := by
    intro x hx
    rcases (mem_zpowers_iff_eq_or_of_sq hv1sq).1 hx with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hv1sq]
  have hV2sq : ∀ x ∈ Subgroup.zpowers v₂, x * x = 1 := by
    intro x hx
    rcases (mem_zpowers_iff_eq_or_of_sq hv2sq).1 hx with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hv2sq]
  have hVsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    exact sq_sup_of_sq hV1sq hV2sq hV12comm x hx
  have hVa : ∀ v ∈ V, a * v = v * a := by
    intro v hv
    rw [hVeq, mem_sup_of_le_normalizer (le_normalizer_of_comm hV12comm)] at hv
    obtain ⟨u, hu, w, hw, rfl⟩ := hv
    calc a * (u * w) = (a * u) * w := by rw [mul_assoc]
      _ = (u * a) * w := by rw [commute_zpowers_right ha1 hu]
      _ = u * (a * w) := by rw [mul_assoc]
      _ = u * (w * a) := by rw [commute_zpowers_right ha2 hw]
      _ = (u * w) * a := by rw [mul_assoc]
  have hVzpcomm : ∀ x ∈ V, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (show Commute x a from (hVa x hx).symm) k).eq
  have hzpAcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl a).zpow_zpow i j).eq
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    exact commute_sup_of_comm hVcomm hzpAcomm hVzpcomm x hx y hy
  have hzpAsq : ∀ x ∈ Subgroup.zpowers a, x * x = 1 := by
    intro x hx
    rcases (mem_zpowers_iff_eq_or_of_sq hasq).1 hx with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hasq]
  have hPsq : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    exact sq_sup_of_sq hVsq hzpAsq hVzpcomm x hx
  have ha_ne : a ≠ 1 := by
    intro h
    have := ha
    rw [h, orderOf_one] at this
    exact (by norm_num : (1 : ℕ) ≠ 2) this
  have h1_ne : v₁ ≠ 1 := by
    intro h
    have := h1
    rw [h, orderOf_one] at this
    exact (by norm_num : (1 : ℕ) ≠ 2) this
  have h2_ne : v₂ ≠ 1 := by
    intro h
    have := h2
    rw [h, orderOf_one] at this
    exact (by norm_num : (1 : ℕ) ≠ 2) this
  have h12_ne : v₁ * v₂ ≠ 1 := by
    intro h
    apply hne
    calc v₁ = v₁ * (v₂ * v₂) := by rw [hv2sq, mul_one]
      _ = (v₁ * v₂) * v₂ := by group
      _ = v₂ := by rw [h, one_mul]
  have hv₂V₁ : v₂ ∉ Subgroup.zpowers v₁ := by
    rw [mem_zpowers_iff_eq_or_of_sq hv1sq]
    push Not
    exact ⟨h2_ne, fun h => hne h.symm⟩
  have hVrel₁ : (Subgroup.zpowers v₁).relIndex V = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨v₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩), hv₂V₁, ?_⟩
    intro b hb
    rw [hVeq, mem_sup_of_le_normalizer (le_normalizer_of_comm hV12comm)] at hb
    obtain ⟨u, hu, w, hw, rfl⟩ := hb
    rcases (mem_zpowers_iff_eq_or_of_sq hv2sq).1 hw with hw1 | hw2
    · right
      rw [hw1]
      simpa using hu
    · left
      rw [hw2]
      have hcalc : v₂ * (u * v₂) = u := by
        rw [← mul_assoc, commute_zpowers_right h12.symm hu, mul_assoc, hv2sq, mul_one]
      simpa [hcalc] using hu
  have hVcard : Nat.card V = 4 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers v₁) (K := V)
    have hinf : Subgroup.zpowers v₁ ⊓ V = Subgroup.zpowers v₁ :=
      inf_eq_left.mpr (show Subgroup.zpowers v₁ ≤ V from le_sup_left)
    have hz : Nat.card (Subgroup.zpowers v₁) = 2 := by rw [Nat.card_zpowers, h1]
    rw [hinf, hVrel₁, hz] at h
    omega
  have haV : a ∉ V := by
    rw [hVeq, mem_sup_zpowers_of_sq hv1sq hv2sq h12]
    push Not
    exact ⟨ha_ne, hav₁, hav₂, hav⟩
  have hVrel : V.relIndex P = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩), haV, ?_⟩
    intro b hb
    by_cases hbV : b ∈ V
    · exact Or.inr hbV
    · left
      rw [hPeq, mem_sup_of_le_normalizer (le_normalizer_of_comm hVzpcomm)] at hb
      obtain ⟨v, hv, w, hw, rfl⟩ := hb
      rcases (mem_zpowers_iff_eq_or_of_sq hasq).1 hw with hw1 | hw2
      · simp only [hw1, mul_one] at hbV
        exact absurd hv hbV
      · rw [hw2]
        have hcalc : a * (v * a) = v := by
          rw [← mul_assoc, hVa v hv, mul_assoc, hasq, mul_one]
        simpa [hcalc] using hv
  have hPcard : Nat.card P = 8 := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := P)
    have hinf : V ⊓ P = V := inf_eq_left.mpr (show V ≤ P from le_sup_left)
    rw [hinf, hVrel, hVcard] at h
    omega
  refine ⟨P, ?_, ?_, ?_, hPcard, hPcomm, hPsq, ?_⟩
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  · exact Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
  · exact Subgroup.mem_sup_left
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
  · intro H haH h1H h2H
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr h1H) (Subgroup.zpowers_le.mpr h2H))
      (Subgroup.zpowers_le.mpr haH)

theorem three_le_pRank_of_involutions [Finite G] {H : Subgroup G} {a v₁ v₂ : G}
    (ha : orderOf a = 2) (h1 : orderOf v₁ = 2) (h2 : orderOf v₂ = 2)
    (h12 : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ v₂) (ha1 : a * v₁ = v₁ * a) (ha2 : a * v₂ = v₂ * a)
    (hav₁ : a ≠ v₁) (hav₂ : a ≠ v₂) (hav : a ≠ v₁ * v₂) (haH : a ∈ H) (h1H : v₁ ∈ H)
    (h2H : v₂ ∈ H) : 3 ≤ CFSG.Open.pRank 2 H := by
  obtain ⟨P, -, -, -, hPcard, hPcomm, hPsq, hPle⟩ :=
    exists_elemAbelian_eight ha h1 h2 h12 hne ha1 ha2 hav₁ hav₂ hav
  have hE : CFSG.Open.IsElemAbelian 2 P :=
    ⟨IsMulCommutative.of_comm (fun x y => Subtype.ext (hPcomm x x.2 y y.2)),
      fun x hx => by simpa [pow_two] using hPsq x hx⟩
  have hk : Nat.card P = 2 ^ 3 := by rw [hPcard]; norm_num
  exact CFSG.SectionRank.le_pRank one_lt_two (hPle H haH h1H h2H) hE hk

end CFSG.SectionRank
