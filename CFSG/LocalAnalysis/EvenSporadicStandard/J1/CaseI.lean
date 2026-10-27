module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Stage
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem class_coset_exists {R : Subgroup G} (hR2 : IsPGroup 2 R) (hSR : S ≤ R)
    (hcard : Nat.card R = 8 * Nat.card S)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Λ)
    (hE : ∀ r ∈ R, ∀ e ∈ H.E, r * e = e * r)
    {y : G} (hyR : y ∈ R) (hy : IsConj H.z y) {l : G} (hl : l ∈ Λ) :
    ∃ r ∈ R, l * y = r * y * r⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({y} : Set G) ⊓ R with hC
  have hy2 : y * y = 1 := H.sq_of_isConj hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact H.z_ne_one (isConj_one_right.1 hy.symm)
  have hCp : IsPGroup 2 C := hR2.to_inf_right
  have hCle : Nat.card C ≤ 16 := (H.star_conj hy hCp inf_le_left).1
  have hyE : y ∉ H.E := fun hyE => h.noconj_E y hyE hy
  have hER : H.E ≤ R := h.E_le.trans (h.le.trans hSR)
  have hDcomm : zpowers y ≤ centralizer (H.E : Set G) :=
    zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he => (hE y hyR e he).symm)
  have hdisj : Disjoint H.E (zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro t htE hty
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hty
    rcases zpow_eq_one_or_self hy2 n with h0 | h1
    · exact h0
    · exact absurd (h1 ▸ htE) hyE
  have hord : orderOf y = 2 := by
    refine orderOf_eq_prime ?_ hy1
    rw [pow_two]; exact hy2
  have hDcard : Nat.card (H.E ⊔ zpowers y : Subgroup G) = 16 := by
    have := Nat.card_congr (mulEquivProdSup hDcomm hdisj).toEquiv
    rw [Nat.card_prod, Nat.card_zpowers, hord, H.card_E] at this
    omega
  have hDC : (H.E ⊔ zpowers y : Subgroup G) ≤ C := by
    refine sup_le (fun e he => ⟨mem_centralizer_singleton_iff.2 (hE y hyR e he).symm, hER he⟩) ?_
    refine zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl, hyR⟩
  have hCge : 16 ≤ Nat.card C := hDcard ▸ Subgroup.card_le_of_le hDC
  have hC16 : Nat.card C = 16 := le_antisymm hCle hCge
  have hRcard : Nat.card R = 16 * Nat.card Λ := by
    have := h.card_S
    omega
  have hcls := card_eq_card_conjClass_mul R y
  rw [hC16, hRcard] at hcls
  set A : Set G := {w | ∃ r ∈ R, w = r * y * r⁻¹} with hA
  set B : Set G := (fun l : G => l * y) '' (Λ : Set G) with hB
  have hAcard : A.ncard = Nat.card Λ := by
    have h1 : Nat.card {x : G // ∃ m ∈ R, x = m * y * m⁻¹} = A.ncard := by
      rw [← Nat.card_coe_set_eq]; rfl
    omega
  have hBcard : B.ncard = Nat.card Λ := by
    rw [hB, Set.ncard_image_of_injective _ (mul_left_injective y)]
    rw [← Nat.card_coe_set_eq]; rfl
  have hAB : A ⊆ B := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r * y * r⁻¹ * y⁻¹, hcomm r hr y hyR, ?_⟩
    group
  have hAeq : A = B := Set.eq_of_subset_of_ncard_le hAB (by omega) (Set.toFinite B)
  have hlB : l * y ∈ B := ⟨l, hl, rfl⟩
  rw [← hAeq] at hlB
  obtain ⟨r, hrR, hr⟩ := hlB
  exact ⟨r, hrR, hr⟩

include h in
theorem class_coset {R : Subgroup G} (hR2 : IsPGroup 2 R) (hSR : S ≤ R)
    (hcard : Nat.card R = 8 * Nat.card S)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Λ)
    (hE : ∀ r ∈ R, ∀ e ∈ H.E, r * e = e * r)
    {y : G} (hyR : y ∈ R) (hy : IsConj H.z y) {l : G} (hl : l ∈ Λ) : IsConj H.z (l * y) := by
  obtain ⟨r, -, hr⟩ := h.class_coset_exists hR2 hSR hcard hcomm hE hyR hy hl
  exact hy.trans (_root_.isConj_iff.2 ⟨r, hr.symm⟩)

include h in
theorem dichotomy {R W : Subgroup G} (hR2 : IsPGroup 2 R) (hSR : S ≤ R)
    (hcard : Nat.card R = 8 * Nat.card S)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Λ)
    (hE : ∀ r ∈ R, ∀ e ∈ H.E, r * e = e * r)
    {σ : G} (hσB : σ ∈ H.B) (hσR : σ ∈ normalizer (R : Set G))
    (hWR : W ≤ R) (hΛW : Λ ≤ W) (hWcard : Nat.card R = 2 * Nat.card W)
    (hWcover : ∀ r ∈ R, r ∈ W ∨ r * H.z ∈ W)
    (hWtrans : ∀ a ∈ W, a ∉ Λ → ∀ b ∈ W, b ∉ Λ →
      ∃ i : ℕ, (σ ^ i * a * (σ ^ i)⁻¹) * b⁻¹ ∈ Λ) :
    (∀ x ∈ R, IsConj H.z x → x ∈ S) ∨ (∀ a ∈ W, IsConj H.z (H.z * a)) := by
  by_cases hall : ∀ x ∈ R, IsConj H.z x → x ∈ S
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨x, hxR, hxc, hxS⟩ := hall
  have hσS : σ ∈ normalizer (S : Set G) := h.B_S hσB
  have hσzi : ∀ i : ℕ, σ ^ i * H.z * (σ ^ i)⁻¹ = H.z := by
    intro i
    have hc : σ ^ i * H.z = H.z * σ ^ i :=
      mem_centralizer_singleton_iff.1 (H.B_le_centralizer (pow_mem hσB i))
    calc σ ^ i * H.z * (σ ^ i)⁻¹ = H.z * σ ^ i * (σ ^ i)⁻¹ := by rw [hc]
      _ = H.z := by group
  have hxi : ∀ i : ℕ, σ ^ i * x * (σ ^ i)⁻¹ ∈ R ∧ IsConj H.z (σ ^ i * x * (σ ^ i)⁻¹) ∧
      σ ^ i * x * (σ ^ i)⁻¹ ∉ S := by
    intro i
    refine ⟨(mem_normalizer_iff.1 (pow_mem hσR i) x).1 hxR,
      hxc.trans (_root_.isConj_iff.2 ⟨σ ^ i, rfl⟩), fun hS => hxS ?_⟩
    have := (mem_normalizer_iff.1 (inv_mem (pow_mem hσS i)) _).1 hS
    simpa [mul_assoc] using this
  have hcl : ∀ i : ℕ, ∀ l ∈ Λ, IsConj H.z (l * (σ ^ i * x * (σ ^ i)⁻¹)) := fun i l hl =>
    h.class_coset hR2 hSR hcard hcomm hE (hxi i).1 (hxi i).2.1 hl
  have hxΛ : x ∉ Λ := fun hxl => h.not_isConj_of_mem hxl hxc
  have hx2 : x * x = 1 := H.sq_of_isConj hxc
  have hΛR : ∀ r ∈ R, ∀ l ∈ Λ, r * l * r⁻¹ ∈ Λ := fun r hr l hl => by
    have h1 := mul_mem (hcomm r hr l (hSR (h.le hl))) hl
    simpa [mul_assoc] using h1
  rcases hWcover x hxR with hxW | hxzW
  · exfalso
    have hWX : ∀ b ∈ W, b ∉ Λ → IsConj H.z b := by
      intro b hb hbΛ
      obtain ⟨i, hi⟩ := hWtrans x hxW hxΛ b hb hbΛ
      have hb' : b = ((σ ^ i * x * (σ ^ i)⁻¹) * b⁻¹)⁻¹ * (σ ^ i * x * (σ ^ i)⁻¹) := by group
      rw [hb']
      exact hcl i _ (inv_mem hi)
    have hx1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hΛcard : 8 ≤ Nat.card Λ := by
      have := Subgroup.card_le_of_le h.E_le
      rw [H.card_E] at this
      exact this
    have hRcard : Nat.card R = 16 * Nat.card Λ := by
      have := h.card_S
      omega
    have hWc : Nat.card W = 8 * Nat.card Λ := by omega
    set Bad : Set G := (Λ : Set G) ∪ (fun l : G => l * x) '' (Λ : Set G) with hBad
    have hBadW : Bad ⊆ (W : Set G) := by
      rintro _ (hl | ⟨l, hl, rfl⟩)
      · exact hΛW hl
      · exact mul_mem (hΛW hl) hxW
    have hΛncard : (Λ : Set G).ncard = Nat.card Λ := by
      rw [← Nat.card_coe_set_eq]; rfl
    have hBadcard : Bad.ncard ≤ 2 * Nat.card Λ := by
      refine (Set.ncard_union_le _ _).trans ?_
      rw [Set.ncard_image_of_injective _ (mul_left_injective x)]
      omega
    have hWncard : (W : Set G).ncard = 8 * Nat.card Λ := by
      rw [← Nat.card_coe_set_eq]; exact hWc
    set T : Set G := (W : Set G) \ Bad with hT
    have hTcard : 6 * Nat.card Λ ≤ T.ncard := by
      rw [hT, Set.ncard_sdiff hBadW]
      omega
    set C : Subgroup G := centralizer ({x} : Set G) ⊓ R with hC
    have hCp : IsPGroup 2 C := hR2.to_inf_right
    have hCle : Nat.card C ≤ 16 := (H.star_conj hxc hCp inf_le_left).1
    have hTC : T ⊆ (C : Set G) := by
      rintro b ⟨hbW, hbBad⟩
      have hbΛ : b ∉ Λ := fun hh => hbBad (Or.inl hh)
      have hb2 := H.sq_of_isConj (hWX b hbW hbΛ)
      have hxbW : x * b ∈ W := mul_mem hxW hbW
      have hxbΛ : x * b ∉ Λ := by
        intro hh
        apply hbBad
        right
        refine ⟨x * (x * b) * x⁻¹, hΛR x hxR _ hh, ?_⟩
        calc x * (x * b) * x⁻¹ * x = x * (x * b) := by group
          _ = b := by rw [← mul_assoc, hx2, one_mul]
      have hxb2 := H.sq_of_isConj (hWX _ hxbW hxbΛ)
      have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      have hcomm' : x * b = b * x := by
        have h3 : x * b = (x * b)⁻¹ := (inv_eq_of_mul_eq_one_right hxb2).symm
        rw [mul_inv_rev, hb1, hx1] at h3
        exact h3
      exact ⟨mem_centralizer_singleton_iff.2 hcomm'.symm, hWR hbW⟩
    have hTle : T.ncard ≤ Nat.card C := by
      refine (Set.ncard_le_ncard hTC (Set.toFinite _)).trans ?_
      rw [← Nat.card_coe_set_eq]
      exact le_rfl
    omega
  · intro a ha
    by_cases haΛ : a ∈ Λ
    · exact h.conj _ (h.z_mul_mem haΛ).1 (h.z_mul_mem haΛ).2
    · have hxzΛ : x * H.z ∉ Λ := fun hh => hxS (by
        have : x = (x * H.z) * H.z⁻¹ := by group
        rw [this]
        exact mul_mem (h.le hh) (inv_mem h.z_mem))
      obtain ⟨i, hi⟩ := hWtrans (x * H.z) hxzW hxzΛ a ha haΛ
      have h1 : σ ^ i * (x * H.z) * (σ ^ i)⁻¹ = (σ ^ i * x * (σ ^ i)⁻¹) * H.z := by
        calc σ ^ i * (x * H.z) * (σ ^ i)⁻¹
            = (σ ^ i * x * (σ ^ i)⁻¹) * (σ ^ i * H.z * (σ ^ i)⁻¹) := by group
          _ = (σ ^ i * x * (σ ^ i)⁻¹) * H.z := by rw [hσzi i]
      rw [h1] at hi
      set xi := σ ^ i * x * (σ ^ i)⁻¹ with hxi_def
      have hyR : H.z * xi * H.z⁻¹ ∈ R :=
        mul_mem (mul_mem (hSR h.z_mem) (hxi i).1) (inv_mem (hSR h.z_mem))
      have hyc : IsConj H.z (H.z * xi * H.z⁻¹) := (hxi i).2.1.trans (_root_.isConj_iff.2 ⟨H.z, rfl⟩)
      have hl0 : H.z * (xi * H.z * a⁻¹)⁻¹ * H.z⁻¹ ∈ Λ := h.z_normalizes (inv_mem hi)
      have := h.class_coset hR2 hSR hcard hcomm hE hyR hyc hl0
      have e : H.z * (xi * H.z * a⁻¹)⁻¹ * H.z⁻¹ * (H.z * xi * H.z⁻¹) = H.z * a := by
        calc H.z * (xi * H.z * a⁻¹)⁻¹ * H.z⁻¹ * (H.z * xi * H.z⁻¹)
            = H.z * a * (H.z * H.z)⁻¹ := by group
          _ = H.z * a := by rw [H.z_mul_self]; simp
      rwa [e] at this

end Stage

end CFSG.EvenSporadicStandard.J1Std
