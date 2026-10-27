module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Seven

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P2b

open Subgroup CFSG.Open

section Offender

variable {G : Type*} [Group G]

theorem elemAb_comm {D : Subgroup G} (hD : IsElemAbelian 2 D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) : a * b = b * a :=
  congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem elemAb_mul_self {D : Subgroup G} (hD : IsElemAbelian 2 D) {a : G} (ha : a ∈ D) :
    a * a = 1 := by
  have := hD.2 a ha
  rwa [pow_two] at this

theorem elemAb_mono {D D' : Subgroup G} (hD : IsElemAbelian 2 D) (h : D' ≤ D) :
    IsElemAbelian 2 D' :=
  ⟨⟨⟨fun a b => Subtype.ext (elemAb_comm hD (h a.2) (h b.2))⟩⟩, fun x hx => hD.2 x (h hx)⟩

theorem elemAb_of {D : Subgroup G} (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (h2 : ∀ a ∈ D, a * a = 1) : IsElemAbelian 2 D :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact h2 x hx⟩

def sqSub (R : Subgroup G) {t : G} (ht : t * t = 1) (hcomm : ∀ r ∈ R, r * t = t * r) :
    Subgroup G where
  carrier := {x | x ∈ R ∨ ∃ r ∈ R, x = t * r}
  mul_mem' := by
    rintro x w (hx | ⟨r, hr, rfl⟩) (hw | ⟨s, hs, rfl⟩)
    · exact Or.inl (mul_mem hx hw)
    · exact Or.inr ⟨x * s, mul_mem hx hs, by rw [← mul_assoc, hcomm x hx, mul_assoc]⟩
    · exact Or.inr ⟨r * w, mul_mem hr hw, by rw [mul_assoc]⟩
    · refine Or.inl ?_
      have e : t * r * (t * s) = r * s :=
        calc t * r * (t * s) = t * (r * t) * s := by group
          _ = t * (t * r) * s := by rw [hcomm r hr]
          _ = (t * t) * r * s := by group
          _ = r * s := by rw [ht, one_mul]
      rw [e]
      exact mul_mem hr hs
  one_mem' := Or.inl (one_mem _)
  inv_mem' := by
    rintro x (hx | ⟨r, hr, rfl⟩)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨r⁻¹, inv_mem hr, ?_⟩
      have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      rw [mul_inv_rev, ht']
      exact hcomm _ (inv_mem hr)

theorem mem_sqSub {R : Subgroup G} {t : G} {ht : t * t = 1} {hcomm : ∀ r ∈ R, r * t = t * r}
    {x : G} : x ∈ sqSub R ht hcomm ↔ x ∈ R ∨ ∃ r ∈ R, x = t * r := Iff.rfl

variable [Finite G]

theorem sqSub_props {R : Subgroup G} {t : G} (ht : t * t = 1) (htR : t ∉ R)
    (hRe : IsElemAbelian 2 R) (hcomm : ∀ r ∈ R, r * t = t * r) :
    sqSub R ht hcomm ≤ centralizer ({t} : Set G) ∧ IsElemAbelian 2 (sqSub R ht hcomm) ∧
      Nat.card (sqSub R ht hcomm) = 2 * Nat.card R := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    rcases mem_sqSub.1 hx with hx | ⟨r, hr, rfl⟩
    · exact hcomm x hx
    · calc t * r * t = t * (r * t) := mul_assoc _ _ _
        _ = t * (t * r) := by rw [hcomm r hr]
  · refine elemAb_of (fun a ha b hb => ?_) (fun a ha => ?_)
    · rcases mem_sqSub.1 ha with ha | ⟨r, hr, rfl⟩ <;> rcases mem_sqSub.1 hb with hb | ⟨s, hs, rfl⟩
      · exact elemAb_comm hRe ha hb
      · calc a * (t * s) = (a * t) * s := by rw [mul_assoc]
          _ = (t * a) * s := by rw [hcomm a ha]
          _ = t * (a * s) := by rw [mul_assoc]
          _ = t * (s * a) := by rw [elemAb_comm hRe ha hs]
          _ = t * s * a := by rw [mul_assoc]
      · calc t * r * b = t * (r * b) := by rw [mul_assoc]
          _ = t * (b * r) := by rw [elemAb_comm hRe hr hb]
          _ = t * b * r := by rw [mul_assoc]
          _ = (b * t) * r := by rw [← hcomm b hb]
          _ = b * (t * r) := by rw [mul_assoc]
      · calc t * r * (t * s) = t * (r * t) * s := by group
          _ = t * (t * r) * s := by rw [hcomm r hr]
          _ = (t * t) * r * s := by group
          _ = r * s := by rw [ht, one_mul]
          _ = s * r := elemAb_comm hRe hr hs
          _ = (t * t) * s * r := by rw [ht, one_mul]
          _ = t * (t * s) * r := by group
          _ = t * (s * t) * r := by rw [← hcomm s hs]
          _ = t * s * (t * r) := by group
    · rcases mem_sqSub.1 ha with ha | ⟨r, hr, rfl⟩
      · exact elemAb_mul_self hRe ha
      · calc t * r * (t * r) = t * (r * t) * r := by group
          _ = t * (t * r) * r := by rw [hcomm r hr]
          _ = (t * t) * (r * r) := by group
          _ = 1 := by rw [ht, elemAb_mul_self hRe hr, one_mul]
  · have hset : ((sqSub R ht hcomm : Subgroup G) : Set G) =
        (R : Set G) ∪ (fun r => t * r) '' (R : Set G) := by
      ext x
      constructor
      · intro hx
        rcases mem_sqSub.1 hx with hx | ⟨r, hr, rfl⟩
        · exact Or.inl hx
        · exact Or.inr ⟨r, hr, rfl⟩
      · rintro (hx | ⟨r, hr, rfl⟩)
        · exact mem_sqSub.2 (Or.inl hx)
        · exact mem_sqSub.2 (Or.inr ⟨r, hr, rfl⟩)
    have hdisj : Disjoint (R : Set G) ((fun r => t * r) '' (R : Set G)) := by
      rw [Set.disjoint_left]
      rintro x hx ⟨r, hr, rfl⟩
      apply htR
      have e : t = (t * r) * r⁻¹ := by group
      rw [e]
      exact mul_mem hx (inv_mem hr)
    calc Nat.card (sqSub R ht hcomm) = ((sqSub R ht hcomm : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ = (R : Set G).ncard + ((fun r => t * r) '' (R : Set G)).ncard := by
          rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      _ = 2 * Nat.card R := by
          rw [Set.ncard_image_of_injective _ (mul_right_injective t), ← Nat.card_coe_set_eq]
          change Nat.card R + Nat.card R = 2 * Nat.card R
          ring

theorem eq_one_of_mem {D : Subgroup G} (hD : IsElemAbelian 2 D) {t e₀ k : G}
    (hte : t * e₀ ∈ D) (hk : k ∈ D) (hkt : k * t * k⁻¹ = t * e₀) : e₀ = 1 := by
  have hc := elemAb_comm hD hk hte
  have h1 : k * (t * e₀) * k⁻¹ = t * e₀ := by rw [hc]; group
  have h2 : k * (t * e₀) * k⁻¹ = (k * t * k⁻¹) * (k * e₀ * k⁻¹) := by group
  rw [h2, hkt] at h1
  have h3 : k * e₀ * k⁻¹ = 1 := mul_left_cancel (a := t * e₀) (by rw [mul_one]; exact h1)
  have h4 := congrArg (fun x => k⁻¹ * x * k) h3
  simpa [mul_assoc] using h4

theorem offender {t : G} (ht : t * t = 1) {X : Set G} (hX : X.ncard = 2 ^ 5)
    (hrank : ∀ K : Subgroup G, K ≤ centralizer ({t} : Set G) → IsElemAbelian 2 K →
      Nat.card K ≤ 2 ^ 6)
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hDX : ∀ d ∈ D, d * t * d⁻¹ ∈ X) :
    Nat.card D ≤ 2 ^ 10 ∧
      (2 ^ 10 ≤ Nat.card D → t ∉ D ∧
        Nat.card (D ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 5 ∧
        {y | ∃ k ∈ D, k * t * k⁻¹ = y} = X ∧
        ∀ r ∈ D, r * t = t * r → ∀ x ∈ X, r * x = x * r) := by
  by_cases htD : t ∈ D
  · have hle : D ≤ centralizer ({t} : Set G) := fun a ha => by
      rw [mem_centralizer_singleton_iff]
      exact elemAb_comm hD ha htD
    have h6 := hrank D hle hD
    refine ⟨h6.trans (by norm_num), fun h => absurd (h.trans h6) (by norm_num)⟩
  · set R : Subgroup G := D ⊓ centralizer ({t} : Set G) with hR
    have hRe : IsElemAbelian 2 R := elemAb_mono hD inf_le_left
    have hRt : ∀ r ∈ R, r * t = t * r := fun r hr =>
      mem_centralizer_singleton_iff.1 (mem_inf.1 hr).2
    have htR : t ∉ R := fun h => htD (mem_inf.1 h).1
    obtain ⟨hS1, hS2, hS3⟩ := sqSub_props ht htR hRe hRt
    have hR32 : Nat.card R ≤ 2 ^ 5 := by
      have h6 := hrank _ hS1 hS2
      rw [hS3] at h6
      norm_num at h6 ⊢
      omega
    set O : Set G := {y | ∃ k ∈ D, k * t * k⁻¹ = y} with hO
    have hOX : O ⊆ X := by
      rintro y ⟨k, hk, rfl⟩
      exact hDX k hk
    have hOcard : O.ncard ≤ 2 ^ 5 := hX ▸ Set.ncard_le_ncard hOX (Set.toFinite X)
    have hcard : Nat.card D = O.ncard * Nat.card R :=
      CFSG.LocalAnalysis.EvenBN.Tits.card_eq_ncard_conj_mul D t
    refine ⟨?_, fun hge => ?_⟩
    · rw [hcard]
      calc O.ncard * Nat.card R ≤ 2 ^ 5 * 2 ^ 5 := Nat.mul_le_mul hOcard hR32
        _ = 2 ^ 10 := by norm_num
    · have h1024 : 1024 ≤ O.ncard * Nat.card R := by
        rw [← hcard]
        norm_num at hge
        exact hge
      have hO32 : O.ncard = 2 ^ 5 := by
        refine Nat.le_antisymm hOcard ?_
        by_contra h
        replace h := lt_of_not_ge h
        have : O.ncard * Nat.card R ≤ 31 * 2 ^ 5 :=
          Nat.mul_le_mul (by omega) hR32
        omega
      have hRcard : Nat.card R = 2 ^ 5 := by
        refine Nat.le_antisymm hR32 ?_
        by_contra h
        replace h := lt_of_not_ge h
        have : O.ncard * Nat.card R ≤ 2 ^ 5 * 31 :=
          Nat.mul_le_mul hOcard (by omega)
        omega
      have hOeq : O = X :=
        Set.eq_of_subset_of_ncard_le hOX (by rw [hX, hO32]) (Set.toFinite X)
      refine ⟨htD, hRcard, hOeq, fun r hr hrt x hx => ?_⟩
      rw [← hOeq] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hrk : r * k = k * r := elemAb_comm hD hr hk
      have hrk' : r * k⁻¹ = k⁻¹ * r := elemAb_comm hD hr (inv_mem hk)
      calc r * (k * t * k⁻¹) = (r * k) * t * k⁻¹ := by group
        _ = (k * r) * t * k⁻¹ := by rw [hrk]
        _ = k * (r * t) * k⁻¹ := by group
        _ = k * (t * r) * k⁻¹ := by rw [hrt]
        _ = k * t * (r * k⁻¹) := by group
        _ = k * t * (k⁻¹ * r) := by rw [hrk']
        _ = k * t * k⁻¹ * r := by group

theorem card_le_two_mul {D D₀ : Subgroup G}
    (h : ∀ a ∈ D, a ∉ D₀ → ∀ b ∈ D, b ∉ D₀ → a * b ∈ D₀) :
    Nat.card D ≤ 2 * Nat.card D₀ := by
  by_cases hle : D ≤ D₀
  · have := Subgroup.card_le_of_le hle
    omega
  · obtain ⟨a, haD, haD₀⟩ := SetLike.not_le_iff_exists.1 hle
    have hsub : (D : Set G) ⊆ (D₀ : Set G) ∪ (fun x => a⁻¹ * x) '' (D₀ : Set G) := by
      intro b hb
      by_cases hbD₀ : b ∈ D₀
      · exact Or.inl hbD₀
      · exact Or.inr ⟨a * b, h a haD haD₀ b hb hbD₀, by group⟩
    calc Nat.card D = (D : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ((D₀ : Set G) ∪ (fun x => a⁻¹ * x) '' (D₀ : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (D₀ : Set G).ncard + ((fun x => a⁻¹ * x) '' (D₀ : Set G)).ncard :=
          Set.ncard_union_le _ _
      _ ≤ (D₀ : Set G).ncard + (D₀ : Set G).ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
      _ = 2 * Nat.card D₀ := by
          rw [← Nat.card_coe_set_eq]
          change Nat.card D₀ + Nat.card D₀ = 2 * Nat.card D₀
          ring

theorem card_le_of_inv {V Q₂ Es D : Subgroup G} {W : Set G} {x : G} (hx : x ∈ W)
    (hWa : ∀ w ∈ W, ∀ v ∈ V, v * w = w * v → v ∈ Es)
    (hWb : ∀ a ∈ W, ∀ b ∈ W, a * b ∈ V ∨ a * b * (a * b) ≠ 1)
    (hWc : ∀ a ∈ Q₂, a ∉ V → a * a = 1 → a ∈ W)
    (hDQ : D ≤ Q₂) (hDx : ∀ a ∈ D, a * x = x * a) (hD : IsElemAbelian 2 D)
    (hEs : Nat.card Es ≤ 32) : Nat.card D ≤ 64 := by
  have h0 : Nat.card (D ⊓ V : Subgroup G) ≤ 32 := by
    refine (Subgroup.card_le_of_le (fun v hv => ?_ : (D ⊓ V : Subgroup G) ≤ Es)).trans hEs
    exact hWa x hx v (mem_inf.1 hv).2 (hDx v (mem_inf.1 hv).1)
  have h2 := card_le_two_mul (D := D) (D₀ := D ⊓ V) (fun a ha haV b hb hbV => by
    have haV' : a ∉ V := fun h => haV (mem_inf.2 ⟨ha, h⟩)
    have hbV' : b ∉ V := fun h => hbV (mem_inf.2 ⟨hb, h⟩)
    have haW := hWc a (hDQ ha) haV' (elemAb_mul_self hD ha)
    have hbW := hWc b (hDQ hb) hbV' (elemAb_mul_self hD hb)
    rcases hWb a haW b hbW with h | h
    · exact mem_inf.2 ⟨mul_mem ha hb, h⟩
    · exact absurd (elemAb_mul_self hD (mul_mem ha hb)) h)
  omega

theorem pRank_eq_of_bounds [Finite G] {K E₀ : Subgroup G} {k₀ : ℕ} (hE₀ : E₀ ≤ K)
    (hE₀a : IsElemAbelian 2 E₀) (hE₀c : Nat.card E₀ = 2 ^ k₀)
    (hbd : ∀ E' : Subgroup G, E' ≤ K → IsElemAbelian 2 E' → Nat.card E' ≤ 2 ^ k₀) :
    CFSG.Open.pRank 2 K = k₀ := by
  have hmem : k₀ ∈ {k | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨E₀, hE₀, hE₀a, hE₀c⟩
  have hbd' : ∀ k ∈ {k | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}, k ≤ k₀ := by
    rintro k ⟨E, hE, hEa, hcard⟩
    have h := hbd E hE hEa
    rw [hcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  unfold CFSG.Open.pRank
  exact le_antisymm (csSup_le ⟨k₀, hmem⟩ hbd') (le_csSup ⟨k₀, hbd'⟩ hmem)

theorem mem_sup_zpowers_cases {H : Subgroup G} {y : G} (hy : y ∈ normalizer (H : Set G))
    (hy2 : y * y ∈ H) {c : G} (hc : c ∈ H ⊔ zpowers y) : c ∈ H ∨ ∃ h ∈ H, c = y * h := by
  have hy' : ∀ h ∈ H, y⁻¹ * h * y ∈ H := fun h hh => ((mem_normalizer_iff''.1 hy) h).1 hh
  let S : Subgroup G :=
    { carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = y * h}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro x w (hx | ⟨h, hh, rfl⟩) (hw | ⟨k, hk, rfl⟩)
        · exact Or.inl (mul_mem hx hw)
        · refine Or.inr ⟨y⁻¹ * x * y * k, mul_mem (hy' x hx) hk, by group⟩
        · exact Or.inr ⟨h * w, mul_mem hh hw, by group⟩
        · refine Or.inl ?_
          have e : y * h * (y * k) = (y * y) * (y⁻¹ * h * y) * k := by group
          rw [e]
          exact mul_mem (mul_mem hy2 (hy' h hh)) hk
      inv_mem' := by
        rintro x (hx | ⟨h, hh, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨y⁻¹ * h⁻¹ * y * (y * y)⁻¹, mul_mem (hy' _ (inv_mem hh)) (inv_mem hy2), ?_⟩
          group }
  have hle : H ⊔ zpowers y ≤ S := by
    apply sup_le
    · intro a ha
      exact Or.inl ha
    · rw [zpowers_le]
      exact Or.inr ⟨1, one_mem _, by simp⟩
  exact hle hc


end Offender

end CFSG.LocalAnalysis.EvenBN.Tits.N.P2b
