module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem exists_mul_zpow_of_mem_sup {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) {v : G} (hv : v ∈ H ⊔ Subgroup.zpowers y) :
    ∃ h ∈ H, ∃ j : ℤ, v = h * y ^ j := by
  have hynorm : ∀ n : ℤ, ∀ h ∈ H, y ^ n * h * (y ^ n)⁻¹ ∈ H := by
    intro n h hh
    have hy' : y⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hy
    have key : ∀ n : ℕ, ∀ h ∈ H, y ^ n * h * (y ^ n)⁻¹ ∈ H ∧ y⁻¹ ^ n * h * (y⁻¹ ^ n)⁻¹ ∈ H := by
      intro n
      induction n with
      | zero => intro h hh; simpa using And.intro hh hh
      | succ n ih =>
        intro h hh
        obtain ⟨ih1, ih2⟩ := ih h hh
        constructor
        · have e : y ^ (n + 1) * h * (y ^ (n + 1))⁻¹ = y * (y ^ n * h * (y ^ n)⁻¹) * y⁻¹ := by
            group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp hy _).mp ih1
        · have e : y⁻¹ ^ (n + 1) * h * (y⁻¹ ^ (n + 1))⁻¹ =
              y⁻¹ * (y⁻¹ ^ n * h * (y⁻¹ ^ n)⁻¹) * y⁻¹⁻¹ := by
            group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp hy' _).mp ih2
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · simpa using (key m h hh).1
    · have := (key m h hh).2
      simpa [zpow_neg, inv_pow] using this
  let P : Subgroup G :=
    { carrier := {v | ∃ h ∈ H, ∃ j : ℤ, v = h * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, j₁, rfl⟩ ⟨h₂, hh₂, j₂, rfl⟩
        refine ⟨h₁ * (y ^ j₁ * h₂ * (y ^ j₁)⁻¹), H.mul_mem hh₁ (hynorm j₁ h₂ hh₂), j₁ + j₂, ?_⟩
        rw [zpow_add]
        group
      one_mem' := ⟨1, H.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, j, rfl⟩
        refine ⟨(y ^ (-j) * h⁻¹ * (y ^ (-j))⁻¹), ?_, -j, ?_⟩
        · exact hynorm (-j) h⁻¹ (H.inv_mem hh)
        · simp only [mul_inv_rev, zpow_neg]
          group }
  have hle : H ⊔ Subgroup.zpowers y ≤ P := by
    refine sup_le (fun h hh => ⟨h, hh, 0, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, H.one_mem, 1, by simp⟩
  exact hle hv

theorem mem_normalizer_of_forall [Finite G] {H : Subgroup G} {y : G}
    (h : ∀ r ∈ H, y * r * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_fintype h

theorem exists_conj_mem_mul_of_centralizes [Finite G] {K₁ : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K₁ : Set G)) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    {R₁ R₂ : Subgroup G} (h₁ : IsSylow2In R₁ K₁) (h₂ : IsSylow2In R₂ K₁)
    (hc : ∀ r ∈ R₁, y * r = r * y) (hn : ∀ r ∈ R₂, y * r * y⁻¹ ∈ R₂) :
    ∃ k ∈ K₁, ∃ κ ∈ R₂, k * y * k⁻¹ = κ * y ∧
      ∀ r ∈ R₂, (k * y * k⁻¹) * r = r * (k * y * k⁻¹) := by
  have hyN₁ : y ∈ Subgroup.normalizer (R₁ : Set G) :=
    mem_normalizer_of_forall fun r hr => by
      have : y * r * y⁻¹ = r := by rw [hc r hr]; group
      rw [this]; exact hr
  have hyN₂ : y ∈ Subgroup.normalizer (R₂ : Set G) := mem_normalizer_of_forall hn
  have hyX : y ∈ K₁ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  set X : Subgroup G := K₁ ⊔ Subgroup.zpowers y with hX
  have hT : ∀ R : Subgroup G, IsSylow2In R K₁ → y ∈ Subgroup.normalizer (R : Set G) →
      IsSylow2In (R ⊔ Subgroup.zpowers y) X := by
    intro R hR hyR
    refine ⟨sup_le_sup_right hR.1 _, ?_, ?_⟩
    · exact IsPGroup.to_sup_of_normal_left' hR.2.1 hy2 (Subgroup.zpowers_le.mpr hyR)
    · intro V' hV'X hV'2 hle
      apply le_antisymm _ hle
      intro v hv
      obtain ⟨k', hk', j, rfl⟩ := exists_mul_zpow_of_mem_sup hy (hV'X hv)
      have hyV' : y ∈ V' := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
      have hk'V' : k' ∈ V' := by
        have := V'.mul_mem hv (V'.inv_mem (V'.zpow_mem hyV' j))
        simpa using this
      have hW : V' ⊓ K₁ ≤ R := by
        have h2 : IsPGroup 2 (V' ⊓ K₁ : Subgroup G) := hV'2.to_le inf_le_left
        have h3 : R ≤ V' ⊓ K₁ := le_inf (le_sup_left.trans hle) hR.1
        exact (hR.2.2 _ inf_le_right h2 h3).le
      have hk'R : k' ∈ R := hW ⟨hk'V', hk'⟩
      exact Subgroup.mul_mem_sup hk'R (Subgroup.zpow_mem_zpowers y j)
  have hT₁ := hT R₁ h₁ hyN₁
  have hT₂ := hT R₂ h₂ hyN₂
  obtain ⟨g, hgX, hg⟩ := exists_conjSub_eq_of_isSylow2In hT₁ hT₂
  obtain ⟨k, hk, j, rfl⟩ := exists_mul_zpow_of_mem_sup hy hgX
  have hyT₁ : y ^ j ∈ R₁ ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers y j)
  have hkT : conjSub k (R₁ ⊔ Subgroup.zpowers y) = R₂ ⊔ Subgroup.zpowers y := by
    rw [← hg, conjSub_mul, conjSub_eq_self_of_mem hyT₁]
  have hconjK : conjSub k K₁ = K₁ := conjSub_eq_self_of_mem hk
  have hR₁k : IsSylow2In (conjSub k R₁) K₁ := hconjK ▸ h₁.conj k
  have hR₁kT : conjSub k R₁ ≤ R₂ := by
    intro x hx
    have hxT : x ∈ R₂ ⊔ Subgroup.zpowers y :=
      hkT ▸ conjSub_mono (le_sup_left : R₁ ≤ R₁ ⊔ Subgroup.zpowers y) hx
    have hxK : x ∈ K₁ := hR₁k.1 hx
    have hW : (R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ ≤ R₂ := by
      have h2 : IsPGroup 2 ((R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ : Subgroup G) :=
        hT₂.2.1.to_le inf_le_left
      have h3 : R₂ ≤ (R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ := le_inf le_sup_left h₂.1
      exact (h₂.2.2 _ inf_le_right h2 h3).le
    exact hW ⟨hxT, hxK⟩
  have hR₂eq : conjSub k R₁ = R₂ := (hR₁k.2.2 R₂ h₂.1 h₂.2.1 hR₁kT).symm
  have hykT : k * y * k⁻¹ ∈ R₂ ⊔ Subgroup.zpowers y := by
    rw [← hkT]
    exact conj_mem_conjSub (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  obtain ⟨ρ, hρ, i, hi⟩ := exists_mul_zpow_of_mem_sup hyN₂ hykT
  have hyK : k * y * k⁻¹ * y⁻¹ ∈ K₁ := by
    have h1 : y * k⁻¹ * y⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp hy _).mp (K₁.inv_mem hk)
    have := K₁.mul_mem hk h1
    simpa [mul_assoc] using this
  have hyi : y ^ (i - 1) ∈ K₁ := by
    have e : y ^ (i - 1) = ρ⁻¹ * (k * y * k⁻¹ * y⁻¹) := by
      rw [hi]
      group
    rw [e]
    exact K₁.mul_mem (K₁.inv_mem (h₂.1 hρ)) hyK
  have hyiR : y ^ (i - 1) ∈ R₂ := by
    have hW : (R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ ≤ R₂ := by
      have h2 : IsPGroup 2 ((R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ : Subgroup G) :=
        hT₂.2.1.to_le inf_le_left
      have h3 : R₂ ≤ (R₂ ⊔ Subgroup.zpowers y) ⊓ K₁ := le_inf le_sup_left h₂.1
      exact (h₂.2.2 _ inf_le_right h2 h3).le
    exact hW ⟨Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers y _), hyi⟩
  refine ⟨k, hk, ρ * y ^ (i - 1), R₂.mul_mem hρ hyiR, ?_, ?_⟩
  · rw [hi]
    group
  · intro r hr
    rw [← hR₂eq] at hr
    obtain ⟨r₁, hr₁, rfl⟩ : ∃ r₁ ∈ R₁, k * r₁ * k⁻¹ = r := by
      refine ⟨k⁻¹ * r * k, ?_, by group⟩
      simpa [mem_conjSub_iff] using hr
    have := hc r₁ hr₁
    calc k * y * k⁻¹ * (k * r₁ * k⁻¹) = k * (y * r₁) * k⁻¹ := by group
      _ = k * (r₁ * y) * k⁻¹ := by rw [this]
      _ = k * r₁ * k⁻¹ * (k * y * k⁻¹) := by group

end CFSG.ClassicalInvolution.Asc77.T7F2
