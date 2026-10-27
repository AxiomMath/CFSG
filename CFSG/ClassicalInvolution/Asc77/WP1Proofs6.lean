module

public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_commutes {A B : Subgroup G} (h : Commutes A B) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have hc : b * a' = a' * b := (h a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hc]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := (h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm
        rw [mul_inv_rev, hc] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem iSup_mem_eq_sup_iSup_ne {ι : Type*} (Δ : Set ι) (g : ι → Subgroup G) {i : ι}
    (hi : i ∈ Δ) :
    (⨆ j ∈ Δ, g j) = g i ⊔ ⨆ j ∈ Δ, ⨆ (_ : j ≠ i), g j := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le i hi le_rfl)
    (iSup₂_le fun j hj => iSup_le fun hne => le_iSup₂_of_le j hj le_rfl))
  by_cases hji : j = i
  · subst hji
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le j hj (le_iSup_of_le hji le_rfl))

theorem inf_sup_centers_eq {Δ : Set (Subgroup G)}
    (hcomm : ∀ R ∈ Δ, ∀ R' ∈ Δ, R ≠ R' → Commutes R R') {R : Subgroup G} (hR : R ∈ Δ) :
    (R ⊔ ⨆ R' ∈ Δ, centerIn R') ⊓
      ((⨆ R' ∈ Δ, centerIn R') ⊔ ⨆ R' ∈ Δ, ⨆ (_ : R' ≠ R), R') = ⨆ R' ∈ Δ, centerIn R' := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup G, Z = ⨆ R' ∈ Δ, centerIn R' := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = ⨆ R' ∈ Δ, ⨆ (_ : R' ≠ R), R' := ⟨_, rfl⟩
  obtain ⟨Z', hZ'⟩ : ∃ Z' : Subgroup G, Z' = ⨆ R' ∈ Δ, ⨆ (_ : R' ≠ R), centerIn R' := ⟨_, rfl⟩
  rw [← hZ, ← hY]
  have hZsplit : Z = centerIn R ⊔ Z' := by
    rw [hZ, hZ']
    exact iSup_mem_eq_sup_iSup_ne Δ centerIn hR
  have hZR : centerIn R ≤ R := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  have hZ'Y : Z' ≤ Y := by
    rw [hZ', hY]
    exact iSup₂_le fun R' hR' => iSup_le fun hne =>
      le_iSup₂_of_le R' hR' (le_iSup_of_le hne (by
        rintro _ ⟨w, _, rfl⟩
        exact w.2))
  have hYC : Commutes R Y := by
    have hle : Y ≤ Subgroup.centralizer (R : Set G) := by
      rw [hY]
      exact iSup₂_le fun R' hR' => iSup_le fun hne =>
        fun w hw r' hr' => hcomm R hR R' hR' (Ne.symm hne) r' hr' w hw
    intro r hr y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hy) r hr
  have hZle : Z ≤ (R ⊔ Z) ⊓ (Z ⊔ Y) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hx, Subgroup.mem_sup_left hx⟩
  apply le_antisymm _ hZle
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have e1 : R ⊔ Z = R ⊔ Z' := by
    rw [hZsplit]
    exact le_antisymm (sup_le le_sup_left (sup_le (hZR.trans le_sup_left) le_sup_right))
      (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
  have e2 : Z ⊔ Y = centerIn R ⊔ Y := by
    rw [hZsplit]
    exact le_antisymm (sup_le (sup_le le_sup_left (hZ'Y.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
  rw [e1] at hx1
  rw [e2] at hx2
  obtain ⟨r, hr, z', hz', hxr⟩ := exists_mul_of_mem_sup_of_commutes
    (fun a ha b hb => hYC a ha b (hZ'Y hb)) hx1
  obtain ⟨c, hc, y, hy, hxc⟩ := exists_mul_of_mem_sup_of_commutes
    (fun a ha b hb => hYC a (hZR ha) b hb) hx2
  have hry : c⁻¹ * r ∈ Y := by
    have h1 : r * z' = c * y := hxr.symm.trans hxc
    have : c⁻¹ * r = y * z'⁻¹ := by
      calc c⁻¹ * r = c⁻¹ * (r * z') * z'⁻¹ := by group
        _ = c⁻¹ * (c * y) * z'⁻¹ := by rw [h1]
        _ = y * z'⁻¹ := by group
    rw [this]
    exact Y.mul_mem hy (Y.inv_mem (hZ'Y hz'))
  have hcR : c ∈ R := hZR hc
  have hcr : c⁻¹ * r ∈ centerIn R := by
    have hmemR : c⁻¹ * r ∈ R := R.mul_mem (R.inv_mem hcR) hr
    refine ⟨⟨c⁻¹ * r, hmemR⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    apply Subtype.ext
    show (g : G) * (c⁻¹ * r) = (c⁻¹ * r) * g
    exact hYC g g.2 _ hry
  have hrZ : r ∈ centerIn R := by
    have : r = c * (c⁻¹ * r) := by group
    rw [this]
    exact (centerIn R).mul_mem hc hcr
  rw [hxr, hZsplit]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hrZ) (Subgroup.mem_sup_right hz')

variable (p f : ℕ) [Fact p.Prime]

theorem l6_5 : L6_5 p f := by
  intro _ _ G _ _ Ω _ Δ _ hcomm R hR
  exact inf_sup_centers_eq hcomm hR

end CFSG.ClassicalInvolution.Asc77
