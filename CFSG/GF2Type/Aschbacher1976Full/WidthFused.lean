module

public import CFSG.GF2Type.Aschbacher1976Full.WidthPair
public import CFSG.GF2Type.Aschbacher1976Common.NotWeaklyClosed
public import CFSG.GF2Type.Aschbacher1976Full.WidthZ1

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]


theorem exists_pair_of_card_le_two {F : Subgroup G} (s : Finset G) (hs : s.card ≤ 2)
    (hsF : ∀ t ∈ s, t ∈ F) : ∃ x y : G, x ∈ F ∧ y ∈ F ∧ ∀ t ∈ s, t = x ∨ t = y := by
  classical
  have h3 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases h3 with h | h | h
  · refine ⟨1, 1, F.one_mem, F.one_mem, fun t ht => ?_⟩
    have := Finset.card_eq_zero.mp h
    simp [this] at ht
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, hsF a (by simp), hsF a (by simp), fun t ht => Or.inl (by simpa using ht)⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, hsF a (by simp), hsF b (by simp), fun t ht => by simpa using ht⟩

section Fused

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem not_twoGen_F (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hw : 2 ≤ w) : ¬ ∃ s : Finset G, s.card ≤ 2 ∧ closure (s : Set G) = Fz z := by
  rintro ⟨s, hs, hcl⟩
  have hsF : ∀ t ∈ s, t ∈ Fz z := fun t ht => hcl ▸ Subgroup.subset_closure (Finset.mem_coe.mpr ht)
  obtain ⟨x, y, hxF, hyF, hsxy⟩ := exists_pair_of_card_le_two s hs hsF
  have hle : Fz z ≤ closure ({x, y} : Set G) := by
    rw [← hcl]
    apply Subgroup.closure_mono
    intro t ht
    rcases hsxy t (Finset.mem_coe.mp ht) with h | h <;> simp [h]
  have hcard32 : Nat.card (closure ({x, y} : Set G)) ≤ 32 :=
    card_closure_pair_le (z_sq hz) (fun f hf => Z_comm_F hD hD.mem_z hf) (fun f hf => sq_F hD hz hf)
      (fun f hf g hg => comm_F hD hz hf hg) hxF hyF
  have hFcard := Subgroup.card_le_of_le hle
  rw [card_Fz hD hz] at hFcard
  have h64 : 2 ^ 6 ≤ 2 ^ (2 * w + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_fused [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : Z4Data z w Z A)
    (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) (hw : 2 ≤ w) :
    ∃ g : G, g⁻¹ * z * g ∈ coreAt z ∧ g⁻¹ * z * g ≠ z := by
  obtain ⟨k, hkZ, hkord, hgen, hk2⟩ := exists_gen_Z hD hz
  have hZk : Subgroup.zpowers k = Z := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr hkZ
    · intro x hx
      obtain ⟨i, rfl⟩ := hgen x hx
      exact zpow_mem_zpowers k i
  have hcZ : centerAt z = Z := Subgroup.ext (fun x => mem_centerAt_iff hD hz hF2)
  have hnot : ¬ CFSG.EvenSporadicStandard.Finkelstein77.WeaklyClosedInNormalizer
      (Subgroup.zpowers k) := by
    intro hwc
    have h2 := CFSG.GF2Type.Aschbacher1976Common.dihedral_or_semidihedral_of_weaklyClosed hnab
      hkord hwc
    obtain ⟨s, hs, hcl⟩ := CFSG.GF2Type.Aschbacher1976Common.twoGen_of_isPGroup h2 hF2
    exact not_twoGen_F hD hz hF2 hw ⟨s, hs, hcl⟩
  unfold CFSG.EvenSporadicStandard.Finkelstein77.WeaklyClosedInNormalizer at hnot
  push Not at hnot
  obtain ⟨h, hle, hne⟩ := hnot
  rw [hZk] at hle hne
  have hconj : conjugate Z h⁻¹ = Z.map (MulAut.conj h).toMonoidHom := by
    unfold conjugate
    rw [inv_inv]
  rw [← hconj] at hle hne
  have hN : normalizer (Z : Set G) = Hz z := by
    rw [← hcZ]
    exact normalizer_centerAt hD hz hF2
  have hleH : conjugate Z h⁻¹ ≤ Hz z := by
    intro y hy
    have := hle hy
    rw [hN] at this
    exact this
  have hg : ∀ x ∈ Z, h⁻¹⁻¹ * x * h⁻¹ ∈ Hz z := by
    intro x hx
    apply hleH
    apply mem_conjugate_iff.mpr
    have e : h⁻¹ * (h⁻¹⁻¹ * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  refine ⟨h⁻¹, ?_, ?_⟩
  · rw [coreAt_eq_Fz hF2]
    exact z1_mem_F hD hz hF2 hg
  · intro heq
    have hgH : h⁻¹ ∈ Hz z := by
      apply mem_centralizer_singleton_iff.mpr
      calc h⁻¹ * z = h⁻¹ * (h⁻¹⁻¹ * z * h⁻¹) := by rw [heq]
        _ = z * h⁻¹ := by group
    exact hne (conjugate_Z_of_mem_H hD hz hF2 hgH)

end Fused

end CFSG.GF2Type.Aschbacher1976Full.Width
