module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs
public import CFSG.GF2Type.Aschbacher1976Full.WidthFused

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]


section Basic

variable {z : G} {Z A : Subgroup G}

theorem ZF_conj_eq (hD : Aschbacher1976Full.Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (g : G) : ZF (g⁻¹ * z * g) = conjugate Z g := by
  have hZ : centerAt z = Z :=
    Subgroup.ext fun x => Aschbacher1976Full.Width.mem_centerAt_iff hD hz hF2
  show centerAt (g⁻¹ * z * g) = conjugate Z g
  rw [centerAt_conj z g, hZ]

theorem exists_inv_conj {u : G} (h : IsConj z u) : ∃ g : G, u = g⁻¹ * z * g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [← hc]; simp⟩

theorem mem_Dinv_iff (hD : Aschbacher1976Full.Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (g : G) :
    g⁻¹ * z * g ∈ Dinv z ↔ g⁻¹ * z * g ≠ z ∧ ∀ x ∈ Z, g⁻¹ * x * g ∈ Hz z := by
  constructor
  · rintro ⟨-, hne, hle⟩
    refine ⟨hne, fun x hx => hle ?_⟩
    rw [ZF_conj_eq hD hz hF2 g] at *
    exact Aschbacher1976Full.Width.mem_conjugate_iff.mpr (by
      rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
  · rintro ⟨hne, hall⟩
    refine ⟨isConj_iff.mpr ⟨g⁻¹, by simp⟩, hne, ?_⟩
    rw [ZF_conj_eq hD hz hF2 g]
    intro y hy
    have hy' := Aschbacher1976Full.Width.mem_conjugate_iff.mp hy
    have := hall _ hy'
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

end Basic

theorem hsPartA_holds : HSPartA := by
  intro G _ _ z hset
  obtain ⟨⟨hsimp, hnab, hz, hsymp⟩, hZ4⟩ := hset
  haveI := hsimp
  have hF2 : IsPGroup 2 (Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Aschbacher1976Full.Width.exists_Z4Data hZ4
  have hcenter : ∀ g : G, ZF (g⁻¹ * z * g) = conjugate Z g := ZF_conj_eq hD hz hF2
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨g, hgF, hgne⟩ := Aschbacher1976Full.Width.exists_fused hnab hD hz hF2 (le_refl 2)
    refine ⟨g⁻¹ * z * g, (mem_Dinv_iff hD hz hF2 g).mpr ⟨hgne, ?_⟩⟩
    have hcomm : g⁻¹ * z * g ∈ centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hF : g⁻¹ * z * g ∈ Fz z := by
        rwa [← Aschbacher1976Full.Width.coreAt_eq_Fz hF2]
      exact Aschbacher1976Full.Width.Z_comm_F hD hx hF
    exact Aschbacher1976Full.Width.conjugate_le_H_of_comm hD hz hcomm
  · intro u hu
    obtain ⟨g, rfl⟩ := exists_inv_conj hu.1
    obtain ⟨hne, hall⟩ := (mem_Dinv_iff hD hz hF2 g).mp hu
    refine ⟨Aschbacher1976Full.Width.z1_mem_F hD hz hF2 hall, fun y hy hyF => ?_⟩
    have hcard : Nat.card ↥(conjugate Z g) = 4 := by
      unfold conjugate
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD.card_Z]
    rw [hcenter g] at hy
    have hyord : orderOf y = 4 := by
      rw [← Nat.card_zpowers, ← hy, hcard]
    have hy2 : y ^ 2 = z := by
      rcases Aschbacher1976Full.Width.sq_F hD hz (by simpa using hyF) with h | h
      · exfalso
        have h4 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h
        rw [hyord] at h4
        norm_num at h4
      · exact h
    have hzy : z ∈ conjugate Z g := by
      rw [hy]
      exact hy2 ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2
    have hzZ : z ∈ conjugate Z 1 := by
      rw [Aschbacher1976Full.Width.conjugate_one']
      exact hD.mem_z
    have heq : conjugate Z g = conjugate Z 1 := by
      rcases Aschbacher1976Full.Width.conj_pair_eq_or_disjoint hD hz hF2 g 1 with h | h
      · exact h
      · exfalso
        have hmem : z ∈ conjugate Z g ⊓ conjugate Z 1 := ⟨hzy, hzZ⟩
        rw [h, Subgroup.mem_bot] at hmem
        rw [hmem, orderOf_one] at hz
        omega
    have huZ : g⁻¹ * z * g ∈ Z := by
      have h1 : g⁻¹ * z * g ∈ conjugate Z g := by
        apply Aschbacher1976Full.Width.mem_conjugate_iff.mpr
        rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
        exact hD.mem_z
      rw [heq, Aschbacher1976Full.Width.conjugate_one'] at h1
      exact h1
    have hsq : (g⁻¹ * z * g) ^ 2 = 1 := by
      have hz2 : z * z = 1 := by rw [← sq]; exact Aschbacher1976Full.Width.z_sq hz
      calc (g⁻¹ * z * g) ^ 2 = g⁻¹ * (z * z) * g := by rw [pow_two]; group
        _ = 1 := by rw [hz2]; group
    have hne1 : g⁻¹ * z * g ≠ 1 := by
      intro h1
      have : z = 1 := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hz
      omega
    exact hne (Aschbacher1976Full.Width.involution_eq hD hz huZ hsq hne1)

end CFSG.GF2Type.Aschbacher1976Full.HS
