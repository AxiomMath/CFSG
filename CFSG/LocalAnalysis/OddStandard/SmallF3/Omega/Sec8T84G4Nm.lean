module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Co
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

section Out

variable {G : Type} [Group G]

theorem sec8t84g4_mem_centralizer_of_le {t : G} {L : Subgroup G}
    (h : L ≤ centralizer ({t} : Set G)) : t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (h ha)

theorem sec8t84g4_outer_mul_cent {L : Subgroup G} {n : ℕ} {ε : ℤˣ} {s c : G}
    (h : InducesOutsideGStar L n ε s) (hc : c ∈ centralizer (L : Set G)) :
    InducesOutsideGStar L n ε (s * c) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hn, hε, hv, hxx, hxn⟩ := h
  refine ⟨V, i1, i2, i3, Q, hQ, e, x, hn, hε, ?_, hxx, hxn⟩
  have h2 := inducesViaP_mul hv (inducesViaP_one_of_centralizer (e := e) hc)
  rwa [mul_one] at h2

end Out

section Norm

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

theorem sec8t84g4_mem_normalizer_of_conj_mem {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_le : A.map (MulAut.conj g) ≤ A := by
    rintro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using h e he
  refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem sec8t84g4_conj_surj_of_swap (ht : t * t = 1) {A A2 : Subgroup G}
    (hs2 : ∀ b ∈ A2, t * b * t⁻¹ ∈ A) {x : G} (hx : x ∈ A2) : ∃ x' ∈ A, x = t * x' * t⁻¹ := by
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  refine ⟨t * x * t⁻¹, hs2 x hx, ?_⟩
  calc x = (t * t) * x * (t⁻¹ * t⁻¹) := by rw [ht, hti]; group
    _ = t * (t * x * t⁻¹) * t⁻¹ := by group

theorem sec8t84g4_zpow_invol (ht : t * t = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  have hz2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  have key : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, hz2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [key, h]; exact zpow_zero t
  · right; rw [key, h]; exact zpow_one t

theorem sec8t84g4_norm_prod (W : Sec8T84Wr G t T1 T2) {A A2 : Subgroup G} (hA : A ≤ T1)
    (hA2 : A2 ≤ T2) (hAn : (A.subgroupOf T1).Normal) (hs1 : ∀ a ∈ A, t * a * t⁻¹ ∈ A2)
    (hs2 : ∀ b ∈ A2, t * b * t⁻¹ ∈ A) :
    ∀ d ∈ T1 ⊔ T2, d ∈ normalizer (A : Set G) ∧ d ∈ normalizer (A2 : Set G) := by
  haveI := hAn
  have hT1 : T1 ≤ normalizer (A : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hA
  have hT2A : ∀ b ∈ T2, b ∈ normalizer (A : Set G) := fun b hb =>
    sec8t84g4_mem_normalizer_of_conj_mem fun x hx => by
      have hc : x * b = b * x := W.comm x (hA hx) b hb
      have : b * x * b⁻¹ = x := by rw [← hc]; group
      rw [this]; exact hx
  have hT1A2 : ∀ a ∈ T1, a ∈ normalizer (A2 : Set G) := fun a ha =>
    sec8t84g4_mem_normalizer_of_conj_mem fun x hx => by
      have hc : a * x = x * a := W.comm a ha x (hA2 hx)
      have : a * x * a⁻¹ = x := by rw [hc]; group
      rw [this]; exact hx
  have hT2A2 : ∀ b ∈ T2, b ∈ normalizer (A2 : Set G) := fun b hb =>
    sec8t84g4_mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨a', ha', rfl⟩ := sec8t84g4_conj_surj_of_swap W.t_sq W.swap2 hb
      obtain ⟨x', hx', rfl⟩ := sec8t84g4_conj_surj_of_swap W.t_sq hs2 hx
      have hn : a' * x' * a'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hT1 ha') x').mp hx'
      have e : (t * a' * t⁻¹) * (t * x' * t⁻¹) * (t * a' * t⁻¹)⁻¹ = t * (a' * x' * a'⁻¹) * t⁻¹ := by
        group
      rw [e]
      exact hs1 _ hn
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84_wr_decomp W hd
  exact ⟨Subgroup.mul_mem _ (hT1 ha) (hT2A b hb), Subgroup.mul_mem _ (hT1A2 a ha) (hT2A2 b hb)⟩

theorem sec8t84g4_T_decomp (W : Sec8T84Wr G t T1 T2) {T : Subgroup G}
    (hT : T = zpowers t ⊔ (T1 ⊔ T2)) {x : G} (hx : x ∈ T) :
    x ∈ T1 ⊔ T2 ∨ ∃ d ∈ T1 ⊔ T2, x = t * d := by
  have hn : zpowers t ≤ normalizer ((T1 ⊔ T2 : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact sec8t84g4_mem_normalizer_of_involution W.t_sq fun y hy => sec8t84_wr_conj_mem W hy
  rw [hT, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx
  obtain ⟨k, hk, d, hd, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rcases sec8t84g4_zpow_invol W.t_sq n with h | h
  · left
    show t ^ n * d ∈ T1 ⊔ T2
    rw [h, one_mul]; exact hd
  · right
    refine ⟨d, hd, ?_⟩
    show t ^ n * d = t * d
    rw [h]

end Norm

end CFSG.OddStandard.SmallF3.Omega
