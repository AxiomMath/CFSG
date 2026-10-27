module

public import CFSG.ClassicalInvolution.Phan.PhanG6Oriented

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

theorem twoHomotopic_nil_of_encard_le_two {I C : Type*} (X : ChamberSystem I C) {J : Set I}
    (hJ : J.encard ≤ 2) (c : C) (γ : List (I × C)) (hγ : X.IsGallery c γ)
    (hγJ : ∀ i ∈ galleryType γ, i ∈ J) (hend : galleryEnd c γ = c) : X.TwoHomotopic c γ [] := by
  have := ElemMove.mk (X := X) (x := c) [] γ [] [] J hJ (by simpa using hγ) (by simp)
    (by simpa using hγJ) (by simp) (by simpa using hend)
  exact TwoHomotopic.of_elemMove (by simpa using this)

theorem commuteTypes_phan (hK : Nat.card K = (p ^ f) ^ 2) {a b : Fin 4} (hab : a ≠ b)
    (h1 : ¬ edgeD 4 a b) (h2 : ¬ edgeD 4 b a) : CommuteTypes (phanSystem S) a b := by
  intro x y z hxy hyz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  rw [phanSystem_adj_mk] at hxy hyz
  obtain ⟨ra, hra, t₁, ht₁, h₁⟩ := exists_mul_of_mem_parab hK a hxy
  obtain ⟨rb, hrb, t₂, ht₂, h₂⟩ := exists_mul_of_mem_parab hK b hyz
  have hnorm := torusSub_le_normalizer_range hK b (S := S)
  have hrb' : t₁ * rb * t₁⁻¹ ∈ (S.ι b).range := by
    have := (Subgroup.mem_normalizer_iff.1 (hnorm ht₁) rb).1 hrb
    simpa using this
  obtain ⟨A, hA⟩ := hra
  obtain ⟨B, hB⟩ := hrb'
  refine ⟨((g * (t₁ * rb * t₁⁻¹) : G) : G ⧸ torusSub S), ?_, ?_⟩
  · rw [phanSystem_adj_mk]
    have : g⁻¹ * (g * (t₁ * rb * t₁⁻¹)) = t₁ * rb * t₁⁻¹ := by group
    rw [this, ← hB]
    exact Lsup_le_parab {b} (ι_mem_Lsup (Set.mem_singleton b) B)
  · rw [phanSystem_adj_mk]
    have hk : (g * (t₁ * rb * t₁⁻¹))⁻¹ * k = ra * (t₁ * t₂) := by
      have e1 : g⁻¹ * h = ra * t₁ := h₁
      have e2 : h⁻¹ * k = rb * t₂ := h₂
      have hk' : g⁻¹ * k = (g⁻¹ * h) * (h⁻¹ * k) := by group
      rw [e1, e2] at hk'
      have hc : (S.ι a) A * (S.ι b) B = (S.ι b) B * (S.ι a) A :=
        (S.comm a b hab h1 h2 A B)
      have hcm : ra * (t₁ * rb * t₁⁻¹) = (t₁ * rb * t₁⁻¹) * ra := by
        rw [← hA, ← hB]
        exact hc
      calc (g * (t₁ * rb * t₁⁻¹))⁻¹ * k = (t₁ * rb * t₁⁻¹)⁻¹ * (g⁻¹ * k) := by group
        _ = (t₁ * rb * t₁⁻¹)⁻¹ * (ra * t₁ * (rb * t₂)) := by rw [hk']
        _ = (t₁ * rb * t₁⁻¹)⁻¹ * (ra * (t₁ * rb * t₁⁻¹) * (t₁ * t₂)) := by group
        _ = (t₁ * rb * t₁⁻¹)⁻¹ * ((t₁ * rb * t₁⁻¹) * ra * (t₁ * t₂)) := by rw [hcm]
        _ = ra * (t₁ * t₂) := by group
    rw [hk]
    exact mul_mem (Lsup_le_parab {a} (by rw [← hA]; exact ι_mem_Lsup (Set.mem_singleton a) A))
      (torusSub_le_parab {a} (mul_mem ht₁ ht₂))

theorem exists_tor_of_mul (hg : GoodFamily S) (a : Fin 4) {A : Su K p f 2} {M : G}
    {x₀ : normOne (unitaryInvolution K p f)} (hx₀ : x₀ * x₀ ≠ 1)
    (hM : tor S a x₀ * M = M * tor S a x₀) (hT : S.ι a A * M ∈ torusSub S) :
    ∃ y, S.ι a A = tor S a y := by
  have hc := torusSub_comm S (tor_mem_torusSub S a x₀) hT
  refine hg.exists_tor_of_comm a hx₀ ?_
  have : tor S a x₀ * S.ι a A * M = S.ι a A * tor S a x₀ * M := by
    calc tor S a x₀ * S.ι a A * M = tor S a x₀ * (S.ι a A * M) := by group
      _ = (S.ι a A * M) * tor S a x₀ := hc
      _ = S.ι a A * (M * tor S a x₀) := by group
      _ = S.ι a A * (tor S a x₀ * M) := by rw [hM]
      _ = S.ι a A * tor S a x₀ * M := by group
  exact mul_right_cancel this

theorem parab_zero_inf_parab_two_three (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f)
    (hg : GoodFamily S) {x : G} (h0 : x ∈ parab S {0}) (h23 : x ∈ parab S {2, 3}) :
    x ∈ torusSub S := by
  obtain ⟨r₀, hr₀, t, ht, rfl⟩ := exists_mul_of_mem_parab hK 0 h0
  have hc2 : ∀ a b, S.ι 0 a * S.ι 2 b = S.ι 2 b * S.ι 0 a := fun a b =>
    S.comm 0 2 (by decide) (by decide) (by decide) a b
  have hc3 : ∀ a b, S.ι 0 a * S.ι 3 b = S.ι 3 b * S.ι 0 a := fun a b =>
    S.comm 0 3 (by decide) (by decide) (by decide) a b
  have hn23 : (S.ι 3).range ≤ Subgroup.normalizer ((S.ι 2).range : Set G) := by
    have hcent : (S.ι 3).range ≤ Subgroup.centralizer ((S.ι 2).range : Set G) := by
      intro g hg3
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      obtain ⟨c, rfl⟩ := hg3
      exact S.comm 2 3 (by decide) (by decide) (by decide) b c
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hLT := Subgroup.coe_mul_of_right_le_normalizer_left (Lsup S {2, 3}) (torusSub S)
    (torusSub_le_normalizer_Lsup hK {2, 3})
  have hx' : r₀ * t ∈ ((Lsup S {2, 3} ⊔ torusSub S : Subgroup G) : Set G) := by
    have : r₀ * t ∈ parab S {2, 3} := h23
    rwa [parab, sup_comm] at this
  rw [hLT] at hx'
  obtain ⟨n, hn, t', ht', hnx0⟩ := hx'
  have hnx : n * t' = r₀ * t := hnx0
  have hLs : Lsup S {2, 3} = (S.ι 2).range ⊔ (S.ι 3).range := Lsup_pair 2 3
  have hR := Subgroup.coe_mul_of_right_le_normalizer_left (S.ι 2).range (S.ι 3).range hn23
  have hn' : n ∈ (((S.ι 2).range ⊔ (S.ι 3).range : Subgroup G) : Set G) := by
    rw [← hLs]
    exact hn
  rw [hR] at hn'
  obtain ⟨r₂, ⟨B, rfl⟩, r₃, ⟨C, rfl⟩, rfl⟩ := hn'
  obtain ⟨A, rfl⟩ := hr₀
  have hnx' : S.ι 0 A * t = S.ι 2 B * S.ι 3 C * t' := hnx.symm
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK hq
  have hcomm : S.ι 0 A * (S.ι 2 B * S.ι 3 C) = (S.ι 2 B * S.ι 3 C) * S.ι 0 A := by
    rw [← mul_assoc, hc2, mul_assoc, hc3, ← mul_assoc]
  have hM : tor S 0 x₀ * (S.ι 2 B * S.ι 3 C)⁻¹ = (S.ι 2 B * S.ι 3 C)⁻¹ * tor S 0 x₀ := by
    have c2 : Commute (tor S 0 x₀) (S.ι 2 B) := hc2 _ _
    have c3 : Commute (tor S 0 x₀) (S.ι 3 C) := hc3 _ _
    exact (c2.mul_right c3).inv_right
  have hmem : S.ι 0 A * (S.ι 2 B * S.ι 3 C)⁻¹ ∈ torusSub S := by
    have : S.ι 0 A * (S.ι 2 B * S.ι 3 C)⁻¹ = t' * t⁻¹ := by
      have e1 : S.ι 0 A = (S.ι 2 B * S.ι 3 C) * (t' * t⁻¹) := by
        calc S.ι 0 A = S.ι 0 A * t * t⁻¹ := by group
          _ = (S.ι 2 B * S.ι 3 C) * t' * t⁻¹ := by rw [hnx']
          _ = (S.ι 2 B * S.ι 3 C) * (t' * t⁻¹) := by group
      calc S.ι 0 A * (S.ι 2 B * S.ι 3 C)⁻¹ = (S.ι 2 B * S.ι 3 C)⁻¹ * S.ι 0 A :=
            (Commute.inv_right (show Commute (S.ι 0 A) (S.ι 2 B * S.ι 3 C) from hcomm)).eq
        _ = t' * t⁻¹ := by rw [e1]; group
    rw [this]
    exact mul_mem ht' (inv_mem ht)
  obtain ⟨y, hy⟩ := exists_tor_of_mul hg 0 hx₀ hM hmem
  rw [hy]
  exact mul_mem (tor_mem_torusSub S 0 y) ht

theorem residue_inter_023 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) (hg : GoodFamily S)
    (c d : G ⧸ torusSub S) (h1 : d ∈ (phanSystem S).residue {0} c)
    (h2 : d ∈ (phanSystem S).residue {2, 3} c) : d = c := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective d
  rw [mem_residue_singleton, phanSystem_adj_mk] at h1
  obtain ⟨s, hs, hsd⟩ := exists_mem_of_mem_residue (fun i => torusSub_le_parab {i})
    (parab S {2, 3}) (fun j hj => parab_mono (by simpa using hj)) g h2
  have ht0 : (g * s)⁻¹ * h ∈ torusSub S := by
    have := QuotientGroup.eq.1 hsd
    simpa using inv_mem this
  have hx : g⁻¹ * h ∈ parab S {2, 3} := by
    have : g⁻¹ * h = s * ((g * s)⁻¹ * h) := by group
    rw [this]
    exact mul_mem hs (torusSub_le_parab _ ht0)
  have := parab_zero_inf_parab_two_three hK hq hg h1 hx
  exact (QuotientGroup.eq.2 this).symm

theorem nullOn_023 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) (hg : GoodFamily S) :
    NullOnPhan S {0, 2, 3} := by
  intro x γ hγ hJ hend
  have hu : ({0, 2, 3} : Set (Fin 4)) = {0} ∪ {2, 3} := by
    ext j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    try tauto
  refine twoHomotopic_nil_of_union (J₁ := {0}) (J₂ := {2, 3}) ?_
    (fun c d => residue_inter_023 hK hq hg c d)
    (fun c γ hγ hJ hend => twoHomotopic_nil_of_encard_le_two (phanSystem S)
      (by simp [Set.encard_singleton]) c γ hγ hJ hend)
    (fun c γ hγ hJ hend => twoHomotopic_nil_of_encard_le_two (phanSystem S)
      (by simpa using pair_encard_le_two 2 3) c γ hγ hJ hend) x γ hγ (fun i hi => ?_) hend
  · intro j hj i hi
    have hi0 : i = 0 := hi
    subst hi0
    rcases hj with rfl | rfl
    · exact commuteTypes_phan hK (by decide) (by decide) (by decide)
    · exact commuteTypes_phan hK (by decide) (by decide) (by decide)
  · have := hJ i hi
    rw [hu] at this
    exact this

end CFSG.ClassicalInvolution.PhanG
