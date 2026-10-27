module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX6Eng

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {R R' : Subgroup G} {z : G}

theorem exists_bad_complement_gen
    (hz2 : z * z = 1)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hfg : ∀ {D₀ D : Subgroup G} (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G)) (hD₀D : D₀ ≤ D) (hbad : z ∉ zStarOf (Subgroup.centralizer (D : Set
        G))) (hmax : ∀ F : Subgroup G, F ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G) → D₀ ≤ F → z ∉ zStarOf (Subgroup.centralizer (F : Set G)) → Nat.card F
        ≤ Nat.card D) {x b : G} (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G)) (hxD : x ∉ D) (hxzD : x * z ∉ D) (hbD : b ∈ D) (hb1 : b ≠ 1) (hb2 : b
        * b = 1) (hbx : x * b = b * x) (hbc : ∀ d ∈ D, d * b = b * d), False)
    (hnsq : ∀ {A H : Subgroup G} (hA : IsPGroup 2 A) (hHA : H ≤ A) (hne : H ≠ A), ∃ x ∈ A, x ∉ H ∧ x
        ∈ Subgroup.normalizer (H : Set G) ∧ x * x ∈ H)
    (hcent : ∀ {E B : Subgroup G} (hE : IsPGroup 2 E) (hBE : B ≤ E) (hEB : E ≤ Subgroup.normalizer
        (B : Set G)) (hB : B ≠ ⊥), ∃ b ∈ B, b ≠ 1 ∧ b * b = 1 ∧ ∀ e ∈ E, e * b = b * e)
    (hinf : ∀ {D : Subgroup G} {z x : G} (hzc : ∀ d ∈ D, d * z = z * d) (hcover : ∀ h ∈ conjSub x D,
        h ∈ D ∨ h * z ∈ D) (h4 : 4 ≤ Nat.card D), D ⊓ conjSub x D ≠ ⊥)
    (hsup : ∀ {D : Subgroup G} {z : G} (hz2 : z * z = 1) (hzc : ∀ d ∈ D, d * z = z * d), ∃ H :
        Subgroup G, ∀ g, g ∈ H ↔ g ∈ D ∨ g * z ∈ D)
    {D₀ : Subgroup G}
    (hD₀A : D₀ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hD₀bad : z ∉ zStarOf (Subgroup.centralizer (D₀ : Set G)))
    (hD₀1 : D₀ ≠ ⊥)
    (hsmall : Nat.card D₀ < 4 → ∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G)
        : Set G), x ∉ D₀ ∧ x * z ∉ D₀ ∧ (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x * z ∈ D₀))
    : ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
        ∧ D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧ ∀ g ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), g ∈ D ∨ g * z ∈ D := by
  classical
  set A := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA
  have hzi : z⁻¹ = z := by
    calc z⁻¹ = z⁻¹ * (z * z) := by rw [hz2, mul_one]
      _ = z := by group
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le inf_le_left
  set 𝒟 : Set (Subgroup G) :=
    {D | D ≤ A ∧ D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G))} with h𝒟
  have hne : ((Set.toFinite 𝒟).toFinset).Nonempty :=
    ⟨D₀, (Set.Finite.mem_toFinset _).mpr ⟨hD₀A, le_refl _, hD₀bad⟩⟩
  obtain ⟨D, hD, hmax⟩ := ((Set.toFinite 𝒟).toFinset).exists_max_image (fun D => Nat.card D) hne
  rw [Set.Finite.mem_toFinset] at hD
  obtain ⟨hDA, hD₀D, hDbad⟩ := hD
  have hmax' : ∀ F : Subgroup G, F ≤ A → D₀ ≤ F →
      z ∉ zStarOf (Subgroup.centralizer (F : Set G)) → Nat.card F ≤ Nat.card D :=
    fun F h1 h2 h3 => hmax F ((Set.Finite.mem_toFinset _).mpr ⟨h1, h2, h3⟩)
  refine ⟨D, hDA, hD₀D, hDbad, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgA, hgD, hgzD⟩ := hcon
  have hzc : ∀ d ∈ D, d * z = z * d := fun d hd => hzS d (hDA hd).1
  obtain ⟨H, hH⟩ := hsup hz2 hzc
  have hHA : H ≤ A := by
    intro h hh
    rcases (hH h).mp hh with h1 | h1
    · exact hDA h1
    · have : h = (h * z) * z := by rw [mul_assoc, hz2, mul_one]
      rw [this]
      exact A.mul_mem (hDA h1) hzA
  have hzD : conjSub z D = D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      have h1 : z * d * z⁻¹ = d := by rw [← hzc d hd]; group
      simpa [h1] using hd
    · intro d hd
      refine ⟨d, hd, ?_⟩
      show z * d * z⁻¹ = d
      rw [← hzc d hd]; group
  have hHD : ∀ h ∈ H, conjSub h D = D := by
    intro h hh
    rcases (hH h).mp hh with h1 | h1
    · exact conjSub_eq_self_of_mem h1
    · have e : h = (h * z) * z := by rw [mul_assoc, hz2, mul_one]
      rw [e, conjSub_mul, hzD, conjSub_eq_self_of_mem h1]
  have key : ∃ x ∈ A, x ∉ D ∧ x * z ∉ D ∧ ∃ B : Subgroup G, B ≤ D ∧ B ≠ ⊥ ∧
      D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (B : Set G) := by
    by_cases h4 : 4 ≤ Nat.card D
    · have hHne : H ≠ A := by
        intro h
        rcases (hH g).mp (h ▸ hgA) with h1 | h1
        · exact hgD h1
        · exact hgzD h1
      obtain ⟨x, hxA, hxH, hxN, hx2⟩ := hnsq hA2 hHA hHne
      have hxD : x ∉ D := fun h => hxH ((hH x).mpr (Or.inl h))
      have hxzD : x * z ∉ D := fun h => hxH ((hH x).mpr (Or.inr h))
      have hxHH : conjSub x H = H := mem_normalizer_iff_conjSub_eq.mp hxN
      have hxiH : ∀ h ∈ H, x⁻¹ * h * x⁻¹⁻¹ ∈ H := by
        intro h hh
        have h1 : x⁻¹ * h * x⁻¹⁻¹ ∈ conjSub x⁻¹ H := Generic.conj_mem_conjSub hh
        rwa [show conjSub x⁻¹ H = H from mem_normalizer_iff_conjSub_eq.mp
          (Subgroup.inv_mem _ hxN)] at h1
      refine ⟨x, hxA, hxD, hxzD, D ⊓ conjSub x D, inf_le_left, ?_, ?_⟩
      · refine hinf hzc (fun h hh => ?_) h4
        have h1 : h ∈ H := by
          rw [← hxHH]
          obtain ⟨d, hd, rfl⟩ := hh
          exact ⟨d, (hH d).mpr (Or.inl hd), rfl⟩
        exact (hH h).mp h1
      · have hDB : D ≤ Subgroup.normalizer ((D ⊓ conjSub x D : Subgroup G) : Set G) := by
          intro d hd
          refine mem_normalizer_iff_conjSub_eq.mpr ?_
          unfold conjSub
          rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d).injective]
          change conjSub d D ⊓ conjSub d (conjSub x D) = D ⊓ conjSub x D
          have h1 : conjSub d (conjSub x D) = conjSub x D := by
            have hcH := hxiH d ((hH d).mpr (Or.inl hd))
            have e : d = x * (x⁻¹ * d * x⁻¹⁻¹) * x⁻¹ := by group
            calc conjSub d (conjSub x D)
                = conjSub (x * (x⁻¹ * d * x⁻¹⁻¹) * x⁻¹) (conjSub x D) := by rw [← e]
              _ = conjSub x (conjSub (x⁻¹ * d * x⁻¹⁻¹) (conjSub x⁻¹ (conjSub x D))) := by
                  rw [conjSub_mul, conjSub_mul]
              _ = conjSub x (conjSub (x⁻¹ * d * x⁻¹⁻¹) D) := by
                  rw [← conjSub_mul x⁻¹ x, inv_mul_cancel, conjSub_one]
              _ = conjSub x D := by rw [hHD _ hcH]
          rw [conjSub_eq_self_of_mem hd, h1]
        have hxB : x ∈ Subgroup.normalizer ((D ⊓ conjSub x D : Subgroup G) : Set G) := by
          refine mem_normalizer_iff_conjSub_eq.mpr ?_
          unfold conjSub
          rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective]
          change conjSub x D ⊓ conjSub x (conjSub x D) = D ⊓ conjSub x D
          rw [← conjSub_mul, hHD _ hx2, inf_comm]
        have hzB : z ∈ Subgroup.normalizer ((D ⊓ conjSub x D : Subgroup G) : Set G) := by
          refine mem_normalizer_iff_conjSub_eq.mpr ?_
          unfold conjSub
          rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective]
          change conjSub z D ⊓ conjSub z (conjSub x D) = D ⊓ conjSub x D
          have h1 : conjSub z (conjSub x D) = conjSub x D := by
            have e : z * x = x * z := by
              have := hzS x hxA.1
              exact this.symm
            rw [← conjSub_mul, e, conjSub_mul, hzD]
          rw [hzD, h1]
        exact sup_le (sup_le hDB (Subgroup.zpowers_le.mpr hxB)) (Subgroup.zpowers_le.mpr hzB)
    ·
      have hD₀le : Nat.card D₀ ≤ Nat.card D := Subgroup.card_le_of_le hD₀D
      obtain ⟨x, hxA, hxD₀, hxzD₀, hxc, hx2⟩ := hsmall (by omega)
      have hD2 : IsPGroup 2 D := hA2.to_le hDA
      obtain ⟨k, hk⟩ := hD2.exists_card_eq
      have hD₀2 : IsPGroup 2 D₀ := hA2.to_le hD₀A
      obtain ⟨k₀, hk₀⟩ := hD₀2.exists_card_eq
      have hk₀1 : 1 ≤ k₀ := by
        by_contra h
        have : k₀ = 0 := by omega
        rw [this, pow_zero, Subgroup.card_eq_one] at hk₀
        exact hD₀1 hk₀
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hcard : Nat.card D ≤ Nat.card D₀ := by
        rw [hk, hk₀]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hDeq : D₀ = D := Subgroup.eq_of_le_of_card_ge hD₀D hcard
      rw [← hDeq]
      refine ⟨x, hxA, hxD₀, hxzD₀, D₀, le_refl _, hD₀1, ?_⟩
      have hD₀N : D₀ ≤ Subgroup.normalizer (D₀ : Set G) := Subgroup.le_normalizer
      have hxN : x ∈ Subgroup.normalizer (D₀ : Set G) := by
        refine mem_normalizer_iff_conjSub_eq.mpr ?_
        refine le_antisymm ?_ ?_
        · rintro _ ⟨d, hd, rfl⟩
          show x * d * x⁻¹ ∈ D₀
          rw [hxc d hd, mul_inv_cancel_right]
          exact hd
        · intro d hd
          refine ⟨d, hd, ?_⟩
          show x * d * x⁻¹ = d
          rw [hxc d hd, mul_inv_cancel_right]
      have hzN : z ∈ Subgroup.normalizer (D₀ : Set G) := by
        rw [← hDeq] at hzD
        exact mem_normalizer_iff_conjSub_eq.mpr hzD
      exact sup_le (sup_le hD₀N (Subgroup.zpowers_le.mpr hxN)) (Subgroup.zpowers_le.mpr hzN)
  obtain ⟨x, hxA, hxD, hxzD, B, hBD, hB1, hEB⟩ := key
  have hEA : D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ A :=
    sup_le (sup_le hDA (Subgroup.zpowers_le.mpr hxA)) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 (D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) :=
    hA2.to_le hEA
  have hBE : B ≤ D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
    hBD.trans (le_sup_left.trans le_sup_left)
  obtain ⟨b, hbB, hb1, hb2, hbc⟩ := hcent hE2 hBE hEB hB1
  exact hfg hDA hD₀D hDbad hmax' hxA hxD hxzD (hBD hbB) hb1 hb2
    (hbc x (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
    (fun d hd => (hbc d (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd))))

end CX6Eng

end CFSG.ClassicalInvolution.Asc77
