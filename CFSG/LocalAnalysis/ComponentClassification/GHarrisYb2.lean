module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb1
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisUT

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

abbrev S1Y : Subgroup D.Y1 := D.S1.subgroupOf D.Y1

omit [Finite Y] in
theorem S1_le_Y1 : D.S1 ≤ D.Y1 := inf_le_right

omit [Finite Y] in
theorem pre_mem_S1 {s₀ : SE} (hs : D.toG s₀ ∈ D.S1) : s₀.d.val < 4 := by
  rw [← SE.mem_centralizer_l_iff]
  have h := mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2
  exact D.toG_injective (by rw [map_mul, map_mul]; exact h)

@[expose] def preS1 (s : D.S1Y) : SE := Classical.choose (D.exists_toG (mem_inf.mp s.2).1)

omit [Finite Y] in
theorem toG_preS1 (s : D.S1Y) : D.toG (D.preS1 s) = ((s : D.Y1) : Y) :=
  Classical.choose_spec (D.exists_toG (mem_inf.mp s.2).1)

omit [Finite Y] in
theorem preS1_lt (s : D.S1Y) : (D.preS1 s).d.val < 4 :=
  D.pre_mem_S1 (by rw [D.toG_preS1]; exact s.2)

omit [Finite Y] in
theorem preS1_mul (s t : D.S1Y) : D.preS1 (s * t) = D.preS1 s * D.preS1 t :=
  D.toG_injective (by rw [map_mul, D.toG_preS1, D.toG_preS1, D.toG_preS1]; rfl)

@[expose] def rhoUT : D.S1Y →* UT3 F4c where
  toFun s := SE.toUT (D.preS1 s)
  map_one' := by
    have h : D.preS1 1 = 1 := D.toG_injective (by rw [D.toG_preS1, map_one]; rfl)
    rw [h]
    exact SE.toUT_lpow.1
  map_mul' s t := by
    rw [D.preS1_mul]
    exact SE.toUT_mul _ _ (D.preS1_lt s) (D.preS1_lt t)

omit [Finite Y] in
theorem rhoUT_surjective : Function.Surjective D.rhoUT := by
  intro u
  obtain ⟨s₀, hs₀, rfl⟩ := SE.toUT_surj u
  have hmem : D.toG s₀ ∈ D.S1 := mem_inf.mpr ⟨D.toG_mem s₀, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, (SE.mem_centralizer_l_iff s₀).mpr hs₀])⟩
  refine ⟨⟨⟨D.toG s₀, D.S1_le_Y1 hmem⟩, hmem⟩, ?_⟩
  change SE.toUT (D.preS1 _) = SE.toUT s₀
  congr 1
  exact D.toG_injective (by rw [D.toG_preS1])

abbrev sigmaX : D.S1Y →* D.Xt := D.piX.comp D.S1Y.subtype

theorem mem_zpowers_l_iff (y : D.Y1) :
    y ∈ zpowers D.lY ↔ (y : Y) = 1 ∨ (y : Y) = D.l ∨ (y : Y) = D.z ∨ (y : Y) = D.l * D.z := by
  classical
  have hlz : D.l * D.z = D.z * D.l := mem_centralizer_singleton_iff.mp D.l_mem_M
  constructor
  · intro hy
    rw [mem_zpowers_iff_mem_range_orderOf, D.orderOf_lY] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    interval_cases j
    · left; simp
    · right; left; simp
    · right; right; left
      simp only [Subgroup.coe_pow]
      rw [pow_two, D.l_mul_l]
    · right; right; right
      simp only [Subgroup.coe_pow]
      rw [pow_succ, pow_two, D.l_mul_l, hlz]
  · rintro (h | h | h | h)
    · rw [show y = 1 from Subtype.ext h]; exact one_mem _
    · rw [show y = D.lY from Subtype.ext h]; exact mem_zpowers _
    · rw [show y = D.lY ^ 2 from Subtype.ext (by rw [h, Subgroup.coe_pow, pow_two, D.l_mul_l])]
      exact pow_mem (mem_zpowers _) 2
    · rw [show y = D.lY ^ 3 from Subtype.ext (by
        rw [h, Subgroup.coe_pow, pow_succ, pow_two, D.l_mul_l, hlz])]
      exact pow_mem (mem_zpowers _) 3

theorem ker_sigmaX_eq : D.sigmaX.ker = D.rhoUT.ker := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, D.mem_zpowers_l_iff]
  change _ ↔ SE.toUT (D.preS1 s) = 1
  have hs : ((D.S1Y.subtype s : D.Y1) : Y) = D.toG (D.preS1 s) := (D.toG_preS1 s).symm
  constructor
  · rintro (h | h | h | h) <;> rw [hs] at h
    · rw [D.toG_injective (h.trans (map_one _).symm)]; exact SE.toUT_lpow.1
    · rw [D.toG_injective h]; exact SE.toUT_lpow.2.1
    · rw [D.toG_injective h]; exact SE.toUT_lpow.2.2.1
    · rw [D.toG_injective (h.trans (map_mul _ _ _).symm)]; exact SE.toUT_lpow.2.2.2
  · intro h
    rcases SE.toUT_ker _ (D.preS1_lt s) h with h' | h' | h' | h' <;> rw [hs, h']
    · left; exact map_one _
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; exact map_mul _ _ _

theorem isSylowOf_S1_Y1 (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : IsSylowOf 2 D.S1 D.Y1 := by
  have h := D.isSylowOf_S1_M1
  rwa [D.M1_eq hO hz] at h

@[expose] def sylowXt (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : Sylow 2 D.Xt :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (Classical.choose (D.isSylowOf_S1_Y1 hO hz).exists_sylow_eq_subgroupOf).mapSurjective
    (QuotientGroup.mk'_surjective (zpowers D.lY))

theorem coe_sylowXt (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) :
    ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) = D.S1Y.map D.piX := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sylowXt, Sylow.coe_mapSurjective,
    Classical.choose_spec (D.isSylowOf_S1_Y1 hO hz).exists_sylow_eq_subgroupOf]

end GHSylow

end CFSG.ComponentClassification.GHarris
