module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IInner

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


theorem d3InnerInvolution_of_sylow (h : D3InnerSylow) : D3InnerInvolution := by
  intro K _ _ n hK t ht3 htE z hz2 hz1 hzI hzt A hA hAt hAz
  by_cases hA1 : A = ⊥
  · subst hA1
    rw [Subgroup.card_bot]
    exact Nat.one_le_pow _ _ (by norm_num)
  haveI := charP_three_of_card hK
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨S, hAS, hSt, hSz⟩ := h K n hK t ht3 htE z hz2 hz1 hzI hzt A hA hA1 hAt hAz
  let φ : D4Model K ≃* ↥(adjointGroup Tag.D4 K) :=
    (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm
  set α : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ t with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ht3, map_one]
  have hαapp : ∀ s : D4Model K, α (φ s) = φ (t s) := fun s => by
    rw [hα, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hαnot : α ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    rintro ⟨y, hy⟩
    apply htE
    have h1 : t = MulAut.conj (φ.symm y) := by
      apply (MulAut.congr φ).injective
      rw [← hα, ← hy, d3f_congr_conj, MulEquiv.apply_symm_apply]
    rw [h1]
    exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _
  obtain ⟨y, hy⟩ := hzI
  have hy2 : y * y = 1 := by
    apply hinj
    rw [map_mul, hy, map_one]
    rw [← pow_two]
    exact hz2
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hz1
    rw [← hy, map_one]
  have hty : t y = y := fixed_of_commute_conj hcen (by rw [hy]; exact hzt.symm)
  set g : ↥(adjointGroup Tag.D4 K) := φ y with hg
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, hy2, map_one]
  have hg1 : g ≠ 1 := fun h' => hy1 (φ.injective (by rw [← hg, h', map_one]))
  have hαg : α g = g := by
    rw [hg, hαapp, hty]
  set S' : Sylow 3 ↥(adjointGroup Tag.D4 K) := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective S with hS'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS'coe : (S' : Subgroup ↥(adjointGroup Tag.D4 K)) =
      (S : Subgroup (D4Model K)).map φ.toMonoidHom := rfl
  have hS'α : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map α.toMonoidHom = S' := by
    rw [hS'coe, Subgroup.map_map]
    have : α.toMonoidHom.comp φ.toMonoidHom = φ.toMonoidHom.comp t.toMonoidHom := by
      refine MonoidHom.ext fun s => ?_
      exact hαapp s
    rw [this, ← Subgroup.map_map, hSt]
  have hS'g : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map (MulAut.conj g).toMonoidHom = S' := by
    rw [hS'coe, Subgroup.map_map]
    have : (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom = φ.toMonoidHom.comp z.toMonoidHom := by
      refine MonoidHom.ext fun s => ?_
      change g * φ s * g⁻¹ = φ (z s)
      rw [← hy, MulAut.conj_apply, hg, map_mul, map_mul, map_inv]
    rw [this, ← Subgroup.map_map, hSz]
  set A' : Subgroup ↥(adjointGroup Tag.D4 K) := A.map φ.toMonoidHom with hA'
  have hAS' : A' ≤ (S' : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    rw [hS'coe]; exact Subgroup.map_mono hAS
  have hfix' : ∀ a ∈ A', α a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change α (φ a) = φ a
    rw [hαapp, hAt a ha]
  have hfixg' : ∀ a ∈ A', g * a * g⁻¹ = a := by
    rintro _ ⟨a, ha, rfl⟩
    change g * φ a * g⁻¹ = φ a
    rw [hg, ← map_inv, ← map_mul, ← map_mul, ← MulAut.conj_apply, hy, hAz a ha]
  have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective φ.injective
  have hb := chev_card_le_inner α hα3 hαnot g hg2 hg1 hαg S' hS'α hS'g A' hAS' hfix' hfixg'
  rw [hcard] at hb
  calc Nat.card A ≤ Nat.card K ^ 2 := hb
    _ = 3 ^ (2 * n) := by rw [hK, ← pow_mul]; ring_nf

end CFSG.LocalAnalysis.GLTheoremA
