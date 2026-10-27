module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QZ

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

theorem famF_twistedG2 :
    FamF .twistedG2 := by
  refine famF_of_fAt fun X _ _ _ n p f _ _ hX _ z hz => ?_
  have hR : ReeTitsModel X .twistedG2 p f := by
    rcases hX with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by simp [classicalTags])
    · exact absurd ht (by simp [chevalleyExceptionalTags])
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier X p f hR
  obtain ⟨-, a', hfa', F, _, _, hF, hw⟩ := hR
  have ha' : a' = a := by omega
  subst ha'
  have : CharP F ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hF
  obtain ⟨E⟩ := hiso a' F hfa hF hw
  have hF' : Nat.card F = 3 ^ (2 * a' + 1) := by rw [hF, hfa]
  have h27 : 27 ≤ Nat.card F := by
    rw [hF']
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF2 : Nat.card F ≠ 2 := by omega
  have hF3 : Nat.card F ≠ 3 := by omega
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set Γ := ReeTag.G2.reeGamma F a' with hΓ
  set t := smallReeH a' F (-1) with ht
  have hz2 : orderOf ((E z : Γ) : ModGL ReeTag.G2.tag F) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hz
  obtain ⟨g, hgΓ, hgz⟩ :=
    (small_Ree_prime_field_involution_fusion a' F hF' w₀ hw₀).2.2.2.2.2 _ (E z).2 hz2
  obtain ⟨ψ, hψC, -, -, -, hψ1, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a' F hF' w₀ hw₀
  set φ : X ≃* Γ := E.trans (MulAut.conj (⟨g, hgΓ⟩ : Γ)) with hφ
  set θ : X →* ModGL ReeTag.G2.tag F := Γ.subtype.comp φ.toMonoidHom with hθdef
  have hθ : Function.Injective θ := Γ.subtype_injective.comp φ.injective
  have hθz : θ z = t := hgz
  have hθΓ : ∀ x, θ x ∈ Γ := fun x => (φ x).2
  have hLθ : ψ.range ≤ θ.range := by
    rintro _ ⟨u, rfl⟩
    refine ⟨φ.symm ⟨ψ u, (mem_inf.1 (hψC u)).1⟩, ?_⟩
    simp [θ]
  have hcomm : ∀ ℓ ∈ ψ.range, ℓ * t = t * ℓ := fun ℓ hℓ =>
    mem_centralizer_iff.1 (hcent (mem_zpowers t)) ℓ hℓ
  set N := ψ.range.comap θ with hNdef
  have hNC : N ≤ centralizer ({z} : Set X) := by
    intro x hx
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 (mem_comap.1 hx)
    have hc := (mem_inf.1 (hψC u)).2
    rw [hu, mem_centralizer_singleton_iff] at hc
    rw [mem_centralizer_singleton_iff]
    apply hθ
    rw [map_mul, map_mul, hθz]
    exact hc
  have hCN : centralizer ({z} : Set X) ≤ zpowers z ⊔ N := by
    intro x hx
    have hxC : θ x ∈ zpowers t ⊔ ψ.range := by
      rw [hsup]
      refine mem_inf.2 ⟨hθΓ x, mem_centralizer_singleton_iff.2 ?_⟩
      change θ x * t = t * θ x
      rw [← hθz, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
    obtain ⟨k, ℓ, hℓ, hxe⟩ := exists_zpow_mul_of_mem_sup hcomm hxC
    have hℓN : z ^ (-k) * x ∈ N := by
      show θ (z ^ (-k) * x) ∈ ψ.range
      rw [map_mul, map_zpow, hθz, hxe, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
        one_mul]
      exact hℓ
    have hx' : x = z ^ k * (z ^ (-k) * x) := by group
    rw [hx']
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers z) k)) (mem_sup_right hℓN)
  let eNL : N ≃* ψ.range :=
    (N.equivMapOfInjective θ hθ).trans (MulEquiv.subgroupCongr (map_comap_eq_self hLθ))
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 F le_rfl (Or.inr hF2) (Or.inr hF3)
  let eN := eNL.trans e.symm
  have : IsSimpleGroup N := eN.isSimpleGroup
  have hnab : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F hF2 hF3
    exact ⟨eN.symm x, eN.symm y, fun h => hxy (by simpa using congrArg eN h)⟩
  have hW : (WSL : SL2 F) * WSL = -1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hW1 : ψ WSL ≠ 1 := by
    intro h1
    rcases (hψ1 WSL).1 h1 with h | h <;>
    · have h01 := congrArg (fun u : SL2 F => (u : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [coe_WSL, Matrix.SpecialLinearGroup.coe_neg] at h01
  have hW2 : ψ WSL ^ 2 = 1 := by
    rw [sq, ← map_mul, hW]
    exact (hψ1 (-1)).2 (Or.inr rfl)
  have hev : Even (Nat.card N) := by
    rw [Nat.card_congr eNL.toEquiv]
    set w : ψ.range := ⟨ψ WSL, MonoidHom.mem_range.2 ⟨WSL, rfl⟩⟩ with hw
    have ho : orderOf w = 2 := by
      rw [hw, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hW2 hW1
    have h2 := orderOf_dvd_natCard w
    rw [ho] at h2
    exact even_iff_two_dvd.2 h2
  exact fAt_of_sup_simple hz hNC hCN hnab hev

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
