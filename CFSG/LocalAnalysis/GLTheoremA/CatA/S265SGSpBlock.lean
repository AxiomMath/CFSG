module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpSU2
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsSupp suppGroup mem_suppGroup coords
  mem_coords longBlock longBlock_injective isSupp_longBlock spEmbed spEmbed_injective
  spEmbed_longBlock isSupp_spEmbed pairMap pairMap_injective pairMap_zero pairMap_one
  range_pairMap commute_suppGroup_compl)
open CFSG.StandardType.WitSpNs (planeMat planeMat_apply planeMat_one planeMat_mul plane plane_inl
  plane_inr mat_longBlock_eq_planeMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem isSupp_planeMat {F : Type} [Field F] {n : ℕ} {S : Set (Fin n ⊕ Fin n)}
    {f : Fin n → Matrix (Fin 2) (Fin 2) F} (hf : ∀ a ∉ S, f (plane a) = 1) :
    IsSupp S (planeMat f) := by
  intro r t hrt
  rw [← planeMat_one, planeMat_apply, planeMat_apply]
  split_ifs with hp
  · rcases not_and_or.1 hrt with hr | ht
    · rw [← hp, hf r hr]
    · rw [hf t ht]
  · rfl

private theorem commute_conj_of {G : Type} [Group G] {A₀ X g : G}
    (h : Commute X (A₀⁻¹ * g * A₀)) : Commute (A₀ * X * A₀⁻¹) g := by
  show A₀ * X * A₀⁻¹ * g = g * (A₀ * X * A₀⁻¹)
  calc A₀ * X * A₀⁻¹ * g = A₀ * (X * (A₀⁻¹ * g * A₀)) * A₀⁻¹ := by group
    _ = A₀ * ((A₀⁻¹ * g * A₀) * X) * A₀⁻¹ := by rw [h.eq]
    _ = g * (A₀ * X * A₀⁻¹) := by group

theorem SG.exists_sl2_commute_sp {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}
    (hℓ : 3 ≤ ℓ) (E : Subgroup (StatedSp ℓ F)) (hEc : ∀ g ∈ E, ∀ g' ∈ E, Commute g g')
    (hE3 : ∀ g ∈ E, g ^ 3 = 1) (a : ↥E) :
    ∃ (ψ : SL(2, F) →* StatedSp ℓ F) (χ : ↥E →* Multiplicative (ZMod 3)),
      Function.Injective ψ ∧ a ∈ χ.ker ∧ ∀ g ∈ χ.ker, ∀ t, Commute (ψ t) (g : StatedSp ℓ F) := by
  obtain ⟨A₀, M, k, hdet, hM, hk⟩ := SG.exists_planeFrame_three (by omega) E hEc hE3
  by_cases h0 : ∃ i, k i a = 1
  ·
    obtain ⟨i, hi⟩ := h0
    refine ⟨(MulAut.conj A₀).toMonoidHom.comp (longBlock F ℓ i), k i,
      (MulAut.conj A₀).injective.comp (longBlock_injective i), hi, fun g hg t => ?_⟩
    show Commute (A₀ * longBlock F ℓ i t * A₀⁻¹) _
    refine commute_conj_of (commute_suppGroup_compl (mem_suppGroup.2 (isSupp_longBlock i t)) ?_)
    rw [mem_suppGroup, hk g]
    refine isSupp_planeMat fun b hb => ?_
    have hb' : b ∈ coords i := by by_contra hc; exact hb hc
    rcases mem_coords.1 hb' with rfl | rfl <;> simp [MonoidHom.mem_ker.1 hg]
  ·
    simp only [not_exists] at h0
    obtain ⟨i, j, hij, hkij⟩ : ∃ i j : Fin ℓ, i ≠ j ∧ k i a = k j a := by
      have key : ∀ x y z : ZMod 3, x ≠ 0 → y ≠ 0 → z ≠ 0 → x = y ∨ x = z ∨ y = z := by decide
      have hne : ∀ l, Multiplicative.toAdd (k l a) ≠ 0 := fun l h => h0 l (toAdd_eq_zero.1 h)
      rcases key _ _ _ (hne ⟨0, by omega⟩) (hne ⟨1, by omega⟩) (hne ⟨2, by omega⟩) with h | h | h
      · exact ⟨_, _, by simp [Fin.ext_iff], Multiplicative.toAdd.injective h⟩
      · exact ⟨_, _, by simp [Fin.ext_iff], Multiplicative.toAdd.injective h⟩
      · exact ⟨_, _, by simp [Fin.ext_iff], Multiplicative.toAdd.injective h⟩
    obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := SG.exists_sl2_sp_two hdet hM
    have hσ := pairMap_injective hij
    refine ⟨(MulAut.conj A₀).toMonoidHom.comp ((spEmbed (pairMap i j) hσ).comp ψ₀), k i / k j,
      (MulAut.conj A₀).injective.comp ((spEmbed_injective hσ).comp hψ₀),
      by rw [MonoidHom.mem_ker, MonoidHom.div_apply, hkij, div_self'], fun g hg t => ?_⟩
    have hg' : k i g = k j g :=
      div_eq_one.1 (by rw [← MonoidHom.div_apply]; exact MonoidHom.mem_ker.1 hg)
    show Commute (A₀ * spEmbed (pairMap i j) hσ (ψ₀ t) * A₀⁻¹) _
    refine commute_conj_of ?_
    obtain ⟨e, he⟩ : ∃ e, e = (Multiplicative.toAdd (k i g)).val := ⟨_, rfl⟩
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : SL(2, F), (N₀ : Matrix (Fin 2) (Fin 2) F) = M ^ e :=
      ⟨⟨M ^ e, by rw [Matrix.det_pow, hdet, one_pow]⟩, rfl⟩
    have hZ : mat 2 F (longBlock F 2 0 N₀ * longBlock F 2 1 N₀) = planeMat fun _ => M ^ e := by
      rw [map_mul, mat_longBlock_eq_planeMat, mat_longBlock_eq_planeMat, planeMat_mul]
      congr 1
      funext l
      fin_cases l <;> simp [hN₀, Function.update_apply]
    have h1 := hψ₀c (M ^ e) ((Commute.refl M).pow_left e) t
    rw [← hZ] at h1
    have hc1 := (Commute.of_map mat_injective h1).map (spEmbed (pairMap i j) hσ)
    rw [map_mul, spEmbed_longBlock, spEmbed_longBlock, pairMap_zero, pairMap_one] at hc1
    have hN : ((N₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * M ^ e = 1 := by
      rw [← hN₀, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hR : (longBlock F ℓ i N₀ * longBlock F ℓ j N₀)⁻¹ * (A₀⁻¹ * g * A₀) ∈
        suppGroup (coords i ∪ coords j)ᶜ := by
      rw [mem_suppGroup, mul_inv_rev, ← map_inv, ← map_inv, map_mul, hk g, map_mul,
        mat_longBlock_eq_planeMat, mat_longBlock_eq_planeMat, planeMat_mul, planeMat_mul]
      refine isSupp_planeMat fun b hb => ?_
      have hb' : b ∈ coords i ∪ coords j := by by_contra hc; exact hb hc
      rcases hb' with hb' | hb' <;> rcases mem_coords.1 hb' with rfl | rfl <;>
        simp only [plane_inl, plane_inr, Function.update_of_ne hij, Function.update_of_ne hij.symm,
          Function.update_self, one_mul, mul_one, ← hg', ← he, hN]
    have hc2 := commute_suppGroup_compl (x := spEmbed (pairMap i j) hσ (ψ₀ t))
      (mem_suppGroup.2 (by rw [← range_pairMap]; exact isSupp_spEmbed hσ _)) hR
    simpa only [mul_inv_cancel_left] using hc1.mul_right hc2

end CFSG.LocalAnalysis.GLTheoremA.S265

end
