module

public import CFSG.GH74.KGroups.L3EpsNoNormalOne

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem transport_setup (ψ : X ≃* Y) {A M : Subgroup (MulAut X)} {P : Subgroup X}
    (hA : IsPGroup 2 A) (hAP : A ⊓ inner X = P.map (MulAut.conj : X →* MulAut X))
    (hMA : M ≤ A) (hMn : ∀ a ∈ A, ∀ n ∈ M, a * n * a⁻¹ ∈ M) :
    IsPGroup 2 (A.map (MulAut.congr ψ).toMonoidHom) ∧
      A.map (MulAut.congr ψ).toMonoidHom ⊓ inner Y =
        (P.map ψ.toMonoidHom).map (MulAut.conj : Y →* MulAut Y) ∧
      M.map (MulAut.congr ψ).toMonoidHom ≤ A.map (MulAut.congr ψ).toMonoidHom ∧
      (∀ a ∈ A.map (MulAut.congr ψ).toMonoidHom, ∀ n ∈ M.map (MulAut.congr ψ).toMonoidHom,
        a * n * a⁻¹ ∈ M.map (MulAut.congr ψ).toMonoidHom) ∧
      Nonempty (M.map (MulAut.congr ψ).toMonoidHom ≃* M) := by
  have hinj : Function.Injective (MulAut.congr ψ).toMonoidHom := (MulAut.congr ψ).injective
  refine ⟨hA.map _, ?_, Subgroup.map_mono hMA, ?_, ⟨((MulAut.congr ψ).subgroupMap M).symm⟩⟩
  · rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ,
      ← Subgroup.map_inf A (inner X) _ hinj, hAP, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => CFSG.ComponentClassification.OuterAutomorphisms.congr_conj ψ x
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨a * m * a⁻¹, hMn a ha m hm, ?_⟩
    simp only [map_mul, map_inv]

end Transport

section Main

variable {X X' : Type} [Group X] [Group X'] {p f : ℕ}

theorem l3eps_no_normal_minus (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hX : StatedClassicalModel X .PSL 3 p f) (hX' : StatedClassicalModel X' .PSU 3 p f)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hPmax : ∀ T : Subgroup X, IsPGroup 2 T → P ≤ T → T ≤ P)
    (A : Subgroup (MulAut X)) (hA : IsPGroup 2 A)
    (hAP : A ⊓ inner X = P.map (MulAut.conj : X →* MulAut X))
    (M : Subgroup (MulAut X)) (hMA : M ≤ A) (hMn : ∀ a ∈ A, ∀ n ∈ M, a * n * a⁻¹ ∈ M)
    {R : Subgroup X'} (hR : IsPGroup 2 R) (hRmax : ∀ T : Subgroup X', IsPGroup 2 T → R ≤ T → T ≤ R)
    (e : M ≃* R) : False := by
  have hp : p.Prime := hX.1.1
  have hq2 : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases hmod with h1 | h3
  ·
    obtain ⟨F, _, _, hF, ⟨ε⟩⟩ := exists_projectiveSL_equiv hX
    have hfin : Finite X := Finite.of_equiv _ ε.symm.toEquiv
    have hF4 : Nat.card F % 4 = 1 := by rw [hF]; exact h1
    set r := ordProj[2] (Nat.card F - 1) with hr
    have hc : LinCtx F r := ⟨hF4, rfl⟩
    obtain ⟨hP2, hPmax2⟩ := Pexp_sylow (F := F) hc.hF2 hF4 rfl
    have hP' : IsPGroup 2 (P.map ε.toMonoidHom) := hP.map ε.toMonoidHom
    obtain ⟨x, hx⟩ := exists_conj_le_of_isPGroup hP2 hPmax2 hP'
    let ψ : X ≃* projectiveSL 3 F := ε.trans (MulAut.conj x⁻¹)
    have hψP : P.map ψ.toMonoidHom = Pexp (F := F) r := by
      have hle : P.map ψ.toMonoidHom ≤ Pexp (F := F) r := by
        rintro _ ⟨y, hy, rfl⟩
        have := hx (ε y) ⟨y, hy, rfl⟩
        simpa [ψ, MulAut.conj_apply] using this
      obtain ⟨hψ2, hψmax⟩ := isMaxPGroup_map ψ hP hPmax
      exact le_antisymm hle (hψmax _ hP2 hle)
    obtain ⟨hA₁, hAP₁, hMA₁, hMn₁, ⟨ι⟩⟩ := transport_setup ψ hA hAP hMA hMn
    rw [hψP] at hAP₁
    have hpres := uni_sylow_one hp2 h1 hX' hR hRmax
    have hq1 : 2 ≤ p ^ f := by omega
    obtain ⟨hm3, hk1, hk2⟩ := sd_numeric h1 hq1
    refine no_normal_minus_one hc _ hA₁ hAP₁ _ hMA₁ hMn₁ hm3 hk1 hk2
      (hpres.congr (e.symm.trans ι.symm)) ?_
    rw [hr, hF]
    simp
  · exact no_normal_minus_three hp2 h5 h3 hX hX' hP hPmax A hA hAP M hMA hR hRmax e

end Main

end CFSG.GH74.KGroups.L3Eps
