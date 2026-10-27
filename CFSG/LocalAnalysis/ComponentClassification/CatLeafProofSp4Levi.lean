module

public import CFSG.ClassicalInvolution.WeakCT.SpModel

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Universal.Symplectic (rootDatum)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

theorem isQuasisimple_statedSp_two {F : Type} [Field F] (h3 : 3 ≤ Nat.card F) :
    IsQuasisimple (StatedSp 2 F) := by
  rcases h3.eq_or_lt with h | h
  · exact Symplectic.isQuasisimple 2 F (by norm_num) (Or.inr (Or.inl ⟨h.symm, le_rfl⟩))
  · exact Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr h))

theorem weylElement_sq_mem_center_sp (F : Type) [Field F] :
    Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2 ∈
      Subgroup.center (StatedSp 2 F) := by
  obtain ⟨O, hE'⟩ := exists_sp_chevalleyExtras F
  have hle : (⨆ γ ∈ (rootDatum 2 F).roots, (rootDatum 2 F).rootGroup γ) ≤
      Subgroup.centralizer {Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2} := by
    refine iSup₂_le fun γ hγ g hg => ?_
    obtain ⟨c, rfl⟩ := ((hE'.param γ hγ).1 g).1 hg
    have heven : Even (∑ j, (rootDatum 2 F).cartan spS j * γ j) := by
      have h : ∑ j, (rootDatum 2 F).cartan spS j * γ j =
          ∑ j, (rootDatum 2 F).cartan spS j * (pair (spS (F := F)) spL (coords γ)) j := by
        rw [sp_pair_coords γ]
      rw [h, pairing_pair, (rootDatum 2 F).isFiniteType.apply_self, sp_cartan_01]
      exact ⟨(coords γ).1 - (coords γ).2, by ring⟩
    have hc := weylElement_sq_commute hE' (k := spS (F := F)) hγ heven c
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hc.eq
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer
      {Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2} := by
    refine hle ?_
    rw [show (⨆ γ ∈ (rootDatum 2 F).roots, (rootDatum 2 F).rootGroup γ) = ⊤ from
      (Symplectic.isCTGroupDatum 2 F).iSup_eq_top]
    trivial
  rw [Subgroup.mem_centralizer_iff] at hg
  exact (hg _ rfl).symm

section Levi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

theorem sp4Hom_injective_of_isQuasisimple (hq : IsQuasisimple (StatedSp 2 F)) (h2 : (2 : F) ≠ 0)
    (hE : Steinberg.ChevalleyExtras D F x C O) {φ : StatedSp 2 F →* K} {e : ℤ × ℤ → F}
    (he1 : e (1, 0) = 1) (he2 : e (-1, 0) = 1)
    (hφ : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      φ (Steinberg.Sp.x 2 F γ c) = x (pair s l (coords γ)) (e (coords γ) * c)) :
    Function.Injective φ := by
  have hC0 : φ (Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2) ≠ 1 := by
    rw [map_pow, hom_weylElement he1 he2 hφ]
    obtain ⟨ψ, hψ, -, -, hsq⟩ := weylElement_one_sq hE s
    rw [hsq]
    intro h
    have h1 : wS (1 : Fˣ) * wS (1 : Fˣ) = (1 : SL(2, F)) := hψ (by rw [h, map_one])
    have h3 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, wS, Steinberg.coe_sl2Upper,
      Steinberg.coe_sl2Lower, Matrix.mul_fin_two] at h3
    apply h2
    simp at h3
    linear_combination -h3
  have hz1 : Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 ^ 2 ≠ 1 := fun h =>
    hC0 (by rw [h, map_one])
  have hker : φ.ker ≤ Subgroup.center (StatedSp 2 F) :=
    CurtisTits.ker_le_center_of_isQuasisimple hq ⟨_, hC0⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  exact hC0 (by rw [← center_sp_eq (hker hg) (weylElement_sq_mem_center_sp F) hg1 hz1]; exact hg)

theorem exists_b2Levi_of_isQuasisimple [Finite F] (hq : IsQuasisimple (StatedSp 2 F))
    (h2 : (2 : F) ≠ 0) (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D s l, ∀ g ∈ D.rootGroup γ, g ∈ φ.range) ∧
      (∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot s) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot s) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot l) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot l) c) := by
  obtain ⟨φ, e, hesq, he1, he2, he3, he4, hφ⟩ := exists_b2Hom hE hdiv hcsl hcls
  have hs : ∃ ρ : SL(2, F) →* K, ∀ c, ρ (tv 0 1 c) = x (sroot s) c ∧
      ρ (tv 1 0 c) = x (-sroot s) c := by
    obtain ⟨ρ, -, hu, hl⟩ := hE.rankOne s
    exact ⟨ρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  have hl : ∃ ρ : SL(2, F) →* K, ∀ c, ρ (tv 0 1 c) = x (sroot l) c ∧
      ρ (tv 1 0 c) = x (-sroot l) c := by
    obtain ⟨ρ, -, hu, hl⟩ := hE.rankOne l
    exact ⟨ρ, fun c => ⟨by rw [tv01_eq_sl2Upper, hu], by rw [tv10_eq_sl2Lower, hl]⟩⟩
  obtain ⟨ρs, hρs⟩ := hs
  obtain ⟨ρl, hρl⟩ := hl
  obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ hρs hρl
  refine ⟨φ, sp4Hom_injective_of_isQuasisimple hq h2 hE he1 he2 hφ, fun γ hγ g hg => ?_,
    fun c => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := pairRoots_subset_zB2 hdiv hcsl hcls hγ
    obtain ⟨c, rfl⟩ := ((hE.param _ (pair_mem_roots_zB2 hcsl hcls z hz)).1 g).1 hg
    refine ⟨Steinberg.Sp.x 2 F (pair (spS (F := F)) spL z) (e z * c), ?_⟩
    rw [hφ _ (pair_mem_sp_roots hz), sp_coords_pair, ← mul_assoc, hesq z hz, one_mul]
  · have h1 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb0
    have h2 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb0
    have h3 := congrArg (fun f : SL(2, F) →* K => f (tv 0 1 c)) hb1
    have h4 := congrArg (fun f : SL(2, F) →* K => f (tv 1 0 c)) hb1
    simp only [MonoidHom.comp_apply] at h1 h2 h3 h4
    exact ⟨h1.trans (hρs c).1, h2.trans (hρs c).2, h3.trans (hρl c).1, h4.trans (hρl c).2⟩

theorem exists_sp4Levi_of_isQuasisimple [Finite F] (hq : IsQuasisimple (StatedSp 2 F))
    (h2 : (2 : F) ≠ 0) (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {i j : Fin D.rank} (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot i) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot i) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot j) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot j) c := by
  obtain ⟨φ, hφ, hle, hv⟩ := exists_b2Levi_of_isQuasisimple hq h2 hE hdiv hcij hcji
  exact ⟨φ, hφ, fun γ hγ g hg => hle γ hγ g hg, hv⟩

end Levi

end CFSG.ComponentClassification.CatLeafProof
