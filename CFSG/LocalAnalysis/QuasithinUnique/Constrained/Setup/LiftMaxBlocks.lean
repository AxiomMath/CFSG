module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSylowMax

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.ABGLocalTools

section Blocks

variable {H : Type*} [Group H]

theorem mem_normalizer_inf_of_coord {D L U : Subgroup H} {b : H} (hDL : D ⊓ L = U)
    (hbL : b ∈ Subgroup.normalizer (L : Set H))
    (hcoord : ∀ u ∈ L, ∃ x ∈ Subgroup.normalizer (D : Set H), x * u * x⁻¹ = b * u * b⁻¹) :
    b ∈ Subgroup.normalizer (U : Set H) := by
  have hUL : U ≤ L := hDL ▸ inf_le_right
  have hUD : U ≤ D := hDL ▸ inf_le_left
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    obtain ⟨x, hx, hxu⟩ := hcoord u (hUL hu)
    have h1 : x * u * x⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hx u).1 (hUD hu)
    have h2 : b * u * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hbL u).1 (hUL hu)
    rw [hxu] at h1
    rw [← hDL]
    exact ⟨h1, h2⟩
  · intro hu
    have huL : u ∈ L := (Subgroup.mem_normalizer_iff.1 hbL u).2 (hUL hu)
    obtain ⟨x, hx, hxu⟩ := hcoord u huL
    have h1 : x * u * x⁻¹ ∈ D := by
      rw [hxu]
      exact hUD hu
    have h2 : u ∈ D := (Subgroup.mem_normalizer_iff.1 hx u).2 h1
    rw [← hDL]
    exact ⟨h2, huL⟩

theorem normalizer_inf_iSup_blocks {r : ℕ} (B L U : Fin r → Subgroup H) (D : Subgroup H)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, x * y = y * x)
    (hLB : ∀ i, L i ≤ B i) (hUL : ∀ i, U i ≤ L i)
    (hBL : ∀ i, B i ≤ Subgroup.normalizer (L i : Set H))
    (hD : D = ⨆ i, U i) (hDL : ∀ i, D ⊓ L i = U i) :
    (∀ i, Subgroup.normalizer (D : Set H) ⊓ B i = Subgroup.normalizer (U i : Set H) ⊓ B i) ∧
      Subgroup.normalizer (D : Set H) ⊓ (⨆ i, B i) =
        ⨆ i, Subgroup.normalizer (U i : Set H) ⊓ B i := by
  classical
  have hcommP : Pairwise fun i j => ∀ x y : H, x ∈ B i → y ∈ B j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  have hnormD : ∀ i, ∀ x ∈ B i, x ∈ Subgroup.normalizer (U i : Set H) →
      x ∈ Subgroup.normalizer (D : Set H) := by
    intro i x hxB hxU
    rw [hD]
    refine mem_normalizer_iSup _ fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact hxU
    · have : x ∈ Subgroup.centralizer (U j : Set H) :=
        Subgroup.mem_centralizer_iff.2 fun u hu =>
          (hcomm i j (Ne.symm hji) x hxB u (hLB j (hUL j hu))).symm
      exact Subgroup.centralizer_le_normalizer _ this
  have hblock : ∀ i, Subgroup.normalizer (D : Set H) ⊓ B i =
      Subgroup.normalizer (U i : Set H) ⊓ B i := by
    intro i
    apply le_antisymm
    · rintro x ⟨hxD, hxB⟩
      exact ⟨mem_normalizer_inf_of_coord (hDL i) (hBL i hxB) fun u _ => ⟨x, hxD, rfl⟩, hxB⟩
    · rintro x ⟨hxU, hxB⟩
      exact ⟨hnormD i x hxB hxU, hxB⟩
  refine ⟨hblock, le_antisymm ?_ ?_⟩
  · rintro x ⟨hxD, hxJ⟩
    have hxr : x ∈ (Subgroup.noncommPiCoprod hcommP).range := by
      rw [Subgroup.noncommPiCoprod_range]
      exact hxJ
    obtain ⟨b, rfl⟩ := hxr
    rw [Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    refine le_iSup (fun j => Subgroup.normalizer (U j : Set H) ⊓ B j) i ⟨?_, (b i).2⟩
    exact mem_normalizer_inf_of_coord (hDL i) (hBL i (b i).2) fun u hu =>
      ⟨_, hxD, conj_noncommPiCoprod_eq B hcommP b i (hLB i hu)⟩
  · refine iSup_le fun i x hx => ⟨?_, le_iSup B i hx.2⟩
    exact hnormD i x hx.2 hx.1

end Blocks

end CFSG.QuasithinUnique.Setup.Lift
