module

public import CFSG.CGT.PushingUpLit.BHS6.AltCoverKernel
public import CFSG.CGT.PushingUpLit.BHS6.SymLocalGrp
public import CFSG.CGT.PushingUpLit.BHS7.FifteenComp

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}

@[expose] def Wset (G T : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin 5))
    (P : Subgroup (Equiv.Perm (Fin 5))) : Set (Subgroup Γ) :=
  {A | IsMaxElemAbelian T A ∧ imgG G φ A = P}

omit [Finite Γ] in
theorem imgG_conjSub {g : Γ} (hgG : g ∈ G) (A : Subgroup Γ) :
    imgG G φ (B6.conjSub g A) = B6.conjSub (φ ⟨g, hgG⟩) (imgG G φ A) := by
  ext σ
  rw [B6.mem_conjSub]
  constructor
  · intro hσ
    obtain ⟨y, hyG, hyA, rfl⟩ := mem_imgG.1 hσ
    rw [B6.mem_conjSub] at hyA
    refine mem_imgG.2 ⟨g⁻¹ * y * g, G.mul_mem (G.mul_mem (G.inv_mem hgG) hyG) hgG, hyA, ?_⟩
    show φ ((⟨g, hgG⟩ : ↥G)⁻¹ * ⟨y, hyG⟩ * ⟨g, hgG⟩) = _
    rw [map_mul, map_mul, map_inv]
  · intro hσ
    obtain ⟨a, haG, haA, ha⟩ := mem_imgG.1 hσ
    have hgaG : g * a * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hgG haG) (G.inv_mem hgG)
    refine mem_imgG.2 ⟨g * a * g⁻¹, hgaG, ?_, ?_⟩
    · rw [B6.mem_conjSub]
      have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rw [this]
      exact haA
    · have h1 : φ ⟨g * a * g⁻¹, hgaG⟩ = φ ⟨g, hgG⟩ * φ ⟨a, haG⟩ * (φ ⟨g, hgG⟩)⁻¹ := by
        show φ ((⟨g, hgG⟩ : ↥G) * ⟨a, haG⟩ * (⟨g, hgG⟩ : ↥G)⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [h1, ha]
      group

omit [Finite Γ] in
theorem isMax_conjSub {g : Γ} (hg : g ∈ T) {A : Subgroup Γ} (hA : IsMaxElemAbelian T A) :
    IsMaxElemAbelian T (B6.conjSub g A) := by
  have := B6.isMaxElemAbelian_conjSub hA g
  rwa [B6.conjSub_eq_self (Subgroup.le_normalizer hg)] at this

theorem ncard_Wset_le {g : Γ} (hgT : g ∈ T) (hgG : g ∈ G)
    {P Q : Subgroup (Equiv.Perm (Fin 5))} (hPQ : B6.conjSub (φ ⟨g, hgG⟩) P = Q) :
    (Wset G T φ P).ncard ≤ (Wset G T φ Q).ncard := by
  refine Set.ncard_le_ncard_of_injOn (B6.conjSub g) (fun A hA => ?_)
    (fun A₁ _ A₂ _ h => (B6.conjSub g).injective h) (Set.toFinite _)
  exact ⟨isMax_conjSub hgT hA.1, by rw [imgG_conjSub hgG, hA.2, hPQ]⟩

theorem ncard_Wset_eq {g : Γ} (hgT : g ∈ T) (hgG : g ∈ G)
    {P Q : Subgroup (Equiv.Perm (Fin 5))} (hPQ : B6.conjSub (φ ⟨g, hgG⟩) P = Q) :
    (Wset G T φ P).ncard = (Wset G T φ Q).ncard := by
  refine le_antisymm (ncard_Wset_le hgT hgG hPQ) ?_
  have hgG' : g⁻¹ ∈ G := G.inv_mem hgG
  refine ncard_Wset_le (T.inv_mem hgT) hgG' ?_
  have : φ ⟨g⁻¹, hgG'⟩ = (φ ⟨g, hgG⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [this, ← hPQ, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]

end CFSG.CGT.PushingUpLit.SYMB
