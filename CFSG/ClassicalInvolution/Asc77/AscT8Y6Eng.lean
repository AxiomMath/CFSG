module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {W : Subgroup G} {z t : G}

theorem exists_good_pair_of_nonabelianE (hcl : ConjInvariant Ω)
    (huniq : ∀ {M : Subgroup G}, M ∈ Ω → ∃ u : G, IsUniqueInvolution M u)
    (huW : ∀ {M R₀ : Subgroup G} {x : G}, M ∈ Ω → R₀ ∈ DSet Ω W → IsSylow2In R₀ M →
      IsUniqueInvolution M x → x ∈ M ⊓ W)
    (hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hrepeq : ∀ ρ σ : Rep Ω W, repElt ρ = repElt σ ↔ ρ.K = σ.K)
    (hrepcomm : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K →
      (repElt ρ * repElt σ = repElt σ * repElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K))
    (hrepstar : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → σ.K ∈ omegaStarNbr Ω ρ.K)
    (hmdc : ∀ ρ : Rep Ω W, ρ.K ∈ dComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) (haE : ∀ J ∈ Ω, AEmpty Ω J)
    (hzW : z ∈ W) (htW : t ∈ W)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ (ρ σ : Rep Ω W) (u v : G), repElt ρ * repElt σ ≠ repElt σ * repElt ρ ∧
      IsUniqueInvolution ρ.K u ∧ IsUniqueInvolution σ.K v ∧ u * v = v * u ∧ u ≠ v ∧
      u ∈ cenZ (z * t) ∧ v ∈ cenZ (z * t) ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({v} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({u * v} : Set G) ≤ sigmaNorm Ω K := by
  obtain ⟨d, hd, e, he, hde⟩ := exists_noncomm_of_not_abelian hab
  obtain ⟨ρ, rfl⟩ := exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := exists_rep_of_mem_muDelta he
  have hKne : ρ.K ≠ σ.K := fun h => hde (by rw [(hrepeq ρ σ).mpr h])
  have hnonbr : σ.K ∉ omegaNbr Ω ρ.K := fun h => hde ((hrepcomm ρ σ hKne).mpr h)
  have hstar : σ.K ∈ omegaStarNbr Ω ρ.K := hrepstar ρ σ hKne
  obtain ⟨zρ, hzρ⟩ := huniq ρ.hK
  obtain ⟨zσ, hzσ⟩ := huniq σ.hK
  have hzρW : zρ ∈ W := (huW ρ.hK ρ.hR ρ.hRK hzρ).2
  have hzσW : zσ ∈ W := (huW σ.hK σ.hR σ.hRK hzσ).2
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcomm : zρ * zσ = zσ * zρ := hcommW _ hzρW _ hzσW
  have hzne : zσ ≠ zρ := by
    intro h
    have hj : IsUniqueInvolution σ.K zρ := by rw [← h]; exact hzσ
    exact hKne (hnt _ ρ.hK _ ⟨σ.hK, zρ, hzρ, hj⟩).symm
  have hmρ := hmdc ρ
  have hmσ := hmdc σ
  have hKρ : ρ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hcl hK hmρ)
  have hKσ : σ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hcl hK hmσ)
  have hg1 : Subgroup.centralizer ({zρ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hcl ρ.hK (hnt _ ρ.hK) hzρ).trans
      (normalizer_le_sigmaNorm_of_mem hcl hK hmρ)
  have hg2 : Subgroup.centralizer ({zσ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hcl σ.hK (hnt _ σ.hK) hzσ).trans
      (normalizer_le_sigmaNorm_of_mem hcl hK hmσ)
  obtain ⟨c, hcmem, hcz⟩ := exists_conj_mul_of_aEmpty (haE ρ.K ρ.hK) hstar hnonbr hzρ
    hzσ hcomm hzne
  have hcN : c ∈ sigmaNorm Ω K := (sup_le hKρ hKσ) hcmem
  have hg3 : Subgroup.centralizer ({zρ * zσ} : Set G) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hcN ?_
    have : c⁻¹ * (zρ * zσ) * c = zρ := by rw [← hcz]; group
    rw [this]
    exact hg1
  exact ⟨ρ, σ, zρ, zσ, hde, hzρ, hzσ, hcomm, Ne.symm hzne,
    mem_cenZ_iff.mpr (hcommW _ hzρW _ haW), mem_cenZ_iff.mpr (hcommW _ hzσW _ haW),
    hg1, hg2, hg3⟩

end T8

end CFSG.ClassicalInvolution.Asc77
