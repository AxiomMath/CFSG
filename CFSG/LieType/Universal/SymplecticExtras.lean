module

public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LieType.Steinberg.Extras
import CFSG.LieType.Universal.SymplecticExtras.Commutator
import CFSG.LieType.Universal.SymplecticExtras.RankOne
import CFSG.LieType.Universal.SymplecticExtras.Torus

public section

namespace CFSG.LieType.Universal.Symplectic

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def rootDatum : UniversalRootDatum (StatedSp n F) where
  rank := n
  cartan := cartanC n
  isFiniteType := isFiniteType_cartanC n
  divisible := ∅
  rootGroup := rootGroup n F

private theorem rootGroup_ne_bot {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    rootGroup n F γ ≠ ⊥ := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hγ
  intro hbot
  have hmem := SpExtras.elt_mem_rootGroup (F := F) hr 1
  rw [hbot, Subgroup.mem_bot, ← SpExtras.elt_zero r] at hmem
  exact one_ne_zero (SpExtras.elt_injective r hmem)

private theorem two_smul_not_mem {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    2 • γ ∉ roots (isFiniteType_cartanC n) ∅ := by
  intro h2
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hγ
  obtain ⟨r', hr'⟩ := SpExtras.exists_stdVec_of_mem_roots h2
  rw [SpExtras.toStd_nsmul', ← hr] at hr'
  have h1 := SpExtras.dot_stdVec r
  have h2' := SpExtras.dot_stdVec r'
  rw [hr', smul_dotProduct, dotProduct_smul, smul_smul, nsmul_eq_mul] at h2'
  push_cast at h2'
  omega

theorem steinbergExtras : SteinbergExtras (rootDatum n F) (weylRep n F) (torus n F) where
  ne_bot _ hγ := rootGroup_ne_bot n F hγ
  two_smul_le _ hγ h2 := absurd h2 (two_smul_not_mem n hγ)
  commutator_mem _ hγ _ hδ hind _ hx _ hy := SpExtras.commutator_mem hγ hδ hind hx hy
  prodInjective_pos L hL hmem hsort := by
    have hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanC n) ∅ := fun γ hγ => ((hmem γ).1 hγ).1
    refine SpExtras.prodInjective_of (n := n) (F := F) 1 L hL hroots (fun γ hγ => ?_) ?_
    · have h : 0 < ht (ι := Fin n) γ := ((hmem γ).1 hγ).2.1
      omega
    · refine hsort.imp fun {γ δ} h => ?_
      have h' : ht (ι := Fin n) γ ≤ ht (ι := Fin n) δ := h
      omega
  prodInjective_neg L hL hmem hsort := by
    have hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanC n) ∅ := fun γ hγ => ((hmem γ).1 hγ).1
    refine SpExtras.prodInjective_of (n := n) (F := F) (-1) L hL hroots (fun γ hγ => ?_) ?_
    · have h : ht (ι := Fin n) γ < 0 := ((hmem γ).1 hγ).2.1
      omega
    · refine hsort.imp fun {γ δ} h => ?_
      have h' : ht (ι := Fin n) δ ≤ ht (ι := Fin n) γ := h
      omega
  posPart_inf_negPart := SpExtras.posPart_inf_negPart
  rankOne_bruhat := SpExtras.rankOne_bruhat
  eq_one_of_mem_normalizer := SpExtras.eq_one_of_mem_normalizer
  torus_commute := SpExtras.torus_commute
  torus_iSupIndep := SpExtras.torus_iSupIndep
  torus_inf_posPart := SpExtras.torus_inf_posPart

end CFSG.LieType.Universal.Symplectic
