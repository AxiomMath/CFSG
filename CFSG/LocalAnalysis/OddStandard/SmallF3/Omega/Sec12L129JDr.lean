module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G}

theorem sec12D_struct (hbd : Sec10BData t L S) :
    ∃ (ρ : ↥(secM t S L ⊓ L) →* ↥(alternatingGroup (Fin 5))) (φ : (Fin 5 → ZMod 2) → G),
      Function.Surjective ρ ∧ ρ.ker = (secB S L).subgroupOf (secM t S L ⊓ L) ∧
      (∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w) ∧
      (∀ x : G, x ∈ secB S L ↔ ∃ v, IsEvenVec v ∧ φ v = x) ∧
      ∀ (y : ↥(secM t S L ⊓ L)) (v : Fin 5 → ZMod 2), IsEvenVec v →
        (y : G) * φ v * (y : G)⁻¹ = φ (permVec (ρ y : Equiv.Perm (Fin 5)) v) := by
  obtain ⟨-, -, hCB, -, hML, φ, hperm, -, -, -⟩ := hbd
  have hperm' : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [hML]
    exact hperm
  obtain ⟨hhom, hinj, hmem, hact, hall⟩ := hperm'
  let σ : ↥(secM t S L ⊓ L) → Equiv.Perm (Fin 5) := fun y => Classical.choose (hact (y : G) y.2)
  have hσspec : ∀ y : ↥(secM t S L ⊓ L), σ y ∈ alternatingGroup (Fin 5) ∧
      ∀ v, IsEvenVec v → (y : G) * φ v * (y : G)⁻¹ = φ (permVec (σ y) v) :=
    fun y => Classical.choose_spec (hact (y : G) y.2)
  have hσmem : ∀ y : ↥(secM t S L ⊓ L), σ y ∈ alternatingGroup (Fin 5) := fun y => (hσspec y).1
  have hσact : ∀ y : ↥(secM t S L ⊓ L), ∀ v, IsEvenVec v →
      (y : G) * φ v * (y : G)⁻¹ = φ (permVec (σ y) v) := fun y => (hσspec y).2
  have huniq : ∀ ρ τ : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → φ (permVec ρ v) = φ (permVec τ v)) → ρ = τ := by
    intro ρ τ h
    refine permVec_injective_five fun v hv => ?_
    exact hinj _ _ (isEvenVec_permVec ρ hv) (isEvenVec_permVec τ hv) (h v hv)
  have hσmul : ∀ y y' : ↥(secM t S L ⊓ L), σ (y * y') = σ y * σ y' := by
    intro y y'
    apply huniq
    intro v hv
    rw [permVec_mul]
    have hy := hσact y (permVec (σ y') v) (isEvenVec_permVec (σ y') hv)
    have hy' := hσact y' v hv
    have hyy' := hσact (y * y') v hv
    rw [Subgroup.coe_mul] at hyy'
    rw [← hyy']
    rw [show (y : G) * (y' : G) * φ v * ((y : G) * (y' : G))⁻¹
        = (y : G) * ((y' : G) * φ v * (y' : G)⁻¹) * (y : G)⁻¹ by group]
    rw [hy', hy]
  let Θ : ↥(secM t S L ⊓ L) →* ↥(alternatingGroup (Fin 5)) :=
    MonoidHom.mk' (fun y => ⟨σ y, hσmem y⟩) (fun y y' => Subtype.ext (hσmul y y'))
  have hΘapply : ∀ y : ↥(secM t S L ⊓ L), (Θ y : Equiv.Perm (Fin 5)) = σ y := fun _ => rfl
  have hΘsurj : Function.Surjective Θ := by
    intro x
    obtain ⟨h, hh, hact'⟩ := hall (x : Equiv.Perm (Fin 5)) x.2
    refine ⟨⟨h, hh⟩, ?_⟩
    apply Subtype.ext
    rw [hΘapply]
    apply huniq
    intro v hv
    rw [← hσact ⟨h, hh⟩ v hv, hact' v hv]
  have hBcomm : ∀ b ∈ secB S L, ∀ b' ∈ secB S L, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨v, hv, rfl⟩ := (hmem b).1 hb
    obtain ⟨w, hw, rfl⟩ := (hmem b').1 hb'
    rw [← hhom v w hv hw, ← hhom w v hw hv, add_comm]
  have hΘker : Θ.ker = (secB S L).subgroupOf (secM t S L ⊓ L) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hσ1 : σ y = 1 := by
        have h' := congrArg Subtype.val h
        simpa [hΘapply] using h'
      have hcomm : (y : G) ∈ centralizer (secB S L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨v, hv, hvφ⟩ := (hmem b).1 hb
        have hyv := hσact y v hv
        rw [hσ1, permVec_one, hvφ] at hyv
        have h1 : (y : G) * b = b * (y : G) := by
          calc (y : G) * b = (y : G) * b * (y : G)⁻¹ * (y : G) := by group
            _ = b * (y : G) := by rw [hyv]
        exact h1.symm
      have hy : (y : G) ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hcomm, y.2.2⟩
      rwa [hCB] at hy
    · intro hb
      apply Subtype.ext
      change σ y = 1
      apply huniq
      intro v hv
      rw [permVec_one, ← hσact y v hv]
      have hφvB : φ v ∈ secB S L := (hmem (φ v)).2 ⟨v, hv, rfl⟩
      rw [hBcomm _ hb _ hφvB]
      group
  exact ⟨Θ, φ, hΘsurj, hΘker, hinj, hmem, fun y v hv => hσact y v hv⟩

end CFSG.OddStandard.SmallF3.Omega
