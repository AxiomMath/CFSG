module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec121_autIn_equiv (F : Sec12Frame t L S) :
    Nonempty (↥(autIn (secM t S L ⊓ L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨φ, hperm⟩ := sec121_exists_perm F
  have hYle : (secM t S L ⊓ L) ≤ normalizer (secA t S L : Set G) := inf_le_left
  let σ : ↥(secM t S L ⊓ L) → Equiv.Perm (Fin 5) :=
    fun y => Classical.choose (hperm.2.2.2.1 (y : G) y.2)
  have hσspec : ∀ y : ↥(secM t S L ⊓ L),
      σ y ∈ alternatingGroup (Fin 5) ∧
        ∀ v, IsEvenVec v → (y : G) * φ v * (y : G)⁻¹ = φ (permVec (σ y) v) :=
    fun y => Classical.choose_spec (hperm.2.2.2.1 (y : G) y.2)
  have hσmem : ∀ y : ↥(secM t S L ⊓ L), σ y ∈ alternatingGroup (Fin 5) :=
    fun y => (hσspec y).1
  have hσact : ∀ y : ↥(secM t S L ⊓ L), ∀ v, IsEvenVec v →
      (y : G) * φ v * (y : G)⁻¹ = φ (permVec (σ y) v) :=
    fun y => (hσspec y).2
  have huniq : ∀ ρ τ : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → φ (permVec ρ v) = φ (permVec τ v)) → ρ = τ := by
    intro ρ τ h
    apply Equiv.ext
    intro k
    have h1 : φ (wvec (ρ k)) = φ (wvec (τ k)) := by
      have h2 := h (wvec k) (wvec_even k)
      rwa [permVec_wvec, permVec_wvec] at h2
    exact wvec_injective (hperm.2.1 _ _ (wvec_even _) (wvec_even _) h1)
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
  have hΘapply : ∀ y : ↥(secM t S L ⊓ L),
      (Θ y : Equiv.Perm (Fin 5)) = σ y := fun _ => rfl
  have hΘsurj : Function.Surjective Θ := by
    intro x
    obtain ⟨h, hh, hact⟩ := hperm.2.2.2.2 (x : Equiv.Perm (Fin 5)) x.2
    refine ⟨⟨h, hh⟩, ?_⟩
    apply Subtype.ext
    rw [hΘapply]
    apply huniq
    intro v hv
    rw [← hσact ⟨h, hh⟩ v hv, hact v hv]
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
        obtain ⟨v, hv, hvφ⟩ := (hperm.2.2.1 b).1 hb
        have hyv := hσact y v hv
        rw [hσ1, permVec_one, hvφ] at hyv
        have h1 : (y : G) * b = b * (y : G) := by
          calc (y : G) * b = (y : G) * b * (y : G)⁻¹ * (y : G) := by group
            _ = b * (y : G) := by rw [hyv]
        exact h1.symm
      have hy : (y : G) ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hcomm, y.2.2⟩
      rwa [F.bdata.2.2.1] at hy
    · intro hb
      apply Subtype.ext
      change σ y = 1
      apply huniq
      intro v hv
      rw [permVec_one, ← hσact y v hv]
      have hφvB : φ v ∈ secB S L := (hperm.2.2.1 (φ v)).2 ⟨v, hv, rfl⟩
      rw [sec12E_B_comm F hb hφvB]
      group
  let Ψ : ↥(secM t S L ⊓ L) →* ↥(autIn (secM t S L ⊓ L) (secA t S L)) :=
    MonoidHom.mk' (fun y =>
      ⟨(secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y), by
        rw [autIn, Subgroup.mem_map]
        exact ⟨Subgroup.inclusion hYle y,
          Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_inclusion]; exact y.2), rfl⟩⟩)
      (fun y y' => Subtype.ext (by
        show (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle (y * y')) =
          (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y) *
          (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y')
        simp only [map_mul]))
  have hΨapply : ∀ y : ↥(secM t S L ⊓ L),
      (Ψ y : MulAut ↥(secA t S L)) =
        (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y) := fun _ => rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    let y : ↥(secM t S L ⊓ L) := ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [hΨapply, ← hax]
    exact congrArg (secA t S L).normalizerMonoidHom (Subtype.ext rfl)
  have hΨker : Ψ.ker = (secB S L).subgroupOf (secM t S L ⊓ L) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hN : (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y) = 1 := by
        have h' := congrArg Subtype.val h
        simpa [hΨapply] using h'
      have hmem : Subgroup.inclusion hYle y ∈ (secA t S L).normalizerMonoidHom.ker :=
        MonoidHom.mem_ker.mpr hN
      rw [Subgroup.normalizerMonoidHom_ker] at hmem
      have hcenA : (y : G) ∈ centralizer (secA t S L : Set G) := by
        rwa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hmem
      have hcenB : (y : G) ∈ centralizer (secB S L : Set G) :=
        (Subgroup.centralizer_le (s := (secB S L : Set G)) (t := (secA t S L : Set G))
          (fun x hx => Subgroup.mem_sup_left hx)) hcenA
      have hy : (y : G) ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hcenB, y.2.2⟩
      rwa [F.bdata.2.2.1] at hy
    · intro hb
      apply Subtype.ext
      change (secA t S L).normalizerMonoidHom (Subgroup.inclusion hYle y) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion, Subgroup.mem_centralizer_iff]
      intro a ha
      exact sec12E_A_comm F ha (Subgroup.mem_sup_left (T := zpowers t) hb)
  have hker : Ψ.ker = Θ.ker := hΨker.trans hΘker.symm
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj))⟩

end CFSG.OddStandard.SmallF3.Omega
