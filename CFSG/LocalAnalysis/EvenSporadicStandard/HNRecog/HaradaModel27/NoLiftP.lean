module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.CentHomSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.LiftSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.EvenSporadicStandard.HNRecog.Harada.S25

theorem blkData1_labels (hblk : blkDataOK blkData1 = true) :
    ∀ j : Fin 5, ∃ p : Fin 1408, blkF 5 blkData1.blk p = some j := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at hblk
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hsz⟩, -⟩, hsurj⟩, -⟩, -⟩, -⟩, -⟩ := hblk
  exact blkSurjOK_spec hsz hsurj

theorem perm_eq_of_label_map {π σ : Equiv.Perm (Fin 5)}
    (hlab : ∀ j : Fin 5, ∃ p : Fin 1408, blkF 5 blkData1.blk p = some j)
    (h : ∀ p : Fin 1408, (blkF 5 blkData1.blk p).map π = (blkF 5 blkData1.blk p).map σ) :
    π = σ := by
  refine Equiv.ext fun j => ?_
  obtain ⟨p, hp⟩ := hlab j
  have := h p
  rw [hp] at this
  simpa using this

section Cert


theorem pZ_sq : pZ ^ 2 = 1 := by
  have h : elemZ * elemZ = 1 := mul_self_eq_one_of_orderOf_eq_two twoHSBasic_spec.2.1
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_two]
  exact h

theorem exists_lift_of_label {w : List ℕ} {π : Equiv.Perm (Fin 5)}
    (hlab : ∀ j : Fin 5, ∃ p : Fin 1408, blkF 5 blkData1.blk p = some j)
    (ψ : ↥(centralizer ({pZ} : Set ↥P1408)) →* Equiv.Perm (Fin 5))
    (hker : ψ.ker = (wordSubgroupP nWords1).subgroupOf (centralizer ({pZ} : Set ↥P1408)))
    (hact : ∀ (x : ↥(centralizer ({pZ} : Set ↥P1408))) (p : Fin 1408),
      blkF 5 blkData1.blk (((x : ↥P1408) : Equiv.Perm (Fin 1408)) p) =
        (blkF 5 blkData1.blk p).map (ψ x))
    (hc : elemW w * elemZ = elemZ * elemW w)
    (hb : ∀ p : Fin 1408, blkF 5 blkData1.blk (elemW w p) = (blkF 5 blkData1.blk p).map π)
    (u : ↥(centralizer ({pZ} : Set ↥P1408))) (hu : ψ u = π) :
    ∃ g ∈ wordSubgroup nWords1, ((u : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW w * g := by
  let u0 : ↥(centralizer ({pZ} : Set ↥P1408)) :=
    ⟨⟨elemW w, elemW_mem w⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)⟩
  have hψ : ψ u0 = π := perm_eq_of_label_map hlab fun p => (hact u0 p).symm.trans (hb p)
  have hk : u0⁻¹ * u ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, hu, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf, mem_wordSubgroupP] at hk
  refine ⟨_, hk, ?_⟩
  simp [u0]

theorem exists_noLift_pZ (hP : Nat.card ↥P1408 = 177408000) (hlift : liftOK = true) :
    ∃ ψ : ↥(centralizer ({pZ} : Set ↥P1408)) →* Equiv.Perm (Fin 5),
      Function.Surjective ψ ∧
      ψ.ker = (wordSubgroupP nWords1).subgroupOf (centralizer ({pZ} : Set ↥P1408)) ∧
      NoLiftV4 pZ ψ := by
  obtain ⟨ψ, hsurj, hker, hact⟩ := exists_hom_centralizer_pZ hP
  have h1 := tableI1OK_true
  simp only [tableI1OK, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨hblk, -⟩, hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h1
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  have hlab := blkData1_labels hblk
  obtain ⟨-, -, hcu, hcv, hbu, hbv⟩ := lift_words hg hlift
  have hno := lift_noComm hg hN hlift
  refine ⟨ψ, hsurj, hker, ?_⟩
  intro u v hu hv hu2 hv2 hc
  obtain ⟨g, hgN, hug⟩ := exists_lift_of_label hlab ψ hker hact hcu hbu u hu
  obtain ⟨h, hhN, hvh⟩ := exists_lift_of_label hlab ψ hker hact hcv hbv v hv
  rw [mem_zpowers_of_sq_eq_one pZ_sq] at hu2 hv2 hc
  have hsq : ∀ x : ↥P1408, x ^ 2 = 1 ∨ x ^ 2 = pZ →
      ((x : Equiv.Perm (Fin 1408)) * x = 1 ∨ (x : Equiv.Perm (Fin 1408)) * x = elemZ) := by
    intro x hx
    rcases hx with hx | hx
    · left
      have := congrArg Subtype.val hx
      simpa [pow_two] using this
    · right
      have := congrArg Subtype.val hx
      simp only [Subgroup.coe_pow, pow_two] at this
      exact this
  refine hno g hgN h hhN ?_ ?_ ?_
  · rw [← hug]
    exact hsq _ hu2
  · rw [← hvh]
    exact hsq _ hv2
  · rw [← hug, ← hvh]
    set x : Equiv.Perm (Fin 1408) := ((u : ↥P1408) : Equiv.Perm (Fin 1408))
    set y : Equiv.Perm (Fin 1408) := ((v : ↥P1408) : Equiv.Perm (Fin 1408))
    have hxy : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rcases hc with hc | hc
    · left
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
      rw [hxy, this, one_mul]
    · right
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [hxy, this]
      rfl

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
