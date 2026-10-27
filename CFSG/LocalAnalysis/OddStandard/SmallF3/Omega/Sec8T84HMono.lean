module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] def hMonoC : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6)))

private instance decidableMemHMonoC : DecidablePred (· ∈ hMonoC) := fun σ =>
  decidable_of_iff' (monoG * σ = σ * monoG)
    (by
      show σ ∈ Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6))) ↔
        monoG * σ = σ * monoG
      rw [Subgroup.mem_centralizer_iff]
      simp only [Set.mem_singleton_iff, forall_eq])

theorem hMonoC_card : Nat.card hMonoC = 16 := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun σ : Equiv.Perm (Fin 6) => σ ∈ hMonoC)]
  decide

theorem monoD_eq_inf : monoD = alternatingGroup (Fin 6) ⊓ hMonoC := rfl

@[expose] noncomputable def hPO (fr : NFrame Q (Fin 6) c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ σ ∈ hMonoC, ∃ J : Finset (Fin 6), g = fr.permOrth σ * fr.signChange J}
  one_mem' := by
    exact ⟨1, hMonoC.one_mem, ∅,
      by rw [fr.permOrth_one, fr.signChange_empty, one_mul]⟩
  mul_mem' := by
    rintro a b ⟨σ, hσ, J, rfl⟩ ⟨τ, hτ, K, rfl⟩
    refine ⟨σ * τ, hMonoC.mul_mem hσ hτ, symmDiff (J.map τ⁻¹.toEmbedding) K, ?_⟩
    exact ffMono_mul fr σ τ J K
  inv_mem' := by
    rintro a ⟨σ, hσ, J, rfl⟩
    refine ⟨σ⁻¹, hMonoC.inv_mem hσ, J.map σ.toEmbedding, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [ffMono_mul fr σ σ⁻¹ J (J.map σ.toEmbedding), mul_inv_cancel, inv_inv, symmDiff_self,
      Finset.bot_eq_empty, fr.signChange_empty, fr.permOrth_one, one_mul]

theorem mem_hPO_iff (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ hPO fr ↔ ∃ σ ∈ hMonoC, ∃ J : Finset (Fin 6), g = fr.permOrth σ * fr.signChange J :=
  Iff.rfl

theorem ffP0_le_hPO (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) : ffP0 hQ fr ≤ hPO fr := by
  intro g hg
  obtain ⟨σ, hσ, J, -, rfl⟩ := (mem_ffP0_iff hQ fr).mp hg
  exact ⟨σ, hσ.2, J, rfl⟩

theorem hPO_card (fr : NFrame Q (Fin 6) c) : Nat.card (hPO fr) = 2 ^ 10 := by
  let F : hMonoC × Finset (Fin 6) → hPO fr := fun x =>
    ⟨fr.permOrth x.1.1 * fr.signChange x.2, ⟨x.1.1, x.1.2, x.2, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨σ, hσ⟩, J⟩ ⟨⟨τ, hτ⟩, K⟩ h
      have hg : fr.permOrth σ * fr.signChange J = fr.permOrth τ * fr.signChange K :=
        congrArg Subtype.val h
      obtain ⟨hστ, hJK⟩ := ffMono_unique fr hg
      exact Prod.ext (Subtype.ext hστ) hJK
    · rintro ⟨g, σ, hσ, J, rfl⟩
      exact ⟨(⟨σ, hσ⟩, J), rfl⟩
  have hcard : Nat.card (hPO fr) = Nat.card (hMonoC × Finset (Fin 6)) :=
    (Nat.card_congr (Equiv.ofBijective F hF)).symm
  have hFin : Nat.card (Finset (Fin 6)) = 64 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
    norm_num
  calc
    Nat.card (hPO fr) = Nat.card (hMonoC × Finset (Fin 6)) := hcard
    _ = Nat.card hMonoC * Nat.card (Finset (Fin 6)) := Nat.card_prod _ _
    _ = 16 * 64 := by rw [hMonoC_card, hFin]
    _ = 2 ^ 10 := by norm_num

theorem hPO_inf_omega (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    hPO fr ⊓ omegaGroup hQ = ffP0 hQ fr := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgPO, hgΩ⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨σ, hσ, J, rfl⟩ := hgPO
    obtain ⟨hσA, hJ⟩ := (ffMono_mem_omega_iff hQ fr σ J).mp hgΩ
    exact (mem_ffP0_iff hQ fr).mpr
      ⟨σ, Subgroup.mem_inf.mpr ⟨hσA, hσ⟩, J, hJ, rfl⟩
  · intro g hg
    exact Subgroup.mem_inf.mpr ⟨ffP0_le_hPO hQ fr hg, ffP0_le_omega hQ fr hg⟩

theorem hPO_le_normalizer (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    hPO fr ≤ normalizer (ffP0 hQ fr : Set (OGroup Q)) := by
  haveI : Finite (ffP0 hQ fr) :=
    Nat.finite_of_card_ne_zero (by rw [ffP0_card hQ fr]; norm_num)
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  rw [← hPO_inf_omega hQ fr]
  exact Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem hg (ffP0_le_hPO hQ fr hn)) (inv_mem hg),
      (omegaGroup_normal hQ).conj_mem n (ffP0_le_omega hQ fr hn) g⟩

end CFSG.OddStandard.SmallF3.Omega
