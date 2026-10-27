module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem primeResidual_eq_top_of_isPerfect {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] :
    CatalogueBPrimeJoin.primeResidual 2 Y = ⊤ := by
  have := CatalogueBPrimeJoin.primeResidual_characteristic 2 Y
  have hodd : Odd (Nat.card (Y ⧸ CatalogueBPrimeJoin.primeResidual 2 Y)) :=
    Nat.coprime_two_left.mp (CatalogueBPrimeJoin.primeResidual_coprime_index 2 Y)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (Y ⧸ CatalogueBPrimeJoin.primeResidual 2 Y) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ hsolv
  rw [eq_top_iff]
  intro y _
  exact (QuotientGroup.eq_one_iff y).mp (Subsingleton.elim _ _)

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem isPComponent_K (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsPComponent 2 ((centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hKM := h.K_le_M β
  have hKperf : Group.IsPerfect ↥(centralizerResidual L β) := isPerfect_perfectResidual_map _
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
  refine ⟨((normal_subgroupOf_iff_le_normalizer hKM).mpr (h.M_le_normalizer_K β)).isSubnormal,
    ?_, ?_⟩
  · have : Group.IsPerfect ↥((centralizerResidual L β).subgroupOf
        (centralizer ({t} : Set X) ⊓ centralizer {β})) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKM).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact primeResidual_eq_top_of_isPerfect
  · have hL := hσ.lieModel_bar_K hFC hKC i j
    have := isSimpleGroup_of_lieModel_psl2 hL
    let e := subgroupOfEquivOfLe hKM
    let e' : ↥((centralizerResidual L β).subgroupOf
        (centralizer ({t} : Set X) ⊓ centralizer {β})) ⧸ pPrimeCore 2 _ ≃*
        Bar (centralizerResidual L β) :=
      QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
    exact LocalCores.isQuasisimple_of_mulEquiv e'.symm
      (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hL)).1

theorem pLayer_M (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (pLayer ↥(centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) 2).map
        (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
      centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hKM := h.K_le_M β
  have hle : pLayer ↥(centralizer ({t} : Set X) ⊓ centralizer {β}) 2 =
      (centralizerResidual L β).subgroupOf (centralizer ({t} : Set X) ⊓ centralizer {β}) := by
    apply le_antisymm
    · refine sSup_le fun J hJ => ?_
      have hJp : Group.IsPerfect ↥J := CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
      have hJM : Group.IsPerfect ↥(J.map (centralizer ({t} : Set X) ⊓ centralizer {β}).subtype) :=
        Group.IsPerfect.ofSurjective (f := (equivMapOfInjective J _
          (centralizer ({t} : Set X) ⊓ centralizer {β}).subtype_injective).toMonoidHom)
          (MulEquiv.surjective _)
      have h1 := le_perfectResidual_map (map_subtype_le J) hJM
      rw [h.perfectResidual_M] at h1
      intro x hx
      exact h1 ⟨x, hx, rfl⟩
    · exact le_sSup (hσ.isPComponent_K hFC hKC i j)
  rw [hle, subgroupOf_map_subtype, inf_eq_left.mpr hKM]

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
