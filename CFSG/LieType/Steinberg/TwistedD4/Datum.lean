module

public import CFSG.LieType.Steinberg.TwistedD4.Weyl
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.Fixed

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open CFSG.LieType.Universal

variable {K : Type} [Field K] (σ : K →+* K)

theorem isRoot_of_mem_twistedDatum_roots
    {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : β ∈ (twistedDatum σ).roots) : IsRoot .G2 β := by
  rw [twistedDatum_roots] at hβ
  exact hβ

theorem twisted_setOf_pos_eq :
    {γ | γ ∈ (twistedDatum σ).roots ∧ 0 < ht γ} =
      {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ 0 < ht γ} := by
  rw [twistedDatum_roots]
  rfl

theorem twisted_setOf_neg_eq :
    {γ | γ ∈ (twistedDatum σ).roots ∧ ht γ < 0} =
      {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ ht γ < 0} := by
  rw [twistedDatum_roots]
  rfl

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem twistedRootGroup_ne_bot
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    twistedRootGroup σ β ≠ ⊥ := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  rw [Ne, Subgroup.eq_bot_iff_forall]
  intro hbot
  by_cases hfix : rho α = α
  · have h := xPar_mem_of_fixed hσ hα hfix (c := 1) (map_one σ)
    rw [hp] at h
    have h1 := hbot ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hβ h⟩ h
    have h2 : xPar (rootOperatorFamily d4) α (1 : K) = xPar (rootOperatorFamily d4) α 0 := by
      rw [xPar_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (xPar_injective hα h2)
  · have h := xOrbit_mem hσ hα hfix (1 : K)
    rw [hp] at h
    have h1 := hbot ⟨_, twistedRootSubgroupD4_le_twistedGroup σ hβ h⟩ h
    have h2 : xOrbit σ α (1 : K) = xOrbit σ α 0 := by
      rw [xOrbit_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (xOrbit_injective σ hα hfix h2)

theorem bruhat_twisted
    (i : Fin (Tag.rank .G2)) {g : twistedGroup σ}
    (hg : g ∈ rankOne (twistedRootGroup σ) i) :
    (∃ h ∈ hHat σ i, ∃ u ∈ twistedRootGroup σ (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup σ (Pi.single i 1), ∃ h ∈ hHat σ i,
        ∃ v ∈ twistedRootGroup σ (Pi.single i 1), g = u * nHat σ i * h * v := by
  match i with
  | ⟨0, _⟩ => exact bruhat_long hσ hg
  | ⟨1, _⟩ => exact bruhat_short hσ hg

theorem eq_one_of_mem_normalizer_twisted
    (i : Fin (Tag.rank .G2)) {u : twistedGroup σ}
    (hu : u ∈ twistedRootGroup σ (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup σ (-Pi.single i 1) : Set (twistedGroup σ))) : u = 1 := by
  match i with
  | ⟨0, _⟩ => exact eq_one_of_mem_normalizer_long hσ hu hn
  | ⟨1, _⟩ => exact eq_one_of_mem_normalizer_short hσ hu hn

variable (σ) in
theorem twistedDatum_isCTGroupDatum :
    IsCTGroupDatum (coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum σ).isFiniteType) (twistedDatum σ).roots
      (twistedDatum σ).rootGroup (nHat σ) (hHat σ) where
  n_mem i := nHat_mem_rankOne σ i
  conj_mem i β hβ x hx := by
    have e : weylAction (twistedDatum σ).isFiniteType
        ((coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem.simple i) β =
          reflect .G2 i β :=
      weylAction_simple_eq_reflect (isFiniteType_cartan .G2) i β
    rw [e]
    exact nHat_conj_mem σ i (isRoot_of_mem_twistedDatum_roots σ hβ) hx
  braid i j := nHat_braidWord σ i j
  H_le i := hHat_le_rankOne hσ i
  sq_mem i := nHat_sq_mem σ i
  H_conj_mem l β hβ h hh x hx :=
    hHat_conj_mem σ l (isRoot_of_mem_twistedDatum_roots σ hβ) hh hx
  conj_H_mem j l h hh := nHat_conj_hHat_mem σ hσ j l hh
  le_rankOne i β hβ hsupp := by
    rcases eq_single_or_neg_of_support (isRoot_of_mem_twistedDatum_roots σ hβ) hsupp with
      rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := iSup_twistedDatum_rootGroup σ

variable (σ) in
theorem twistedDatum_steinbergExtras
    : SteinbergExtras (twistedDatum σ) (nHat σ) (hHat σ) where
  ne_bot β hβ := twistedRootGroup_ne_bot hσ (isRoot_of_mem_twistedDatum_roots σ hβ)
  two_smul_le β _ h2 :=
    absurd (eq_one_of_isRoot_nsmul (isRoot_of_mem_twistedDatum_roots σ h2)) (by norm_num)
  commutator_mem := commutator_mem_twistedDatum
  prodInjective_pos L hnd hmem hsort :=
    prodInjective_twisted σ 1 L hnd
      (fun β hβ => ⟨isRoot_of_mem_twistedDatum_roots σ ((hmem β).1 hβ).1, by
        rw [one_mul]; exact ((hmem β).1 hβ).2.1⟩)
      (hsort.imp fun h => by rwa [one_mul, one_mul])
  prodInjective_neg L hnd hmem hsort :=
    prodInjective_twisted σ (-1) L hnd
      (fun β hβ => ⟨isRoot_of_mem_twistedDatum_roots σ ((hmem β).1 hβ).1, by
        rw [neg_one_mul]; exact neg_pos.2 ((hmem β).1 hβ).2.1⟩)
      (hsort.imp fun h => by rw [neg_one_mul, neg_one_mul]; exact neg_le_neg h)
  posPart_inf_negPart := by
    rw [twisted_setOf_pos_eq, twisted_setOf_neg_eq]
    exact posPart_inf_negPart_twisted σ
  rankOne_bruhat i g hg := bruhat_twisted hσ i hg
  eq_one_of_mem_normalizer i u hu hn := eq_one_of_mem_normalizer_twisted hσ i hu hn
  torus_commute i j h hh h' hh' := hHat_commute σ hh hh'
  torus_iSupIndep := hHat_iSupIndep σ hσ
  torus_inf_posPart := by
    rw [twisted_setOf_pos_eq]
    exact torus_inf_posPart_twisted σ

end CFSG.LieType.Steinberg.TwistedD4
