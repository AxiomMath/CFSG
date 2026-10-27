module

public import CFSG.LieType.Steinberg.TwistedE6.Unipotent
public import CFSG.LieType.Steinberg.TwistedE6.RankOne
public import CFSG.LieType.Steinberg.TwistedE6.Fixed
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Universal

variable {k : Type*} [Field k] (θ : k →+* k)

theorem isRoot_of_mem_twistedDatum_roots {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : β ∈ (twistedDatum k θ).roots) : IsRoot .F4 β := by
  rw [twistedDatum_roots] at hβ
  exact hβ

theorem twisted_setOf_pos_eq :
    {γ | γ ∈ (twistedDatum k θ).roots ∧ 0 < ht γ} =
      {γ : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 γ ∧ 0 < ht γ} := by
  rw [twistedDatum_roots]
  rfl

theorem twisted_setOf_neg_eq :
    {γ | γ ∈ (twistedDatum k θ).roots ∧ ht γ < 0} =
      {γ : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 γ ∧ ht γ < 0} := by
  rw [twistedDatum_roots]
  rfl

theorem twistedRootGroup_ne_bot (hθ : ∀ c, θ (θ c) = c) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) : twistedRootGroup k θ β ≠ ⊥ := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  intro hbot
  by_cases hfix : rho α = α
  · have h := xFixed_mem θ hα hfix 1 (map_one θ)
    rw [hp, hbot, Subgroup.mem_bot] at h
    have h' := congrArg Subtype.val h
    rw [xFixed_val] at h'
    have h'' : e6Data_valid.xm k α 1 = e6Data_valid.xm k α 0 := by
      rw [h', e6Data_valid.xm_zero]
      rfl
    exact one_ne_zero (e6Data_valid.xm_injective k hα h'')
  · have h := xPair_mem θ hθ hα hfix 1
    rw [hp, hbot, Subgroup.mem_bot] at h
    have h' := congrArg Subtype.val h
    rw [xPair_val] at h'
    have h'' : e6Data_valid.xm k α 1 *
        e6Data_valid.xm k (rho α) ((twistSign α : k) * θ 1) =
          e6Data_valid.xm k α 0 * e6Data_valid.xm k (rho α) 0 := by
      rw [h', e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
      rfl
    exact one_ne_zero (xm_mul_xm_rho_inj hα hfix h'').1

theorem bruhat_twisted (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4)) {g : fixedGroup k θ}
    (hg : g ∈ rankOne (twistedRootGroup k θ) i) :
    (∃ h ∈ hHat k θ i, ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), ∃ h ∈ hHat k θ i,
        ∃ v ∈ twistedRootGroup k θ (Pi.single i 1), g = u * nHat θ i * h * v := by
  fin_cases i
  · exact bruhat_fixed θ hθ (a := nd 1) (i := nf 0) rfl rfl rfl rfl hg
  · exact bruhat_fixed θ hθ (a := nd 3) (i := nf 1) rfl rfl rfl rfl hg
  · exact bruhat_pair θ hθ (a := nd 2) (b := nd 4) (i := nf 2) (Or.inl ⟨rfl, rfl⟩) rfl rfl rfl hg
  · exact bruhat_pair θ hθ (a := nd 0) (b := nd 5) (i := nf 3) (Or.inr ⟨rfl, rfl⟩) rfl rfl rfl hg

theorem eq_one_of_mem_normalizer_twisted (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4))
    {u : fixedGroup k θ} (hu : u ∈ twistedRootGroup k θ (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup k θ (-Pi.single i 1) : Set (fixedGroup k θ))) : u = 1 := by
  fin_cases i
  · exact eq_one_of_mem_normalizer_fixed θ (a := nd 1) (i := nf 0) rfl rfl hu hn
  · exact eq_one_of_mem_normalizer_fixed θ (a := nd 3) (i := nf 1) rfl rfl hu hn
  · exact eq_one_of_mem_normalizer_pair θ hθ (a := nd 2) (b := nd 4) (i := nf 2)
      (Or.inl ⟨rfl, rfl⟩) rfl hu hn
  · exact eq_one_of_mem_normalizer_pair θ hθ (a := nd 0) (b := nd 5) (i := nf 3)
      (Or.inr ⟨rfl, rfl⟩) rfl hu hn

theorem twistedDatum_isCTGroupDatum (hθ : ∀ c, θ (θ c) = c)
    (htop : ⨆ β ∈ (twistedDatum k θ).roots, (twistedDatum k θ).rootGroup β = ⊤) :
    IsCTGroupDatum (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum k θ).isFiniteType) (twistedDatum k θ).roots
      (twistedDatum k θ).rootGroup (nHat θ) (hHat k θ) where
  n_mem i := nHat_mem_rankOne θ hθ i
  conj_mem i β hβ x hx := by
    have e : weylAction (twistedDatum k θ).isFiniteType
        ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple i) β =
          reflect .F4 i β :=
      weylAction_simple_apply (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) i β
    rw [e]
    exact nHat_conj_mem θ i (isRoot_of_mem_twistedDatum_roots θ hβ) hx
  braid i j := nHat_braidWord θ i j
  H_le i := hHat_le_rankOne θ hθ i
  sq_mem i := nHat_sq_mem θ i
  H_conj_mem l β hβ h hh x hx :=
    hHat_conj_mem θ l (isRoot_of_mem_twistedDatum_roots θ hβ) hh hx
  conj_H_mem j l h hh := nHat_conj_hHat_mem θ hθ j l hh
  le_rankOne i β hβ hsupp := by
    rcases eq_single_of_support (isRoot_of_mem_twistedDatum_roots θ hβ) hsupp with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := htop

theorem twistedDatum_steinbergExtras (hθ : ∀ c, θ (θ c) = c) :
    SteinbergExtras (twistedDatum k θ) (nHat θ) (hHat k θ) where
  ne_bot β hβ := twistedRootGroup_ne_bot θ hθ (isRoot_of_mem_twistedDatum_roots θ hβ)
  two_smul_le β _ h2 :=
    absurd (isRoot_of_mem_twistedDatum_roots θ h2) (not_isRoot_two_smul (τ := .F4) β)
  commutator_mem := commutator_mem_twistedDatum
  prodInjective_pos L hnd hmem hsort :=
    prodInjective_twisted θ 1 L hnd
      (fun β hβ => ⟨isRoot_of_mem_twistedDatum_roots θ ((hmem β).1 hβ).1, by
        rw [one_mul]; exact ((hmem β).1 hβ).2.1⟩)
      (hsort.imp fun h => by rwa [one_mul, one_mul])
  prodInjective_neg L hnd hmem hsort :=
    prodInjective_twisted θ (-1) L hnd
      (fun β hβ => ⟨isRoot_of_mem_twistedDatum_roots θ ((hmem β).1 hβ).1, by
        rw [neg_one_mul]; exact neg_pos.2 ((hmem β).1 hβ).2.1⟩)
      (hsort.imp fun h => by rw [neg_one_mul, neg_one_mul]; exact neg_le_neg h)
  posPart_inf_negPart := by
    rw [twisted_setOf_pos_eq, twisted_setOf_neg_eq]
    exact posPart_inf_negPart_twisted θ
  rankOne_bruhat i g hg := bruhat_twisted θ hθ i hg
  eq_one_of_mem_normalizer i u hu hn := eq_one_of_mem_normalizer_twisted θ hθ i hu hn
  torus_commute i j h hh h' hh' := hHat_commute θ hθ hh hh'
  torus_iSupIndep := hHat_iSupIndep θ
  torus_inf_posPart := by
    rw [twisted_setOf_pos_eq]
    exact torus_inf_posPart_twisted θ

end CFSG.LieType.Steinberg.TwistedE6
