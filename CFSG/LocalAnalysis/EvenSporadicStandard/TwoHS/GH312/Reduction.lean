module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHWr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.PCoreTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.WreathCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.Components
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.TwoComponents
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3Socle
public import CFSG.GH74.GLS.Stage2.Local.P34Comp

public section

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

open Subgroup

@[expose] def GH312AlmostSimple : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.pPrimeCore 2 X = ⊥ → center X = ⊥ →
    (∃ P : Sylow 2 X,
      Nonempty (↥P ≃* RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)))) →
    (∃ u : X, u * u = 1 ∧ u ≠ 1 ∧
      Nonempty (↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))) →
    ∀ T : Subgroup X, T.Normal → IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      centralizer (T : Set X) = ⊥ →
      Nonempty (X ≃* Equiv.Perm (Fin 9)) ∨ Nonempty (X ≃* PGSp45)

theorem gh312Fixed_of_almostSimple (h : GH312AlmostSimple) : GH312Fixed := by
  intro X _ _ hO hZ hP hU
  obtain ⟨P, ⟨ι⟩⟩ := hP
  obtain ⟨u, hu2, hu1, ⟨e⟩⟩ := hU
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial X := ⟨u, 1, hu1⟩
  have hPcard : Nat.card (P : Subgroup X) = 2 ^ 7 := by
    rw [show Nat.card (P : Subgroup X) = Nat.card W8 from Nat.card_congr ι.toEquiv,
      SAFyGH.card_W8]
    norm_num
  have hO₂ : CFSG.pCore 2 X = ⊥ :=
    pCore_two_eq_bot_of_centralizer_equiv hZ P hPcard hu1 e
  have hF : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X 2 hO, hO₂]
  have hZuniq : ∀ a ∈ Subgroup.center ↥(P : Subgroup X),
      ∀ b ∈ Subgroup.center ↥(P : Subgroup X), orderOf a = 2 → orderOf b = 2 → a = b :=
    fun a ha b hb ha2 hb2 => eq_of_mem_center_of_orderOf_eq_two ι ha hb ha2 hb2
  have hne_layer : CFSG.layer X ≠ ⊥ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk94.layer_ne_bot_of_cores hO hO₂
  let 𝒞 : Set (Subgroup X) := {M : Subgroup X | CFSG.IsComponent M}
  have hCne : 𝒞.Nonempty := by
    obtain ⟨K, hK⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk94.exists_isComponent_of_layer_ne_bot hne_layer
    exact ⟨K, hK⟩
  have hCle : 𝒞.ncard ≤ 2 := ncard_setOf_isComponent_le_two hF P hZuniq (le_of_eq hPcard)
  have hCpos : 0 < 𝒞.ncard := hCne.ncard_pos
  rcases (by omega : 𝒞.ncard = 1 ∨ 𝒞.ncard = 2) with h1 | h2
  ·
    obtain ⟨K, hKset⟩ := Set.ncard_eq_one.mp h1
    have hall : {M : Subgroup X | CFSG.IsComponent M} = {K} := by simpa [𝒞] using hKset
    have hK : CFSG.IsComponent K := by
      have hmem : K ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
        rw [hall]; simp
      simpa using hmem
    obtain ⟨_, hKnorm, hKcen⟩ := componentLayerOf_top_eq_of_components_eq_singleton hF hall
    obtain ⟨hKsimple, hKna⟩ := CFSG.GH74.GLS.Stage2.Local.P34.component_isSimple hF hK
    rcases h X hO hZ ⟨P, ⟨ι⟩⟩ ⟨u, hu2, hu1, ⟨e⟩⟩ K hKnorm hKsimple hKna hKcen with
      h9 | hpg
    · exact Or.inl h9
    · exact Or.inr (Or.inr hpg)
  ·
    obtain ⟨K, L, hKLne, hKLset⟩ := Set.ncard_eq_two.mp h2
    have hall : {M : Subgroup X | CFSG.IsComponent M} = {K, L} := by
      simpa [𝒞] using hKLset
    have hK : CFSG.IsComponent K := by
      have hmem : K ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
        rw [hall]; simp
      simpa using hmem
    have hL : CFSG.IsComponent L := by
      have hmem : L ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
        rw [hall]; simp
      simpa using hmem
    obtain ⟨hKsimple, hKna⟩ := CFSG.GH74.GLS.Stage2.Local.P34.component_isSimple hF hK
    obtain ⟨hcommK, _⟩ :=
      CFSG.GH74.GLS.Stage2.Local.P34.components_commute_inf hF hK hL hKLne
    have hcomm : K ≤ Subgroup.centralizer (L : Set X) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcommK a ha b hb).symm
    have hconj : ∃ g : X, CFSG.conjugate K g = L := by
      obtain ⟨g, -, hg⟩ := exists_mem_sylow_conjugate_eq_of_isComponent hF P hZuniq hK hL
      exact ⟨g, hg⟩
    have hperm : ∀ x : X, CFSG.conjugate K x = K ∨ CFSG.conjugate K x = L := by
      intro x
      have hmem : CFSG.conjugate K x ∈
          ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) :=
        CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hK x
      rw [hall] at hmem
      simpa using hmem
    obtain ⟨eK⟩ := nonempty_mulEquiv_alternatingGroup_five_of_two_components (X := X)
      hu2 hu1 e hKLne hKsimple hKna hcomm hperm hconj
    obtain ⟨eProd⟩ := nonempty_mulEquiv_prod_of_components_eq_pair hF hKLne hall
    obtain ⟨g, hg⟩ := hconj
    have hKLiso : ↥K ≃* ↥L :=
      ((MulAut.conj g⁻¹).subgroupMap K).trans (MulEquiv.subgroupCongr hg)
    have eL : ↥L ≃* alternatingGroup (Fin 5) := hKLiso.symm.trans eK
    exact Or.inr (Or.inl ⟨eProd.trans (eK.prodCongr eL)⟩)

end CFSG.EvenSporadicStandard.TwoHS.GH312
