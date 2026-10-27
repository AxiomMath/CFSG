module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Action
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNode
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein

variable {G : Type} [Group G]

theorem mk_mem_normalizer_barM {M K : Subgroup G} {u : G} (huM : u ∈ M)
    (huK : u ∈ Subgroup.normalizer (K : Set G)) :
    (QuotientGroup.mk (⟨u, huM⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.normalizer ((barM M K : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  have h1 : K.map (MulAut.conj u).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp huK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have := barM_map_conj huM K
  rw [h1] at this
  exact this.symm

theorem mem_normalizer_inf {S L : Subgroup G} {u : G} (hS : u ∈ Subgroup.normalizer (S : Set G))
    (hL : u ∈ Subgroup.normalizer (L : Set G)) :
    u ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hS hL ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hS h, hL h]

theorem exists_block_action {M L : Subgroup G} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6)
    (φ : ↥(barM M L) ≃* ↥(alternatingGroup Ω)) {U : Subgroup G} (hUM : U ≤ M)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) :
    ∃ π : ↥U →* Perm Ω,
      (∀ u : ↥U, ConjSpec φ (QuotientGroup.mk (⟨u, hUM u.2⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M)
        (π u)) ∧
      π.ker = (U ⊓ blockCentralizer M L).subgroupOf U := by
  let ψ : ↥U →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM)
  obtain ⟨π, hπ, hker⟩ := exists_action h5 h6 φ ψ
    (fun u => mk_mem_normalizer_barM (hUM u.2) (hUL u.2))
  refine ⟨π, hπ, ?_⟩
  ext u
  rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨u.2, ⟨⟨u, hUM u.2⟩, h, rfl⟩⟩
  · rintro ⟨-, ⟨m, hm, hmu⟩⟩
    have : m = ⟨u, hUM u.2⟩ := Subtype.ext hmu
    subst this
    exact hm

theorem perm_mem_normalizer {Q : Type*} [Group Q] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {C E : Subgroup Q} (φ : ↥C ≃* ↥(alternatingGroup Ω)) (R : Subgroup ↥(alternatingGroup Ω))
    (hR : (E.subgroupOf C).map φ.toMonoidHom = R) {u : Q}
    (huC : u ∈ Subgroup.normalizer (C : Set Q)) (huE : u ∈ Subgroup.normalizer (E : Set Q))
    {σ : Perm Ω} (hσ : ConjSpec φ u σ) (hσA : σ ∈ alternatingGroup Ω) :
    (⟨σ, hσA⟩ : ↥(alternatingGroup Ω)) ∈ Subgroup.normalizer (R : Set ↥(alternatingGroup Ω)) := by
  have hmem : ∀ c : ↥C, φ c ∈ R ↔ (c : Q) ∈ E := by
    intro c
    rw [← hR]
    constructor
    · rintro ⟨c', hc', h⟩
      have : c' = c := φ.injective h
      subst this
      exact hc'
    · intro h
      exact ⟨c, h, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro r
  obtain ⟨c, rfl⟩ := φ.surjective r
  have hcm : u * (c : Q) * u⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 huC c).1 c.2
  have hspec := hσ c ⟨_, hcm⟩ rfl
  have heq : φ ⟨u * (c : Q) * u⁻¹, hcm⟩ =
      (⟨σ, hσA⟩ : ↥(alternatingGroup Ω)) * φ c * (⟨σ, hσA⟩ : ↥(alternatingGroup Ω))⁻¹ :=
    Subtype.ext hspec
  rw [← heq, hmem, hmem]
  exact Subgroup.mem_normalizer_iff.1 huE c

theorem transfer_map {X Y L K : Subgroup G} {A : Type*} [Group A] (hLX : L ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) (hKL : K ≤ L)
    (φ : ↥(barM Y L) ≃* A) (R : Subgroup A)
    (hR : ((barM Y K).subgroupOf (barM Y L)).map φ.toMonoidHom = R) :
    ((barM X K).subgroupOf (barM X L)).map ((Proving.barMEquiv hLX hLY h).trans φ).toMonoidHom =
      R := by
  rw [← hR, ← Proving.barMEquiv_map_subgroupOf hLX hLY h hKL, Subgroup.map_map]
  rfl

section TransferData

variable [Finite G] {M S L : Subgroup G}

theorem pair_data_at_M (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (h : AlternatingGeometry.PairActionData (L ⊔ S) S L n) :
    ∃ φ : ↥(barM M L) ≃* AlternatingGeometry.AltB (Fin n),
      ((barM M (S ⊓ L)).subgroupOf (barM M L)).map φ.toMonoidHom =
        AlternatingGeometry.EA (Fin n) ∧
      ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map φ.toMonoidHom =
        AlternatingGeometry.NA (Fin n) := by
  obtain ⟨φ, hS, hSLb, hact⟩ := h
  have hA' := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hSX : S ≤ L ⊔ S := hA'.twoRadical.1
  have hO2 := AlternatingGeometry.pCore_le_of_isTwoRadicalIn hA'.twoRadical
  have hS' : (((barM (L ⊔ S) S) ⊓ (barM (L ⊔ S) L)).subgroupOf (barM (L ⊔ S) L)).map
      φ.toMonoidHom = AlternatingGeometry.EA (Fin n) := by
    rw [← AlternatingGeometry.barM_inf hO2]; exact hS
  have hN : ((barM (L ⊔ S) (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM (L ⊔ S) L)).map φ.toMonoidHom = AlternatingGeometry.NA (Fin n) := by
    rw [AlternatingGeometry.barM_normalizer_inf hSX hO2]
    exact AlternatingGeometry.map_normalizer_eq_NA (by simpa using hn) φ hS' hSLb hact
  have hcore := Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  exact ⟨(Proving.barMEquiv hL.le le_sup_left hcore).trans φ,
    transfer_map hL.le le_sup_left hcore inf_le_right φ _ hS,
    transfer_map hL.le le_sup_left hcore inf_le_right φ _ hN⟩

theorem quad_data_at_M (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {n : ℕ}
    (h : AlternatingGeometry.QuadBlockData (L ⊔ S) S L n) :
    ∃ φ : ↥(barM M L) ≃* AlternatingGeometry.AltW (Fin n) (Fin 4),
      ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map φ.toMonoidHom =
        AlternatingGeometry.wN AlternatingGeometry.d8 (Fin n) := by
  obtain ⟨φ, hN⟩ := h
  have hcore := Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  exact ⟨(Proving.barMEquiv hL.le le_sup_left hcore).trans φ,
    transfer_map hL.le le_sup_left hcore inf_le_right φ _ hN⟩

end TransferData

end CFSG.HardMathSupport.RichardWeiss.Coordinator
