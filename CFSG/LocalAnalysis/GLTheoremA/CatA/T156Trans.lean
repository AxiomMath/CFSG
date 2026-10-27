module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Sub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Composite

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Group Ω] [Finite Ω]

noncomputable def compIso {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) (π : ↥H →* Ω) (hN : ¬ p ∣ Nat.card π.ker) :
    PQuot p X ≃* PQuot p (Y.map π) :=
  (pquotIsoOf hp h).symm.trans (pquotMap hp π hN Y)

theorem compIso_rel {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) (π : ↥H →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {z : ↥H}
    (hz : z ∈ Subgroup.normalizer (Y : Set ↥H)) (x x' : PQuot p X) :
    indRel p X (z : G) x x' ↔
      indRel p (Y.map π) (π z) (compIso hp h π hN x) (compIso hp h π hN x') := by
  obtain ⟨y, rfl⟩ := (pquotIsoOf hp h).surjective x
  obtain ⟨y', rfl⟩ := (pquotIsoOf hp h).surjective x'
  unfold compIso
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [indRel_pquotIsoOf hp h hz y y', indRel_pquotMap hp π hN hz y y']

noncomputable def psimpleIso {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem psimple3_congr {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {p : ℕ}
    {X : Subgroup G₁} {Y : Subgroup G₂} (hp3 : p = 3) (e : PQuot p X ≃* PQuot p Y)
    (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple 3 X) Q ↔ catalogIs (PSimple 3 Y) Q := by
  subst hp3
  exact catalogIs_congr (psimpleIso e)

theorem isTD4_congr {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {p : ℕ}
    {X : Subgroup G₁} {Y : Subgroup G₂} (hp3 : p = 3) (e : PQuot p X ≃* PQuot p Y) :
    IsTD4 3 X ↔ IsTD4 3 Y :=
  psimple3_congr hp3 e _

theorem isChevSimple_congr {r : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsChevSimple r S) : IsChevSimple r T := by
  rcases h with h | h
  · exact Or.inl ((catalogIs_congr e).1 h)
  · exact Or.inr ((catalogIs_congr e).1 h)

theorem card2_compIso {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) (π : ↥H →* Ω) (hN : ¬ p ∣ Nat.card π.ker) :
    card2 p X = card2 p (Y.map π) := by
  unfold card2
  rw [Nat.card_congr (compIso hp h π hN).toEquiv]

theorem centCard2_compIso {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) (π : ↥H →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {z : ↥H}
    (hz : z ∈ Subgroup.normalizer (Y : Set ↥H)) :
    centCard2 p X (z : G) = centCard2 p (Y.map π) (π z) := by
  unfold centCard2
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquiv (compIso hp h π hN).toEquiv
    (fun q => compIso_rel hp h π hN hz q q))

end Composite

section Transfer

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Group Ω] [Finite Ω]

theorem innDiagOn_of_Omega {p : ℕ} {X : Subgroup G} {S' : Subgroup Ω} {A : Subgroup G} {A' : Subgroup Ω}
    (e : PQuot p X ≃* PQuot p S') (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hcorr : ∀ a ∈ A, ∃ a' ∈ A', ∀ x x', indRel p X a x x' ↔ indRel p S' a' (e x) (e x'))
    (h : InnDiagOn p A' S') : InnDiagOn p A X := by
  refine ⟨hAX, ?_⟩
  obtain ⟨-, hM⟩ := h
  refine Y10F.glaMarking_congr e ?_ hM
  intro lab R _ I F θ hθ a ha
  obtain ⟨a', ha', hiff⟩ := hcorr a ha
  obtain ⟨φ, hφ, hφ'⟩ := hθ a' ha'
  exact ⟨φ, hφ, (glaInduces_centerQuot e (indRel p X a) (indRel p S' a') hiff θ φ).2 hφ'⟩

theorem innDiagOn_to_Omega {p : ℕ} {X : Subgroup G} {S' : Subgroup Ω} {A : Subgroup G} {A' : Subgroup Ω}
    (e : PQuot p X ≃* PQuot p S') (hA'S : A' ≤ Subgroup.normalizer (S' : Set Ω))
    (hcorr : ∀ a' ∈ A', ∃ a ∈ A, ∀ x x', indRel p X a x x' ↔ indRel p S' a' (e x) (e x'))
    (h : InnDiagOn p A X) : InnDiagOn p A' S' := by
  refine ⟨hA'S, ?_⟩
  obtain ⟨-, hM⟩ := h
  refine Y10F.glaMarking_congr e.symm ?_ hM
  intro lab R _ I F θ hθ a' ha'
  obtain ⟨a, ha, hiff⟩ := hcorr a' ha'
  obtain ⟨φ, hφ, hφ'⟩ := hθ a ha
  refine ⟨φ, hφ, ?_⟩
  have hrel : ∀ y y', indRel p S' a' y y' ↔ indRel p X a (e.symm y) (e.symm y') := by
    intro y y'
    have := hiff (e.symm y) (e.symm y')
    simp only [MulEquiv.apply_symm_apply] at this
    exact this.symm
  exact (glaInduces_centerQuot e.symm (indRel p S' a') (indRel p X a) hrel θ φ).2 hφ'

theorem fieldOn_to_Omega {p : ℕ} {X : Subgroup G} {S' : Subgroup Ω} {g : G} {w : Ω}
    (e : PQuot p X ≃* PQuot p S') (hw : w ∈ Subgroup.normalizer (S' : Set Ω))
    (hiff : ∀ x x', indRel p X g x x' ↔ indRel p S' w (e x) (e x'))
    (hF : FieldOn p g X) : FieldOn p w S' :=
  ⟨hw, (glaPrimeField_marking_transfer e p _ _ hiff).1 hF.2⟩

end Transfer

section Layers

variable {G : Type} [Group G] [Finite G]

theorem normalizes_inf_centralizer_singleton {L : Subgroup G} {c b : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcb : c * b = b * c) :
    c ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  have inv_comm : ∀ d : G, d * b = b * d → d⁻¹ * b = b * d⁻¹ := by
    intro d hdb
    calc d⁻¹ * b = d⁻¹ * (b * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * b) * d⁻¹ := by rw [hdb]
      _ = b * d⁻¹ := by group
  have fwd : ∀ d : G, d ∈ Subgroup.normalizer (L : Set G) → d * b = b * d →
      ∀ t ∈ L ⊓ Subgroup.centralizer ({b} : Set G),
        d * t * d⁻¹ ∈ L ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro d hdL hdb t ht
    obtain ⟨htL, htC⟩ := Subgroup.mem_inf.1 ht
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hdL t).1 htL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at htC ⊢
    calc (d * t * d⁻¹) * b = d * t * (d⁻¹ * b) := by group
      _ = d * t * (b * d⁻¹) := by rw [inv_comm d hdb]
      _ = d * (t * b) * d⁻¹ := by group
      _ = d * (b * t) * d⁻¹ := by rw [htC]
      _ = (d * b) * t * d⁻¹ := by group
      _ = (b * d) * t * d⁻¹ := by rw [hdb]
      _ = b * (d * t * d⁻¹) := by group
  refine Subgroup.mem_normalizer_iff.2 ?_
  intro t
  constructor
  · exact fwd c hcL hcb t
  · intro ht
    have hc'L : c⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hcL
    have hc'b : c⁻¹ * b = b * c⁻¹ := inv_comm c hcb
    have h1 := fwd c⁻¹ hc'L hc'b _ ht
    have e : c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t := by group
    rw [e] at h1
    exact h1

end Layers

end CFSG.LocalAnalysis.GLTheoremA.T156

end
