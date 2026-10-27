module

public import CFSG.ClassicalInvolution.Q3.Q3LFinal

public section

namespace CFSG.ClassicalInvolution.Q3.Q3B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification CFSG.LocalCores CFSG

section Class

variable {Y : Type} [Group Y]

@[expose] def conjClass (L : Subgroup Y) : Set (Subgroup Y) :=
  Set.range fun g : Y => conjSub g L

theorem mem_conjClass_self (L : Subgroup Y) : L ∈ conjClass L :=
  ⟨1, conjSub_one L⟩

theorem exists_conjSub_eq {L M : Subgroup Y} (hM : M ∈ conjClass L) : ∃ g : Y, conjSub g L = M :=
  hM

theorem conjInvariant_conjClass (L : Subgroup Y) : ConjInvariant (conjClass L) := by
  rintro g _ ⟨h, rfl⟩
  exact ⟨g * h, by show conjSub (g * h) L = conjSub g (conjSub h L); rw [conjSub_mul]⟩

theorem conjClass_generated {L : Subgroup Y} (hgen : Subgroup.normalClosure (L : Set Y) = ⊤) :
    (⨆ M ∈ conjClass L, M) = ⊤ := by
  have hn : (⨆ M ∈ conjClass L, M).Normal := normal_biSup (conjInvariant_conjClass L)
  have hLle : L ≤ ⨆ M ∈ conjClass L, M := le_iSup₂_of_le L (mem_conjClass_self L) le_rfl
  rw [eq_top_iff, ← hgen]
  exact Subgroup.normalClosure_le_normal (fun x hx => hLle hx)

theorem inClass3_conjClass {L : Subgroup Y} {z : Y} (hz : IsClassicalMember3 L z)
    (hgen : Subgroup.normalClosure (L : Set Y) = ⊤) : InClass3 (conjClass L) where
  nonempty := ⟨L, mem_conjClass_self L⟩
  conjInvariant := conjInvariant_conjClass L
  generated := conjClass_generated hgen
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g * z * g⁻¹, hz.conj g⟩

theorem not_le_center_of_mem_conjClass {L : Subgroup Y} {z : Y} (hz : IsClassicalMember3 L z)
    {M : Subgroup Y} (hM : M ∈ conjClass L) : ¬ M ≤ Subgroup.center Y := by
  obtain ⟨g, rfl⟩ := hM
  exact (hz.conj g).not_le_center

end Class

section Normal

variable {Y : Type} [Group Y] [Finite Y] {L T N : Subgroup Y}

theorem normal_eq_top_or_le_centralizer (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤)
    (hN : N.Normal) (hLN : L ≤ N) : N = ⊤ ∨ L ≤ Subgroup.centralizer (T : Set Y) := by
  rcases component_normal_subgroup ((isComponent_iff_open T).mpr hT) hN with h | h
  · left
    rw [eq_top_iff, ← hTL]
    exact sup_le h hLN
  · right
    have h' : N ≤ Subgroup.centralizer (T : Set Y) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
    exact hLN.trans h'

omit [Finite Y] in
theorem false_of_commutes_top {z : Y} (hz : IsClassicalMember3 L z) {Λb : Set (Subgroup Y)}
    (hne : Λb.Nonempty) (hb : Λb ⊆ conjClass L)
    (hcomm : Commutes (⊤ : Subgroup Y) (⨆ M ∈ Λb, M)) : False := by
  obtain ⟨M, hM⟩ := hne
  have hMle : M ≤ ⨆ M ∈ Λb, M := le_iSup₂_of_le M hM le_rfl
  refine not_le_center_of_mem_conjClass hz (hb hM) fun x hx => ?_
  rw [Subgroup.mem_center_iff]
  intro g
  exact hcomm g (Subgroup.mem_top g) x (hMle hx)

theorem connected_or_le_centralizer {z : Y} (hz : IsClassicalMember3 L z)
    (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤)
    (hgen : Subgroup.normalClosure (L : Set Y) = ⊤) :
    NonCommConnected (conjClass L) ∨ L ≤ Subgroup.centralizer (T : Set Y) := by
  by_cases hconn : NonCommConnected (conjClass L)
  · exact Or.inl hconn
  right
  obtain ⟨Λ₁, Λ₂, hU, h1, h2, hi1, hi2, hcomm⟩ := exists_split ⟨L, mem_conjClass_self L⟩
    (conjInvariant_conjClass L) (conjClass_generated hgen) hconn
  have hn1 : (⨆ M ∈ Λ₁, M).Normal := normal_biSup hi1
  have hn2 : (⨆ M ∈ Λ₂, M).Normal := normal_biSup hi2
  have hc12 : Commutes (⨆ M ∈ Λ₁, M) (⨆ M ∈ Λ₂, M) := commutes_biSup hcomm
  have hc21 : Commutes (⨆ M ∈ Λ₂, M) (⨆ M ∈ Λ₁, M) := fun a ha b hb => (hc12 b hb a ha).symm
  have hsub1 : Λ₁ ⊆ conjClass L := fun M hM => hU ▸ Or.inl hM
  have hsub2 : Λ₂ ⊆ conjClass L := fun M hM => hU ▸ Or.inr hM
  have hLU : L ∈ Λ₁ ∪ Λ₂ := hU ▸ mem_conjClass_self L
  rcases hLU with hL1 | hL2
  · rcases normal_eq_top_or_le_centralizer hT hTL hn1
      (le_iSup₂_of_le L hL1 le_rfl) with h | h
    · rw [h] at hc12
      exact (false_of_commutes_top hz h2 hsub2 hc12).elim
    · exact h
  · rcases normal_eq_top_or_le_centralizer hT hTL hn2
      (le_iSup₂_of_le L hL2 le_rfl) with h | h
    · rw [h] at hc21
      exact (false_of_commutes_top hz h1 hsub1 hc21).elim
    · exact h

end Normal

section Conn


@[expose] def SolvableMemberInnerTightConn : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (conjClass L) →
          ¬ T ≤ Subgroup.centralizer ({z} : Set Y) → L ≤ T ⊔ Subgroup.centralizer (T : Set Y)

theorem solvableMemberInnerTight_of_conn (h : SolvableMemberInnerTightConn) :
    SolvableMemberInnerTight := by
  intro Y _ _ hBelow hO z L hz T hT hTL
  by_cases hTz : T ≤ Subgroup.centralizer ({z} : Set Y)
  · exact le_sup_of_le_right (hz.le_centralizer_of_le_centralizer hT hTz)
  by_cases hgen : Subgroup.normalClosure (L : Set Y) = ⊤
  · rcases connected_or_le_centralizer hz hT hTL hgen with hconn | hle
    · exact h Y hBelow hO z L hz T hT hTL hgen hconn hTz
    · exact le_sup_of_le_right hle
  · rcases normal_eq_top_or_le_centralizer hT hTL
      (Subgroup.normalClosure_normal (s := (L : Set Y))) Subgroup.le_normalClosure with h1 | h1
    · exact (hgen h1).elim
    · exact le_sup_of_le_right h1

theorem solvableMemberInnerTightConn_of_tight (h : SolvableMemberInnerTight) :
    SolvableMemberInnerTightConn :=
  fun Y _ _ hBelow hO z L hz T hT hTL _ _ _ => h Y hBelow hO z L hz T hT hTL

@[expose] def TightNormalizesComponentConn : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (conjClass L) →
          ¬ T ≤ Subgroup.centralizer ({z} : Set Y) → L ≤ Subgroup.normalizer (T : Set Y)

@[expose] def TightNormalInnerConn : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (conjClass L) →
          T.Normal → ¬ T ≤ Subgroup.centralizer ({z} : Set Y) →
            L ≤ T ⊔ Subgroup.centralizer (T : Set Y)

theorem solvableMemberInnerTightConn_of_normalizes_of_normalInner
    (h1 : TightNormalizesComponentConn) (h2 : TightNormalInnerConn) :
    SolvableMemberInnerTightConn := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn hTz
  have hN : L ≤ Subgroup.normalizer (T : Set Y) := h1 Y hBelow hO z L hz T hT hTL hgen hconn hTz
  have hTn : T.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTL]
    exact sup_le Subgroup.le_normalizer hN
  exact h2 Y hBelow hO z L hz T hT hTL hgen hconn hTn hTz

theorem tightNormalizesComponentConn_of_conn (h : SolvableMemberInnerTightConn) :
    TightNormalizesComponentConn := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn hTz
  exact (h Y hBelow hO z L hz T hT hTL hgen hconn hTz).trans
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))

theorem tightNormalInnerConn_of_conn (h : SolvableMemberInnerTightConn) :
    TightNormalInnerConn := by
  intro Y _ _ hBelow hO z L hz T hT hTL hgen hconn _ hTz
  exact h Y hBelow hO z L hz T hT hTL hgen hconn hTz

end Conn

end CFSG.ClassicalInvolution.Q3.Q3B

