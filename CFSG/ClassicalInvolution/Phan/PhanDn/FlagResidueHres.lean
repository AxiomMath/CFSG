module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueJoin
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueA
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueD
public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoTriangulable
import CFSG.Monster.B.GSide.HomotopyLocal
public import CFSG.ClassicalInvolution.Phan.Geometry.Cycles

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan CFSG.Monster.B.Recog CFSG.StandardType
open CFSG.ClassicalGroups.Unitary

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} {m : ℕ}

private theorem ncard_le_of_forall_le {C : Set (Fin (m + 1))} {a b : ℕ}
    (hC : ∀ t ∈ C, a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b) : C.ncard ≤ b + 1 - a := by
  rw [← Set.ncard_image_of_injective C Fin.val_injective, ← Set.ncard_Icc_nat]
  exact Set.ncard_le_ncard (fun _ ⟨t, ht, e⟩ => e ▸ hC t ht) (Set.finite_Icc a b)

theorem flagResidue_hres (E : QuadExt F K σ) (hm : 3 ≤ m)
    (hnd : ∀ W : Submodule K (Fin (m + 1) → K), Nondeg σ W → 4 ≤ Module.finrank K W →
      (ndGraph σ W).Connected ∧ (5 ≤ Module.finrank K W → Triangulable (ndGraph σ W)))
    (hΓ : ∀ m', 2 ≤ m' → m' < m →
      (flagGraph σ m').Connected ∧ (3 ≤ m' → Triangulable (flagGraph σ m')))
    {J : Set (Fin (m + 1))} (hJ : J.Nonempty)
    (hJS : Jᶜ ∉ QTwo.qTwoShape (ggCoxeterMatrixD (m + 1))) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
  refine flagResidue_conn_tri_of_model E hm (fun C hC hCu h3 => ?_) hJ hJS
  have key : ∀ {V : Type} {G : SimpleGraph V}
      (_ : residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ ≃g G), G.Connected →
      (4 ≤ C.ncard → Triangulable G) →
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ).Connected ∧
        (4 ≤ C.ncard →
          Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ)) :=
    fun e hc ht => ⟨e.connected_iff.2 hc,
      fun h4 => (CFSG.Monster.B.GSide.triangulable_iff_of_iso e).2 (ht h4)⟩
  have unit : ∀ {a c : ℕ}, c ≤ m + 1 → C.ncard + 1 ≤ c - a →
      ∀ e : residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ ≃g
        ndGraph σ (coordBlock (m + 1) K a c),
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ).Connected ∧
        (4 ≤ C.ncard →
          Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ)) := by
    intro a c hc hdim e
    have hd := aRes_finrank_coordBlock (K := K) (m + 1) a c (by omega) hc
    obtain ⟨h₁, h₂⟩ := hnd (coordBlock (m + 1) K a c) coordBlock_nondeg (by omega)
    exact key e h₁ fun h4 => h₂ (by omega)
  rcases DConn.cases (by omega) hC hCu (by omega) with
    ⟨a, b, hab, hbm, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨k, hk₁, hk₂, rfl⟩
  · obtain ⟨e⟩ := nonempty_residueGraph_iso_ndGraph_stem E hab hbm
    refine unit (by omega) ?_ e
    have := ncard_le_of_forall_le (C := {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b})
      (a := a) (b := b) fun t ht => ht
    omega
  · obtain ⟨e⟩ := nonempty_residueGraph_iso_ndGraph_last E ha
    refine unit (by omega) ?_ e
    have := ncard_le_of_forall_le (C := {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) + 1 ≤ m})
      (b := m - 1) fun t ht => ⟨ht.1, by have := ht.2; omega⟩
    omega
  · obtain ⟨e⟩ := nonempty_residueGraph_iso_ndGraph_alt E ha
    refine unit (by omega) ?_ e
    have hsub : {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ ((t : ℕ) + 2 ≤ m ∨ (t : ℕ) = m)} ⊆
        {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) + 2 ≤ m} ∪ {Fin.last m} := by
      rintro t ⟨hat, ht | ht⟩
      · exact Or.inl ⟨hat, ht⟩
      · exact Or.inr (Fin.ext ht)
    have h₁ := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    have h₂ := ncard_le_of_forall_le
      (C := {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) + 2 ≤ m}) (b := m - 2)
      fun t ht => ⟨ht.1, by have := ht.2; omega⟩
    rw [Set.ncard_singleton] at h₁
    omega
  ·
    have hcard := ncard_le_of_forall_le (C := {t : Fin (m + 1) | k ≤ (t : ℕ)}) (b := m)
      fun t ht => ⟨ht, by have := t.is_lt; omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + k := ⟨m - k, by omega⟩
    have hset : {t : Fin (m' + k + 1) | k ≤ (t : ℕ)}ᶜ = {j : Fin (m' + k + 1) | (j : ℕ) < k} := by
      ext t
      simp
    rw [hset] at key ⊢
    obtain ⟨e⟩ := nonempty_residueGraph_init_iso E (by omega : 1 ≤ m') hk₁
    obtain ⟨h₁, h₂⟩ := hΓ m' (by omega) (by omega)
    exact key e h₁ fun h4 => h₂ (by omega)

theorem flagResidue_hres_of_card_four (E : QuadExt F K σ) (hm : 3 ≤ m)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hΓ : ∀ m', 2 ≤ m' → m' < m →
      (flagGraph σ m').Connected ∧ (3 ≤ m' → Triangulable (flagGraph σ m')))
    {J : Set (Fin (m + 1))} (hJ : J.Nonempty)
    (hJS : Jᶜ ∉ QTwo.qTwoShape (ggCoxeterMatrixD (m + 1))) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) :=
  flagResidue_hres E hm
    (fun W hW h4 => ⟨ndGraph_connected hσ (W := W) hW h4,
      fun h5 => ndGraph_triangulable hσ hK hW h5⟩) hΓ hJ hJS

end CFSG.ClassicalInvolution.PhanDn
