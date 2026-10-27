module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem Ivk73Cfg.u2_data_subgroupOf
    (h : Ivk73Cfg N L K Q) :
    (HasL2Model (↥(K.subgroupOf L) ⧸ pPrimeCore 2 ↥(K.subgroupOf L)) Odd ∨
      Nonempty ((↥(K.subgroupOf L) ⧸ pPrimeCore 2 ↥(K.subgroupOf L)) ≃*
        alternatingGroup (Fin 7))) ∧ Odd (Nat.card (center ↥(K.subgroupOf L))) := by
  let ψ : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe h.K_le
  let e2 : (↥(K.subgroupOf L) ⧸ pPrimeCore 2 ↥(K.subgroupOf L)) ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
  have hkb := h.kbar_cases
  have hodd := odd_center_K hkb
  refine ⟨?_, ?_⟩
  · rcases hkb with hL | he
    · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv e2.symm hL)
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨e2.trans e⟩
  · have h1 : (center ↥(K.subgroupOf L)).map ψ.toMonoidHom = center ↥K := Subgroup.map_center_eq ψ
    rw [← h1, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective] at hodd
    exact hodd

theorem Ivk73Cfg.false_of_comp_u2
    (h : Ivk73Cfg N L K Q)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1)
    (hcomp : ∀ y : ↥L, y * y = 1 → y ≠ 1 → ∀ B : Subgroup ↥L,
      IsCompIn (centralizer ({y} : Set ↥L)) B →
      (HasL2Model (↥B ⧸ pPrimeCore 2 ↥B) Odd ∨
        Nonempty ((↥B ⧸ pPrimeCore 2 ↥B) ≃* alternatingGroup (Fin 7))) →
      Odd (Nat.card (center ↥B)) → False) : False := by
  obtain ⟨u, huQ, hu2, huL⟩ := h.exists_involution_mem_L hOut
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  let y : ↥L := ⟨u, huL⟩
  have hy2 : y * y = 1 := Subtype.ext huu
  have hy1 : y ≠ 1 := by
    intro h1
    have : u = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hu2
    omega
  have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
  have hterm := h.terminal u hu2 huC
  have hKM : K ≤ centralizer ({u} : Set N) ⊓ L := le_inf hterm.1 h.K_le
  have hM : IsCompIn (centralizer ({u} : Set N) ⊓ L) K :=
    LU.Local.isCompIn_mono' hterm hKM inf_le_left
  have hB : IsCompIn (centralizer ({y} : Set ↥L)) (K.subgroupOf L) := by
    rw [← subgroupOf_centralizer_inf_eq u huL]
    exact ⟨Subgroup.subgroupOf_mono L hKM,
      (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({u} : Set N) ⊓ L) (H := L)
        inf_le_right).2 hM.2⟩
  obtain ⟨hU, hZ⟩ := h.u2_data_subgroupOf
  exact hcomp y hy2 hy1 _ hB hU hZ

end CFSG.GH74.GLS.IVK
