module

public import CFSG.GH74.GLS.Stage2.Local.P27.QIdG
public import CFSG.GH74.GLS.Stage2.Local.Prop27BrFacts
public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt
public import CFSG.GH74.GLS.Stage2.Local.P27.DatumPlus

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27

variable {G : Type} [Group G] [Finite G]

theorem dich_of_datum
    {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁) :
    (FullCPsp4 x q ∧ Nat.card ↥(T ⊓ Jx x) = Nat.card ↥U) ∨
      (FullCL4 x q ∧ Nat.card ↥(T ⊓ Jx x) = 2 * Nat.card ↥U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hcfg.x_mem).symm
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hcfg.z_central.1, pow_two] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hhat, -, -⟩ :=
    P27Br.datum_facts ⟨T, D₁, D₂, U, T₁, q, n, t', hcfg, hsyl, htr⟩
  have hK : (∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧
        Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* L2 F)) ∨
      Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7)) := by
    rcases hhat with ⟨r, hr, hr3, F, _, _, hF, ⟨e⟩⟩ | hA
    · exact Or.inl ⟨F, inferInstance, inferInstance, ⟨hF ▸ hr, hF ▸ hr3⟩, ⟨e⟩⟩
    · exact Or.inr hA
  have ht : ∃ t ∈ Ixz z x, orderOf t = 2 := ⟨t', hsyl.U_syl.le hsyl.t'_U, hsyl.t'_ord⟩
  have hmain := qdich_of_datum hzx hzz htr.I_le_J hK ht hcfg.q_odd hcfg.q_gt hcfg.I_L2
  have hUc : Nat.card ↥U = 2 ^ padicValNat 2 (Nat.card ↥(Ixz z x)) := by
    rw [hsyl.U_syl.card_eq, Nat.factorization_def _ Nat.prime_two]
  have hWc : Nat.card ↥(T ⊓ Jx x) = 2 ^ padicValNat 2 (Nat.card ↥(Jx x)) := by
    rw [(P27Br.Jx_sylow hcfg.T_syl).card_eq, Nat.factorization_def _ Nat.prime_two]
  rcases hmain with ⟨hL2, hv⟩ | ⟨hv, hrest⟩
  · left
    refine ⟨hL2, ?_⟩
    rw [hWc, hUc, hv]
  · right
    refine ⟨hrest, ?_⟩
    rw [hWc, hUc, hv, pow_succ, mul_comm]

theorem fullCL4_of_datum
    {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁)
    (hge : 2 * Nat.card ↥U ≤ Nat.card ↥(T ⊓ Jx x)) : FullCL4 x q := by
  rcases dich_of_datum hcfg hsyl htr with ⟨-, h1⟩ | ⟨h, -⟩
  · exfalso
    have : 0 < Nat.card ↥U := Nat.card_pos
    omega
  · exact h

theorem fullCL4_of_extra
    {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t') (htr : Tr z x T D₁ D₂ U T₁)
    (hex : Extra z x T D₁ D₂ U t') (hD₂ : Nat.card ↥D₂ = 2 * Nat.card ↥U) : FullCL4 x q :=
  fullCL4_of_datum hcfg hsyl htr (le_of_eq (by rw [hex.T_inf_J, hD₂]))

end CFSG.GH74.GLS.Stage2.Local.P27.QId
