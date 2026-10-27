module

public import CFSG.GH74.GLS.Stage2.Local.Prop27Br

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27Br

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.GH74.GLS.Stage2.Local.P34

variable {G : Type} [Group G] [Finite G]

theorem fusionX_of_dihJ {x t' : G} (hDih : P34.DihJ (HBar (Jx x))) (ht'J : t' ∈ Jx x)
    (ht'2 : orderOf t' = 2) (hxt' : IsConj x t') :
    ∀ j ∈ Jx x, orderOf j = 2 → IsConj x j := by
  intro j hj hj2
  obtain ⟨c, -, hcj⟩ := P34.exists_conj_of_involutions hDih ht'J hj ht'2 hj2
  exact hxt'.trans (isConj_iff.2 ⟨c, hcj⟩)

theorem datum_facts
    {z x : G} (h : P27.Datum z x) :
    ∃ (T D₁ D₂ U T₁ : Subgroup G) (q n : ℕ) (t' : G),
      P27.Cfg z x T q ∧ P27.Syl z x T D₁ D₂ U n t' ∧ P27.Tr z x T D₁ D₂ U T₁ ∧
      Ixz z x ≠ ⊥ ∧ x ∉ Jx x ∧ T₁ ⊓ Jx x = ⊥ ∧ Nat.card ↥(T ⊓ Jx x) ≤ Nat.card ↥D₂ ∧
      CFSG.GorensteinWalter.HasDihedralSylowTwo ↥(Jx x) ∧
      ((∃ r : ℕ, Odd r ∧ 3 < r ∧ IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun s => s = r)) ∨
        Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7))) ∧
      (∀ j ∈ Jx x, orderOf j = 2 → IsConj x j) ∧
      (∀ j ∈ Jx x, orderOf j = 2 → IsConj z (x * j)) := by
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hT⟩ := h
  have hx2 : orderOf x = 2 := hC.x_nc.1
  have hxT : x ∈ T := hS.D₁_le hS.x_mem
  have hT₁D₁ : T₁ ≤ D₁ := hT.T₁_le
  have hT₁T : T₁ ≤ T := hT₁D₁.trans hS.D₁_le
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => hS.comm a (hT₁D₁ ha) b hb
  have hT₁c : ∀ a ∈ T₁, ∀ a' ∈ T₁, a * a' = a' * a := by
    intro a ha a' ha'
    have := hT.T₁_cyc
    let _ := IsCyclic.commGroup (α := ↥T₁)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥T₁) ⟨a', ha'⟩)
  have hint : T₁ ⊓ D₂ = ⊥ := le_bot_iff.1 ((inf_le_inf_right D₂ hT₁D₁).trans hS.inter.le)
  have hxJ : x ∉ Jx x := x_not_mem_Jx hx2 hC.T_syl hxT hcomm hT₁c hint hT.x_mem_T₁ hT.S1
  have hT₁J : T₁ ⊓ Jx x = ⊥ :=
    T₁_inf_Jx hx2 hxJ hT.T₁_cyc (hC.T_syl.isPGroup.to_le hT₁T) hT.x_mem_T₁
  have ht'T : t' ∈ T := hS.D₂_le hS.t'_mem
  have ht'I : t' ∈ Ixz z x := hS.U_syl.le hS.t'_U
  have ht'J : t' ∈ Jx x := hT.I_le_J ht'I
  have ht'2 : orderOf t' = 2 := hS.t'_ord
  have hdih := hasDihedralSylowTwo_Jx hC.T_syl hcomm hint hS.D₂_dih hT₁J hT.S1 ht'T ht'J ht'2
  have ht'2' : orderOf (⟨t', ht'J⟩ : ↥(Jx x)) = 2 := by
    rw [← ht'2]
    exact (Subgroup.orderOf_coe _).symm
  have hhat := dihJ_of_perfect_dihedral (Jx_isPerfect x) ht'2' hdih
  have hcard : Nat.card ↥(T ⊓ Jx x) ≤ Nat.card ↥D₂ := by
    have hW : T ⊓ Jx x ≤ T₁ ⊔ D₂ := fun g hg => hT.S1 g hg
    have hWA : (T ⊓ Jx x) ⊓ T₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨⟨-, hgJ⟩, hgT₁⟩
      have : g ∈ T₁ ⊓ Jx x := ⟨hgT₁, hgJ⟩
      rw [hT₁J] at this
      exact this
    obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le_sup hcomm hint hW hWA
    exact Nat.card_le_card_of_injective φ hφ
  have hne : Ixz z x ≠ ⊥ := by
    intro hbot
    have hmem : t' ∈ (⊥ : Subgroup G) := hbot ▸ ht'I
    rw [Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at ht'2
    omega
  exact ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hT, hne, hxJ, hT₁J, hcard, hdih, hhat,
    fusionX_of_dihJ (dihJ_of_hat hhat) ht'J ht'2 hS.t'_conj,
    fusion_of_dihJ (dihJ_of_hat hhat) ht'J ht'2 hS.xt'_conj⟩

end CFSG.GH74.GLS.Stage2.Local.P27Br
