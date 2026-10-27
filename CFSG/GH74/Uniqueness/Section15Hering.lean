module

public import CFSG.GH74.Uniqueness.Section15HeringCaseB
public import CFSG.GH74.Uniqueness.Section15HeringL32
public import CFSG.GH74.Uniqueness.Section15HeringEnd4
public import CFSG.GH74.Uniqueness.Section15HeringStmt

public section

namespace CFSG.GH74.Uniqueness

open Subgroup MulAction Hering

universe u

theorem Hering.hering32_field {F : Type*} [Field F] [Finite F] {m : ℕ} :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [MulAction G F], Nat.card G = n →
      Hyp G F m → HasRegularNormal G F ∨
        (m = 3 ∧ Nonempty (G ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ hn hG
  by_contra hcon
  obtain ⟨hnoReg, hnotGL⟩ := not_or.mp hcon
  have hC : CE G F m :=
    { toHyp := hG
      noReg := hnoReg
      notGL := hnotGL
      ih := fun X₀ hX₀ hX₀hyp => ih (Nat.card X₀)
        (by
          rw [← hn, ← Subgroup.card_top (G := G)]
          exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hX₀))
        X₀ rfl hX₀hyp }
  obtain ⟨p, hp, hp2, hpΓ⟩ := hC.exists_odd_prime_dvd_card_stab01
  obtain ⟨hmp, P, hE⟩ := hC.endHyp hp hp2 hpΓ
  have h3 := hE.three_le
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · have hp3 : p = 3 := by
      interval_cases p
      · rfl
      · norm_num at hp
    subst hp3
    exact hnotGL ⟨hmp, hE.nonempty_mulEquiv_GL⟩
  · exact hE.false_of_five_le hge

theorem hering32 {G : Type*} [Group G] [Finite G] {Γ : Type*} [MulAction G Γ] [FaithfulSMul G Γ]
    {m : ℕ} (hm : 2 ≤ m) {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m) (e : Γ ≃ F)
    (h2 : MulAction.IsMultiplyPretransitive G Γ 2)
    (hstab : ∀ g : G, g • e.symm 0 = e.symm 0 →
      ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x : F, e (g • e.symm x) = a * σ x)
    (hK : ∀ a : Fˣ, ∃ g : G, g • e.symm 0 = e.symm 0 ∧ ∀ x : F, e (g • e.symm x) = a * x) :
    (∃ N : Subgroup G, N.Normal ∧ ∀ γ δ : Γ, ∃! n : N, (n : G) • γ = δ) ∨
      (m = 3 ∧ Nonempty (G ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
  let act : MulAction G F := e.symm.mulAction G
  have hsmul : ∀ (g : G) (x : F), g • x = e (g • e.symm x) := fun g x => rfl
  have hHyp : Hyp G F m :=
    { two_le := hm
      card := hF
      faithful := ⟨fun {g₁ g₂} h => FaithfulSMul.eq_of_smul_eq_smul (α := Γ) fun γ => by
        have := h (e γ)
        rw [hsmul, hsmul, e.symm_apply_apply] at this
        exact e.injective this⟩
      twoTrans := by
        rw [is_two_pretransitive_iff]
        intro a b c d hab hcd
        obtain ⟨g, hg1, hg2⟩ := (is_two_pretransitive_iff.mp h2) (e.symm.injective.ne hab)
          (e.symm.injective.ne hcd)
        exact ⟨g, by rw [hsmul, hg1, e.apply_symm_apply], by rw [hsmul, hg2, e.apply_symm_apply]⟩
      stab := fun g hg => by
        have h1 : g • e.symm 0 = e.symm 0 := by
          have := congrArg e.symm hg
          rwa [hsmul, e.symm_apply_apply] at this
        obtain ⟨a, σ, h⟩ := hstab g h1
        exact ⟨a, σ, fun x => by rw [hsmul]; exact h x⟩
      mul := fun a => by
        obtain ⟨g, -, hg⟩ := hK a
        exact ⟨g, fun x => by rw [hsmul]; exact hg x⟩ }
  rcases Hering.hering32_field _ G rfl hHyp with ⟨N, hN, hreg⟩ | h
  · left
    refine ⟨N, hN, fun γ δ => ?_⟩
    obtain ⟨n, hn, huniq⟩ := hreg (e γ) (e δ)
    refine ⟨n, ?_, fun n' hn' => huniq n' ?_⟩
    · have := hn
      rw [hsmul, e.symm_apply_apply] at this
      exact e.injective this
    · have hn'' : (n' : G) • γ = δ := hn'
      show (n' : G) • e γ = e δ
      rw [hsmul, e.symm_apply_apply, hn'']
  · exact Or.inr h

theorem hering32_stmt : Hering32Stmt :=
  fun _ _ _ _ _ _ _ hm _ _ _ hF e h2 hstab hK => hering32 hm hF e h2 hstab hK

end CFSG.GH74.Uniqueness
