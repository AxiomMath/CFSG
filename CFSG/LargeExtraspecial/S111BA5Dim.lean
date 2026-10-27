module

public import CFSG.LargeExtraspecial.S111BO2
public import CFSG.LargeExtraspecial.S111BA5Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

omit [Finite G] in
theorem two_mul_le_of_dvd_of_lt {a b : ℕ} (hab : a ∣ b) (hlt : a < b) : 2 * a ≤ b := by
  obtain ⟨c, rfl⟩ := hab
  rcases c with _ | _ | c
  · simp at hlt
  · simp at hlt
  · nlinarith

theorem two_mul_card_le_of_lt {H : Type*} [Group H] [Finite H] {E F : Subgroup H} (hEF : E ≤ F)
    {x : H} (hxF : x ∈ F) (hxE : x ∉ E) : 2 * Nat.card E ≤ Nat.card F := by
  refine two_mul_le_of_dvd_of_lt (Subgroup.card_dvd_of_le hEF)
    (lt_of_le_of_ne (Subgroup.card_le_of_le hEF) fun he => hxE ?_)
  rw [Subgroup.eq_of_le_of_card_ge hEF he.ge]
  exact hxF

theorem finrank_fixSub_le_four_mul {L E : Subgroup S.O} (hEL : E ≤ L)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hsq : ∀ x ∈ L, x * x = 1)
    (hcard : Nat.card L = 4 * Nat.card E) :
    finrank (ZMod 2) (fixSub S E) ≤ 4 * finrank (ZMod 2) (fixSub S L) := by
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have hsq' : ∀ x ∈ L, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) * x = 1 := fun x hx =>
    congrArg Subtype.val (hsq x hx)
  obtain ⟨x₁, hx₁L, hx₁E⟩ : ∃ x ∈ L, x ∉ E := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show L ≤ E from hcon)
    omega
  have hV : ∀ v ∈ fixSub S E, (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ fixSub S E := by
    intro v hv
    refine (mem_fixSub S).mpr fun e he => ?_
    rw [← coe_mul_apply, hcomm e (hEL he) x₁ hx₁L, coe_mul_apply, (mem_fixSub S).mp hv e he]
  have h1 := finrank_le_two_mul_finrank_inf_fixSpace (hsq' x₁ hx₁L) hV
  set V₁ := fixSub S E ⊓ fixSpace (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hV₁
  have hV₁L : ∀ v ∈ V₁, ∀ y ∈ L, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V₁ := by
    intro v hv y hy
    obtain ⟨hvE, hvx⟩ := Submodule.mem_inf.mp hv
    refine Submodule.mem_inf.mpr ⟨(mem_fixSub S).mpr fun e he => ?_, ?_⟩
    · rw [← coe_mul_apply, hcomm e (hEL he) y hy, coe_mul_apply, (mem_fixSub S).mp hvE e he]
    · rw [mem_fixSpace] at hvx ⊢
      rw [← coe_mul_apply, hcomm x₁ hx₁L y hy, coe_mul_apply, hvx]
  set H₁ := L ⊓ ptFix S V₁ with hH₁
  have hEH₁ : E ≤ H₁ := fun e he =>
    ⟨hEL he, mem_ptFix.mpr fun v hv => (mem_fixSub S).mp (Submodule.mem_inf.mp hv).1 e he⟩
  have hx₁H₁ : x₁ ∈ H₁ :=
    ⟨hx₁L, mem_ptFix.mpr fun v hv => mem_fixSpace.mp (Submodule.mem_inf.mp hv).2⟩
  have hc1 := two_mul_card_le_of_lt hEH₁ hx₁H₁ hx₁E
  by_cases hLH : L ≤ H₁
  · have hle : V₁ ≤ fixSub S L := fun v hv =>
      (mem_fixSub S).mpr fun y hy => mem_ptFix.mp (hLH hy).2 v hv
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨x₂, hx₂L, hx₂H⟩ : ∃ x ∈ L, x ∉ H₁ := by
    by_contra hcon
    push Not at hcon
    exact hLH hcon
  have h2 := finrank_le_two_mul_finrank_inf_fixSpace (hsq' x₂ hx₂L)
    (fun v hv => hV₁L v hv x₂ hx₂L)
  set V₂ := V₁ ⊓ fixSpace (x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hV₂
  set H₂ := L ⊓ ptFix S V₂ with hH₂
  have hH₁₂ : H₁ ≤ H₂ := fun y hy =>
    ⟨hy.1, mem_ptFix.mpr fun v hv => mem_ptFix.mp hy.2 v (Submodule.mem_inf.mp hv).1⟩
  have hx₂H₂ : x₂ ∈ H₂ :=
    ⟨hx₂L, mem_ptFix.mpr fun v hv => mem_fixSpace.mp (Submodule.mem_inf.mp hv).2⟩
  have hc2 := two_mul_card_le_of_lt hH₁₂ hx₂H₂ hx₂H
  have hH₂L : H₂ = L := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have hle : V₂ ≤ fixSub S L := fun v hv => (mem_fixSub S).mpr fun y hy =>
    mem_ptFix.mp (show y ∈ H₂ by rw [hH₂L]; exact hy).2 v hv
  have := Submodule.finrank_mono hle
  omega

namespace Pair111

variable (P : Pair111 S g A h k k')
  {φ : ↥(S.Lbar k ⊔ S.Lbar k') →* alternatingGroup (Fin 5)}
include P

theorem finrank_fixSub_Lbar : finrank (ZMod 2) (fixSub S (S.Lbar k)) = 1 := by
  rw [P.hy.hyp4.fixSub_eq, finrank_span_singleton (cl_conj_z_ne_zero S P.memQ P.ne)]

theorem card_Lbar_eq_of_A5 (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k)) :
    Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k') := by
  have hk := card_eq_card_inf_mul_card_range le_sup_left φ (hφk.trans (subgroupOf_O2Sub _).symm)
  rw [P.inf_O2Sub_eq] at hk
  set R := (φ.comp (inclusion (le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k'))).range with hR
  have h2 : IsPGroup 2 R :=
    (isPGroup_Lbar S P.memQ).of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have h4 := card_le_four_of_isPGroup_alternating h2
  have hE0 : 0 < Nat.card (Ebar S k k') := Nat.card_pos
  have hR4 : Nat.card R = 4 := by
    by_contra hne
    have h3 : Nat.card R ≤ 3 := by omega
    rw [hk] at hidx
    nlinarith
  rw [hk, hR4, mul_comm]

theorem card_Lbar_eq_of_A5' (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k)) :
    Nat.card (S.Lbar k') = 4 * Nat.card (Ebar S k' k) := by
  rw [← P.card_Ebar_eq, P.hy'.cons.card_Lbar, ← P.hy.cons.card_Lbar]
  exact P.card_Lbar_eq_of_A5 hφk hidx

theorem fix_Ut_of_mem_O2Sub {o : S.O} (ho : o ∈ O2Sub (S.Lbar k ⊔ S.Lbar k')) {u : S.Qt}
    (hu : u ∈ S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) : (o : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
  S9.fix_Ut_of_normal P.hy.hyp4 le_sup_left (O2Sub_le _) (fun _ hx _ hp => O2Sub_normal hx hp)
    (isPGroup_O2Sub _) ho hu

end Pair111

end CFSG.LargeExtraspecial.S11
