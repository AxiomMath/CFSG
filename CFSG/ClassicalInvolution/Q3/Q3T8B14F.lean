module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14E
public import CFSG.ClassicalInvolution.Q3.Q3T8B14L
public import CFSG.ClassicalInvolution.Q3.Q3T8B12
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3T8B01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77.Thompson

section Std8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_std8_of_omegaNbr {K : Subgroup G} (hs : AscStand Ω K)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z) {J : Subgroup G}
    (hJ : J ∈ omegaNbr Ω K) {t : G} (ht : IsUniqueInvolution J t) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8 Ω K J S R T W z t := by
  have hΩ : HypOmegaMod Ω := hs.hyp
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved G Ω hΩ S).1
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { stand := hs
      noTwins := hnt
      hz := hz
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hs.mem hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

end Std8

section Leaf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem mem_of_eq' {H : Subgroup G} {a b : G} (e : a = b) (h : b ∈ H) : a ∈ H := by
  rw [e]
  exact h

private theorem closure_eq_of_mem {A B : Set G} (h₁ : ∀ a ∈ A, a ∈ Subgroup.closure B)
    (h₂ : ∀ b ∈ B, b ∈ Subgroup.closure A) : Subgroup.closure A = Subgroup.closure B :=
  le_antisymm ((Subgroup.closure_le _).mpr h₁) ((Subgroup.closure_le _).mpr h₂)

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
