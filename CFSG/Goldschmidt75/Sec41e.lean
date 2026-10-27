module

public import CFSG.Goldschmidt75.Sec41d
public import CFSG.Goldschmidt75.ZStar24
public import CFSG.Goldschmidt.Steps.StrongEmb

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.ne_bot (h : MinCE G T S₁ S₂) : S₁ ≠ ⊥ := by
  intro h0
  apply h.fail
  have h1 : normalClosure ({1} : Set G) = ⊥ :=
    le_bot_iff.mp (normalClosure_le_normal (by simp))
  rw [h0, Subgroup.coe_bot, h1, commutator_bot_left]
  exact bot_le

theorem MinCE.le_of_normal (h : MinCE G T S₁ S₂) {N : Subgroup G} (hNn : N.Normal) (hN : N ≠ ⊥) :
    S₁ ≤ N := by
  have hO := h.oddCore_eq_bot
  by_contra hS
  set R := S₁ ⊓ N with hR
  have hRcl : fusionStronglyClosed (R : Set G) T := fun a ha g hg =>
    ⟨h.sc₁ a ha.1 g hg, by simpa using hNn.conj_mem a ha.2 g⁻¹⟩
  have hRlt : Nat.card R < Nat.card S₁ := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun hc => hS ?_
    exact (Subgroup.eq_of_le_of_card_ge inf_le_left hc.ge).symm.le.trans inf_le_right
  have hS₂pos : 0 < Nat.card S₂ := Nat.card_pos
  have hihS := h.ihS T R S₂ (inf_le_left.trans h.le₁) h.le₂ hRcl h.sc₂
    (inf_le_left.trans h.comm) (le_bot_iff.mp (h.disj ▸ inf_le_inf_right _ inf_le_left))
    (Nat.mul_lt_mul_of_pos_right hRlt hS₂pos)
  rw [hO, le_bot_iff] at hihS
  have hR1 : R ≠ ⊥ := by
    intro hR0
    have := hNn
    have h1 := commutator_eq_bot_of_inf_eq_bot T (oddCore_eq_bot_of_normal hO) h.le₁ h.sc₁ hR0
    apply h.not_le_centralizer hNn hN
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact h1
  have hM1 : normalClosure (R : Set G) ≠ ⊥ := fun h0 =>
    hR1 (le_bot_iff.mp (h0 ▸ le_normalClosure))
  apply h.symm.not_le_centralizer normalClosure_normal hM1
  rw [← commutator_eq_bot_iff_le_centralizer]
  exact le_bot_iff.mp (hihS ▸ commutator_mono le_rfl le_normalClosure)

theorem MinCE.isSimpleGroup (h : MinCE G T S₁ S₂) : IsSimpleGroup G := by
  have hnt : Nontrivial G := by
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one S₁).resolve_left h.ne_bot
    exact ⟨⟨x, 1, hx1⟩⟩
  refine ⟨fun N hNn => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    have h₁ := h.le_of_normal hNn hN
    have h₂ := h.symm.le_of_normal hNn hN
    rw [eq_top_iff, ← h.sup_eq_top]
    exact sup_le (normalClosure_le_normal h₁) h₂

theorem MinCE.closure_invClass (h : MinCE G T S₁ S₂) : closure (invClass S₁) = ⊤ := by
  have := h.isSimpleGroup
  have heq : closure (invClass S₁) = normalClosure (invClass S₁) := by
    refine le_antisymm ((closure_le _).mpr subset_normalClosure) ?_
    change closure (Group.conjugatesOfSet (invClass S₁)) ≤ _
    refine closure_mono fun y hy => ?_
    obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    exact invClass_normal S₁ c a ha
  rw [heq]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (invClass S₁)) with h0 | h0
  · exfalso
    obtain ⟨z, hzS, hz2, -⟩ := exists_central_involution T h.le₁ h.sc₁ h.ne_bot
    have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two hz2
    have hzsq : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    have hmem : z ∈ normalClosure (invClass S₁) :=
      subset_normalClosure ⟨1, z, hzS, hz1, hzsq, by group⟩
    rw [h0, mem_bot] at hmem
    exact hz1 hmem
  · exact h0

theorem MinCE.iSup_centralizer_eq_top
    (h : MinCE G T S₁ S₂) :
    (⨆ s : {s : G // s ∈ S₁ ∧ s ≠ 1 ∧ s ^ 2 = 1}, centralizer ({s.1} : Set G)) = ⊤ := by
  have := h.isSimpleGroup
  rcases centralizers_eq_top_or_stronglyEmbedded T h.le₁ h.sc₁ h.ne_bot h.closure_invClass with
    h0 | ⟨M, hM⟩
  · exact h0
  · exfalso
    obtain ⟨z₁, hz₁S, hz₁2, -⟩ := exists_central_involution T h.le₁ h.sc₁ h.ne_bot
    obtain ⟨z₂, hz₂S, hz₂2, -⟩ := exists_central_involution T h.le₂ h.sc₂ h.symm.ne_bot
    obtain ⟨c, hc⟩ := isConj_iff.mp ((CFSG.Goldschmidt.N9 G M hM).2.2 z₁ z₂ hz₁2 hz₂2)
    have h1 : c⁻¹⁻¹ * z₁ * c⁻¹ ∈ (T : Subgroup G) := by
      rw [inv_inv, hc]
      exact h.le₂ hz₂S
    have h2 := h.sc₁ z₁ hz₁S c⁻¹ h1
    rw [inv_inv, hc] at h2
    have h3 : z₂ ∈ S₁ ⊓ S₂ := ⟨h2, hz₂S⟩
    rw [h.disj, mem_bot] at h3
    exact ne_one_of_orderOf_eq_two hz₂2 h3

end CFSG.Goldschmidt75
