module

public import CFSG.Goldschmidt75.Sec4Defs
public import CFSG.Goldschmidt75.Sig3Trans

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_odd_of_mem_sylow (T : Sylow 2 G) {X : Subgroup G}
    (hX : Odd (Nat.card X)) {x : G} (hx : x ∈ X) (hxT : x ∈ (T : Subgroup G)) : x = 1 := by
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hxT⟩
  exact eq_one_of_mem_odd_of_two_power hX hx (k := k) (congrArg Subtype.val hk)

theorem card_quotient_lt {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have h1 : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : 1 < Nat.card N := by
    rcases Nat.lt_or_ge 1 (Nat.card N) with h | h
    · exact h
    · exfalso
      apply hN
      rw [← Subgroup.card_eq_one]
      have : 0 < Nat.card N := Nat.card_pos
      omega
  have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  rw [h1]
  exact lt_mul_of_one_lt_right h3 h2

theorem card_lt_of_ne_top {K : Subgroup G} (hK : K ≠ ⊤) : Nat.card K < Nat.card G :=
  lt_of_le_of_ne (Subgroup.card_le_card_group K) fun h => hK ((Subgroup.card_eq_iff_eq_top K).mp h)

theorem exists_sylow_subgroupOf (T : Sylow 2 G) {S₁ S₂ K : Subgroup G} (h₁ : S₁ ≤ T)
    (h₂ : S₂ ≤ T) (hc₁ : fusionStronglyClosed (S₁ : Set G) T)
    (hc₂ : fusionStronglyClosed (S₂ : Set G) T) (hK : S₁ ⊔ S₂ ≤ K) :
    ∃ TH : Sylow 2 K, S₁.subgroupOf K ≤ TH ∧ S₂.subgroupOf K ≤ TH ∧
      fusionStronglyClosed ((S₁.subgroupOf K : Subgroup K) : Set K) TH ∧
      fusionStronglyClosed ((S₂.subgroupOf K : Subgroup K) : Set K) TH := by
  have hp : IsPGroup 2 ((S₁ ⊔ S₂).subgroupOf K) :=
    (T.isPGroup'.to_le (sup_le h₁ h₂)).comap_subtype
  obtain ⟨TH, hTH⟩ := hp.exists_le_sylow
  obtain ⟨T', hT'⟩ := (TH.isPGroup'.map K.subtype).exists_le_sylow
  have hle : ∀ {S : Subgroup G}, S ≤ S₁ ⊔ S₂ → S.subgroupOf K ≤ TH := fun hS x hx =>
    hTH (mem_subgroupOf.mpr (hS (mem_subgroupOf.mp hx)))
  have hST' : ∀ {S : Subgroup G}, S ≤ S₁ ⊔ S₂ → S ≤ T' := fun hS x hx =>
    hT' ⟨⟨x, hK (hS hx)⟩, hle hS (mem_subgroupOf.mpr hx), rfl⟩
  have hcl : ∀ {S : Subgroup G}, S ≤ S₁ ⊔ S₂ → S ≤ T → fusionStronglyClosed (S : Set G) T →
      fusionStronglyClosed ((S.subgroupOf K : Subgroup K) : Set K) TH := by
    intro S hS hST hc a ha k hk
    have h1 : ((k⁻¹ * a * k : K) : G) ∈ (T' : Subgroup G) := hT' ⟨_, hk, rfl⟩
    have h2 := stronglyClosed_of_le_sylow T T' hc (hST' hS) _ ha _ (by simpa using h1)
    exact mem_subgroupOf.mpr (by simpa using h2)
  exact ⟨TH, hle le_sup_left, hle le_sup_right, hcl le_sup_left h₁ hc₁,
    hcl le_sup_right h₂ hc₂⟩

theorem normalClosure_le_normalClosureIn (T : Sylow 2 G) {S K : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T)
    (hK : normalClosure (S : Set G) ≤ K) : normalClosure (S : Set G) ≤ normalClosureIn K S := by
  have hSK : S ≤ K := le_normalClosure.trans hK
  change closure (Group.conjugatesOfSet (S : Set G)) ≤ _
  refine (closure_le _).mpr fun y hy => ?_
  obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
  obtain ⟨c, rfl⟩ := isConj_iff.1 hay
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure T hST hS c⁻¹
  have h1 : c * a * c⁻¹ ∈ conjSub m S := by
    rw [← hmeq, mem_conjSub]
    simpa [mul_assoc] using ha
  rw [mem_conjSub] at h1
  have hmK : m ∈ K := hK hm
  have h2 : (⟨m * (c * a * c⁻¹) * m⁻¹, hSK h1⟩ : K) ∈
      normalClosure ((S.subgroupOf K : Subgroup K) : Set K) :=
    subset_normalClosure (mem_subgroupOf.mpr h1)
  have h3 := (normalClosure_normal (s := ((S.subgroupOf K : Subgroup K) : Set K))).conj_mem _ h2
    (⟨m, hmK⟩ : K)⁻¹
  refine ⟨_, h3, ?_⟩
  simp [mul_assoc]

variable {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.oddCore_eq_bot (h : MinCE G T S₁ S₂) : goldschmidtOddCore G = ⊥ := by
  by_contra hO
  apply h.fail
  have hthm := h.ihG _ (card_quotient_lt hO)
  have key := thmA_quotient hthm T h.le₁ h.le₂ h.sc₁ h.sc₂ h.comm (by
    intro s₁ hs₁ s₂ hs₂ hmem
    have h1 := eq_one_of_mem_odd_of_mem_sylow T odd_card_oddCore hmem
      (mul_mem (inv_mem (h.le₂ hs₂)) (h.le₁ hs₁))
    have heq : s₂ = s₁ := inv_mul_eq_one.mp h1
    have hs : s₁ ∈ S₁ ⊓ S₂ := ⟨hs₁, heq ▸ hs₂⟩
    rw [h.disj, mem_bot] at hs
    rw [hs]
    exact one_mem _)
  rwa [oddCore_quotient_eq_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at key

theorem MinCE.sup_eq_top (h : MinCE G T S₁ S₂) : normalClosure (S₁ : Set G) ⊔ S₂ = ⊤ := by
  by_contra hK
  apply h.fail
  set H₁ := normalClosure (S₁ : Set G)
  set K := H₁ ⊔ S₂
  have hO := h.oddCore_eq_bot
  have hSK : S₁ ⊔ S₂ ≤ K := sup_le_sup_right le_normalClosure _
  obtain ⟨TH, hT₁, hT₂, hc₁, hc₂⟩ := exists_sylow_subgroupOf T h.le₁ h.le₂ h.sc₁ h.sc₂ hSK
  have hA := thmA_in (h.ihG K (card_lt_of_ne_top hK)) TH hT₁ hT₂ hc₁ hc₂ h.comm h.disj
  have hH₁ : H₁ ≤ normalClosureIn K S₁ :=
    normalClosure_le_normalClosureIn T h.le₁ h.sc₁ le_sup_left
  have hS₂ : S₂ ≤ normalClosureIn K S₂ := fun x hx =>
    ⟨⟨x, (le_sup_right : S₂ ≤ K) hx⟩, subset_normalClosure (mem_subgroupOf.mpr hx), rfl⟩
  have h1 : ⁅H₁, S₂⁆ ≤ oddCoreOf K ⊓ H₁ :=
    le_inf ((commutator_mono hH₁ hS₂).trans hA) (commutator_le_left H₁ S₂)
  have h2 : oddCoreOf K ⊓ H₁ ≤ oddCoreOf H₁ := oddCoreOf_inf_le_of_le le_sup_left
  have h3 : oddCoreOf H₁ ≤ goldschmidtOddCore G := oddCoreOf_le_of_normal
  rw [hO] at h3
  have hbot : ⁅H₁, S₂⁆ = ⊥ := le_bot_iff.mp (h1.trans (h2.trans h3))
  have hS₂C : S₂ ≤ centralizer (H₁ : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hbot
  have hH₂C : normalClosure (S₂ : Set G) ≤ centralizer (H₁ : Set G) :=
    normalClosure_le_normal hS₂C
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hH₂C]
  exact bot_le

end CFSG.Goldschmidt75
