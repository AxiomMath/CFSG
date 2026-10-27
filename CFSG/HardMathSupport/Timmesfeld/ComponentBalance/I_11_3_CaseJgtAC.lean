module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_RedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

theorem t113_T_le_normalizer_K {B L T : Subgroup Q}
    (h : ∀ g ∈ B, ∀ t ∈ T, ∃ b ∈ B, GLBConj (g * t) L = GLBConj b L) :
    T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q) := by
  have key : ∀ t ∈ T, GLBConj t (t113K B L) ≤ t113K B L := by
    intro t ht
    have : GLBConj t (t113K B L) = ⨆ g ∈ B, GLBConj t (GLBConj g L) := by
      simp only [t113K, GLBConj, Subgroup.map_iSup]
    rw [this]
    refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    obtain ⟨b, hb, e⟩ := h g hg t ht
    rw [e]
    exact le_iSup₂_of_le b hb le_rfl
  intro t ht
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key t ht) ?_
  have h2 := gLBConj_mono t (key t⁻¹ (T.inv_mem ht))
  rwa [gLBConj_gLBConj_inv] at h2

theorem t113_h_of_T_le_normalizer {B L T : Subgroup Q}
    (hBT : B ≤ Subgroup.normalizer (T : Set Q)) (hTL : T ≤ Subgroup.normalizer (L : Set Q)) :
    ∀ g ∈ B, ∀ t ∈ T, ∃ b ∈ B, GLBConj (g * t) L = GLBConj b L := by
  intro g hg t ht
  refine ⟨g, hg, ?_⟩
  have hgt : g * t * g⁻¹ ∈ T := ((Subgroup.mem_normalizer_iff.1 (hBT hg)) t).1 ht
  have e : g * t = (g * t * g⁻¹) * g := by group
  rw [e, ← gLBConj_gLBConj, mem_normalizer_iff_gLBConj_eq.1 (hTL hgt)]

theorem t113_not_le_normalizer_L {B L T : Subgroup Q} {x : Q} (R : Red113 B L x T)
    (hK : ¬ T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q)) :
    ¬ T ≤ Subgroup.normalizer (L : Set Q) := fun h =>
  hK (t113_T_le_normalizer_K (t113_h_of_T_le_normalizer R.T_norm h))

theorem t113_A_centralizes_T {B L T : Subgroup Q} {x : Q} (R : Red113 B L x T)
    (hK : ¬ T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q)) :
    ∀ a ∈ t113A B L, ∀ t ∈ T, a * t = t * a := by
  have Tr := R.tri
  have hBT : ∀ b ∈ B, ∀ u ∈ T, b * u * b⁻¹ ∈ T := fun b hb u hu =>
    ((Subgroup.mem_normalizer_iff.1 (R.T_norm hb)) u).1 hu
  by_contra hcon
  push Not at hcon
  obtain ⟨a0, ha0, t, ht, hne⟩ := hcon
  have hCTbot : T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) = ⊥ := by
    have hn : B ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) : Subgroup Q) : Set Q) := by
      have fwd : ∀ b ∈ B, ∀ h ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q),
          b * h * b⁻¹ ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) := by
        intro b hb h hh
        refine ⟨hBT b hb h hh.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
        have hc2 : Commute a h := Subgroup.mem_centralizer_iff.1 hh.2 a ha
        have hab : Commute a b := Tr.comm_B ha.2 hb
        exact ((hab.mul_right hc2).mul_right hab.inv_right).eq
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fwd b hb h, fun h' => ?_⟩
      have := fwd b⁻¹ (B.inv_mem hb) _ h'
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [e] at this
    rcases R.T_min _ inf_le_left hn with h | h
    · exact h
    · exfalso
      have : t ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) := by
        rw [h]; exact ht
      exact hne (Subgroup.mem_centralizer_iff.1 this.2 a0 ha0)
  have hCT : ∀ u ∈ T, (∀ a ∈ t113A B L, a * u = u * a) → u = 1 := by
    intro u hu hc
    have : u ∈ T ⊓ Subgroup.centralizer ((t113A B L : Subgroup Q) : Set Q) :=
      ⟨hu, Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha⟩
    rw [hCTbot, Subgroup.mem_bot] at this
    exact this
  have hTL := t113_not_le_normalizer_L R hK
  have hT1 : ∀ u ∈ T, u ∈ Subgroup.normalizer (L : Set Q) → u = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨τ, hτT, hτN, hτ1⟩ := hcon
    set T1 : Subgroup Q := T ⊓ Subgroup.normalizer (L : Set Q) with hT1def
    have hcard : Nat.card T1 ≤ 2 := by
      have hrel := Subgroup.relIndex_mul_card (H := T1) (K := T)
      have hinf : T1 ⊓ T = T1 := inf_eq_left.2 inf_le_left
      rw [hinf] at hrel
      have hr1 : T1.relIndex T ≠ 1 := fun h1 =>
        hTL (fun u hu => (Subgroup.relIndex_eq_one.1 h1 hu).2)
      have hpos : 0 < Nat.card T1 := Nat.card_pos
      have hTpos : 0 < Nat.card T := Nat.card_pos
      have hr0 : T1.relIndex T ≠ 0 := by
        intro h0
        rw [h0] at hrel
        omega
      have hr2 : 2 ≤ T1.relIndex T := by omega
      have := R.T_card
      by_contra hgt
      push Not at hgt
      nlinarith
    have hfix : ∀ a ∈ t113A B L, a * τ = τ * a := by
      intro a ha
      have hu : a * τ * a⁻¹ ∈ T1 := by
        refine ⟨hBT a ha.2 τ hτT, ?_⟩
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha.1 hτN) (Subgroup.inv_mem _ ha.1)
      have hu1 : a * τ * a⁻¹ ≠ 1 := by
        intro h1
        apply hτ1
        calc τ = a⁻¹ * (a * τ * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      by_contra hne'
      have hune : a * τ * a⁻¹ ≠ τ := fun h2 => hne' (by
        calc a * τ = (a * τ * a⁻¹) * a := by group
          _ = τ * a := by rw [h2])
      have h3 : 2 < Nat.card T1 := by
        have := Fintype.ofFinite ↥T1
        rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
        refine ⟨⟨1, T1.one_mem⟩, ⟨τ, ⟨hτT, hτN⟩⟩, ⟨a * τ * a⁻¹, hu⟩, ?_, ?_, ?_⟩
        · intro h; exact hτ1 (congrArg Subtype.val h).symm
        · intro h; exact hu1 (congrArg Subtype.val h).symm
        · intro h; exact hune (congrArg Subtype.val h).symm
      omega
    exact hτ1 (hCT τ hτT hfix)
  have hrel := R.hidx_all (GLBConj t L) (Tr.comp_conj t)
  have hsub : Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B ≤
      t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) := by
    rintro b ⟨hbM, hbB⟩
    have hbM' := mem_normalizer_iff_gLBConj_eq.1 hbM
    have h1 : t * b * t⁻¹ ∈ Subgroup.normalizer (L : Set Q) := by
      rw [mem_normalizer_iff_gLBConj_eq]
      have := congrArg (GLBConj t⁻¹) hbM'
      simpa only [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] using this
    have hτT : t * b * t⁻¹ * b⁻¹ ∈ T := by
      have : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
      rw [this]
      exact T.mul_mem ht (hBT b hbB t⁻¹ (T.inv_mem ht))
    have hτb : (t * b * t⁻¹ * b⁻¹) * b ∈ Subgroup.normalizer (L : Set Q) := by
      have : (t * b * t⁻¹ * b⁻¹) * b = t * b * t⁻¹ := by group
      rw [this]; exact h1
    have hτ1 : t * b * t⁻¹ * b⁻¹ = 1 := by
      by_contra hτ1
      set τ := t * b * t⁻¹ * b⁻¹ with hτ
      have e1 : GLBConj τ L = GLBConj b⁻¹ L := by
        have h2 := mem_normalizer_iff_gLBConj_eq.1 hτb
        rw [← gLBConj_gLBConj] at h2
        have h3 := congrArg (GLBConj b⁻¹) h2
        rwa [gLBConj_inv_gLBConj] at h3
      apply hτ1
      apply hCT τ hτT
      intro a ha
      have hab : a * b⁻¹ = b⁻¹ * a := (Tr.comm_B ha.2 (B.inv_mem hbB))
      have e2 : GLBConj (τ * a) L = GLBConj τ L := by
        rw [← gLBConj_gLBConj, e1, gLBConj_gLBConj, ← hab, ← gLBConj_gLBConj,
          mem_normalizer_iff_gLBConj_eq.1 ha.1]
      have h3 : τ * a * τ⁻¹ ∈ Subgroup.normalizer (L : Set Q) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        have := congrArg (GLBConj τ⁻¹) e2
        simpa only [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] using this
      have h4 : τ * a * τ⁻¹ * a⁻¹ = 1 := by
        refine hT1 _ ?_ (Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ ha.1))
        have : τ * a * τ⁻¹ * a⁻¹ = τ * (a * τ⁻¹ * a⁻¹) := by group
        rw [this]
        exact T.mul_mem hτT (hBT a ha.2 τ⁻¹ (T.inv_mem hτT))
      have h5 : τ * a * τ⁻¹ = a := mul_inv_eq_one.1 h4
      exact (mul_inv_eq_iff_eq_mul.1 h5).symm
    have h5 : t * b * t⁻¹ = b := mul_inv_eq_one.1 hτ1
    refine ⟨⟨?_, hbB⟩, ?_⟩
    · rw [← h5]; exact h1
    · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h5).symm
  have hcardA := Tr.card_A
  have hrelm := Subgroup.relIndex_mul_card
    (H := Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q)) (K := B)
  have hle3 : (Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q)).relIndex B ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hrel
  have hA_le : Nat.card (t113A B L) ≤
      Nat.card ↥(Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B) := by
    have := Nat.mul_le_mul_right
      (Nat.card ↥(Subgroup.normalizer ((GLBConj t L : Subgroup Q) : Set Q) ⊓ B)) hle3
    omega
  have hAt_le := Subgroup.card_le_of_le hsub
  have heq : t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) = t113A B L :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_trans hA_le hAt_le)
  have hmem : a0 ∈ t113A B L ⊓ Subgroup.centralizer ({t} : Set Q) := by
    rw [heq]; exact ha0
  exact hne (Subgroup.mem_centralizer_singleton_iff.1 hmem.2)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
