module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16FieldMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def Input23_16At3Ext : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsExtremalType (K ⧸ Subgroup.center K) →
    ∀ (B : Type) [Group B] [Finite B] (ρ : B →* MulAut K),
      IsElemAbelian 3 (⊤ : Subgroup B) →
      (∃ H : Subgroup B, Nat.card B = 3 * Nat.card H ∧ ∀ h ∈ H, IsFieldAutThree (ρ h)) →
      (⊤ : Subgroup K) ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E

theorem isThreeType_of_extremal {K : Type*} [Group K] (h : IsExtremalType (K ⧸ Subgroup.center K)) :
    IsThreeType K := by
  rcases h with ⟨F, hF, hFin, -, he⟩ | ⟨F, hF, hFin, q, hq, -, -, he⟩
  · exact Or.inl ⟨F, hF, hFin, he⟩
  · exact Or.inr ⟨F, hF, hFin, q, hq, he⟩

theorem isLThreeEpsBar_of_extremal {Y : Type*} [Group Y] (h : IsExtremalType Y) :
    IsLThreeEpsBar Y := by
  rcases h with ⟨F, hF, hFin, h1, he⟩ | ⟨F, hF, hFin, q, hq, h2, h8, he⟩
  · exact Or.inl ⟨F, hF, hFin, by omega, he⟩
  · exact Or.inr ⟨F, hF, hFin, q, hq, by omega, h8, he⟩

theorem i2316e_core {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hT : IsThreeType K)
    (hW : ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 → IsInnDiagThree x → x ≠ 1 →
      x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
          ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i))
    {B : Type} [Group B] [Finite B] (ρ : B →* MulAut K) (hBel : IsElemAbelian 3 (⊤ : Subgroup B))
    (hH : ∃ H : Subgroup B, Nat.card B = 3 * Nat.card H ∧ ∀ h ∈ H, IsFieldAutThree (ρ h)) :
    (⊤ : Subgroup K) ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E := by
  obtain ⟨H, hcardH, hHf⟩ := hH
  obtain ⟨hF1, hF3⟩ := field3Structure_holds K hq hT
  have hp : Nat.Prime 3 := Nat.prime_three
  have hF2 : ∀ α : MulAut K, IsFieldAutThree α → IsInnDiagThree α → α = 1 := fun α h1 h2 =>
    LocalBalance.AutL3.input7_fieldInnDiag_holds K hq α h1 h2
  obtain ⟨k, hk⟩ := exists_card_eq_pow hp hBel
  have hkB : Nat.card B = 3 ^ k := by rwa [Subgroup.card_top] at hk
  have hrankTop : CFSG.Open.pRank 3 (⊤ : Subgroup B) = k := pRank_eq_of_card hp hBel hk
  have hrk : ∀ E : Subgroup B, Nat.card B = 3 * Nat.card E →
      CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E := by
    intro E hE
    have hEel : IsElemAbelian 3 E := isElemAbelian_of_le' hBel le_top
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hkB
        have := Nat.card_pos (α := ↥E)
        omega
      · exact h0
    have hEc : Nat.card E = 3 ^ (k - 1) := by
      have h3 : 3 ^ k = 3 * 3 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hkB] at hE
      omega
    rw [pRank_eq_of_card hp hEel hEc, hrankTop]
  have hmem : ∀ E : Subgroup B, Nat.card B = 3 * Nat.card E → fixedSubgroup ρ E ≤
      ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E :=
    fun E hE => le_iSup₂_of_le E (hrk E hE) le_rfl
  have hB3 : ∀ b : B, b ^ 3 = 1 := fun b => hBel.2 b (Subgroup.mem_top b)
  have hBcomm : ∀ a b : B, a * b = b * a := fun a b =>
    elemAbelian_comm hBel (Subgroup.mem_top a) (Subgroup.mem_top b)
  by_cases htriv : ∀ h ∈ H, ρ h = 1
  · refine le_trans ?_ (hmem H hcardH)
    intro k _ e he
    rw [htriv e he]
    rfl
  push Not at htriv
  obtain ⟨h0, hh0, hρ0⟩ := htriv
  set f : MulAut K := ρ h0 with hfdef
  have hf : IsFieldAutThree f := hHf h0 hh0
  have hf3 : f ^ 3 = 1 := by rw [hfdef, ← map_pow, hB3, map_one]
  set A : Subgroup (MulAut K) := ρ.range with hA
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha⟩ := a.2
      obtain ⟨b', hb⟩ := b.2
      apply Subtype.ext
      show (a : MulAut K) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hBcomm]
    · obtain ⟨x', rfl⟩ := hx
      rw [← map_pow, hB3, map_one]
  set Hb : Subgroup (MulAut K) := H.map ρ with hHb
  have hHbel : IsElemAbelian 3 Hb :=
    isElemAbelian_of_le' hAel (by rintro _ ⟨h, -, rfl⟩; exact ⟨h, rfl⟩)
  have hHbf : ∀ α ∈ Hb, IsFieldAutThree α := by
    rintro _ ⟨h, hh, rfl⟩
    exact hHf h hh
  have hHbcard : Nat.card Hb ≤ 3 := hF3 Hb hHbel hHbf
  have hfHb : f ∈ Hb := ⟨h0, hh0, rfl⟩
  have hHb3 : Nat.card Hb = 3 := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow hp hHbel
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hj
      exact hρ0 (Subgroup.mem_bot.1 (hj ▸ hfHb))
    have : 3 ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj1)
    have h2 : 3 ^ j ≤ 3 := hj ▸ hHbcard
    have : j = 1 := by
      have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (le_antisymm (by simpa using h2) (by simpa using ‹3 ^ 1 ≤ 3 ^ j›) : 3 ^ j = 3 ^ 1)
      exact this
    rw [hj, this]
    norm_num
  by_cases hcyc : ∀ b : B, ρ b ∈ Hb
  ·
    have hAHb : A = Hb := le_antisymm (by rintro _ ⟨b, rfl⟩; exact hcyc b)
      (by rintro _ ⟨h, -, rfl⟩; exact ⟨h, rfl⟩)
    have hcardZ := Subgroup.card_ker_mul_card_range ρ
    have hAcard : Nat.card ρ.range = 3 := by rw [← hA, hAHb]; exact hHb3
    rw [hAcard] at hcardZ
    refine le_trans ?_ (hmem ρ.ker (by omega))
    intro k _ e he
    rw [MonoidHom.mem_ker.1 he]
    rfl
  push Not at hcyc
  obtain ⟨b0, hb0⟩ := hcyc
  have hindexH : H.index = 3 := by
    have := Subgroup.card_mul_index H
    have hHpos : 0 < Nat.card H := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hHpos ?_
    rw [this, hcardH, mul_comm]
  set f' : B →* ↥A := ρ.rangeRestrict with hf'
  have hf's : Function.Surjective f' := ρ.rangeRestrict_surjective
  set H' : Subgroup ↥A := H.map f' with hH'
  have hH'card : Nat.card H' = Nat.card Hb := by
    have : H'.map A.subtype = Hb := by
      rw [hH', Subgroup.map_map]
      rfl
    rw [← this, Subgroup.card_map_of_injective A.subtype_injective]
  have hidx : H'.index ∣ 3 := hindexH ▸ Subgroup.index_map_dvd H hf's
  have hidx1 : H'.index ≠ 1 := by
    intro h1
    have htop : H' = ⊤ := Subgroup.index_eq_one.1 h1
    have : f' b0 ∈ H' := htop ▸ Subgroup.mem_top _
    obtain ⟨h, hh, hfh⟩ := this
    apply hb0
    refine ⟨h, hh, ?_⟩
    exact congrArg Subtype.val hfh
  have hidx3 : H'.index = 3 := by
    rcases (Nat.dvd_prime hp).1 hidx with h | h
    · exact absurd h hidx1
    · exact h
  have hAcard : Nat.card A = 9 := by
    have := Subgroup.card_mul_index H'
    rw [hidx3, hH'card, hHb3] at this
    omega
  have hcardZ : Nat.card B = Nat.card ρ.ker * 9 := by
    have := Subgroup.card_ker_mul_card_range ρ
    rw [← hA, hAcard] at this
    exact this.symm
  have hxex : ∃ x ∈ A, IsInnDiagThree x ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hfield : ∀ α ∈ A, IsFieldAutThree α := by
      intro α hα
      have h3 : α ^ 3 = 1 := hAel.2 α hα
      rcases hF1 α h3 with hd | hfl
      · by_cases h1 : α = 1
        · rw [h1]; exact Or.inl rfl
        · exact absurd (hno α hα hd) h1
      · exact hfl
    have := hF3 A hAel hfield
    omega
  obtain ⟨x, hxA, hxD, hx1⟩ := hxex
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hfA : f ∈ A := ⟨h0, rfl⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    elemAbelian_comm hAel ha hb
  have hfx : f * x = x * f := hAcomm f hfA x hxA
  have hW' := hW f x hf hρ0 hf3 hxD hx1 hx3 hfx
  have hx2 : x ^ 2 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx3
  have hxinv : IsInnDiagThree x⁻¹ := i2326s_isInnDiagThree_inv hxD
  have hfxi : ∀ i < 3, f * x ^ i ≠ 1 := by
    intro i hi h
    interval_cases i
    · simp at h
      exact hρ0 h
    · simp at h
      have : f = x⁻¹ := eq_inv_of_mul_eq_one_left h
      exact hρ0 (hF2 f hf (this ▸ hxinv))
    · rw [hx2] at h
      have hfx' : f = x := by
        have := eq_inv_of_mul_eq_one_left h
        simpa using this
      exact hρ0 (hF2 f hf (hfx' ▸ hxD))
  have hhyper : ∀ y ∈ A, y ≠ 1 → y ^ 3 = 1 →
      Lemma512Ns.fixedSub y ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E := by
    intro y hyA hy1 hy3
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hzA : Subgroup.zpowers y ≤ ρ.range := Subgroup.zpowers_le.2 hyA
    have hc := i2316_card_comap ρ _ hzA
    rw [Nat.card_zpowers, hord] at hc
    rw [← i2316_fixed_comap ρ hyA]
    exact hmem _ (by omega)
  refine hW'.trans (sup_le (hhyper x hxA hx1 hx3) (iSup₂_le fun i hi => ?_))
  have hyA : f * x ^ i ∈ A := A.mul_mem hfA (A.pow_mem hxA i)
  have hy3 : (f * x ^ i) ^ 3 = 1 := by
    have hcm : Commute f (x ^ i) := (Commute.pow_right (show Commute f x from hfx) i)
    rw [hcm.mul_pow, hf3, one_mul, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  exact hhyper _ hyA (hfxi i hi) hy3

theorem input23_16At3Ext_of_pair (hA : BGLFieldPairGeneration) : Input23_16At3Ext := by
  intro K _ _ hq hE B _ _ ρ hBel hH
  refine i2316e_core hq (isThreeType_of_extremal hE) ?_ ρ hBel hH
  intro f x hf hf1 hf3 hx hx1 hx3 hc
  have h := hA K hq (isLThreeEpsBar_of_extremal hE) f x hf hf1 hf3 hx hx1 hx3 hc
  refine h.trans (le_sup_of_le_right (sup_le ?_ ?_))
  · refine (i183_glaPLayer_le 3 _).trans ?_
    refine le_iSup₂_of_le 0 (by norm_num) ?_
    simp
  · refine (i183_glaPLayer_le 3 _).trans ?_
    refine le_iSup₂_of_le 1 (by norm_num) ?_
    simp

end CFSG.HardMathSupport.Solomon.Coordinator
