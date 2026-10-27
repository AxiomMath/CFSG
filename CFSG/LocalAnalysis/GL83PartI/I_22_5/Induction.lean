module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Gen

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def centGen (p k : ℕ) (B L : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ B) (_ : p ^ k ≤ Nat.card E), L ⊓ Subgroup.centralizer (E : Set G)

theorem le_centGen {k : ℕ} {B L E : Subgroup G} (hEB : E ≤ B) (hk : p ^ k ≤ Nat.card E) :
    L ⊓ Subgroup.centralizer (E : Set G) ≤ centGen p k B L :=
  le_iSup₂_of_le E hEB (le_iSup (fun _ : p ^ k ≤ Nat.card E =>
    L ⊓ Subgroup.centralizer (E : Set G)) hk)

theorem le_centGen_zero (B L : Subgroup G) : L ≤ centGen p 0 B L := by
  refine le_trans ?_ (le_centGen (E := ⊥) bot_le (by simp))
  intro x hx
  refine ⟨hx, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro h hh
  have : h = 1 := Subgroup.mem_bot.1 hh
  rw [this, one_mul, mul_one]

theorem index_cases (hp : p.Prime) {a b c k r : ℕ} (hr : 1 ≤ r) (hca : c ∣ a) (hab : a ∣ b)
    (ha : ∃ i, a = p ^ i) (hb : ∃ i, b = p ^ i) (hc : ∃ i, c = p ^ i)
    (hB : p ^ (k + 1 + r) ≤ b) (hA : a ≤ p ^ r * c) (hC : c ≤ p ^ k) :
    p ^ 2 * a ≤ b ∨ (b = p * a ∧ c < a) := by
  obtain ⟨ia, rfl⟩ := ha
  obtain ⟨ib, rfl⟩ := hb
  obtain ⟨ic, rfl⟩ := hc
  have hp1 := hp.one_lt
  have e1 : ic ≤ ia := (Nat.pow_dvd_pow_iff_le_right hp1).1 hca
  have e2 : ia ≤ ib := (Nat.pow_dvd_pow_iff_le_right hp1).1 hab
  have e3 : k + 1 + r ≤ ib := (Nat.pow_le_pow_iff_right hp1).1 hB
  have e4 : ia ≤ r + ic := by
    refine (Nat.pow_le_pow_iff_right hp1).1 ?_
    rw [pow_add]
    exact hA
  have e5 : ic ≤ k := (Nat.pow_le_pow_iff_right hp1).1 hC
  by_cases h : ia + 2 ≤ ib
  · left
    calc p ^ 2 * p ^ ia = p ^ (ia + 2) := by ring
      _ ≤ p ^ ib := Nat.pow_le_pow_right hp.pos h
  · right
    have hib : ib = ia + 1 := by omega
    refine ⟨by rw [hib]; ring, ?_⟩
    exact Nat.pow_lt_pow_right hp1 (by omega)

section Main

variable [Finite G] [Fact p.Prime]

theorem IsFam.layer_le_centGen (k : ℕ) : ∀ {B : Subgroup G} {𝒦 : Set (Subgroup G)},
    IsFam p B 𝒦 → ∀ {K₀ : Subgroup G}, K₀ ∈ 𝒦 → ∀ {r : ℕ}, 1 ≤ r →
    p ^ (k + r) ≤ Nat.card B → Nat.card (stab B K₀) ≤ p ^ r * Nat.card (cen B K₀) →
    layer 𝒦 ≤ centGen p k B (layer 𝒦) := by
  induction k with
  | zero =>
    intro B _ _ _ _ _ _ _ _
    exact le_centGen_zero B _
  | succ k ih =>
    intro B 𝒦 hF K₀ hK₀ r hr hB hA
    have hp := (Fact.out : p.Prime)
    by_cases hC : p ^ (k + 1) ≤ Nat.card (cen B K₀)
    · refine le_trans ?_ (le_centGen (inf_le_left : cen B K₀ ≤ B) hC)
      refine le_inf le_rfl (iSup₂_le fun K hK x hx => ?_)
      exact Subgroup.mem_centralizer_iff.2 fun b hb => hF.cen_comm hK₀ hb hK x hx
    · have hCB : cen B K₀ ≤ B := inf_le_left
      have hAB : stab B K₀ ≤ B := inf_le_left
      have hCA : cen B K₀ ≤ stab B K₀ := cen_le_stab B K₀
      have hCle : Nat.card (cen B K₀) ≤ p ^ k := by
        obtain ⟨j, hj⟩ := exists_card_eq_pow (elem_mono hF.elem hCB)
        rw [hj] at hC ⊢
        have : j < k + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (not_le.1 hC)
        exact Nat.pow_le_pow_right hp.pos (by omega)
      have hnum := index_cases hp hr (Subgroup.card_dvd_of_le hCA) (Subgroup.card_dvd_of_le hAB)
        (exists_card_eq_pow (elem_mono hF.elem hAB)) (exists_card_eq_pow hF.elem)
        (exists_card_eq_pow (elem_mono hF.elem hCB)) hB hA hCle
      have hnorm : layer 𝒦 ≤ normJoin hF K₀ := by
        rcases hnum with h | ⟨h1, h2⟩
        · exact hF.layer_le_normJoin_two hK₀ h
        · exact hF.layer_le_normJoin_one hK₀ h1
            (fun hle => absurd (Subgroup.card_le_of_le hle) (not_le.2 h2))
      refine hnorm.trans (iSup₂_le fun M hM => ?_)
      obtain ⟨b, hb, hbA, hMb⟩ := hM
      refine (le_layer hMb).trans ?_
      obtain ⟨B', hAB', hB'B, hbB', hsup⟩ := exists_complement hF.elem hAB hb hbA
      have hFN := hF.isFam_normFam hK₀ hb hbA hB'B hsup
      have hcardB : Nat.card B = p * Nat.card B' :=
        card_eq_of_complement hF.elem hB'B hb hbB' hsup
      have hM₀ : normSub (hF.normComm hK₀ hb hbA) ∈ normFam hF b hb :=
        normSub_mem_normFam hF hK₀ hb hbA
      have hB'big : p ^ (k + r) ≤ Nat.card B' := by
        have h1 : p * p ^ (k + r) ≤ p * Nat.card B' := by
          rw [← hcardB, ← pow_succ']
          calc p ^ (k + r + 1) = p ^ (k + 1 + r) := by ring_nf
            _ ≤ Nat.card B := hB
        exact Nat.le_of_mul_le_mul_left h1 hp.pos
      have hA' : Nat.card (stab B' (normSub (hF.normComm hK₀ hb hbA))) ≤
          p ^ r * Nat.card (cen B' (normSub (hF.normComm hK₀ hb hbA))) :=
        calc Nat.card (stab B' (normSub (hF.normComm hK₀ hb hbA)))
            ≤ Nat.card (stab B K₀) :=
              Subgroup.card_le_of_le (hF.stab_normSub_le hK₀ hb hbA hAB' hB'B hbB')
          _ ≤ p ^ r * Nat.card (cen B K₀) := hA
          _ ≤ p ^ r * Nat.card (cen B' (normSub (hF.normComm hK₀ hb hbA))) :=
              Nat.mul_le_mul_left _
                (Subgroup.card_le_of_le (hF.cen_le_cen_normSub hK₀ hb hbA hAB'))
      have hIH := ih hFN hM₀ hr hB'big hA'
      refine hIH.trans ?_
      refine iSup₂_le fun E' hE'B' => iSup_le fun hE'k => ?_
      have hE'B : E' ≤ B := hE'B'.trans hB'B
      have hbE' : b ∉ E' := fun h => hbB' (hE'B' h)
      have hcard : Nat.card (E' ⊔ Subgroup.zpowers b : Subgroup G) = p * Nat.card E' :=
        card_sup_zpowers hF.elem hE'B hb hbE'
      have hEB : E' ⊔ Subgroup.zpowers b ≤ B := sup_le hE'B ((Subgroup.zpowers_le).2 hb)
      have hEk : p ^ (k + 1) ≤ Nat.card (E' ⊔ Subgroup.zpowers b : Subgroup G) := by
        rw [hcard, pow_succ']
        exact Nat.mul_le_mul_left _ hE'k
      refine le_trans ?_ (le_centGen hEB hEk)
      rintro z ⟨hzN, hzE'⟩
      have hzN' := hF.layer_normFam_le hb hzN
      refine ⟨hzN'.1, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have hle : E' ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({z} : Set G) := by
        refine sup_le (fun e he => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact ((Subgroup.mem_centralizer_iff.1 hzE') e he).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact ((Subgroup.mem_centralizer_iff.1 hzN'.2) b rfl).symm
      have := (Subgroup.mem_centralizer_iff.1 (hle hh)) z rfl
      exact this.symm

end Main

end GL83.CompFam
