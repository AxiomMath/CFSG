module

public import CFSG.GH74.GLS.C3.Layer1.Back91Choice
public import CFSG.GH74.GLS.C3.Layer1.Back93
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves
public import CFSG.GH74.GLS.C3.Layer1.U1aFinal
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem lex_le_iff' {a b c d : ℕ} :
    (toLex (a, b) : ℕ ×ₗ ℕ) ≤ toLex (c, d) ↔ a < c ∨ (a = c ∧ b ≤ d) := by
  simp [Prod.Lex.le_iff]

omit [Finite G] in
theorem pRank_bot_eq_zero : pRank 2 ↥(⊥ : Subgroup G) = 0 := by
  have : pRank 2 ↥(⊥ : Subgroup G) ≤ 0 :=
    CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two (k := 0) fun A _ => by simp
  omega

theorem normalizer_le_conjugate {M Q E : Subgroup G} (hΓ : gammaK 2 Q 1 ≤ M) {g : G}
    (hE : E ≤ conjugate Q g) (hE1 : 1 ≤ pRank 2 ↥E) : normalizer (E : Set G) ≤ conjugate M g := by
  intro n hn
  rw [mem_conjugate_iff']
  set E' : Subgroup G := conjugate E g⁻¹ with hE'
  have hE'Q : E' ≤ Q := by
    intro y hy
    rw [hE', mem_conjugate_iff'] at hy
    have hy' : g⁻¹ * y * g ∈ E := by simpa using hy
    have := hE hy'
    rw [mem_conjugate_iff'] at this
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  have hE'1 : 1 ≤ pRank 2 ↥E' := by rw [hE', pRank_conjugate']; exact hE1
  have hn' : g * n * g⁻¹ ∈ normalizer (E' : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    have h1 := hn (g⁻¹ * y * g)
    have e1 : y ∈ E' ↔ g⁻¹ * y * g ∈ E := by
      rw [hE', mem_conjugate_iff']
      simp
    have e2 : g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ ∈ E' ↔
        g⁻¹ * (g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹) * g ∈ E := by
      rw [hE', mem_conjugate_iff']
      simp
    rw [e1, e2]
    have : g⁻¹ * (g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * y * g) * n⁻¹ := by group
    rw [this]
    exact h1
  have hle : normalizer (E' : Set G) ≤ gammaK 2 Q 1 := by
    unfold gammaK
    exact le_iSup₂_of_le E' hE'Q (le_iSup_of_le hE'1 le_rfl)
  exact hΓ (hle hn')

theorem prop91_ab_core
    {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (hGs : IsSimpleGroup G) (hGn : ∃ a b : G, a * b ≠ b * a) (hG : IsKProperSimple G)
    (hs : IsSimpleGroup (kBar L)) (hn : ∃ a b : kBar L, a * b ≠ b * a)
    (hlist : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)))
    (hR : T ⊓ (L ⊔ CMK M L) = (T ⊓ K) ⊔ Q)
    (hcomm : ∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p) (hPQ : (T ⊓ K) ⊓ Q = ⊥)
    (h81 : B_iv2_8_1) (h92 : B_lemma92) :
    (CFSG.IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4) ∧
    (∃ g : G, g ∉ M ∧ conjugate Q g ≤ M ∧ ¬ L ≤ conjugate M g ∧
      conjugate Q g ≤ (T ⊓ K) ⊔ Q ∧ conjugate Q g ⊓ Q = ⊥) ∧
    (HasL2Model (kBar L) Odd →
      ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model (kBar L) (fun r => r = q)) := by
  have hQ2 : IsPGroup 2 ↥Q := hh.sylowQ.isPGroup
  have hQCMK : Q ≤ CMK M L := hh.sylowQ.le
  obtain ⟨g, hgM, hg2, hgT, hmax⟩ := exists_best_conj hh.sylowTM hQ2
    (exists_conj_inter_of_hyp9A hGs hGn hh hs hn)
  set V : Subgroup G := conjugate Q g ⊓ M with hV
  have hVQg : V ≤ conjugate Q g := inf_le_left
  have hVM : V ≤ M := inf_le_right
  have hVp : IsPGroup 2 ↥V := (isPGroup_conjugate' hQ2 g).to_le hVQg
  have hLg : ¬ L ≤ conjugate M g := by
    intro hLM
    have hVne : V ≠ ⊥ := by
      intro h0
      rw [h0] at hg2
      have := pRank_bot_eq_zero (G := G)
      omega
    exact hgM (h81 G hG M L Q hh.maximal hh.L_comp hh.L_normal.2 hh.sylowQ hh.gamma g hVne hLM)
  have hΓ : gammaIn L V ≠ L := by
    intro hL
    apply hLg
    rw [← hL]
    refine iSup₂_le fun E hEV => iSup_le fun hE1 => ?_
    exact inf_le_of_left_le (normalizer_le_conjugate hh.gamma (hEV.trans hVQg) hE1)
  obtain ⟨hlist', ⟨hVe, hV4⟩, hVL, hVC⟩ := h92 G L M V hh.L_normal.1 hh.L_normal.2 hlist hVp hVM hg2 hΓ
  obtain ⟨hVab, hVsq⟩ := forall_of_isElementaryAbelian hVe
  have hVR : V ≤ (T ⊓ K) ⊔ Q := by
    rw [← hR]
    exact le_inf hgT hVL
  have hVne : V ≠ ⊥ := by
    intro h0
    rw [h0] at hV4
    simp at hV4
  have hPQ' : ∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p := hcomm
  have hQne : Q ≠ ⊥ := by
    intro h0
    have hx := hh.x_mem_Q
    rw [h0, Subgroup.mem_bot] at hx
    have := hh.orderOf_x
    rw [hx, orderOf_one] at this
    omega
  have hVpR : pRank 2 ↥V = 2 := by
    have h1 := card_eq_two_pow_pRank hVe
    rw [hV4] at h1
    have : (2 : ℕ) ^ pRank 2 ↥V = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective le_rfl this
  have hQM : Q ≤ conjugate M g := by
    refine q_le_of_projections hcomm hPQ hQ2 hQne hVR hVab hVsq hVne ?_ ?_
    · intro v hv hv1 c hc
      have hvQ : g * v * g⁻¹ ∈ Q := mem_conjugate_iff'.1 (hVQg hv)
      have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hVsq v hv) hv1
      have hvo' : orderOf (g * v * g⁻¹) = 2 := by
        rw [← hvo]; exact U1a.orderOf_conj_eq' g
      have hcc : g * c * g⁻¹ ∈ centralizer ({g * v * g⁻¹} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have : c * v = v * c := hc
        calc g * c * g⁻¹ * (g * v * g⁻¹) = g * (c * v) * g⁻¹ := by group
          _ = g * (v * c) * g⁻¹ := by rw [this]
          _ = g * v * g⁻¹ * (g * c * g⁻¹) := by group
      have := hh.gamma (U1a.centralizer_le_gammaK hvQ hvo' hcc)
      exact mem_conjugate_iff'.2 this
    · intro U hUQ hUM hUab hUsq
      have hUe : CFSG.IsElementaryAbelian 2 ↥U := isElementaryAbelian_of_forall hUab hUsq
      have hUc : Nat.card ↥U = 2 ^ pRank 2 ↥U := card_eq_two_pow_pRank hUe
      set U' : Subgroup G := conjugate U g⁻¹ with hU'
      have hU'1 : U' ≤ conjugate Q g⁻¹ ⊓ M := by
        refine le_inf (conjugate_le_conjugate' hUQ _) ?_
        have := conjugate_le_conjugate' hUM g⁻¹
        rwa [conjugate_inv_conjugate'] at this
      by_cases hr : 2 ≤ pRank 2 ↥U
      · have hg'M : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
        have hrk : pRank 2 ↥U' ≤ pRank 2 ↥(conjugate Q g⁻¹ ⊓ M) := pRank_mono' hU'1
        have hS := hmax g⁻¹ hg'M (by rw [hU', pRank_conjugate'] at hrk; omega)
        have hle : pRank 2 ↥(conjugate Q g⁻¹ ⊓ M) ≤ pRank 2 ↥V := by
          rcases (lex_le_iff'.1 hS) with h | h
          · exact h.le
          · exact h.1.le
        rw [hU', pRank_conjugate'] at hrk
        have : pRank 2 ↥U ≤ 2 := by omega
        calc Nat.card ↥U = 2 ^ pRank 2 ↥U := hUc
          _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
          _ = Nat.card ↥V := by rw [hV4]
      · have : pRank 2 ↥U ≤ 1 := by omega
        calc Nat.card ↥U = 2 ^ pRank 2 ↥U := hUc
          _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
          _ ≤ Nat.card ↥V := by rw [hV4]; norm_num
  have hVeq : V = conjugate Q g := by
    have hg'M : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
    have hQg : conjugate Q g⁻¹ ≤ M := by
      have := conjugate_le_conjugate' hQM g⁻¹
      rwa [conjugate_inv_conjugate'] at this
    have hinf : conjugate Q g⁻¹ ⊓ M = conjugate Q g⁻¹ := inf_eq_left.2 hQg
    have hrk : pRank 2 ↥(conjugate Q g⁻¹ ⊓ M) = pRank 2 ↥Q := by rw [hinf, pRank_conjugate']
    have hcd : Nat.card ↥(conjugate Q g⁻¹ ⊓ M) = Nat.card ↥Q := by rw [hinf, card_conjugate']
    have hQ2' : 2 ≤ pRank 2 ↥(conjugate Q g⁻¹ ⊓ M) := by rw [hrk]; exact hh.rankQ
    have hS := hmax g⁻¹ hg'M hQ2'
    rw [hrk, hcd] at hS
    have hV1 : pRank 2 ↥V ≤ pRank 2 ↥Q := by
      have := pRank_mono' hVQg
      rwa [pRank_conjugate'] at this
    have hcardV : Nat.card ↥V ≤ Nat.card ↥(conjugate Q g) := Subgroup.card_le_of_le hVQg
    rw [card_conjugate'] at hcardV
    have hge : Nat.card ↥Q ≤ Nat.card ↥V := by
      rcases (lex_le_iff'.1 hS) with h | h
      · exact absurd h (by omega)
      · exact h.2
    exact Subgroup.eq_of_le_of_card_ge hVQg (by rw [card_conjugate']; exact hge)
  have hQ4 : Nat.card ↥Q = 4 := by
    rw [← card_conjugate' Q g, ← hVeq]; exact hV4
  have hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
    intro q hq q' hq'
    have hx : g⁻¹ * q * g ∈ V := by
      rw [hVeq, mem_conjugate_iff']
      have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rwa [e]
    have hx' : g⁻¹ * q' * g ∈ V := by
      rw [hVeq, mem_conjugate_iff']
      have e : g * (g⁻¹ * q' * g) * g⁻¹ = q' := by group
      rwa [e]
    have := hVab _ hx _ hx'
    have e : g⁻¹ * q * g * (g⁻¹ * q' * g) = g⁻¹ * (q * q') * g := by group
    have e' : g⁻¹ * q' * g * (g⁻¹ * q * g) = g⁻¹ * (q' * q) * g := by group
    rw [e, e'] at this
    exact mul_left_cancel (mul_right_cancel this)
  have hQsq : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    have hx : g⁻¹ * q * g ∈ V := by
      rw [hVeq, mem_conjugate_iff']
      have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rwa [e]
    have := hVsq _ hx
    have e : g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g := by group
    rw [e] at this
    have h2 : q * q = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) this
      simpa [mul_assoc] using this
    exact h2
  refine ⟨⟨isElementaryAbelian_of_forall hQab hQsq, hQ4⟩, ⟨g, hgM, ?_, hLg, ?_, ?_⟩, hlist'⟩
  · rw [← hVeq]; exact hVM
  · rw [← hVeq]; exact hVR
  · rw [← hVeq]
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ V ⊓ CMK M L := ⟨hy.1, hQCMK hy.2⟩
    rwa [hVC] at this

end CFSG.GH74.GLS.C3.Layer1.Back
