module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Module

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem lemma2_4_16 (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h244 : Lemma244) : Lemma2_4_16 := by
  intro G _ _ T M H S L D n hcfg Z hZ
  obtain ⟨⟨hTS, hTnS, hTnR⟩, ⟨hOL, hUQ⟩, ⟨hJbaum, hRsyl, h3⟩, h4, -, -, h7, -⟩ :=
    h8 G T M H S L D n hcfg
  obtain ⟨-, -, h113⟩ := h11 G T M H S L D n hcfg
  have hST : S ≤ T := hcfg.S_le_T
  obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x ∈ T, x ∉ S := by
    by_contra hcon
    exact hcfg.S_ne_T (le_antisymm hST fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)
  have hZcases : (centerOf L = ⊥ ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ Z = centerOf L) := by
    by_cases hc : centerOf L = ⊥
    · left; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩
    · right; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩
  have hRL : thompsonJ S ≤ L := hRsyl.1
  have hUL : blockU L ≤ L := blockU_le L
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRH : thompsonJ S ≤ H := hRS.trans hcfg.S_le_H
  have hUnH : H ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [hUQ]; exact hcfg.H_le_normalizer_Q
  have hZLeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hZLU : centerOf L ≤ blockU L := hZLeq ▸ blockZ_le_blockU L
  have hlin := hcfg.lin2
  have hcardR : Nat.card (thompsonJ S) = Nat.card (blockU L) * 2 ^ n := by
    have := lin2_card_sylow hlin hRsyl
    rwa [hOL] at this
  have hcardU : Nat.card (blockU L) = 2 ^ (2 * n) * Nat.card (centerOf L) := by
    rw [lin2_card_U hlin, hZLeq]
  have hUpos : 0 < Nat.card (blockU L) := Nat.card_pos
  have hZR : ∀ x ∈ T, x ∉ S → centerOf (thompsonJ S) = blockU L ⊓ conjR (blockU L) x := by
    intro x hx hxS
    exact ((h3 x hx hxS).2.1).symm
  have hcardZR : ∀ x ∈ T, x ∉ S →
      Nat.card (centerOf (thompsonJ S)) * 2 ^ n = Nat.card (blockU L) := by
    intro x hx hxS
    have hRsup := (h3 x hx hxS).1
    have hle : conjR (blockU L) x ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
      refine le_trans ?_ (hRH.trans hUnH)
      rw [hRsup]; exact le_sup_right
    have h1 := card_sup_mul_card_inf hle
    rw [sup_comm, ← hRsup, inf_comm, ← hZR x hx hxS, card_conjR, hcardR] at h1
    have : Nat.card (blockU L) * (Nat.card (centerOf (thompsonJ S)) * 2 ^ n) =
        Nat.card (blockU L) * Nat.card (blockU L) := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hUpos this
  have hZx_le : ∀ x ∈ T, ∀ z : Subgroup G, z ≤ centerOf (thompsonJ S) →
      conjR z x ≤ centerOf (thompsonJ S) := by
    intro x hx z hz
    calc conjR z x ≤ conjR (centerOf (thompsonJ S)) x := conjR_mono hz x
      _ = centerOf (thompsonJ S) := centerOf_normalized (hTnR hx)
  have hZ1 : IsElemAbelian 2 Z ∧ Nat.card Z = 2 ^ n ∧
      S ≤ Subgroup.normalizer (Z : Set G) := by
    rcases hZcases with ⟨hc, hZe⟩ | ⟨hc, hZe⟩
    · have hel : IsElemAbelian 2 (centerOf (thompsonJ S)) := by
        refine IsElemAbelian.mono ?_ (h7 x₀ hx₀T hx₀S).1
        rw [hZR x₀ hx₀T hx₀S]; exact inf_le_left
      have hcZ : Nat.card (centerOf (thompsonJ S)) = 2 ^ n := by
        have h1 := hcardZR x₀ hx₀T hx₀S
        rw [hcardU, hc, Subgroup.card_bot, mul_one] at h1
        have h2 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
        rw [h2] at h1
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
      refine ⟨hZe ▸ hel, hZe ▸ hcZ, fun g hg => ?_⟩
      rw [hZe, ← conjR_eq_self_iff]
      exact centerOf_normalized (hTnR (hST hg))
    · have h4' := (h4 x₀ hx₀T hx₀S).2
      rcases h4' with h4' | ⟨hel, hcZ, -⟩
      · exact absurd h4' hc
      · refine ⟨hZe ▸ hel, hZe ▸ hcZ, fun g hg => ?_⟩
        rw [hZe, ← conjR_eq_self_iff, conjR_centerOf, conjR_eq_of_mem_normalizer
          (hcfg.S_le_normalizer hg)]
  have hZcard := hZ1.2.1
  have hZne : Z ≠ ⊥ := by
    intro h
    have : Nat.card Z = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hZcard] at this
    have h4' : 4 ≤ 2 ^ n := by
      have : 2 ≤ n := hcfg.one_lt
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hZ2 : ∀ x ∈ T, x ∉ S →
      (centerOf L = ⊥ ∧ conjR Z x = Z ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ centerOf (thompsonJ S) = Z ⊔ conjR Z x ∧ Z ⊓ conjR Z x = ⊥) := by
    intro x hx hxS
    rcases hZcases with ⟨hc, hZe⟩ | ⟨hc, hZe⟩
    · left
      refine ⟨hc, ?_, hZe⟩
      rw [hZe]
      exact centerOf_normalized (hTnR hx)
    · right
      refine ⟨hc, ?_⟩
      have hZS : Z ≤ S := by
        rw [hZe]
        exact (hZLU.trans (hUQ ▸ le_rfl)).trans hcfg.Q_le_S
      have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := by
        rw [hZe, hcfg.H_eq]
        exact sup_le (le_normalizer_centerOf L) (fun g hg => by
          rw [← conjR_eq_self_iff, conjR_centerOf, conjR_eq_of_mem_normalizer
            (hcfg.S_le_normalizer hg)])
      have hNT : T ⊓ Subgroup.normalizer (Z : Set G) = S := h244 G T M H S L hcfg.cs Z hZne hZS hHZ
      have hxN : x ∉ Subgroup.normalizer (Z : Set G) := fun hxn => hxS (hNT ▸ ⟨hx, hxn⟩)
      have hne : conjR Z x ≠ Z := fun he => hxN (conjR_eq_self_iff.1 he)
      have hTI : Z ⊓ conjR Z x = ⊥ := by
        have := (h113 hc).1 x⁻¹
        rw [hZe] at hne ⊢
        exact this (by simpa [conjR] using hne)
      refine ⟨?_, hTI⟩
      have hZR' : Z ≤ centerOf (thompsonJ S) := by
        rw [hZe]
        refine le_inf (hZLU.trans (by rw [(h3 x hx hxS).1]; exact le_sup_left)) ?_
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact Subgroup.mem_centralizer_iff.1 hz.2 r (hRL hr)
      have hZxR := hZx_le x hx Z hZR'
      have hnorm : conjR Z x ≤ Subgroup.normalizer (Z : Set G) := by
        intro z hz
        have hzc : z ∈ centerOf (thompsonJ S) := hZxR hz
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_iff.1 hzc.2 y (hZR' hy).1
      have hinf : conjR Z x ⊓ Z = ⊥ := by rw [inf_comm]; exact hTI
      have h1 := card_sup_mul_card_inf hnorm
      rw [hinf, Subgroup.card_bot, mul_one, card_conjR, hZcard] at h1
      have hcR : Nat.card (centerOf (thompsonJ S)) = 2 ^ (2 * n) := by
        have h2 := hcardZR x hx hxS
        have hcL : Nat.card (centerOf L) = 2 ^ n := by rw [← hZe, hZcard]
        rw [hcardU, hcL] at h2
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
      refine (Subgroup.eq_of_le_of_card_ge (sup_le hZR' hZxR) ?_).symm
      rw [sup_comm, h1, hcR]
      exact le_of_eq (by rw [two_mul, pow_add])
  refine ⟨hZ1, hZ2, ?_⟩
  intro x hx hxS
  have hLU : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [← hOL]; exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hZxR : conjR Z x ≤ centerOf (thompsonJ S) := by
    rcases hZ2 x hx hxS with ⟨-, hcx, hZe⟩ | ⟨-, hZR2, -⟩
    · rw [hcx, hZe]
    · rw [hZR2]; exact le_sup_right
  have hZxU : conjR Z x ≤ blockU L := by
    refine hZxR.trans ?_
    rw [hZR x hx hxS]; exact inf_le_left
  have hWU : (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) ≤ blockU L := iSup_le fun ℓ => by
    calc conjR (conjR Z x) (ℓ : G) ≤ conjR (blockU L) (ℓ : G) := conjR_mono hZxU _
      _ = blockU L := conjR_eq_of_mem_normalizer (hLU ℓ.2)
  have hWconj : ∀ g ∈ L, conjR (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) g ≤
      ⨆ ℓ : L, conjR (conjR Z x) (ℓ : G) := by
    intro g hg
    rw [conjR_def, Subgroup.map_iSup]
    refine iSup_le fun ℓ => ?_
    have : (conjR (conjR Z x) (ℓ : G)).map (MulAut.conj g⁻¹).toMonoidHom =
        conjR (conjR Z x) ((ℓ : G) * g) := (conjR_conjR _ _ _)
    rw [this]
    exact le_iSup (fun ℓ : L => conjR (conjR Z x) (ℓ : G)) ⟨(ℓ : G) * g, L.mul_mem ℓ.2 hg⟩
  have hWnorm : ∀ g ∈ L, ∀ y ∈ (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)),
      g * y * g⁻¹ ∈ (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) := by
    intro g hg y hy
    have h1 := hWconj g⁻¹ (L.inv_mem hg)
    rw [conjR_le_iff, inv_inv] at h1
    exact mem_conjR.1 (h1 hy)
  have hWnormL := le_normalizer_of_conj_mem hWnorm
  have hirr := hcfg.short.2.2.2.2
  have hZLcentral : L ≤ Subgroup.normalizer ((blockZ L : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 hz.2 g hg).symm
  have hW' := hirr.2 ((⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) ⊔ blockZ L) le_sup_right
    (sup_le hWU (blockZ_le_blockU L)) (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hWnormL hg, hZLcentral hg⟩)
  have hZxW : conjR Z x ≤ ⨆ ℓ : L, conjR (conjR Z x) (ℓ : G) := by
    have := le_iSup (fun ℓ : L => conjR (conjR Z x) (ℓ : G)) ⟨1, L.one_mem⟩
    simpa using this
  have hWeq : (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) = blockU L := by
    rcases hW' with hW1 | hW1
    · exfalso
      have hWle : (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) ≤ centerOf L := by
        rw [← hZLeq, ← hW1]; exact le_sup_left
      rcases hZ2 x hx hxS with ⟨hc, -, -⟩ | ⟨hc, -, hTI⟩
      · have : conjR Z x ≤ ⊥ := by
          have := hZxW.trans hWle
          rwa [hc] at this
        exact hZne (conjR_eq_bot_iff.1 (le_bot_iff.1 this))
      · rcases hZcases with ⟨hc', -⟩ | ⟨-, hZe⟩
        · exact hc hc'
        · have hle : conjR Z x ≤ Z := by
            have := hZxW.trans hWle
            rwa [← hZe] at this
          apply hZne
          rw [← conjR_eq_bot_iff (g := x)]
          have := inf_eq_right.2 hle
          rw [hTI] at this
          exact this.symm
    · refine le_antisymm hWU ?_
      have hU' : blockU L = ⁅blockU L, L⁆ := by
        conv_lhs => unfold blockU blockQ
        rw [hOL]
      rw [hU', Subgroup.commutator_le]
      intro u hu ℓ hℓ
      have hu' : u ∈ (((⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) ⊔ blockZ L : Subgroup G) : Set G) :=
        hW1 ▸ hu
      have hWn : (⨆ ℓ : L, conjR (conjR Z x) (ℓ : G)) ≤
          Subgroup.normalizer ((blockZ L : Subgroup G) : Set G) :=
        (hWU.trans ((blockU_le L).trans (fun g hg => hZLcentral hg)))
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hWn] at hu'
      obtain ⟨w, hw, z, hz, rfl⟩ := hu'
      have hzℓ : ℓ * z = z * ℓ := Subgroup.mem_centralizer_iff.1 hz.2 ℓ hℓ
      have e : ⁅w * z, ℓ⁆ = w * (ℓ * w⁻¹ * ℓ⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev]
        have : z * ℓ * z⁻¹ = ℓ := by
          rw [← hzℓ]; group
        calc w * z * ℓ * (z⁻¹ * w⁻¹) * ℓ⁻¹ = w * (z * ℓ * z⁻¹) * w⁻¹ * ℓ⁻¹ := by group
          _ = w * ℓ * w⁻¹ * ℓ⁻¹ := by rw [this]
          _ = w * (ℓ * w⁻¹ * ℓ⁻¹) := by group
      rw [e]
      exact mul_mem hw (hWnorm ℓ hℓ w⁻¹ (inv_mem hw))
  have hle : blockU L ≤ weakClosure Z (blockU L) := by
    refine hWeq.symm.le.trans (iSup_le fun ℓ => ?_)
    have hconj : conjR (conjR Z x) (ℓ : G) = conjR Z (x * ℓ) := conjR_conjR _ _ _
    have hle' : conjR Z (x * ℓ) ≤ blockU L := by
      rw [← hconj]
      exact (le_iSup (fun ℓ : L => conjR (conjR Z x) (ℓ : G)) ℓ).trans hWU
    rw [hconj]
    exact le_iSup₂_of_le (x * ℓ) hle' le_rfl
  have hge : weakClosure Z (blockU L) ≤ blockU L := iSup₂_le fun g hg => hg
  exact ⟨hWeq.symm, le_antisymm hle hge⟩

end CFSG.QuasithinUnique.Lin2
