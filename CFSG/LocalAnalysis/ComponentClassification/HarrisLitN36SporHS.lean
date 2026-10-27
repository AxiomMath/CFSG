module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Normal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporInputs

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier

@[expose] def HS2CNormalFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → Nonempty (Y ≃* NativeSporadic.HS) →
    ∀ σ : MulAut Y, orderOf σ = 2 → σ ∉ innAut Y → Nat.card ↥(fixedPoints σ) = 40320 →
    ∀ L : Subgroup ↥(fixedPoints σ), L.Normal → Nat.card ↥L ≠ 168 ∧ Nat.card ↥L ≠ 360

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem card_bar_pow (h : Config G p m τ K) (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥) :
    Nat.card ↥(K.map (QuotientGroup.mk' (center G))) * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
  obtain ⟨-, hL⟩ := h.isComponent_bar hO
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hodd := AutL2Facts.isOddPrimePower_of hpP h.ne_two hm1 hF'
  have hsub : Nat.card ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
      (fixedPoints (quotAut τ))) = Nat.card ↥(K.map (QuotientGroup.mk' (center G))) :=
    Nat.card_congr (subgroupOfEquivOfLe h.isTwoComponentIn_bar.1).toEquiv
  rw [← hsub, Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
  have hev : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
    have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
      have : 16 ∣ (p ^ m) ^ 2 - 1 := by have := h.sixteen_dvd; rwa [← pow_mul, mul_comm]
      exact (by norm_num : 2 ∣ 16).trans this
    exact h2.mul_left _
  exact Nat.div_mul_cancel hev

end Config

theorem eq_nine_of_mul {q : ℕ} (h : q * (q ^ 2 - 1) = 720) : q = 9 := by
  rcases lt_trichotomy q 9 with hq | hq | hq
  · have : q * (q ^ 2 - 1) ≤ 8 * (8 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    omega
  · exact hq
  · have : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    omega

theorem pow_mem_of_dvd_40320 {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h7 : 7 ≤ p ^ m) (hd : p ^ m ∣ 80640) : p ^ m = 7 ∨ p ^ m = 9 := by
  have hpd : p ∣ 2 ^ 8 * 3 ^ 2 * 5 * 7 := by
    have := (dvd_pow_self p (show m ≠ 0 by omega)).trans hd
    norm_num
    exact this
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
            hp2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  have hle : p ^ m ≤ 80640 := Nat.le_of_dvd (by norm_num) hd
  rcases hp' with rfl | rfl | rfl
  · have hm' : m ≤ 10 := by
      by_contra hc
      have : 3 ^ 11 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m <;> first | (norm_num at h7; done) | (norm_num at hd; done) | norm_num
  · have hm' : m ≤ 7 := by
      by_contra hc
      have : 5 ^ 8 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m <;> first | (norm_num at h7; done) | norm_num at hd
  · have hm' : m ≤ 6 := by
      by_contra hc
      have : 7 ^ 7 ≤ 7 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m <;> first | (norm_num at h7; done) | (norm_num at hd; done) | norm_num

open Hin in
theorem rowFor_spor_HS
    (hmult : HSJ3TwoMultiplierFact) (h2B : TwoHSTwoBFact) (h2C : HS2CNormalFact) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .HS := by
  intro G _ _ p m τ K h ⟨e⟩
  have := h.simple_bar
  set σ := quotAut τ with hσdef
  have hO := h.pPrimeCore_bar_eq_bot CatalogueU.sporadicOddCoreFree_HS e
  have hq := h.card_bar_pow hO
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  by_cases hinn : σ ∈ innAut (G ⧸ center G)
  ·
    obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    have hle : K.map (QuotientGroup.mk' (center G)) ≤ centralizer ({t} : Set (G ⧸ center G)) := by
      rw [centralizer_eq_fixedPoints_conj, ht]
      exact h.isTwoComponentIn_bar.1
    obtain ⟨hB, -⟩ := h.isComponent_bar hO
    have hB' : CFSG.IsComponent ((K.map (QuotientGroup.mk' (center G))).subgroupOf
        (centralizer ({t} : Set (G ⧸ center G)))) := by
      have heq : fixedPoints σ = centralizer ({t} : Set (G ⧸ center G)) := by
        rw [centralizer_eq_fixedPoints_conj, ht]
      rw [← heq]
      exact hB
    have hBA := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      hle).mpr hB'
    obtain ⟨-, -, h360⟩ := cti_hs_involution_local_components_simple_order_360 ⟨e⟩ ht2 hBA
    rw [h360] at hq
    have h9 : p ^ m = 9 := eq_nine_of_mul (by omega)
    obtain ⟨rfl, rfl⟩ : p = 3 ∧ m = 2 := by
      have h32 : p ^ m = 3 ^ 2 := by rw [h9]; norm_num
      obtain ⟨hp3, hm2⟩ := Nat.Prime.pow_inj' h.prime Nat.prime_three (by have := h.one_le; omega)
        (by norm_num) h32
      exact ⟨hp3, hm2⟩
    have hτ : τ ∈ innAut G := h.bar_mem_innAut_iff.mp ⟨t, ht⟩
    have hZ2 : Nat.card ↥(center G) = 2 := by
      have h1 := hmult.1 G h.quasisimple h.center_isPGroup ⟨e⟩
      have h2 : 1 < Nat.card ↥(center G) := by
        rw [Finite.one_lt_card_iff_nontrivial, nontrivial_iff_ne_bot]
        exact h.center_ne_bot
      omega
    exact Or.inr (Or.inl ⟨⟨e⟩, hZ2, h2B G h.quasisimple ⟨e⟩ hZ2 τ h.orderOf_eq hτ K h.comp
      h.lieModel, hτ⟩)
  · exfalso
    set ψ := e.trans hsPermEquiv with hψ
    have hσ2 : orderOf (MulAut.congr ψ σ) = 2 := by
      rw [orderOf_congr]
      exact h.orderOf_bar
    obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := hs_involution_centralizers
    obtain ⟨r, hr, hcard, hinn'⟩ := exists_row_of_autModel hs_autModel
      (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩) hcover hσ2
    have hout : r.outer = true := by
      by_contra hc
      apply hinn
      rw [← congr_mem_innAut_iff ψ]
      exact hinn'.2 (by simpa using hc)
    have hco : r.centOrder = 40320 ∨ r.centOrder = 1920 := by
      have hmem : (r.outer, r.classSize, r.centOrder) ∈
          [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320),
            (true, 23100, 1920)] := by
        rw [← hmap]
        exact List.mem_map_of_mem hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩
      · rw [hout] at h1; exact absurd h1 (by decide)
      · rw [hout] at h1; exact absurd h1 (by decide)
      · exact Or.inl h1
      · exact Or.inr h1
    have hcardσ : Nat.card ↥(fixedPoints σ) = r.centOrder := by
      rw [← card_fixedPoints_congr ψ σ, hcard]
    have hd := h.card_bar_dvd
    rcases hco with h40 | h19
    ·
      rw [h40] at hcardσ
      have hqd : p ^ m ∣ 80640 := by
        have h1 : p ^ m ∣ Nat.card ↥(K.map (QuotientGroup.mk' (center G))) * 2 := by
          rw [hq]; exact dvd_mul_right _ _
        rw [hcardσ] at hd
        exact h1.trans (Nat.mul_dvd_mul_right hd 2)
      have hqm := pow_mem_of_dvd_40320 h.prime h.ne_two h.one_le h.seven_le hqd
      have hK : Nat.card ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
          (fixedPoints σ)) = Nat.card ↥(K.map (QuotientGroup.mk' (center G))) :=
        Nat.card_congr (subgroupOfEquivOfLe h.isTwoComponentIn_bar.1).toEquiv
      obtain ⟨h168, h360⟩ := h2C _ h.simple_bar ⟨e⟩ σ h.orderOf_bar hinn hcardσ _ h.bar_normal
      rw [hK] at h168 h360
      rcases hqm with h7 | h9
      · rw [h7, show (7 : ℕ) * (7 ^ 2 - 1) = 336 by norm_num] at hq
        exact h168 (by omega)
      · rw [h9, show (9 : ℕ) * (9 ^ 2 - 1) = 720 by norm_num] at hq
        exact h360 (by omega)
    · rw [hcardσ, h19] at hd
      obtain ⟨q, hq7, hq16, hq'⟩ := h.card_bar hO
      exact false_of_card_dvd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hd hq7 hq16 hq'

end CFSG.ComponentClassification.HarrisLit.N36
