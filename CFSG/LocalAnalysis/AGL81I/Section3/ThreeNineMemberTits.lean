module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveSteps
public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroup

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem index_modEq_one_of_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) {Y : Subgroup G}
    (hN : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Y) : Y.index ≡ 1 [MOD p] := by
  have hPY : (P : Subgroup G) ≤ Y := Subgroup.le_normalizer.trans hN
  have hG : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index ≡ 1 [MOD p] := by
    have h := card_sylow_modEq_one (p := p) (G := G)
    rw [Sylow.card_eq_index_normalizer P] at h
    exact h
  have hY : (Subgroup.normalizer
      (((P : Subgroup G).subgroupOf Y : Subgroup Y) : Set Y)).index ≡ 1 [MOD p] := by
    have h := card_sylow_modEq_one (p := p) (G := Y)
    rw [Sylow.card_eq_index_normalizer (P.subtype hPY)] at h
    exact h
  rw [← Subgroup.subgroupOf_normalizer_eq hPY] at hY
  have hmul := Subgroup.relIndex_mul_index hN
  rw [← hmul] at hG
  have h1 := (hY.mul_right Y.index).symm.trans hG
  simpa using h1

section Tits

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.TitsFive CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowPair
open CFSG.StandardType.SylowOvergroup CFSG.StandardType.TitsGenerators
open CFSG.AGLEmbedding.MaxD2 (Gsub Rsub)
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDArr)

theorem tits_card_of_pairP_le (hc : titsFiveCheck () = true)
    {Y : Subgroup (Equiv.Perm (Fin pairData.n))} (hPY : pairP pairData titsS ≤ Y)
    (hYG : Y ≤ titsD) (hY : Y ≠ titsD) : Nat.card Y ∣ 1200 ∨ Nat.card Y = 7800 := by
  obtain ⟨hpair, hsg, -, -⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, -, hN, -, hSide, hCover, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  by_cases hYN : Y ≤ pairN pairData titsS
  · left
    have h1 := Subgroup.card_dvd_of_le hYN
    rwa [card_pairN hS hN] at h1
  · right
    obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
    rcases dichotomy hS hpair hPY (hYG.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hyY
      with h | ⟨i, hi, hk, -, a, ha, hle⟩
    · exact absurd h hyN
    · have key : ∀ i < 24, pairData.kind[i]! ≠ 0 → i = 23 := by decide
      have hlen24 : pairData.repW.length = 24 := rfl
      have hi23 : i = 23 := key i (by omega) hk
      subst hi23
      have hL : pairSide pairData titsS 0 ≤
          pairClosure (pairP pairData titsS) ((pairReps pairData titsS).getD (23 + 1) 1) :=
        pairSide_le_pairClosure hS (invsOK_of_checkCover hCover) hsg (i := 23) (k := 0) hi
          (by show pairData.kind[23]! = 0 + 1; decide)
      have hLY : (pairSide pairData titsS 0).map (MulAut.conj a).toMonoidHom ≤ Y :=
        (Subgroup.map_mono hL).trans hle
      have haG : a ∈ titsD := (le_of_eq hG) (pairN_le_pairG ha)
      have hYeq : Y = (pairSide pairData titsS 0).map (MulAut.conj a).toMonoidHom :=
        eq_map_conj_of_maximal haG (pairSide_maximal hc) hLY hYG hY
      have hcardL : Nat.card ↥(pairSide pairData titsS 0) = 7800 :=
        card_pairSide hS hSide (k := 0) (by simp [pairData])
      rw [hYeq, Subgroup.card_map_of_injective (MulAut.conj a).injective, hcardL]

theorem tits_card_of_index
    {Y : Subgroup ↥titsD} (hY : Y ≠ ⊤) (h5 : ¬ 5 ∣ Y.index) :
    Nat.card Y ∣ 1200 ∨ Nat.card Y = 7800 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : titsFiveCheck () = true := Certificates.certificate465004
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, hP, -, -, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hPG : pairP pairData titsS ≤ titsD := hG ▸ pairP_le_pairG
  have hP25 : Nat.card ↥(pairP pairData titsS) = 5 ^ 2 := by
    rw [card_pairP hS hP]
    rfl
  have hD : Nat.card ↥titsD = 5 ^ 2 * 718848 := by
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  let S : Sylow 5 ↥titsD := Sylow.ofCard ((pairP pairData titsS).subgroupOf titsD) (by
    have h1 : Nat.card ↥((pairP pairData titsS).subgroupOf titsD) = 5 ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv).trans hP25
    exact h1.trans (card_eq_pow_factorization hD (by norm_num)))
  have hSc : (S : Subgroup ↥titsD) = (pairP pairData titsS).subgroupOf titsD :=
    Sylow.coe_ofCard _ _
  refine forall_of_sylow_le S (fun Y => Nat.card Y ∣ 1200 ∨ Nat.card Y = 7800) ?_ ?_ hY h5
  · intro g Y hY'
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    rwa [Subgroup.card_map_of_injective hinj] at hY'
  · intro Y hSY hYtop
    have hPY : pairP pairData titsS ≤ Y.map titsD.subtype := by
      intro x hx
      refine ⟨⟨x, hPG hx⟩, hSY ?_, rfl⟩
      rw [hSc]
      exact hx
    have hne : Y.map titsD.subtype ≠ titsD := by
      intro heq
      apply hYtop
      have htop : (⊤ : Subgroup ↥titsD).map titsD.subtype = titsD := by
        rw [Subgroup.map_top titsD.subtype, Subgroup.range_subtype]
      exact (Subgroup.map_subtype_inj (H := titsD)).mp (heq.trans htop.symm)
    have h := tits_card_of_pairP_le hc hPY (Subgroup.map_subtype_le Y) hne
    have hc' : Nat.card ↥(Y.map titsD.subtype) = Nat.card Y :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective Y titsD.subtype titsD.subtype_injective).toEquiv).symm
    rcases h with h | h
    · exact Or.inl (Eq.mpr (congrArg (· ∣ 1200) hc'.symm) h)
    · exact Or.inr (hc'.symm.trans h)

theorem threeNineFiveTits_holds :
    ThreeNineFiveTits := by
  intro X _ _ K E D X₁ d h hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 hK
  have hcardK : Nat.card ↥K = 17971200 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ
    rw [CFSG.Sporadic.Schreier.Tits.titsD_center] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hout : ¬ d ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
    have h2 := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier (G := ↥K) (p := 2) (f := 1)
      hK).1
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) d hd
    obtain ⟨k, hk⟩ := h2 x
    have h3 : d ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk
    exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
      (h.d_prime.dvd_of_dvd_pow h3))
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hout
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  have hDinf : D ⊓ K = D := inf_eq_left.mpr hDK
  rw [hDinf] at hDsylK
  have hDcard := hDsylK.card_eq
  rw [hcardK] at hDcard
  have hd1 : 1 < Nat.card D := by
    have hD1 : D ≠ ⊥ := h.D_ne_bot
    rw [hDcard]
    by_contra hle
    push Not at hle
    have h0 : (17971200 : ℕ).factorization d = 0 := by
      by_contra hne
      have : 1 < d ^ (17971200 : ℕ).factorization d :=
        Nat.one_lt_pow hne h.d_prime.one_lt
      omega
    rw [h0, pow_zero] at hDcard
    exact hD1 (Subgroup.card_eq_one.mp hDcard)
  have hdK : d ∣ 17971200 := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hDcard
    omega
  have hd313 : d = 3 ∨ d = 13 := by
    have hfac : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1))
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  set Y : Subgroup ↥K := X₁.subgroupOf K with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 5 ((Q : Subgroup X) ⊓ K) K := by
    have hQ : CFSG.ABGLocalTools.IsSylowOf 5 (Q : Subgroup X) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index
    exact hQ.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  have hQcard := hQsyl.card_eq
  rw [hcardK] at hQcard
  have hv5 : (5 : ℕ) ^ (17971200 : ℕ).factorization 5 = 5 ^ 2 :=
    (card_eq_pow_factorization (p := 5) (a := 2) (k := 718848) (by norm_num)
      (by norm_num)).symm
  rw [hv5] at hQcard
  have hQY : ((Q : Subgroup X) ⊓ K).subgroupOf K ≤ Y := fun x hx =>
    h.inf_K_le Q.isPGroup' hEQ hx
  have h25 : 25 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hQY
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hQcard] at this
  have hidx := Y.card_mul_index
  rw [hcardK] at hidx
  have h5 : ¬ 5 ∣ Y.index := by
    intro h5
    obtain ⟨m, hm⟩ := h25
    obtain ⟨j, hj⟩ := h5
    rw [hm, hj] at hidx
    have h2 : 125 * (m * j) = 17971200 := by rw [← hidx]; ring
    omega
  set Y' : Subgroup ↥CFSG.Sporadic.Schreier.Tits.titsD := Y.map φ.toMonoidHom
  have hY'card : Nat.card Y' = Nat.card Y :=
    (Nat.card_congr (Subgroup.equivMapOfInjective Y φ.toMonoidHom φ.injective).toEquiv).symm
  have hY'top : Y' ≠ ⊤ := by
    intro htop
    apply hYtop
    have : Y = Y'.map φ.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      simp
    rw [this, htop, Subgroup.map_top_of_surjective _ φ.symm.surjective]
  have hidx' := Y'.card_mul_index
  rw [Nat.card_congr φ.symm.toEquiv, hcardK, hY'card] at hidx'
  have hidxeq : Y'.index = Y.index := by
    have h1 : Nat.card Y * Y'.index = Nat.card Y * Y.index := hidx'.trans hidx.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by
      have := Nat.card_pos (α := Y); omega)) h1
  have hcard := tits_card_of_index hY'top (by rw [hidxeq]; exact h5)
  rw [hY'card] at hcard
  have hDY : D.subgroupOf K ≤ Y := fun x hx => h.D_le hx
  have hdY : Nat.card D ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hDY
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv] at this
  rcases hd313 with rfl | rfl
  ·
    have hv3 : (3 : ℕ) ^ (17971200 : ℕ).factorization 3 = 3 ^ 3 :=
      (card_eq_pow_factorization (p := 3) (a := 3) (k := 665600) (by norm_num)
        (by norm_num)).symm
    rw [hDcard, hv3] at hdY
    rcases hcard with h1 | h1
    · have := hdY.trans h1
      norm_num at this
    · rw [h1] at hdY
      norm_num at hdY
  ·
    have hv13 : (13 : ℕ) ^ (17971200 : ℕ).factorization 13 = 13 ^ 1 :=
      (card_eq_pow_factorization (p := 13) (a := 1) (k := 1382400) (by norm_num)
        (by norm_num)).symm
    rw [hDcard, hv13] at hdY
    rcases hcard with h1 | h1
    · have := hdY.trans h1
      norm_num at this
    · rw [h1] at hidx
      have hY2304 : Y.index = 2304 := by omega
      let S13 : Sylow 13 ↥K := Sylow.ofCard (D.subgroupOf K) (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard, hcardK])
      have hN : Subgroup.normalizer ((S13 : Subgroup ↥K) : Set ↥K) ≤ Y := by
        intro n hn
        have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
        rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
        exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
      have hmod := index_modEq_one_of_normalizer_le S13 hN
      rw [hY2304] at hmod
      exact absurd hmod (by decide)

end Tits

end CFSG.LocalAnalysis.AGL81I.Section3
