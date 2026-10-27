module

public import CFSG.CGT.Timmesfeld75.Sec5ElevenNum
public import CFSG.CGT.Timmesfeld75.Sec5ElevenIso
public import CFSG.CGT.Timmesfeld75.Sec5Ten

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

@[expose] def Small64Input : Prop :=
  ∀ (a : ℕ), (a = 4 ∨ a = 5) → ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a F))) →
    ∀ (V : Type) [Group V] [Finite V], (∀ x y : V, x * y = y * x) → (∀ x : V, x * x = 1) →
      Nat.card V = 2 ^ 6 → ∀ ρ : Y →* MulAut V, ρ.ker ≤ Subgroup.center Y →
        (∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w) → False

@[expose] def Lemma29Input : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m → ∀ (Y : Type) [Group Y] [Finite Y] (E : Subgroup Y),
    commutator Y = ⊤ → IsWC E → Subgroup.normalClosure (E : Set Y) = ⊤ →
    E ⊓ Subgroup.center Y = ⊥ → 4 ≤ Nat.card E →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL n F))) →
    (3 ≤ n → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m →
      ∀ e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL n F),
        Nat.card (E.map (QuotientGroup.mk' (Subgroup.center Y))) = 2 ^ (m * (n - 1)) ∧
        ((∃ c : Fin n → F, c ≠ 0 ∧
            (E.map (QuotientGroup.mk' (Subgroup.center Y))).map e.toMonoidHom =
              transvImage n F (transvCenter n F c)) ∨
         (∃ a : Fin n → F, a ≠ 0 ∧
            (E.map (QuotientGroup.mk' (Subgroup.center Y))).map e.toMonoidHom =
              transvImage n F (transvAxis n F a)))) →
    ∀ (V : Type) [Group V] [Finite V], (∀ x y : V, x * y = y * x) → (∀ x : V, x * x = 1) →
      Nat.card V = (2 ^ m) ^ n → ∀ ρ : Y →* MulAut V, ρ.ker ≤ Subgroup.center Y →
        (∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w) →
        ∃ (e : Y ≃* SL(n, GaloisField 2 m)) (φ : V ≃* Multiplicative (Fin n → GaloisField 2 m)),
          ∀ (y : Y) (v : V), φ (ρ y v) = Multiplicative.ofAdd (((e y : SL(n, GaloisField 2 m)) :
            Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ v)))

section Helpers

theorem false_of_prime_dvd {Y V : Type} [Group Y] [Finite Y] [Group V] [Finite V]
    (ρ : Y →* MulAut V) (hρ : ρ.ker ≤ Subgroup.center Y) {r k d : ℕ} (hk : 0 < k)
    (hr : IsPrimitivePrimeDivisor r k) (hV : Nat.card V = 2 ^ d) (hdk : d < k)
    (hrK : r ∣ Nat.card (Y ⧸ Subgroup.center Y)) : False := by
  have hdvd := card_quotient_dvd_card_range ρ hρ
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hinj : Function.Injective (ρ.range.subtype : ↥ρ.range →* MulAut V) :=
    Subtype.val_injective
  have := faithful_le_of_primitive ρ.range.subtype hinj hk hV hr (hrK.trans hdvd)
  omega

theorem five_dvd_card_alt {K : Type} [Group K] {k : ℕ} (hk : k = 6 ∨ k = 7)
    (e : K ≃* alternatingGroup (Fin k)) : 5 ∣ Nat.card K := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rcases hk with rfl | rfl <;>
    rw [card_alternatingGroup, Fintype.card_fin] <;> norm_num [Nat.factorial]

theorem isPrimitivePrimeDivisor_five : IsPrimitivePrimeDivisor 5 4 := by
  refine ⟨by norm_num, by norm_num, fun j hj0 hj => ?_⟩
  interval_cases j <;> norm_num

theorem isPrimitivePrimeDivisor_seventeen : IsPrimitivePrimeDivisor 17 8 := by
  refine ⟨by norm_num, by norm_num, fun j hj0 hj => ?_⟩
  interval_cases j <;> norm_num

theorem card_normIn_eq_pow {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} (hS3 : Sec3 T T₁)
    {n m : ℕ} (hq : Nat.card T / Nat.card (normIn T T₁) = 2 ^ m)
    (hT : Nat.card T = (2 ^ m) ^ n) (h4 : 4 < Nat.card T) :
    1 ≤ n ∧ Nat.card (normIn T₁ T) = (2 ^ m) ^ (n - 1) := by
  have hdvd : Nat.card (normIn T T₁) ∣ Nat.card T := Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hmul : 2 ^ m * Nat.card (normIn T T₁) = Nat.card T := by
    rw [← hq]
    exact Nat.div_mul_cancel hdvd
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this, pow_zero] at hT
    omega
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine ⟨hn, ?_⟩
  rw [hS3.card_normIn_swap, Nat.add_sub_cancel]
  have h2 : 0 < 2 ^ m := pow_pos (by norm_num) m
  refine Nat.eq_of_mul_eq_mul_left h2 ?_
  rw [hmul, hT, pow_succ, mul_comm]

end Helpers

theorem eq_of_six (hSmall : Small64Input) {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F]
    [Finite F] {a s m n : ℕ} (hs : 1 ≤ s) (ha : 2 ≤ a) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hd6 : m * n = 6) (hstar : m * (n - 1) = s * (a - 1)) (hF : Nat.card F = 2 ^ s)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a F)) {V : Type} [Group V] [Finite V]
    (hVc : ∀ x y : V, x * y = y * x) (hVsq : ∀ x : V, x * x = 1) (hV : Nat.card V = 2 ^ 6)
    (ρ : Y →* MulAut V) (hker : ρ.ker ≤ Subgroup.center Y)
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w) : m = s ∧ n = a := by
  have hmn : (m = 1 ∧ n = 6) ∨ (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2) := by
    have hm6 : m ≤ 6 := by nlinarith
    interval_cases m <;> omega
  have hsle : s ≤ s * (a - 1) := Nat.le_mul_of_pos_right _ (by omega)
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h5 : s * (a - 1) = 5 := by omega
    have hs5 : s ≤ 5 := by omega
    interval_cases s
    · exact ⟨rfl, by omega⟩
    · omega
    · omega
    · omega
    · obtain rfl : a = 2 := by omega
      exfalso
      have hK : 11 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
        rw [Nat.card_congr e.toEquiv, ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
        norm_num
      exact false_of_prime_dvd ρ hker (k := 10) (d := 6) (by norm_num)
        isPrimitivePrimeDivisor_eleven hV (by norm_num) hK
  · have h4 : s * (a - 1) = 4 := by omega
    have hs4 : s ≤ 4 := by omega
    interval_cases s
    · obtain rfl : a = 5 := by omega
      exact (hSmall 5 (Or.inr rfl) Y ⟨F, inferInstance, inferInstance, by simpa using hF, ⟨e⟩⟩
        V hVc hVsq hV ρ hker htr).elim
    · exact ⟨rfl, by omega⟩
    · omega
    · obtain rfl : a = 2 := by omega
      exfalso
      have hK : 17 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
        rw [Nat.card_congr e.toEquiv, ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
        norm_num
      exact false_of_prime_dvd ρ hker (k := 8) (d := 6) (by norm_num)
        isPrimitivePrimeDivisor_seventeen hV (by norm_num) hK
  · have h3 : s * (a - 1) = 3 := by omega
    have hs3 : s ≤ 3 := by omega
    interval_cases s
    · obtain rfl : a = 4 := by omega
      exact (hSmall 4 (Or.inl rfl) Y ⟨F, inferInstance, inferInstance, by simpa using hF, ⟨e⟩⟩
        V hVc hVsq hV ρ hker htr).elim
    · omega
    · exact ⟨rfl, by omega⟩

theorem step511_core_of
    (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (h215 : Lemma215Stmt) (hList : ListWCIdentification)
    (h9 : A9Input) (hAlt : AltCoverInput) (hMult : MultPrimeInput) (hSmall : Small64Input)
    (hNat : Lemma29Input) (h1 : Sec4NoA) (h3 : Sec4Nine) (h57 : Step57) : Step511Core := by
  intro G _ T T₁ hy h4 n m hq hT
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hS3 : Sec3 T T₁ := hP.sec3 hS
  have hTwc := hP.wc
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm hTwc.1 ha hb
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  have hHN := hSub_le_normalizer hL₁N
  have hsec58 := sec58 h1 hy hS hI
  have htr := h57 G T T₁ hy
  have hnine : ∀ c ∈ hSub T (normIn T₁ T), (∀ t ∈ T, c * t = t * c) →
      ∀ x ∈ hSub T (normIn T₁ T), ⁅c, x⁆ ∈ T := by
    intro c hc hct x hx
    rw [← hsec58] at hc hx
    exact h3 G T T₁ hy hS hI h4 c hc hct x hx
  have hO := sec59 h214 hInv hIso h215 hList h9 h1 h3 h57 hy h4
  obtain ⟨hn1, hLpow⟩ := card_normIn_eq_pow hS3 hq hT h4
  obtain ⟨hL4, -⟩ := card_normIn_facts h214 hInv hIso hy hS3 h4
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0, pow_zero, one_pow] at hT
    omega
  have hn2 : 2 ≤ n := by
    by_contra h
    have h0 : n = 1 := by omega
    rw [h0, Nat.sub_self, pow_zero] at hLpow
    omega
  have hV : Nat.card ↥T = 2 ^ (m * n) := by rw [hT, ← pow_mul]
  have hd3 : 3 ≤ m * n := by
    by_contra h
    push Not at h
    have : 2 ^ (m * n) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hVc : ∀ a b : ↥T, a * b = b * a := fun a b => Subtype.ext (hTc a a.2 b b.2)
  have hVsq : ∀ a : ↥T, a * a = 1 := fun a => Subtype.ext (elemAbelian_mul_self hTwc.1 a.2)
  have hker := ker_actHBar_le_center hTc hL₁N hnine
  have htrρ : ∀ v w : ↥T, v ≠ 1 → w ≠ 1 →
      ∃ y : ↥(hBar T (normIn T₁ T)), actHBar T (normIn T₁ T) hTc y v = w := by
    intro v w hv hw
    obtain ⟨h, hh, hhv⟩ := htr v v.2 (fun h => hv (Subtype.ext h)) w w.2
      (fun h => hw (Subtype.ext h))
    exact ⟨⟨barElt T (hHN hh), barElt_mem_hBar hL₁N _ hh⟩, Subtype.ext hhv⟩
  have hEcard : Nat.card ((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))) =
      Nat.card (normIn T₁ T) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barSub_le_hBar).toEquiv]
    exact card_barSub hL₁N (le_antisymm (le_trans (le_inf inf_le_right
      (le_trans inf_le_left (normIn_le T₁ T))) hS3.cfg.inf.le) bot_le)
  have hĒcard : Nat.card (((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))).map
      (QuotientGroup.mk' (Subgroup.center ↥(hBar T (normIn T₁ T))))) =
      Nat.card (normIn T₁ T) := by
    rw [card_map_eq_of_inf_ker_eq_bot _ (by rw [QuotientGroup.ker_mk']; exact hO.inf_center),
      hEcard]
  have hLexp : Nat.card (normIn T₁ T) = 2 ^ (m * (n - 1)) := by rw [hLpow, ← pow_mul]
  have alt_case : ∀ {k : ℕ}, (k = 6 ∨ k = 7) →
      Nonempty (↥(hBar T (normIn T₁ T)) ⧸ Subgroup.center ↥(hBar T (normIn T₁ T)) ≃*
        alternatingGroup (Fin k)) →
      NaturalSL T (hSub T (normIn T₁ T)) n m ∨
        (Nat.card T = 16 ∧ ∃ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
          (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
            IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))) := by
    intro k hk hKe
    obtain ⟨e⟩ := hKe
    have hĒ4 : Nat.card (((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))).map
        (QuotientGroup.mk' (Subgroup.center ↥(hBar T (normIn T₁ T))))) = 4 := by
      have := hO.stdPair.card_alternating (k := k) (by omega) (by omega) ⟨e⟩
      simp only [show k ≤ 7 by omega, ite_true] at this
      exact this
    have hmn2 : m * (n - 1) = 2 := by
      have : 2 ^ (m * (n - 1)) = 2 ^ 2 := by
        rw [← hLexp, ← hĒcard, hĒ4]
        norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    have hmn : (m = 1 ∧ n = 3) ∨ (m = 2 ∧ n = 2) := by
      have hm2 : m ≤ 2 := by
        have : m ≤ m * (n - 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      interval_cases m <;> omega
    rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      exact false_of_prime_dvd (actHBar T (normIn T₁ T) hTc) hker (k := 4) (d := 3) (by norm_num)
        isPrimitivePrimeDivisor_five hV (by norm_num) (five_dvd_card_alt hk e)
    · right
      have hZ := card_center_dvd_three_of_ident59 hAlt hO hk ⟨e⟩
      refine ⟨by rw [hT]; norm_num, normal_subgroupOf_hSub hL₁N, ?_⟩
      rcases hk with rfl | rfl
      · exact Or.inl (isHatA_of hL₁N hO.perfect hZ ⟨e⟩)
      · exact Or.inr (isHatA_of hL₁N hO.perfect hZ ⟨e⟩)
  rcases hO.ident with ⟨a, s, ha, hs, hmodel⟩ | ⟨hA⟩ | ⟨hA⟩
  ·
    left
    have hmodel' := hmodel
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
    have hĒ : Nat.card (((barSub T (normIn T₁ T)).subgroupOf (hBar T (normIn T₁ T))).map
        (QuotientGroup.mk' (Subgroup.center ↥(hBar T (normIn T₁ T))))) = 2 ^ (s * (a - 1)) := by
      rcases Nat.lt_or_ge a 3 with ha3 | ha3
      · obtain rfl : a = 2 := by omega
        simpa using (hO.stdPair.of_psl2 hmodel').1
      · exact (hO.stdPair.of_psl ha3 F hF e).1
    have hstar : m * (n - 1) = s * (a - 1) := by
      have : 2 ^ (m * (n - 1)) = 2 ^ (s * (a - 1)) := by rw [← hLexp, ← hĒcard, hĒ]
      exact Nat.pow_right_injective (le_refl 2) this
    have hmsna : m = s ∧ n = a := by
      by_cases hd6 : m * n = 6
      · exact eq_of_six hSmall hs ha hm1 hn2 hd6 hstar hF e (V := ↥T) hVc hVsq
          (by rw [hV, hd6]) (actHBar T (normIn T₁ T) hTc) hker htrρ
      · exact eq_of_transitive_primitive hMult hO.perfect hs ha hm1 hn2 hd3 hd6 hstar hF e hV
          (actHBar T (normIn T₁ T) hTc) htrρ
    obtain ⟨hms, hna⟩ := hmsna
    subst hms
    subst hna
    obtain ⟨e', φ, hcompat⟩ := hNat n m hn2 hm1 _ _ hO.perfect hO.wc hO.cl hO.inf_center
      hO.four_le ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
      (fun h3 F hFld hFfin hF e => hO.stdPair.2.2.2.1 n m h3 F hFld hFfin hF e) ↥T hVc hVsq hT
      (actHBar T (normIn T₁ T) hTc) hker htrρ
    exact naturalSL_of hL₁N hTc e' φ hcompat
  ·
    exact alt_case (k := 6) (Or.inl rfl) hA
  · exact alt_case (k := 7) (Or.inr rfl) hA

end CFSG.CGT.Timmesfeld75
