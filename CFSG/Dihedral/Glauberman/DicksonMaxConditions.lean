module

public import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Dickson

public section

namespace CFSG.Glauberman.Dickson.MaxCases

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.GorensteinWalter
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown CFSG.Glauberman.Dickson.MaxSubfield
open CFSG.Glauberman.Dickson.MaxTrace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem psl2_case
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {M : Subgroup (PSL2MatrixGroup F)}
    (hM : IsCoatom M) {m : ℕ} (hm : m ≠ 0) (hmf : m ∣ f)
    (e : M ≃* PSL2MatrixGroup (GaloisField p m)) (W : SubfieldConjugacyWitness p m M) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ f = m * r := by
  have hp' := hp.out
  have hp3 := three_le_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hMc := le_overgroup_of_witness W
  have hMcard : Nat.card M = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_psl2_galoisField' hp2 hm]
  have hx3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm p)
  obtain ⟨j, rfl⟩ := hmf
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hf0 (mul_zero m)
  have hj1 : j ≠ 1 := by
    rintro rfl
    apply hM.1
    apply Subgroup.eq_top_of_card_eq
    rw [hMcard, card_psl2_odd hF hp2, mul_one]
  have hjodd : ¬ 2 ∣ j := by
    rintro ⟨i, rfl⟩
    have h := card_eq_of_isCoatom_subfield hF hp2 hM W.card_eq hMc (dvd_refl m)
      ⟨i, by ring⟩
    rw [hMcard] at h
    have h9 : 9 ≤ (p ^ m) ^ 2 := by nlinarith
    have hpos : 0 < p ^ m * ((p ^ m) ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hjprime : j.Prime := by
    by_contra hnp
    have hr := Nat.minFac_prime hj1
    have hrlt : j.minFac < j :=
      lt_of_le_of_ne (Nat.minFac_le (Nat.pos_of_ne_zero hj0)) (fun h => hnp (h ▸ hr))
    have h := card_ge_of_isCoatom_subfield hF hp2 hM W.card_eq hMc (k := m * j.minFac)
      (dvd_mul_right m _) (Nat.mul_dvd_mul_left m (Nat.minFac_dvd j))
      (Nat.mul_lt_mul_of_pos_left hrlt (Nat.pos_of_ne_zero hm))
    rw [hMcard] at h
    have hsq : (p ^ m) ^ 2 ≤ p ^ (m * j.minFac) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right hp'.pos (Nat.mul_le_mul_left m hr.two_le)
    have := half_lt_half_of_sq_le hx3 hsq
    omega
  exact ⟨j, hjprime, fun h => hjodd ⟨1, by omega⟩, rfl⟩

theorem pgl2_case
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {M : Subgroup (PSL2MatrixGroup F)}
    (hM : IsCoatom M) {m : ℕ} (hm : m ≠ 0) (hmf : 2 * m ∣ f)
    (e : M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))
    (W : SubfieldConjugacyWitness p m M) : f = 2 * m := by
  have hp3 := three_le_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hMc := le_overgroup_of_witness W
  have hMcard : Nat.card M = p ^ m * ((p ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_pgl2_galoisField' hm]
  have hx3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm p)
  obtain ⟨j, rfl⟩ := hmf
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hf0 (mul_zero _)
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hne (mul_one _)
  have h := card_ge_of_isCoatom_subfield hF hp2 hM W.card_eq hMc (k := 2 * m)
    (dvd_mul_left m 2) (dvd_mul_right _ _) (by
      have : 2 ≤ j := by omega
      have : 0 < 2 * m := by omega
      nlinarith)
  rw [hMcard] at h
  have := lt_half_of_sq_le hx3 (le_of_eq (show (p ^ m) ^ 2 = p ^ (2 * m) by
    rw [← pow_mul, mul_comm]))
  omega

theorem nine_le_sq (hp2 : p ≠ 2) : 9 ≤ p ^ 2 := by
  have := three_le_of_ne_two hp2
  nlinarith

theorem sixty_le_card (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) :
    60 ≤ Nat.card (PSL2MatrixGroup F) := by
  rw [card_psl2_odd hF hp2]
  have h1 : 24 ≤ (p ^ f) ^ 2 - 1 := by
    have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have := Nat.mul_le_mul hq5 h1
  omega

theorem eq_three_of_card_le (hp2 : p ≠ 2) {n : ℕ} (hn : n < 60)
    (h : p * (p ^ 2 - 1) / 2 ≤ n) : p = 3 := by
  by_contra hp3
  have hp5 : 5 ≤ p := by
    have := three_le_of_ne_two hp2
    rcases hp.out.odd_of_ne_two hp2 with ⟨j, hj⟩
    omega
  have : 24 ≤ p ^ 2 - 1 := by
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  have := Nat.mul_le_mul hp5 this
  omega

theorem prime_of_card_lt (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) {c : PGL2 F} {K₀ : Subfield F}
    (hK₀ : Nat.card K₀ = p ^ 1)
    (hMc : ∀ x ∈ M, c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage K₀)
    (hf1 : f ≠ 1) (hn : Nat.card M < 360) : f.Prime := by
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  by_contra hnp
  have hr := Nat.minFac_prime hf1
  have hrlt : f.minFac < f :=
    lt_of_le_of_ne (Nat.minFac_le (Nat.pos_of_ne_zero hf0)) (fun h => hnp (h ▸ hr))
  have h := card_ge_of_isCoatom_subfield hF hp2 hM hK₀ hMc (k := f.minFac)
    (one_dvd _) (Nat.minFac_dvd f) hrlt
  have h9 : 9 ≤ p ^ f.minFac :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f.minFac := Nat.pow_le_pow_right (by norm_num) hr.two_le
      _ ≤ p ^ f.minFac := Nat.pow_le_pow_left (three_le_of_ne_two hp2) _
  have := le_mul_sq_sub_one h9
  omega

theorem alternatingFour_case
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) (e : M ≃* alternatingGroup (Fin 4)) :
    (f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
      ∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧
        Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m)) := by
  classical
  have hp' := hp.out
  have hp3 := three_le_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two hF hp2)
  have hMcard : Nat.card M = 12 := by rw [Nat.card_congr e.toEquiv, card_alternatingFour']
  have hGcard := card_psl2_odd hF hp2
  have hK1 : Nat.card (fixField F p 1) = p ^ 1 := card_fixField hF (one_dvd f) one_ne_zero
  obtain ⟨a₀, b₀, ha₀, hb₀, ha₀1, hb₀1, hab₀, hc₀⟩ := alternatingFour_klein
  obtain ⟨a, haM, b, hbM, ha1, hb1, hab, ha2, hb2, hc⟩ :=
    klein_of_mulEquiv e ha₀ hb₀ ha₀1 hb₀1 hab₀ hc₀
  obtain ⟨c, hMc⟩ := exists_conj_pglImage h2 (fixField F p 1) M
    (fun A hA => (pow_of_mulEquiv_alternatingFour e hA).elim (trace_mem_of_pow_two _)
      (trace_mem_of_pow_three _)) haM hbM ha1 hb1 hab ha2 hb2 hc
  by_cases hf1 : f = 1
  · subst hf1
    left
    obtain ⟨V, hVcard, hV⟩ := exists_kleinFour e
    have horder : ∀ x ∈ M, x ^ 2 = 1 ∨ x ^ 3 = 1 :=
      fun x hx => pow_of_mulEquiv_alternatingFour e hx
    have hsimple : IsSimpleGroup (PSL2MatrixGroup F) :=
      BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    have hG60 := sixty_le_card hF hp2 hq5
    have hNV : M = Subgroup.normalizer (V : Set (PSL2MatrixGroup F)) :=
      eq_of_isCoatom_le hM (le_normalizer_of_sq conj_mem_self hV)
        (normalizer_ne_top (by omega) (by omega))
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
    have h8 : p % 8 = 3 ∨ p % 8 = 5 := by
      by_contra h8
      have h16 := sq_mod_sixteen_of_mod_eight' (show p % 8 = 1 ∨ p % 8 = 7 by omega)
      have h8G : 8 ∣ Nat.card (PSL2MatrixGroup F) := by
        rw [hGcard, pow_one]
        obtain ⟨t, ht⟩ : 16 ∣ p ^ 2 - 1 := by omega
        rw [ht, show p * (16 * t) = 2 * (8 * (p * t)) by ring,
          Nat.mul_div_cancel_left _ (by norm_num)]
        exact dvd_mul_right 8 _
      obtain ⟨s, -, hsV, hsN, hs8⟩ := exists_normalizing_two_element (le_top : V ≤ ⊤) hVcard
        (by rwa [Subgroup.card_top])
      rw [← hNV] at hsN
      exact hsV (mem_of_pow_eight horder hV hsN hs8)
    refine ⟨rfl, by unfold Nat.ModEq; omega, fun h10 => ?_⟩
    have h10' : p % 10 = 1 ∨ p % 10 = 9 := by unfold Nat.ModEq at h10; omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
    have hVidx : ¬ 2 ∣ V.index := by
      have h1 := V.card_mul_index
      rw [hVcard, hGcard, pow_one] at h1
      have h9 := sq_mod_sixteen_of_mod_eight h8
      obtain ⟨t, ht⟩ : ∃ t, p ^ 2 = 16 * t + 9 := ⟨p ^ 2 / 16, by omega⟩
      rw [ht, show 16 * t + 9 - 1 = 2 * (4 * (2 * t + 1)) by omega,
        show p * (2 * (4 * (2 * t + 1))) = 2 * (4 * (p * (2 * t + 1))) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)] at h1
      have hidx : V.index = p * (2 * t + 1) := by omega
      rw [hidx]
      intro h2'
      have hodd : Odd (p * (2 * t + 1)) := (hp'.odd_of_ne_two hp2).mul (odd_two_mul_add_one t)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')
    obtain ⟨H, ⟨eH⟩⟩ := (CFSG.Glauberman.Dickson.dickson_psl2_subgroup_existence hF).2.2.2.2.2.2.2
      (Or.inr (by rw [pow_one]; exact sq_mod_five_of_mod_ten' h10'))
    obtain ⟨ι, hι⟩ := CFSG.Glauberman.Dickson.exists_injective_alternatingFour_alternatingFive
    let φ : alternatingGroup (Fin 4) →* PSL2MatrixGroup F :=
      H.subtype.comp (eH.symm.toMonoidHom.comp ι)
    have hφ : Function.Injective φ := Subtype.val_injective.comp (eH.symm.injective.comp hι)
    let eA : φ.range ≃* alternatingGroup (Fin 4) := (MonoidHom.ofInjective hφ).symm
    obtain ⟨D, hDcard, hD⟩ := exists_kleinFour eA
    have hAH : φ.range ≤ H := by
      rintro _ ⟨y, rfl⟩
      exact (eH.symm (ι y)).2
    have hAcard : Nat.card φ.range = 12 := by
      rw [Nat.card_congr eA.toEquiv, card_alternatingFour']
    have hHcard : Nat.card H = 60 := by
      rw [Nat.card_congr eH.toEquiv, card_alternatingFive']
    have hp11 : 11 ≤ p := by
      have : p ≠ 9 := by
        rintro rfl
        norm_num at hp'
      omega
    have hH : H ≠ ⊤ := by
      apply ne_top_of_card_lt
      rw [hHcard, hGcard, pow_one]
      apply lt_card_psl2_of
      have : 120 ≤ p ^ 2 - 1 := by
        have : 121 ≤ p ^ 2 := by nlinarith
        omega
      have := Nat.mul_le_mul hp11 this
      omega
    apply not_isCoatom_normalizer_of_sylow hVp hVidx (D := D) (A := φ.range) (K := H)
      (IsPGroup.of_card (n := 2) (by rw [hDcard]; norm_num)) (hDcard.trans hVcard.symm)
      (le_normalizer_of_sq conj_mem_self hD) (by rw [← hNV, hMcard, hAcard]) hAH hH
      (by rw [hAcard, hHcard]; norm_num)
    rw [← hNV]
    exact hM
  · right
    have h1 := card_ge_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 1) (dvd_refl 1)
      (one_dvd f) (by omega)
    rw [hMcard, pow_one] at h1
    have hp3' := eq_three_of_card_le hp2 (by norm_num) h1
    subst hp3'
    have hfodd : ¬ 2 ∣ f := by
      intro h2f
      have := card_eq_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 1) (dvd_refl 1)
        (by simpa using h2f)
      rw [hMcard] at this
      norm_num at this
    have hfprime := prime_of_card_lt hF hp2 hM hK1 hMc hf1 (by rw [hMcard]; norm_num)
    refine ⟨1, f, hfprime, fun h => hfodd ⟨1, by omega⟩, (one_mul f).symm, ?_⟩
    obtain ⟨e3⟩ := nonempty_psl2_galoisField_three
    exact ⟨e.trans e3.symm⟩

theorem exists_sqrt_five_mem [CharP F p] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h : p = 5 ∨ p ^ 2 % 5 = 1) : ∃ s ∈ fixField F p 1, s ^ 2 = 5 := by
  have hK1 : Nat.card (fixField F p 1) = p ^ 1 := card_fixField hF (one_dvd f) one_ne_zero
  obtain ⟨s, hs⟩ := CFSG.Glauberman.Dickson.isSquare_five (F := fixField F p 1) (f := 1) hK1 hp2
    (h.imp id fun h => by rw [pow_one]; exact h)
  refine ⟨s, s.2, ?_⟩
  have h' := congrArg (fixField F p 1).subtype hs
  rw [map_mul, map_ofNat] at h'
  rw [pow_two]
  exact h'.symm

theorem alternatingFive_case (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) (e : M ≃* alternatingGroup (Fin 5))
    (h5 : p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) :
    ((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
        (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∨
      ∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧
        Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m)) := by
  classical
  have hp' := hp.out
  have hp3 := three_le_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two hF hp2)
  have hMcard : Nat.card M = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingFive']
  have hGcard := card_psl2_odd hF hp2
  have hK1 : Nat.card (fixField F p 1) = p ^ 1 := card_fixField hF (one_dvd f) one_ne_zero
  obtain ⟨a₀, b₀, ha₀, hb₀, ha₀1, hb₀1, hab₀, hc₀⟩ := alternatingFive_klein
  obtain ⟨a, haM, b, hbM, ha1, hb1, hab, ha2, hb2, hc⟩ :=
    klein_of_mulEquiv e ha₀ hb₀ ha₀1 hb₀1 hab₀ hc₀
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
  by_cases hsq : p = 5 ∨ p ^ 2 % 5 = 1
  · obtain ⟨s, hsK, hs5⟩ := exists_sqrt_five_mem hF hp2 hsq
    obtain ⟨c, hMc⟩ := exists_conj_pglImage h2 (fixField F p 1) M
      (fun A hA => (pow_of_mulEquiv_alternatingFive e hA).elim (trace_mem_of_pow_two _)
        (fun h => h.elim (trace_mem_of_pow_three _) (trace_mem_of_pow_five h2 hsK hs5)))
      haM hbM ha1 hb1 hab ha2 hb2 hc
    by_cases hf1 : f = 1
    · subst hf1
      rcases hsq with rfl | hsq
      · exfalso
        apply hM.1
        apply Subgroup.eq_top_of_card_eq
        rw [hMcard, hGcard]
        norm_num
      · left
        left
        refine ⟨rfl, ?_⟩
        have := sq_mod_five_of_mod_ten hpodd hsq
        unfold Nat.ModEq
        omega
    · right
      have h1 := card_ge_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 1) (dvd_refl 1)
        (one_dvd f) (by omega)
      rw [hMcard, pow_one] at h1
      have hp5 : p = 5 := by
        rcases hsq with h | h
        · exact h
        · exfalso
          have hp3' : p ≠ 3 := by
            rintro rfl
            norm_num at h
          have hp5' : p ≠ 5 := by
            rintro rfl
            norm_num at h
          have hp7 : 7 ≤ p := by omega
          have : 48 ≤ p ^ 2 - 1 := by
            have : 49 ≤ p ^ 2 := by nlinarith
            omega
          have := Nat.mul_le_mul hp7 this
          omega
      subst hp5
      have hfodd : ¬ 2 ∣ f := by
        intro h2f
        have := card_eq_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 1) (dvd_refl 1)
          (by simpa using h2f)
        rw [hMcard] at this
        norm_num at this
      have hfprime := prime_of_card_lt hF hp2 hM hK1 hMc hf1 (by rw [hMcard]; norm_num)
      refine ⟨1, f, hfprime, fun h => hfodd ⟨1, by omega⟩, (one_mul f).symm, ?_⟩
      obtain ⟨e5⟩ := nonempty_psl2_galoisField_five
      exact ⟨e.trans e5.symm⟩
  · push Not at hsq
    have h54 : p ^ 2 % 5 = 4 := by
      have hp5 : p % 5 ≠ 0 := by
        intro h0
        rcases hp'.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h0) with h | h
        · norm_num at h
        · exact hsq.1 h.symm
      have h := Nat.pow_mod p 2 5
      have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hne := hsq.2
      rw [h] at hne ⊢
      interval_cases hr : p % 5 <;> omega
    have hfe : 2 ∣ f := by
      by_contra hfe
      rcases h5 with h | h
      · exact hsq.1 h
      · exact not_five_dvd h54 hfe h
    have hK2 : Nat.card (fixField F p 2) = p ^ 2 := card_fixField hF hfe two_ne_zero
    obtain ⟨c, hMc⟩ := exists_conj_pglImage h2 (fixField F p 2) M
      (fun A hA => (pow_of_mulEquiv_alternatingFive e hA).elim (trace_mem_of_pow_two _)
        (fun h => h.elim (trace_mem_of_pow_three _) trace_mem_fixField_two_of_pow_five))
      haM hbM ha1 hb1 hab ha2 hb2 hc
    by_cases hf2 : f = 2
    · left
      right
      refine ⟨hf2, ?_⟩
      have h := Nat.pow_mod p 2 5
      have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have h10 : p % 5 = (p % 10) % 5 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
      rw [h] at h54
      unfold Nat.ModEq
      interval_cases hr : p % 5 <;> omega
    · exfalso
      have h1 := card_ge_of_isCoatom_subfield hF hp2 hM hK2 hMc (k := 2) (dvd_refl 2) hfe
        (by obtain ⟨i, hi⟩ := hfe; omega)
      rw [hMcard] at h1
      have := le_mul_sq_sub_one (nine_le_sq hp2)
      omega

theorem exists_conj_of_permFour_even
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    [CharP F p] (hfe : 2 ∣ f) {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M)
    (e : M ≃* Equiv.Perm (Fin 4)) :
    ∃ c : PGL2 F, ∀ x ∈ M,
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage (fixField F p 1) := by
  classical
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two hF hp2)
  let M₄ : Subgroup (PSL2MatrixGroup F) :=
    ((alternatingGroup (Fin 4)).map e.symm.toMonoidHom).map M.subtype
  let e₄ : M₄ ≃* alternatingGroup (Fin 4) :=
    ((e.symm.subgroupMap (alternatingGroup (Fin 4))).trans
      (Subgroup.equivMapOfInjective _ M.subtype Subtype.val_injective)).symm
  have hmem : ∀ x, x ∈ M₄ ↔ ∃ h : x ∈ M, e ⟨x, h⟩ ∈ alternatingGroup (Fin 4) := by
    intro x
    constructor
    · rintro ⟨y, ⟨σ, hσ, rfl⟩, rfl⟩
      refine ⟨(e.symm σ).2, ?_⟩
      change e (e.symm σ) ∈ alternatingGroup (Fin 4)
      rw [e.apply_symm_apply]
      exact hσ
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, ⟨e ⟨x, h⟩, hx, e.symm_apply_apply _⟩, rfl⟩
  have hnormal : ∀ g ∈ M, ∀ x ∈ M₄, g * x * g⁻¹ ∈ M₄ := by
    intro g hg x hx
    obtain ⟨hxM, hxA⟩ := (hmem x).mp hx
    rw [hmem]
    refine ⟨M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg), ?_⟩
    change e (⟨g, hg⟩ * ⟨x, hxM⟩ * (⟨g, hg⟩ : M)⁻¹) ∈ alternatingGroup (Fin 4)
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.Normal.conj_mem inferInstance _ hxA _
  obtain ⟨V, hVcard, hV⟩ := exists_kleinFour e₄
  have horder : ∀ x ∈ M₄, x ^ 2 = 1 ∨ x ^ 3 = 1 :=
    fun x hx => pow_of_mulEquiv_alternatingFour e₄ hx
  have hsimple : IsSimpleGroup (PSL2MatrixGroup F) :=
    BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hG60 := sixty_le_card hF hp2 hq5
  have hNV : M = Subgroup.normalizer (V : Set (PSL2MatrixGroup F)) :=
    eq_of_isCoatom_le hM (le_normalizer_of_sq hnormal hV)
      (normalizer_ne_top (by omega) (by omega))
  obtain ⟨a₀, b₀, ha₀, hb₀, ha₀1, hb₀1, hab₀, hc₀⟩ := alternatingFour_klein
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, ha2, hb2, hc⟩ :=
    klein_of_mulEquiv e₄ ha₀ hb₀ ha₀1 hb₀1 hab₀ hc₀
  obtain ⟨c, hc4⟩ := exists_conj_pglImage h2 (fixField F p 1) M₄
    (fun A hA => (horder _ hA).elim (trace_mem_of_pow_two _) (trace_mem_of_pow_three _))
    ha hb ha1 hb1 hab ha2 hb2 hc
  refine ⟨c, ?_⟩
  have hmemY : ∀ y, y ∈ overgroup (fixField F p 1) c ↔
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL y * c⁻¹ ∈ pglImage (fixField F p 1) :=
    fun y => Iff.rfl
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp', hp'.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hF⟩
  have hYcard : Nat.card (overgroup (fixField F p 1) c) = p * (p ^ 2 - 1) := by
    rw [card_overgroup hodd (by omega), card_subfieldSubgroup_eq _
      (fun x => isSquare_of_mem_fixField hF hp2 (by simpa using hfe) x.2), pgl2_card_formula,
      card_fixField hF (one_dvd f) one_ne_zero, pow_one]
  have h8 : 8 ∣ Nat.card (overgroup (fixField F p 1) c) := by
    rw [hYcard]
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
    have h := Nat.pow_mod p 2 8
    have hlt : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h2' : p % 2 = (p % 8) % 2 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
    have h1 : p ^ 2 % 8 = 1 := by
      rw [h]
      interval_cases hr : p % 8 <;> omega
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp'.pos
    exact Dvd.dvd.mul_left (by omega) p
  have hVY : V ≤ overgroup (fixField F p 1) c := fun v hv => hc4 v ((hV v).mp hv).1
  obtain ⟨s, hsY, hsV, hsN, hs8⟩ := exists_normalizing_two_element hVY hVcard h8
  rw [← hNV] at hsN
  have hsM₄ : s ∉ M₄ := fun h => hsV (mem_of_pow_eight horder hV h hs8)
  intro x hx
  by_cases hx4 : x ∈ M₄
  · exact hc4 x hx4
  · have hsx : s⁻¹ * x ∈ M₄ := by
      rw [hmem] at hx4 hsM₄ ⊢
      push Not at hx4 hsM₄
      refine ⟨M.mul_mem (M.inv_mem hsN) hx, ?_⟩
      have := inv_mul_mem_alternating (hsM₄ hsN) (hx4 hx)
      rw [← map_inv, ← map_mul] at this
      exact this
    have := (overgroup (fixField F p 1) c).mul_mem hsY ((hmemY _).mpr (hc4 _ hsx))
    rw [mul_inv_cancel_left] at this
    exact (hmemY x).mp this

theorem permFour_case
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) (e : M ≃* Equiv.Perm (Fin 4))
    (h16 : 16 ∣ p ^ (2 * f) - 1) :
    (f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∨
      ∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two hF hp2)
  have hMcard : Nat.card M = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
  have hK1 : Nat.card (fixField F p 1) = p ^ 1 := card_fixField hF (one_dvd f) one_ne_zero
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
  obtain ⟨c, hMc⟩ : ∃ c : PGL2 F, ∀ x ∈ M,
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage (fixField F p 1) := by
    by_cases hfe : 2 ∣ f
    · exact exists_conj_of_permFour_even hF hp2 hq5 hfe hM e
    · have h8 : p % 8 = 1 ∨ p % 8 = 7 := by
        by_contra h8
        exact not_sixteen_dvd (by omega) hfe h16
      obtain ⟨s, hsK, hs2⟩ : ∃ s ∈ fixField F p 1, s ^ 2 = 2 := by
        let : Fintype (fixField F p 1) := Fintype.ofFinite _
        have hK : Fintype.card (fixField F p 1) = p := by
          rw [Fintype.card_eq_nat_card, hK1, pow_one]
        obtain ⟨s, hs⟩ := FiniteField.isSquare_two_iff.mpr (by rw [hK]; omega)
        refine ⟨s, s.2, ?_⟩
        have h' := congrArg (fixField F p 1).subtype hs
        rw [map_mul, map_ofNat] at h'
        rw [pow_two]
        exact h'.symm
      obtain ⟨a₀, b₀, ha₀, hb₀, ha₀1, hb₀1, hab₀, hc₀⟩ := permFour_klein
      obtain ⟨a, ha, b, hb, ha1, hb1, hab, ha2, hb2, hc⟩ :=
        klein_of_mulEquiv e ha₀ hb₀ ha₀1 hb₀1 hab₀ hc₀
      exact exists_conj_pglImage h2 (fixField F p 1) M
        (fun A hA => (pow_of_mulEquiv_permFour e hA).elim (trace_mem_of_pow_three _)
          (trace_mem_of_pow_four h2 hsK hs2)) ha hb ha1 hb1 hab ha2 hb2 hc
  by_cases hf1 : f = 1
  · subst hf1
    left
    refine ⟨rfl, ?_⟩
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp'.pos
    rw [mul_one] at h16
    have := mod_eight_of_sq_mod_sixteen (show p ^ 2 % 16 = 1 by omega)
    unfold Nat.ModEq
    omega
  · right
    have h1 := card_ge_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 1) (dvd_refl 1)
      (one_dvd f) (by omega)
    rw [hMcard, pow_one] at h1
    have hp3' := eq_three_of_card_le hp2 (by norm_num) h1
    subst hp3'
    have hfe : 2 ∣ f := by
      by_contra hfe
      exact not_sixteen_dvd (by norm_num) hfe h16
    by_cases hf2 : f = 2
    · refine ⟨1, hf2, ?_⟩
      obtain ⟨e3⟩ := nonempty_pgl2_galoisField_three
      exact ⟨e.trans e3.symm⟩
    · exfalso
      have h1 := card_ge_of_isCoatom_subfield hF hp2 hM hK1 hMc (k := 2) (one_dvd 2) hfe
        (by obtain ⟨i, hi⟩ := hfe; omega)
      rw [hMcard] at h1
      norm_num at h1

end CFSG.Glauberman.Dickson.MaxCases
