module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7TypeBound
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.OffenderFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Reduction
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Numerics

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev

section Survivors


@[expose] def E7SurvivorBound (s : Fin Tag.E7.rank) (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k (adjointGroup .E7 K) (Fin m → k)) (y : Fin m → k)
    (χ : adjointGroup .E7 K → k) (b : ℕ),
    IsSimpleRep ρ → Function.Injective ρ →
    IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ
      (Finset.univ.erase s) → b < n →
    (∀ z : Kˣ, χ (dC .E7 K s z) = (algebraMap K k (z : K)) ^ (2 ^ b)) →
    ∀ A : Subgroup (adjointGroup .E7 K), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card K ^ Module.finrank k (Representation.invariants (ρ.comp A.subtype)) <
        Nat.card K ^ m

end Survivors

@[expose] def adjointQuotientEquiv7
    (K : Type) [Field K] [Finite K] : AdjointQuotient .E7 K ≃* adjointGroup .E7 K :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

section Main


theorem survivor_numerics {n δ m c e : ℕ} (hδ : 1 ≤ δ) (hnδ : n ∣ δ) (hcm : c ≤ m)
    (hoff : 2 ^ (δ * m) ≤ e * 2 ^ (δ * c)) (hs : e * (2 ^ n) ^ c < (2 ^ n) ^ m) : False := by
  obtain ⟨r, rfl⟩ := hnδ
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp at hδ
    · exact h0
  have h1 : 2 ^ (n * r * m) = 2 ^ (n * r * (m - c)) * 2 ^ (n * r * c) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h1] at hoff
  have h2 : 2 ^ (n * r * (m - c)) ≤ e :=
    Nat.le_of_mul_le_mul_right hoff (by positivity)
  have h3 : 2 ^ (n * (m - c)) ≤ 2 ^ (n * r * (m - c)) := by
    apply Nat.pow_le_pow_right (by norm_num)
    calc n * (m - c) = n * 1 * (m - c) := by ring
      _ ≤ n * r * (m - c) := by gcongr
  have h4 : (2 ^ n) ^ m = 2 ^ (n * (m - c)) * (2 ^ n) ^ c := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h4] at hs
  have h5 : 2 ^ (n * (m - c)) * (2 ^ n) ^ c ≤ e * (2 ^ n) ^ c :=
    Nat.mul_le_mul_right _ (h3.trans h2)
  omega

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem noIrrFFOffender_E7_of_survivors
    (h56 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      E7SurvivorBound n7 K n)
    (h132 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      E7SurvivorBound n1 K n)
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  classical
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel hquad
  by_contra hcon
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hq (MulEquiv.refl _)
  obtain ⟨n, hnq⟩ : ∃ n, n = q.exponent := ⟨_, rfl⟩
  have hn : 1 ≤ n := hnq ▸ q.exponent_pos
  have hK2 : Nat.card K = 2 ^ n := by rw [hK, hq, hnq]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK2
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_E7 hql hn hK2 (e.trans e0)
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* adjointGroup .E7 K :=
    e.trans (e0.trans (adjointQuotientEquiv7 K))
  let f : ↥L →* adjointGroup .E7 K :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, eS.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y :=
      eS.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  let ι : adjointGroup .E7 K ≃* ↥L := (MulEquiv.ofBijective f hf).symm
  have hι : ∀ l, ι.symm l = eS (QuotientGroup.mk l) := fun l => rfl
  have hnt : Nontrivial (adjointGroup .E7 K) :=
    ⟨⟨xC .E7 K n7 1, 1, xC_ne_one n7 1⟩⟩
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, hιKinj, hWcard, hent, hext, hfix⟩ :=
    offender_periodic_data_fix hW hql.1 hirr hEN hE hel hquad hoff ι hn hK2
  let _ : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  obtain ⟨y, χ, J, ht⟩ :=
    exists_isChevType (hw := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7) (p := 2) hρ
  have hδper : ∀ (i : Fin Tag.E7.rank) (t : Kˣ), χ (dC .E7 K i t) ^ (2 ^ δ) = χ (dC .E7 K i t) :=
    fun i t => chi_pow_of_entries δ hρ hent ht _ (dC_mem_H i t)
  have hnper := fun (i : Fin Tag.E7.rank) (t : Kˣ) => chi_dC_pow_card hρ ht hK2 i t
  have hbound := e7TypeBound hn hK2 k m ρ y χ J
  have hfin : Module.finrank k (Fin m → k) = m := Module.finrank_fin_fun k
  have hG : Nat.card (adjointGroup .E7 K) < 2 ^ (133 * n) := by
    rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hK2]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := ordE7_lt h2
    rwa [← pow_mul, mul_comm] at this
  obtain ⟨hnf, Θ, hΘrel, -, hΘker, hΘinv⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK2 .E7
      (Or.inl rfl)
  by_cases hout : ∃ (a : MulAut W) (ha : a ∈ E), Θ (phiOf ι (hEN ha)) ≠ 1
  ·
    obtain ⟨a, ha, hΘ1⟩ := hout
    have hφ2 := phiOf_sq ι (hEN ha) (by rw [← pow_two]; exact hel.2 a ha)
    rcases hΘinv (phiOf ι (hEN ha)) (by rw [pow_two]; exact hφ2) with h1 | ⟨hev, hfrob⟩
    · exact absurd h1 hΘ1
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf (phiOf ι (hEN ha))
    have hσ : Θ (phiOf ι (hEN ha)) = σ := hΘrel _ g σ hgσ
    obtain ⟨B, hBu, hB⟩ := hext a ha
    have htw := chi_eq_of_twist ρ hρ ht (phiOf ι (hEN ha)) g σ hgσ B hBu hB
    have hn2per : ∀ (i : Fin Tag.E7.rank) (t : Kˣ),
        χ (dC .E7 K i t) ^ (2 ^ (n / 2)) = χ (dC .E7 K i t) := by
      intro i t
      have h1 := htw i t
      have hcoe : Units.map σ.toRingHom.toMonoidHom t = t ^ (2 ^ (n / 2)) :=
        Units.ext (by simp [← hσ, hfrob])
      rw [hcoe, chi_dC_pow hρ ht] at h1
      exact h1
    obtain ⟨r, hr⟩ := hev
    have hr1 : 1 ≤ r := by omega
    have hn2 : n / 2 = r := by omega
    have hg1 : 1 ≤ Nat.gcd δ (n / 2) := Nat.gcd_pos_of_pos_left _ hδ
    have hper : ∀ (i : Fin Tag.E7.rank) (t : Kˣ),
        χ (dC .E7 K i t) ^ (2 ^ Nat.gcd δ (n / 2)) = χ (dC .E7 K i t) :=
      fun i t => pow_two_pow_gcd _ δ (n / 2) (hδper i t) (hn2per i t)
    have hgn : Nat.gcd δ (n / 2) ∣ n :=
      (Nat.gcd_dvd_right δ (n / 2)).trans (by rw [hn2]; exact ⟨2, by omega⟩)
    obtain ⟨-, h2⟩ := hbound (Nat.gcd δ (n / 2)) hρ hρinj ht hg1 hgn hper
    have hnum := outer_numerics_e7 hδ (Nat.gcd_dvd_right δ (n / 2)) (Nat.gcd_dvd_left δ (n / 2))
      hg1 ⟨r, hr⟩ hn h2
    have hOut : ∀ B : Subgroup (MulAut (adjointGroup .E7 K)),
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : adjointGroup .E7 K →* MulAut _).range) := by
      intro B _ hBsq
      rw [← hΘker]
      refine card_le_two_mul_of_theta Θ B ?_
      intro b hb b' hb' h1 h1'
      rcases hΘinv b (by rw [pow_two]; exact hBsq b hb) with h | ⟨-, hf⟩
      · exact absurd h h1
      rcases hΘinv b' (by rw [pow_two]; exact hBsq b' hb') with h' | ⟨-, hf'⟩
      · exact absurd h' h1'
      exact RingEquiv.ext fun c => (hf c).trans (hf' c).symm
    have hlt : 2 * (Nat.card (Subgroup.center ↥L) * Nat.card (adjointGroup .E7 K)) < Nat.card W := by
      rw [hZ, Subgroup.card_bot, one_mul, hWcard]
      calc 2 * Nat.card (adjointGroup .E7 K) < 2 * 2 ^ (133 * n) := by omega
        _ = 2 ^ (133 * n + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) hnum
    exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 2) hOut hlt) hcon
  ·
    push Not at hout
    have hEL : E ≤ L := by
      intro a ha
      have h1 : phiOf ι (hEN ha) ∈ Θ.ker := hout a ha
      rw [hΘker] at h1
      obtain ⟨s, hs⟩ := h1
      refine mem_of_psiAut_inner hW hql.1 hirr hEN hel eS ha s fun x => ?_
      rw [psiAut_eq_phiOf eS ι hι, ← hs, MulAut.conj_apply]
    have hg1 : 1 ≤ Nat.gcd δ n := Nat.gcd_pos_of_pos_left _ hδ
    have hper : ∀ (i : Fin Tag.E7.rank) (t : Kˣ),
        χ (dC .E7 K i t) ^ (2 ^ Nat.gcd δ n) = χ (dC .E7 K i t) :=
      fun i t => pow_two_pow_gcd _ δ n (hδper i t) (hnper i t)
    obtain ⟨h1, h2⟩ := hbound (Nat.gcd δ n) hρ hρinj ht hg1 (Nat.gcd_dvd_right δ n) hper
    have hlarge : ∀ h133 : (Nat.gcd δ n = n → 133 ≤ m), False := by
      intro h133
      have h1' : n / Nat.gcd δ n = 1 → 133 ≤ m := by
        intro h
        refine h133 ?_
        have hle : Nat.gcd δ n ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right δ n)
        have hpos : 0 < Nat.gcd δ n := hg1
        by_contra hne
        have hlt : Nat.gcd δ n < n := lt_of_le_of_ne hle hne
        have : 2 ≤ n / Nat.gcd δ n := by
          rw [Nat.le_div_iff_mul_le hpos]
          obtain ⟨t, ht⟩ := Nat.gcd_dvd_right δ n
          set g := Nat.gcd δ n with hgdef
          have ht2 : 2 ≤ t := by
            rcases Nat.lt_or_ge t 2 with h | h
            · interval_cases t <;> omega
            · exact h
          calc 2 * g ≤ t * g := Nat.mul_le_mul_right _ ht2
            _ = n := by rw [ht]; ring
        omega
      have hnum := inner_numerics_e7 hδ (Nat.gcd_dvd_right δ n) (Nat.gcd_dvd_left δ n) hg1 h1' h2 hn
      have hlt : Nat.card ↥(L ⊔ E) < Nat.card W := by
        rw [sup_eq_left.2 hEL, hWcard]
        calc Nat.card ↥L = Nat.card (adjointGroup .E7 K) := Nat.card_congr ι.symm.toEquiv
          _ < 2 ^ (133 * n) := hG
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) hnum
      exact absurd (card_mul_card_fixV_lt_of_card_sup_lt hW hql hirr hEN hE hel hlt) hcon
    by_cases hgn : Nat.gcd δ n = n
    · have ht1 : n / Nat.gcd δ n = 1 := by rw [hgn]; exact Nat.div_self (by omega)
      rcases h1 ht1 with h133 | ⟨s, hs, hJ, b, hb, hχ⟩
      · exact hlarge fun _ => h133
      ·
        subst hJ
        set A : Subgroup (adjointGroup .E7 K) := (E.subgroupOf L).map ι.symm.toMonoidHom with hA
        have hAmap : A.map (L.subtype.comp ι.toMonoidHom) = E := by
          rw [hA, Subgroup.map_map]
          have : (L.subtype.comp ι.toMonoidHom).comp ι.symm.toMonoidHom = L.subtype := by
            ext x; simp
          rw [this, Subgroup.subgroupOf_map_subtype, inf_of_le_left hEL]
        have hcardA : Nat.card A = Nat.card E := by
          rw [hA, Subgroup.card_map_of_injective ι.symm.injective]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
        have hAne : A ≠ ⊥ := by
          intro h0
          apply hE
          rw [← hAmap, h0, Subgroup.map_bot]
        have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
          rintro _ ⟨x, hx, rfl⟩
          have h2x : (x : MulAut W) ^ 2 = 1 := hel.2 _ (Subgroup.mem_subgroupOf.1 hx)
          have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using h2x)
          rw [← map_pow, hx2, map_one]
        have hc := hfix A
        rw [hAmap] at hc
        have hcm : Module.finrank k (Representation.invariants (ρ.comp A.subtype)) ≤ m := by
          have := Submodule.finrank_le (Representation.invariants (ρ.comp A.subtype))
          rwa [hfin] at this
        have hsurv : Nat.card A * Nat.card K ^ Module.finrank k
            (Representation.invariants (ρ.comp A.subtype)) < Nat.card K ^ m := by
          rcases hs with rfl | rfl
          · exact h56 K n hn hK2 k m ρ y χ b hρ hρinj ht hb hχ A hAne hA2
          · exact h132 K n hn hK2 k m ρ y χ b hρ hρinj ht hb hχ A hAne hA2
        rw [hcardA, hK2] at hsurv
        have hnδ : n ∣ δ := by rw [← hgn]; exact Nat.gcd_dvd_left δ n
        refine survivor_numerics hδ hnδ hcm ?_ hsurv
        calc 2 ^ (δ * m) = Nat.card W := hWcard.symm
          _ ≤ Nat.card E * Nat.card (fixV E) := hoff
          _ ≤ Nat.card E * 2 ^ (δ * Module.finrank k
              (Representation.invariants (ρ.comp A.subtype))) := Nat.mul_le_mul_left _ hc
    · exact hlarge fun h => absurd h hgn

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
