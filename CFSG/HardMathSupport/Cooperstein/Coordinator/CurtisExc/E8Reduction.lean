module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Exclusion
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTwist
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev

section TypeBound


@[expose] def E8TypeBound (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k (adjointGroup .E8 K) (Fin m → k)) (y : Fin m → k)
    (χ : adjointGroup .E8 K → k) (J : Finset (Fin Tag.E8.rank)) (g : ℕ),
    IsSimpleRep ρ → Function.Injective ρ →
    IsChevType .E8 K 2 exists_weyl_neg_E8 ρ y χ J → 1 ≤ g → g ∣ n →
    (∀ (i : Fin Tag.E8.rank) (t : Kˣ), χ (dC .E8 K i t) ^ (2 ^ g) = χ (dC .E8 K i t)) →
    (n / g = 1 → 248 ≤ m) ∧ (2 ≤ n / g → 248 * (n / g) + 1 ≤ m)

end TypeBound

section Glue

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {G : Type} [Group G]

@[expose] def phiOf (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : MulAut G :=
  ι.trans ((X1.conjAut L hb).trans ι.symm)

theorem phiOf_apply (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (x : G) :
    phiOf ι hb x = ι.symm (X1.conjAut L hb (ι x)) := rfl

theorem psiAut_eq_phiOf (eS : ↥L ⧸ Subgroup.center ↥L ≃* G) (ι : G ≃* ↥L)
    (hι : ∀ l, ι.symm l = eS (QuotientGroup.mk l)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : psiAut L eS hb = phiOf ι hb := by
  refine MulEquiv.ext fun x => ?_
  have hx' : eS (QuotientGroup.mk (ι x)) = x := by rw [← hι]; exact MulEquiv.symm_apply_apply ι x
  rw [phiOf_apply, hι]
  calc psiAut L eS hb x = psiAut L eS hb (eS (QuotientGroup.mk (ι x))) := by rw [hx']
    _ = _ := psiAut_mk eS hb (ι x)

theorem phiOf_sq (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) :
    phiOf ι hb * phiOf ι hb = 1 := by
  refine MulEquiv.ext fun x => ?_
  show phiOf ι hb (phiOf ι hb x) = x
  rw [phiOf_apply, phiOf_apply, MulEquiv.apply_symm_apply]
  have : ι.symm (X1.conjAut L hb (X1.conjAut L hb (ι x))) = x := by
    have h : X1.conjAut L hb (X1.conjAut L hb (ι x)) = ι x := by
      apply Subtype.ext
      rw [X1.coe_conjAut, X1.coe_conjAut]
      calc b * (b * (ι x : MulAut W) * b⁻¹) * b⁻¹ = (b * b) * (ι x : MulAut W) * (b * b)⁻¹ := by
            group
        _ = (ι x : MulAut W) := by rw [hb2]; group
    rw [h, MulEquiv.symm_apply_apply]
  exact this

end Glue

section Numerics

theorem inner_numerics {n δ m g : ℕ} (hδ : 1 ≤ δ) (hgn : g ∣ n) (hgδ : g ∣ δ) (hg : 1 ≤ g)
    (h1 : n / g = 1 → 248 ≤ m) (h2 : 2 ≤ n / g → 248 * (n / g) + 1 ≤ m) (hn : 1 ≤ n) :
    248 * n ≤ δ * m := by
  obtain ⟨a, rfl⟩ := hgn
  have ha : g * a / g = a := Nat.mul_div_cancel_left a hg
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  rw [ha] at h1 h2
  rcases Nat.lt_or_ge a 2 with h | h
  · have ha1 : a = 1 := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hn
      · omega
    subst ha1
    have := h1 rfl
    calc 248 * (g * 1) = g * 248 := by ring
      _ ≤ δ * m := Nat.mul_le_mul hgδ' this
  · have := h2 h
    calc 248 * (g * a) ≤ g * (248 * a + 1) := by nlinarith
      _ ≤ δ * m := Nat.mul_le_mul hgδ' this

theorem outer_numerics {n δ m g : ℕ} (hδ : 1 ≤ δ) (hgn : g ∣ n / 2) (hgδ : g ∣ δ) (hg : 1 ≤ g)
    (hev : Even n) (hn : 1 ≤ n) (h2 : 2 ≤ n / g → 248 * (n / g) + 1 ≤ m) :
    248 * n + 1 ≤ δ * m := by
  obtain ⟨j, hj⟩ := hgn
  obtain ⟨r, hr⟩ := hev
  have hn2 : n / 2 = r := by omega
  rw [hn2] at hj
  have hnj : n = g * (2 * j) := by rw [mul_comm 2 j, ← mul_assoc]; rw [← hj]; omega
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hj; omega
    · exact h0
  have ha : n / g = 2 * j := by rw [hnj]; exact Nat.mul_div_cancel_left _ hg
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  have := h2 (by rw [ha]; omega)
  rw [ha] at this
  calc 248 * n + 1 ≤ g * (248 * (2 * j) + 1) := by rw [hnj]; nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ' this

end Numerics

section Chi


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem chi_dC_pow {ρ : Representation k (adjointGroup τ K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (i : Fin τ.rank) (t : Kˣ) (N : ℕ) :
    χ (dC τ K i (t ^ N)) = χ (dC τ K i t) ^ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  induction N with
  | zero => rw [pow_zero, dC_one, pow_zero]; exact hμ.chi_one
  | succ N ih =>
    rw [pow_succ, dC_mul, hμ.chi_mul (dC_mem_H i _) (dC_mem_H i _), ih, pow_succ]

theorem chi_dC_pow_card {ρ : Representation k (adjointGroup τ K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {n : ℕ} (hK : Nat.card K = 2 ^ n) (i : Fin τ.rank)
    (t : Kˣ) : χ (dC τ K i t) ^ (2 ^ n) = χ (dC τ K i t) := by
  have h1 : t ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := t)
    rwa [Nat.card_units, hK] at this
  have h2 : χ (dC τ K i t) ^ (2 ^ n - 1) = 1 := by
    rw [← chi_dC_pow hρ ht, h1, dC_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
    exact hμ.chi_one
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc χ (dC τ K i t) ^ (2 ^ n) = χ (dC τ K i t) ^ (2 ^ n - 1) * χ (dC τ K i t) := by
        rw [← pow_succ]; congr 1; omega
    _ = χ (dC τ K i t) := by rw [h2, one_mul]

end Chi

section Main


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem noIrrFFOffender_E8_of_typeBound
    (hB : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      E8TypeBound K n)
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  classical
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel hquad
  by_contra hcon
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hq (MulEquiv.refl _)
  obtain ⟨n, hnq⟩ : ∃ n, n = q.exponent := ⟨_, rfl⟩
  have hn : 1 ≤ n := hnq ▸ q.exponent_pos
  have hK2 : Nat.card K = 2 ^ n := by rw [hK, hq, hnq]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK2
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_E8 hql hn hK2 (e.trans e0)
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* adjointGroup .E8 K :=
    e.trans (e0.trans (adjointQuotientEquiv K))
  let f : ↥L →* adjointGroup .E8 K :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, eS.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y :=
      eS.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  let ι : adjointGroup .E8 K ≃* ↥L := (MulEquiv.ofBijective f hf).symm
  have hι : ∀ l, ι.symm l = eS (QuotientGroup.mk l) := fun l => rfl
  have hnt : Nontrivial (adjointGroup .E8 K) :=
    ⟨⟨xC .E8 K n8 1, 1, xC_ne_one n8 1⟩⟩
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, hιKinj, hWcard, hent, hext⟩ :=
    offender_periodic_data hW hql.1 hirr hEN hE hel hquad hoff ι hn hK2
  letI : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (hw := exists_weyl_neg_E8) (p := 2) hρ
  have hδper : ∀ (i : Fin Tag.E8.rank) (t : Kˣ), χ (dC .E8 K i t) ^ (2 ^ δ) = χ (dC .E8 K i t) :=
    fun i t => chi_pow_of_entries δ hρ hent ht _ (dC_mem_H i t)
  have hnper := fun (i : Fin Tag.E8.rank) (t : Kˣ) => chi_dC_pow_card hρ ht hK2 i t
  have hbound := hB K n hn hK2 k m ρ y χ J
  have hG : Nat.card (adjointGroup .E8 K) < 2 ^ (248 * n) := by
    rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK2]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := ordE8_lt h2
    rwa [← pow_mul, mul_comm] at this
  obtain ⟨hnf, Θ, hΘrel, -, hΘker, hΘinv⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK2 .E8
      (Or.inr rfl)
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
    have hn2per : ∀ (i : Fin Tag.E8.rank) (t : Kˣ),
        χ (dC .E8 K i t) ^ (2 ^ (n / 2)) = χ (dC .E8 K i t) := by
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
    have hper : ∀ (i : Fin Tag.E8.rank) (t : Kˣ),
        χ (dC .E8 K i t) ^ (2 ^ Nat.gcd δ (n / 2)) = χ (dC .E8 K i t) :=
      fun i t => pow_two_pow_gcd _ δ (n / 2) (hδper i t) (hn2per i t)
    have hgn : Nat.gcd δ (n / 2) ∣ n :=
      (Nat.gcd_dvd_right δ (n / 2)).trans (by rw [hn2]; exact ⟨2, by omega⟩)
    obtain ⟨-, h2⟩ := hbound (Nat.gcd δ (n / 2)) hρ hρinj ht hg1 hgn hper
    have hnum := outer_numerics hδ (Nat.gcd_dvd_right δ (n / 2)) (Nat.gcd_dvd_left δ (n / 2))
      hg1 ⟨r, hr⟩ hn h2
    have hOut : ∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : adjointGroup .E8 K →* MulAut _).range) := by
      intro B _ hBsq
      rw [← hΘker]
      refine card_le_two_mul_of_theta Θ B ?_
      intro b hb b' hb' h1 h1'
      rcases hΘinv b (by rw [pow_two]; exact hBsq b hb) with h | ⟨-, hf⟩
      · exact absurd h h1
      rcases hΘinv b' (by rw [pow_two]; exact hBsq b' hb') with h' | ⟨-, hf'⟩
      · exact absurd h' h1'
      exact RingEquiv.ext fun c => (hf c).trans (hf' c).symm
    have hlt : 2 * (Nat.card (Subgroup.center ↥L) * Nat.card (adjointGroup .E8 K)) < Nat.card W := by
      rw [hZ, Subgroup.card_bot, one_mul, hWcard]
      calc 2 * Nat.card (adjointGroup .E8 K) < 2 * 2 ^ (248 * n) := by omega
        _ = 2 ^ (248 * n + 1) := by rw [pow_succ]; ring
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
    have hper : ∀ (i : Fin Tag.E8.rank) (t : Kˣ),
        χ (dC .E8 K i t) ^ (2 ^ Nat.gcd δ n) = χ (dC .E8 K i t) :=
      fun i t => pow_two_pow_gcd _ δ n (hδper i t) (hnper i t)
    obtain ⟨h1, h2⟩ := hbound (Nat.gcd δ n) hρ hρinj ht hg1 (Nat.gcd_dvd_right δ n) hper
    have hnum := inner_numerics hδ (Nat.gcd_dvd_right δ n) (Nat.gcd_dvd_left δ n) hg1 h1 h2 hn
    have hlt : Nat.card ↥(L ⊔ E) < Nat.card W := by
      rw [sup_eq_left.2 hEL, hWcard]
      calc Nat.card ↥L = Nat.card (adjointGroup .E8 K) := Nat.card_congr ι.symm.toEquiv
        _ < 2 ^ (248 * n) := hG
        _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) hnum
    exact absurd (card_mul_card_fixV_lt_of_card_sup_lt hW hql hirr hEN hE hel hlt) hcon

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator
