module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Ident
import CFSG.GH74.Orders.LieType

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

theorem le_center_or_eq_top_of_isQuasisimple {G : Type*} [Group G] (hq : CFSG.Open.IsQuasisimple G)
    (N : Subgroup G) [N.Normal] : N ≤ Subgroup.center G ∨ N = ⊤ := by
  have hn : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hq.2 _ hn with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hdec : ∀ g : G, ∃ n ∈ N, n⁻¹ * g ∈ Subgroup.center G := by
      intro g
      have hg : (QuotientGroup.mk' (Subgroup.center G) g) ∈
          N.map (QuotientGroup.mk' (Subgroup.center G)) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := hg
      exact ⟨n, hn, QuotientGroup.eq.mp hng⟩
    have hcomm : commutator G ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      obtain ⟨n, hn, hz⟩ := hdec a
      obtain ⟨m, hm, hw⟩ := hdec b
      have conj_eq : ∀ (u v : G), u⁻¹ * v ∈ Subgroup.center G → ∀ x, v * x * v⁻¹ = u * x * u⁻¹ := by
        intro u v huv x
        have hc := Subgroup.mem_center_iff.mp huv x
        calc v * x * v⁻¹ = u * (u⁻¹ * v * x) * (u⁻¹ * v)⁻¹ * u⁻¹ := by group
          _ = u * (x * (u⁻¹ * v)) * (u⁻¹ * v)⁻¹ * u⁻¹ := by rw [hc]
          _ = u * x * u⁻¹ := by group
      have e : a * b * a⁻¹ * b⁻¹ = n * (m * n⁻¹ * m⁻¹) :=
        calc a * b * a⁻¹ * b⁻¹ = (n * b * n⁻¹) * b⁻¹ := by rw [conj_eq n a hz b]
          _ = n * (b * n⁻¹ * b⁻¹) := by group
          _ = n * (m * n⁻¹ * m⁻¹) := by rw [conj_eq m b hw]
      rw [e]
      exact mul_mem hn (mul_mem (mul_mem hm (inv_mem hn)) (inv_mem hm))
    exact top_le_iff.mp (hq.1 ▸ hcomm)

@[expose] def CentralOrTop (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → N ≤ Subgroup.center G ∨ N = ⊤

theorem eq_top_of_centralOrTop {K H : Type*} [Group K] [Group H] (hK : CentralOrTop K)
    (φ : K →* H) (hφ : Function.Surjective φ) (hZ : Subgroup.center H = ⊥)
    (L : Subgroup H) [hL : L.Normal] (hL1 : L ≠ ⊥) : L = ⊤ := by
  rcases hK (L.comap φ) (hL.comap φ) with h | h
  · exfalso
    apply hL1
    rw [eq_bot_iff, ← hZ]
    intro x hx
    obtain ⟨k, rfl⟩ := hφ x
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := hφ y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (h hx)) k']
  · rw [eq_top_iff]
    intro x _
    obtain ⟨k, rfl⟩ := hφ x
    have : k ∈ L.comap φ := h ▸ Subgroup.mem_top k
    exact this

section Quasisimple


theorem centralOrTop_of_valid {c : CompData} (hc : c.Valid) (hne : c ≠ CompData.sl23) :
    CentralOrTop c.G := by
  intro N hN
  rcases hc with ⟨t, n, hFT, hadm, rfl⟩ | h | rfl
  · exact le_center_or_eq_top_of_isQuasisimple
      (ModelFacts.modelClauseZero t n 3 1 Nat.prime_three hFT hadm).1 N
  · exact absurd h hne
  · haveI := (CFSG.Sporadic.Mathieu.fam_m11_simplicity).2.2
    rcases hN.eq_bot_or_eq_top with h | h
    · exact Or.inl (h ▸ bot_le)
    · exact Or.inr h

theorem eq_top_of_orbitLie
    {H : Type} [Group H] [Finite H] {M : Subgroup H} {z : H} (hO : OrbitHyp H M z)
    (hl : OrbitLie H M z) (L : Subgroup H) [L.Normal] (hL1 : L ≠ ⊥) : L = ⊤ := by
  obtain ⟨c, hc, hne, φ, hφ, -, -⟩ := hl
  exact eq_top_of_centralOrTop (centralOrTop_of_valid hc hne) φ hφ (center_eq_bot hO) L hL1

end Quasisimple

section Orders

private theorem prod_Icc_two_three {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 2 3, f i = f 2 * f 3 := by
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

private theorem ordA_one_odd (k : ℕ) : ordA 1 (2 * k + 1) = 2 * k * (k + 1) * (2 * k + 1) := by
  have h2 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  have h3 : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]
    simp
  have h4 : (∏ i ∈ Finset.Icc 2 (1 + 1), ((2 * k + 1) ^ i - 1)) = 4 * k * (k + 1) := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, Finset.Icc_self, Finset.prod_singleton, h2]
  have h5 : (2 * k + 1) ^ (1 * (1 + 1) / 2) = 2 * k + 1 := by norm_num
  simp only [ordA, h3, h4, h5]
  have : (2 * k + 1) * (4 * k * (k + 1)) = 2 * (2 * k * (k + 1) * (2 * k + 1)) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

private theorem ordA_one_ne_g23 {q : ℕ} (hq : Odd q) : ordA 1 q ≠ 4245696 := by
  obtain ⟨k, rfl⟩ := hq
  rw [ordA_one_odd]
  intro h
  have hk : k ≤ 102 := by
    by_contra hk
    have hk103 : 103 ≤ k := by omega
    have : 2 * 103 * (103 + 1) * (2 * 103 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr
    omega
  interval_cases k <;> omega

private theorem ordA_two_ne_g23 (q : ℕ) : ordA 2 q ≠ 4245696 := by
  intro h
  rcases Nat.lt_or_ge q 11 with hq | hq
  · interval_cases q <;> revert h <;> decide
  · unfold ordA at h
    rw [prod_Icc_two_three] at h
    have hg0 : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg3 : Nat.gcd (2 + 1) (q - 1) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h3 : 1331 ≤ q ^ 3 := (by norm_num : 1331 = 11 ^ 3) ▸ Nat.pow_le_pow_left hq 3
    have h2 : 121 ≤ q ^ 2 := (by norm_num : 121 = 11 ^ 2) ▸ Nat.pow_le_pow_left hq 2
    have hlt : 4245697 ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) /
        Nat.gcd (2 + 1) (q - 1) := by
      rw [Nat.le_div_iff_mul_le hg0, show 2 * (2 + 1) / 2 = 3 by norm_num]
      calc 4245697 * Nat.gcd (2 + 1) (q - 1) ≤ 1331 * (120 * 1330) := by omega
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
    omega

private theorem ordTwistedA_two_ne_g23 (q : ℕ) : ordTwistedA 2 q ≠ 4245696 := by
  intro h
  rcases Nat.lt_or_ge q 11 with hq | hq
  · interval_cases q <;> revert h <;> decide
  · unfold ordTwistedA at h
    rw [prod_Icc_two_three] at h
    have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg3 : Nat.gcd (2 + 1) (q + 1) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h3 : 1331 ≤ q ^ 3 := (by norm_num : 1331 = 11 ^ 3) ▸ Nat.pow_le_pow_left hq 3
    have h2 : 121 ≤ q ^ 2 := (by norm_num : 121 = 11 ^ 2) ▸ Nat.pow_le_pow_left hq 2
    have e2 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
      have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, Int.toNat_natCast]
    have e3 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
      have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hlt : 4245697 ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 + 1)) /
        Nat.gcd (2 + 1) (q + 1) := by
      rw [Nat.le_div_iff_mul_le hg0, show 2 * (2 + 1) / 2 = 3 by norm_num]
      calc 4245697 * Nat.gcd (2 + 1) (q + 1) ≤ 1331 * (120 * 1332) := by omega
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
    rw [e2, e3] at h
    omega

end Orders

section Exclusion

variable {H : Type} [Group H] [Finite H]

theorem card_fStarQuot_of_fStarSimple (hs : FStarSimple H) :
    Nat.card (TL4.FStarQuot H) = Nat.card (genFittingFStar H) := by
  haveI := hs.1
  have hZ : Subgroup.center ↥(genFittingFStar H) = ⊥ := TL4.center_eq_bot_of_isSimpleGroup hs.2
  exact Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv

theorem card_dvd_factorial_of_mulEquiv_m12 {G : Type} [Group G]
    (e : G ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12) : Nat.card G ∣ Nat.factorial 12 := by
  have h := Subgroup.card_subgroup_dvd_card CFSG.Blueprint.NativeSporadic.M12
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 12)), Fintype.card_perm,
    Fintype.card_fin] at h
  rw [Nat.card_congr e.toEquiv]
  exact h

theorem not_thm6Exit_of_card_fStar (hs : FStarSimple H)
    (hx : TL4.Thm6Exit H) (hc : Nat.card (genFittingFStar H) = 4245696) : False := by
  have hq : Nat.card (TL4.FStarQuot H) = 4245696 := (card_fStarQuot_of_fStarSimple hs).trans hc
  rcases hx with ⟨p, f, hp, hp2, ⟨-, hL, -⟩ | ⟨hL | hL, -⟩⟩ | ⟨⟨e⟩, -⟩
  · have h1 : Nat.card (TL4.FStarQuot H) = ordA 1 (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
    exact ordA_one_ne_g23 (hp.odd_of_ne_two hp2).pow (h1.symm.trans hq)
  · have h1 : Nat.card (TL4.FStarQuot H) = ordA 2 (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
    exact ordA_two_ne_g23 _ (h1.symm.trans hq)
  · have h1 : Nat.card (TL4.FStarQuot H) = ordTwistedA 2 (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hp2 hL
    exact ordTwistedA_two_ne_g23 _ (h1.symm.trans hq)
  · have h1 := card_dvd_factorial_of_mulEquiv_m12 e
    rw [hq] at h1
    exact absurd h1 (by norm_num [Nat.factorial])

end Exclusion

section Identification


theorem orbitLie_of_card_fStar
    {H : Type} [Group H] [Finite H] {M : Subgroup H} {z : H} (hO : OrbitHyp H M z)
    (hI : OrbitIdent H M z) (hc : Nat.card (genFittingFStar H) = 4245696) :
    OrbitLie H M z := by
  have hle : Nat.card (genFittingFStar H) ≤ Nat.card H := Subgroup.card_le_card_group _
  have hdvd : Nat.card (genFittingFStar H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  rcases hI with hl | ⟨-, -, hx, -⟩ | ⟨-, ⟨e⟩, -⟩ | ⟨hm, -⟩
  · exact hl
  · exact (not_thm6Exit_of_card_fStar hO.fstar hx hc).elim
  · have h1 := hdvd.trans (card_dvd_factorial_of_mulEquiv_m12 e)
    rw [hc] at h1
    exact absurd h1 (by norm_num [Nat.factorial])
  · rcases hm with hm | hm
    · have h1 := TL4.card_of_lieModel_psp_three_two_one hm
      omega
    · have h1 := TL4.card_of_lieModel_pomegaPlus_four_two_one hm
      rw [hc, h1] at hdvd
      exact absurd hdvd (by norm_num)

end Identification

open scoped MatrixGroups

private theorem card_sl2_zmod3 : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field 2]
  simp [ZMod.card, Fin.prod_univ_two]

section Members


theorem nonempty_mulEquiv_q8_of_orbitLie
    {H : Type} [Group H] [Finite H] {M : Subgroup H} {z : H} (hO : OrbitHyp H M z)
    (hl : OrbitLie H M z) : Nonempty (↥M ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨c, -, -, φ, -, -, F, -, hMF, h24, hF⟩ := hl
  have hMΦ : M ∈ CoreAssembly.conjClass M := CoreAssembly.mem_conjClass_self M
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥M))
  obtain ⟨e⟩ := hO.hyp.sylow M hMΦ _ (isSylow2In_map_subtype M S)
  have hPM : (S : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hP8 : Nat.card ↥((S : Subgroup ↥M).map M.subtype) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h8 : 8 ∣ Nat.card M := hP8 ▸ Subgroup.card_dvd_of_le hPM
  have hdvd : Nat.card M ∣ 24 := h24 ▸ Subgroup.card_dvd_of_le hMF
  have hM : Nat.card M = 8 ∨ Nat.card M = 24 := by
    have h1 : Nat.card M ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 0 < Nat.card M := Nat.card_pos
    have h3 : Nat.card M = 8 ∨ Nat.card M = 16 ∨ Nat.card M = 24 := by omega
    rcases h3 with h | h | h
    · exact Or.inl h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · exact Or.inr h
  rcases hM with h | h
  · have hPM' : (S : Subgroup ↥M).map M.subtype = M :=
      Subgroup.eq_of_le_of_card_ge hPM (by rw [h, hP8])
    exact ⟨(MulEquiv.subgroupCongr hPM'.symm).trans e⟩
  · exfalso
    have hMeq : M = F.map φ := Subgroup.eq_of_le_of_card_ge hMF (by rw [h24, h])
    subst hMeq
    obtain ⟨f⟩ := hF.nonempty_equiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ((hO.hyp.twoGroup _ hMΦ).of_equiv f)
    rw [card_sl2_zmod3] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Members

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23
