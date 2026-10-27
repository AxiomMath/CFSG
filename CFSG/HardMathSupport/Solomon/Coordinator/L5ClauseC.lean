module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5UniEven
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Assembly
public import CFSG.HardMathSupport.Solomon.Proving.CentralizerFixed
public import CFSG.HardMathSupport.Solomon.Proving.OddCore
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.U5HeisCentOdd
public import CFSG.HardMathSupport.Solomon.Proving.LowerElt
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Balance.Alt
  CFSG.HardMathSupport.Solomon.Proving

theorem mod_four_eq_two_of_five_dvd {m : ℕ} (h5 : 5 ∣ 2 ^ m + 1) : m % 4 = 2 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ m = 4 * k + r :=
    ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 4).symm⟩
  have h16 : 16 ^ k % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h1 : (2 ^ (4 * k + r) + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
  rw [pow_add, pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num, Nat.add_mod, Nat.mul_mod, h16,
    one_mul, Nat.mod_mod] at h1
  have hm : (4 * k + r) % 4 = r := by omega
  rw [hm]
  interval_cases r <;> simp_all

variable {G : Type} [Group G] [Finite G]

theorem heis_map_of_injective {Lb P : Type*} [Group Lb] [Group P] (ψ : MulAut Lb →* MulAut P)
    (hψ : Function.Injective ψ) (hinn : innerAut P ≤ (innerAut Lb).map ψ)
    {D H : Subgroup (MulAut Lb)} (hD : IsElemAbelian 5 D) (hD2 : Nat.card D = 5 ^ 2)
    (hH : innerAut Lb ≤ H) (hDH : D ≤ Subgroup.normalizer (H : Set (MulAut Lb)))
    (hΔ : localDeltaIn 5 H D ≠ ⊥) :
    IsElemAbelian 5 (D.map ψ) ∧ Nat.card (D.map ψ) = 5 ^ 2 ∧ innerAut P ≤ H.map ψ ∧
      D.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup (MulAut P)) : Set (MulAut P)) ∧
      localDeltaIn 5 (H.map ψ) (D.map ψ) ≠ ⊥ := by
  refine ⟨i1910_isElemAbelian_map ψ hD, by rw [Subgroup.card_map_of_injective hψ, hD2],
    hinn.trans (Subgroup.map_mono hH), (Subgroup.map_mono hDH).trans (Subgroup.le_normalizer_map ψ),
    fun h0 => hΔ ?_⟩
  have hle := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le 5 ψ hψ H D
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
  exact hle

theorem input19_10ClauseC_five_primeFormP_even {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsElemAbelian 5 B) (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B)
    {L : Subgroup G} (hL : GLAPComponent 5 X L) {ℓ m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ m K) (hℓ : ℓ = 2) (h5 : 5 ∣ ℓ ^ m + 1)
    (e : barOf 5 L ⧸ Subgroup.center (barOf 5 L) ≃* primeFormP h (idGram K 5))
    (hS : Nonempty ((↥L ⧸ oPrimeP 5 ↥L) ≃* StatedProj (StatedSU 5 (ℓ ^ m) K)))
    (hnot : ¬ IsCompLocallyBalanced 5 2 B L) : Input19_10ClauseC X B L := by
  classical
  subst hℓ
  have hp : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have := h.finite
  have hm4 := mod_four_eq_two_of_five_dvd h5
  have hperf : commutator (barOf 5 L) = ⊤ := (isQuasisimple_barOf hp hL).1
  have hodd := odd_card_center_barOf hp (by norm_num) L
  set Γ := centerQuotHom e with hΓ
  set ψ := centerQuotAut e with hψ
  have hΓs := centerQuotHom_surjective e
  have hΓk := ker_centerQuotHom e
  have hψinj := centerQuotAut_injective e hperf
  have hψinn := innerAut_le_map_centerQuotAut e
  set R := (primeFormD h (idGram K 5)).comap ψ with hR
  have hinn : innerAut (barOf 5 L) ≤ R := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_comap, centerQuotAut_conj]
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective (normOneScalars h (gramSU h (idGram K 5)) 5) (Γ x)
    rw [← hg, QuotientGroup.mk'_apply, ← primeFormConjHom_eq_conj]
    exact ⟨_, rfl⟩
  have hU : HeisUpper 5 (barOf 5 L) R :=
    (heisUpper_primeFormP h hp (by norm_num) (by omega) (by omega) h5).of_injective ψ hψinj hψinn
  have hA2 := hasCentTorus_two_primeFormP_five h hΓs hΓk hodd h5
  simp only [IsCompLocallyBalanced, IsLocallyBalanced, not_forall] at hnot
  obtain ⟨D, ⟨hDA, hDe, hD2⟩, H, hH, hDH, hΔ⟩ := hnot
  have hAe := isElemAbelian_autBar hB L
  obtain ⟨hAcard, hAR⟩ := hU D hDe hD2 H hH hDH hΔ _ hDA hAe
  obtain ⟨hBN, hm⟩ := five_count_basic hBX hB hrank hL hA2 hAcard
  have hpgA : IsPGroup 5 (autBar 5 B L) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hAe.2 _ g.2)⟩
  obtain ⟨β, hβ⟩ : ∃ β, Nat.card (autBar 5 B L) = 5 ^ β := IsPGroup.iff_card.1 hpgA
  have hβ3 : β ≤ 3 := by
    rw [hβ] at hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hAcard
  have hβ2 : 2 ≤ β := by
    have hdvd : 5 ^ 2 ∣ 5 ^ β := by rw [← hD2, ← hβ]; exact Subgroup.card_dvd_of_le hDA
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hpgB : IsPGroup 5 B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  have hpgC0 : IsPGroup 5 (centB 5 B L) := hpgB.to_le (centB_le 5 B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB 5 B L) = 5 ^ γ := IsPGroup.iff_card.1 hpgC0
  have hmB : CFSG.Open.pRank 5 B = γ + β := by
    rw [hm, pRank_eq_of_card hp (isElemAbelian_of_le_sub (centB_le 5 B L) hB) hγ,
      pRank_eq_of_card hp hAe hβ]
  have hcardB : Nat.card B = 5 ^ (γ + β) := by
    have := card_B_eq 5 B L
    have hri : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact fun b hb => ⟨hb, hBN hb⟩
    rw [this, hri, one_mul, hβ, hγ, ← pow_add, add_comm]
  have hcN := centB_le_normalizer 5 B L
  obtain ⟨z, hzA, hz5, hzcase⟩ : ∃ z ∈ autBar 5 B L, z ^ 5 = 1 ∧
      ((β = 2 ∧ z = 1) ∨ (β = 3 ∧ z ∉ R)) := by
    rcases (by omega : β = 2 ∨ β = 3) with hb2 | hb3
    · exact ⟨1, Subgroup.one_mem _, one_pow _, Or.inl ⟨hb2, rfl⟩⟩
    · obtain ⟨z, hzA, hzD⟩ : ∃ z ∈ autBar 5 B L, z ∉ D := by
        by_contra hc
        push Not at hc
        have := Subgroup.card_le_of_le (show autBar 5 B L ≤ D from hc)
        rw [hβ, hD2, hb3] at this
        norm_num at this
      exact ⟨z, hzA, hAe.2 z hzA, Or.inr ⟨hb3, fun hzR => hzD (hAR z hzA hzR)⟩⟩
  have hT3 : HasTorus 5 3 (barOf 5 L) z := by
    rcases hzcase with ⟨-, rfl⟩ | ⟨-, hzR⟩
    · exact hasTorus_three_primeFormP_five h hΓs hΓk hodd h5
    · exact hasTorus_three_primeFormP_five_fix h hΓs hΓk hodd h5 (b := ψ z)
        (fun x => centerQuotAut_apply e z x) hzR (by rw [← map_pow, hz5, map_one])
  obtain ⟨E, hE, hEc, hEZ, hEz⟩ := hT3
  set C : Subgroup G := ((Subgroup.zpowers z).comap (barAut 5 L)).map
    (Subgroup.normalizer (L : Set G)).subtype ⊓ B with hCdef
  have hCB : C ≤ B := inf_le_right
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := by
    rintro _ ⟨⟨x, -, rfl⟩, -⟩
    exact x.2
  have hCz : ∀ x (hx : x ∈ C), barAut 5 L ⟨x, hCN hx⟩ ∈ Subgroup.zpowers z := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    exact hx
  have hzpow : ∀ y ∈ Subgroup.zpowers z, ∃ k : ℕ, y = z ^ k := by
    intro y hy
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hy : y ∈ Submonoid.powers z)
    exact ⟨k, hk.symm⟩
  have hzk_fix : ∀ k : ℕ, ∀ x ∈ E, (z ^ k) x = x := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hEz x hx, ih x hx]
  have hCE : ∀ c (hc : c ∈ C), ∀ x ∈ E, barAut 5 L ⟨c, hCN hc⟩ x = x := by
    intro c hc x hx
    obtain ⟨k, hk⟩ := hzpow _ (hCz c hc)
    rw [hk]
    exact hzk_fix k x hx
  have hCinn : ∀ c (hc : c ∈ C), barAut 5 L ⟨c, hCN hc⟩ ∈ innerAut (barOf 5 L) →
      barAut 5 L ⟨c, hCN hc⟩ = 1 := by
    intro c hc hinner
    obtain ⟨k, hk⟩ := hzpow _ (hCz c hc)
    rw [hk] at hinner ⊢
    rcases hzcase with ⟨-, rfl⟩ | ⟨-, hzR⟩
    · exact one_pow k
    by_contra hk1
    apply hzR
    have hkR : z ^ k ∈ R := hinn hinner
    have hz1 : z ≠ 1 := fun h1 => hk1 (by rw [h1, one_pow])
    have hzo : orderOf z = 5 := orderOf_eq_prime hz5 hz1
    have hcop : Nat.Coprime k 5 := by
      by_contra hnc'
      have h5k : 5 ∣ k := (Nat.Prime.coprime_iff_not_dvd hp |>.not_left).1 (by
        rwa [Nat.coprime_comm] at hnc')
      obtain ⟨j, rfl⟩ := h5k
      exact hk1 (by rw [pow_mul, hz5, one_pow])
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
      (show Nat.Coprime k (orderOf z) by rw [hzo]; exact hcop)
    have hmemR : (z ^ k) ^ j ∈ R := Subgroup.pow_mem _ hkR j
    rwa [hj] at hmemR
  have hcentC : centB 5 B L ≤ C := by
    intro x hx
    obtain ⟨hx', hxB, h1⟩ := mem_centB.1 hx
    refine ⟨⟨⟨x, hx'⟩, ?_, rfl⟩, hxB⟩
    show barAut 5 L ⟨x, hx'⟩ ∈ Subgroup.zpowers z
    rw [h1]
    exact Subgroup.one_mem _
  have hCcard : Nat.card C = 5 ^ (γ + β - 2) := by
    let φ : ↥C →* MulAut (barOf 5 L) := (barAut 5 L).comp (Subgroup.inclusion hCN)
    have hφker : Nat.card φ.ker = Nat.card (centB 5 B L) := by
      refine Nat.card_congr ⟨fun x => ⟨((x : C) : G), mem_centB.2 ⟨hCN (x : C).2, hCB (x : C).2,
        x.2⟩⟩, fun y => ⟨⟨(y : G), hcentC y.2⟩, (mem_centB.1 y.2).2.2⟩, fun x => rfl, fun y => rfl⟩
    have hφrange : φ.range = Subgroup.zpowers z := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact hCz (x : G) x.2
      · rw [Subgroup.zpowers_le]
        obtain ⟨⟨n, hnN⟩, hnB, hnz⟩ := hzA
        have hnB' : n ∈ B := (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hnB)).1
        have hnC : n ∈ C := ⟨⟨⟨n, hnN⟩, by
          show barAut 5 L ⟨n, hnN⟩ ∈ Subgroup.zpowers z
          rw [hnz]
          exact Subgroup.mem_zpowers z, rfl⟩, hnB'⟩
        exact ⟨⟨n, hnC⟩, hnz⟩
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hφker, hφrange, Nat.card_zpowers, hγ] at h1
    rcases hzcase with ⟨hb2, rfl⟩ | ⟨hb3, hzR⟩
    · rw [orderOf_one, mul_one] at h1
      rw [← h1, hb2, Nat.add_sub_cancel]
    · have hz1 : z ≠ 1 := fun h1' => hzR (h1' ▸ Subgroup.one_mem _)
      rw [orderOf_eq_prime hz5 hz1] at h1
      rw [← h1, hb3, show γ + 3 - 2 = γ + 1 by omega, pow_succ]
  obtain ⟨P, hP, hPcard, hPC⟩ := exists_elemAbelian_centralizer_fixed hp (by norm_num) hBX hB hL
    C hCB hCN E hE hEZ hCE hCinn
  have hCEc : Nat.card C * Nat.card E = 5 ^ (γ + β + 1) := by
    rw [hCcard, hEc, ← pow_add]
    congr 1
    omega
  have hPcard' : Nat.card P = 5 ^ (γ + β + 1) := hPcard.trans hCEc
  have hrkP : CFSG.Open.pRank 5 P = γ + β + 1 := pRank_eq_of_card hp hP hPcard'
  have hPmap : P.map X.subtype ≤ X ⊓ Subgroup.centralizer (C : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer (C : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have := Subgroup.mem_centralizer_iff.1 (hPC hx) ⟨c, hCB.trans hBX hc⟩ hc
    exact congrArg Subtype.val this
  have hrkPmap : CFSG.Open.pRank 5 (P.map X.subtype) = γ + β + 1 :=
    pRank_eq_of_card hp (i1910_isElemAbelian_map X.subtype hP)
      (by rw [Subgroup.card_map_of_injective X.subtype_injective, hPcard'])
  have hrkC : γ + β + 1 ≤ CFSG.Open.pRank 5 (X ⊓ Subgroup.centralizer (C : Set G)) := by
    rw [← hrkPmap]
    exact CFSG.SectionRank.pRank_mono hp.one_lt hPmap
  have hlt : GLATwoLocalRank 5 ↥X < CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) := by
    have h1 : CFSG.Open.pRank 5 P ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) :=
      CFSG.SectionRank.pRank_mono hp.one_lt le_top
    omega
  have hOodd := odd_card_gLAPPrimeCore_of_lt hp hlt
  refine ⟨⟨K, inferInstance, h.finite, 2 ^ m, m, rfl, hm4, by rw [h.card, pow_mul'],
    hS⟩, ?_, C, hCB, ?_, by rw [hmB]; omega⟩
  ·
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨t, htXC⟩, hto⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have htX : t ∈ X := (Subgroup.mem_inf.1 htXC).1
    have htB : ∀ b ∈ B, b * t = t * b :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 htXC).2
    have hto' : orderOf t = 2 :=
      (Subgroup.orderOf_coe (⟨t, htXC⟩ : ↥(X ⊓ Subgroup.centralizer (B : Set G)))).trans hto
    have ht2 : t ^ 2 = 1 := by
      rw [← hto']
      exact pow_orderOf_eq_one t
    have htO : (⟨t, htX⟩ : ↥X) ∉ GLAPPrimeCore 5 ↥X := by
      intro hmem
      have h1 := Subgroup.orderOf_dvd_natCard (GLAPPrimeCore 5 ↥X) hmem
      have h2 : orderOf (⟨t, htX⟩ : ↥X) = 2 :=
        (Subgroup.orderOf_coe (⟨t, htX⟩ : ↥X)).symm.trans hto'
      rw [h2] at h1
      exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)
    by_cases htN : t ∈ Subgroup.normalizer (L : Set G)
    ·
      have hτA : ∀ d ∈ autBar 5 B L, barAut 5 L ⟨t, htN⟩ * d = d * barAut 5 L ⟨t, htN⟩ := by
        rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
        have hbB : b ∈ B := (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hb)).1
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (htB b hbB).symm
      have hτ2 : barAut 5 L ⟨t, htN⟩ ^ 2 ^ 1 = 1 := by
        have h1 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 = 1 := Subtype.ext ht2
        rw [pow_one, ← map_pow, h1, map_one]
      obtain ⟨hDe', hD2', hH', hDH', hΔ'⟩ :=
        heis_map_of_injective ψ hψinj hψinn hDe hD2 hH hDH hΔ
      obtain ⟨A0, B0, ω, hA0, hB0, hA5, hB5, hω, hAB⟩ :=
        exists_heis_primeFormP h h5 hDe' hD2' hH' hDH' hΔ'
      have hcomm : ∀ y ∈ D.map ψ, ψ (barAut 5 L ⟨t, htN⟩) * y = y * ψ (barAut 5 L ⟨t, htN⟩) := by
        rintro _ ⟨d, hd, rfl⟩
        rw [← map_mul, ← map_mul, hτA d (hDA hd)]
      have hψτ : ψ (barAut 5 L ⟨t, htN⟩) = 1 :=
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.eq_one_of_commute_heis_primeFormP_five h hm4 hAB hω hA5 hB5 (hcomm _ hA0) (hcomm _ hB0)
          (e := 1) (by rw [← map_pow, hτ2, map_one])
      have hτ1 : barAut 5 L ⟨t, htN⟩ = 1 := hψinj (by rw [hψτ, map_one])
      obtain ⟨P', S, hPc', hPe', hPcard'', hS, hS2, hPS⟩ :=
        exists_twoLocal_lower_elt hp (by norm_num) hBX hB hL C hCB hCN E hE hEZ hCE hCinn htX
          htN hτ1 (fun c hc => htB c (hCB hc)) ht2 htO
      have hrk : CFSG.Open.pRank 5 P' = γ + β + 1 :=
        pRank_eq_of_card hp ⟨hPc', hPe'⟩ (hPcard''.trans hCEc)
      have h1 : CFSG.Open.pRank 5 P' ≤ GLATwoLocalRank 5 ↥X :=
        pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
      omega
    ·
      have hL' := glaPComponent_gLBConj_of_mem hL htX
      have hne := barX_gLBConj_ne hL htX htN
      have hC₂ := centB_le_centB_gLBConj (p := 5) (L := L) htB
      obtain ⟨eL⟩ := nonempty_barOf_gLBConj hp L t
      obtain ⟨E₁, U, hE₁, hE₁c, hE₁Z, hU1, hU2, hE₁U⟩ := hA2
      have hE₂ : IsElemAbelian 5 (E₁.map eL.toMonoidHom) := i1910_isElemAbelian_map _ hE₁
      have hE₂c : Nat.card (E₁.map eL.toMonoidHom) = 5 ^ 2 := by
        rw [Subgroup.card_map_of_injective eL.injective, hE₁c]
      have hE₂Z : E₁.map eL.toMonoidHom ⊓ Subgroup.center (barOf 5 (GLBConj t L)) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩
        have hxZ' : x ∈ Subgroup.center (barOf 5 L) := by
          have hxZ2 : eL.toMonoidHom x ∈ Subgroup.center (barOf 5 (GLBConj t L)) := hxZ
          rw [Subgroup.mem_center_iff] at hxZ2 ⊢
          intro g
          apply eL.injective
          have := hxZ2 (eL g)
          simpa only [map_mul, MulEquiv.coe_toMonoidHom] using this
        have h1 : x ∈ E₁ ⊓ Subgroup.center (barOf 5 L) := ⟨hx, hxZ'⟩
        rw [hE₁Z, Subgroup.mem_bot] at h1
        rw [h1, map_one]
        exact Subgroup.one_mem _
      obtain ⟨P', S, hPc', hPe', hPcard'', hS, hS2, hPS⟩ :=
        exists_twoLocal_lower_pair hp (by norm_num) hBX hB hL hL' hne.symm (centB 5 B L) le_rfl hC₂
          E₁ U (E₁.map eL.toMonoidHom) hE₁ hE₁Z ⟨hU1, hU2⟩ hE₁U hE₂ hE₂Z
      have hc4 : Nat.card (centB 5 B L) * Nat.card E₁ * Nat.card (E₁.map eL.toMonoidHom) =
          5 ^ (γ + 4) := by
        rw [hγ, hE₁c, hE₂c]
        ring
      have hrk : CFSG.Open.pRank 5 P' = γ + 4 :=
        pRank_eq_of_card hp ⟨hPc', hPe'⟩ (hPcard''.trans hc4)
      have h1 : CFSG.Open.pRank 5 P' ≤ GLATwoLocalRank 5 ↥X :=
        pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
      omega
  ·
    have h1 := Subgroup.card_mul_index (C.subgroupOf B)
    have h2 : Nat.card (C.subgroupOf B) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
    rw [h2, hCcard, hcardB] at h1
    have h3 : 5 ^ (γ + β) = 5 ^ (γ + β - 2) * 5 ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [h3] at h1
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [this]
    norm_num

end CFSG.HardMathSupport.Solomon.Coordinator
