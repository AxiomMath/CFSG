module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26S4A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)
open scoped commutatorElement

@[expose] def TightS26DichR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      DEdgeless Φ → ⊤ ∉ Φ → (∃ W' ∈ WSet Φ, MuIsoZ2 Φ W') →
        ∀ A ∈ Φ, ∀ u ∈ A, ∀ m : ℕ, 1 ≤ m → orderOf u = 2 ^ (m + 1) →
          (∃ P : Subgroup X, IsSylow2In P A ∧ Nat.card P = 2 ^ (m + 2)) →
            ∀ β : MulAut X, β u = u → β ^ 2 ^ (m + 1) = 1 →
              β ^ 2 ^ m = 1 ∨ β ^ 2 ^ m = MulAut.conj (u ^ 2 ^ m)

theorem natCard_map_mk_of_isPGroup_gen {H : Type} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] (hN : Odd (Nat.card N)) {P : Subgroup H} (hP : IsPGroup 2 P) :
    Nat.card ↥(P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have h := natCard_map_mk_mul (N := N) P
  have h1 : Nat.card ↥(N ⊓ P) = 1 := by
    obtain ⟨k, hk⟩ := (hP.to_le (inf_le_right : N ⊓ P ≤ P)).exists_card_eq
    have hodd : Odd (Nat.card ↥(N ⊓ P)) := odd_natCard_inf hN P
    rw [hk] at hodd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)
        (Nat.not_even_iff_odd.mpr hodd)
  rw [h1, mul_one] at h
  exact h

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.s26_setup (hs : TightStd8R r n Rd Sd z J S R T W t) {P M : Subgroup Y}
    (hPD : P ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W)
    (hMΩ : M ∈ CoreAssembly.conjClass (tightCore Rd)) (hPM : IsSylow2In P M)
    (hMK : M ≠ tightCore Rd) (hMJ : M ≠ J) {u : Y} (hu : IsUniqueInvolution M u) :
    ∃ (b c : Y) (m : ℕ), 1 ≤ m ∧ orderOf b = 2 ^ (m + 1) ∧ orderOf c = 2 ^ (m + 1) ∧
      b ^ 2 ^ m = u ∧ c ^ 2 ^ m = t ∧ b ∈ W ∧ c ∈ W ∧ c ∈ T ∧ conjSub b (tightCore Rd) =
        tightCore Rd ∧ conjSub b J = J ∧ b * c = c * b ∧ Nat.card T = 2 ^ (m + 2) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup Y), s ∈ Subgroup.normalizer (W : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨hPW, -, hPcyc, hP4, hPcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hPD hMΩ hPM
  obtain ⟨-, -, hTcyc, hT4, hTcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hTD hJΩ hTsyl
  have hPT : Nat.card P = Nat.card T := hΩ.omega3 M hMΩ J hJΩ P T hPM hTsyl
  have hcardUT : Nat.card ↥(T ⊓ W) = Nat.card ↥(P ⊓ W) := by omega
  obtain ⟨b, m, hm, hbU, hbo, hbcard⟩ := s26_exists_gen hPcyc hW2.to_inf_right hP4
  obtain ⟨c, m', -, hcU, hco, hccard⟩ := s26_exists_gen hTcyc hW2.to_inf_right hT4
  have hmm : m' = m := by
    rw [hccard, hbcard] at hcardUT
    have := Nat.pow_right_injective (le_refl 2) hcardUT
    omega
  subst hmm
  have hbW : b ∈ W := hbU.2
  have hcW : c ∈ W := hcU.2
  have hbM : b ∈ M := hPM.1 hbU.1
  have hbu : b ^ 2 ^ m' = u := s26_pow_eq_of_uniqueInvolution hu hbM hbo
  have hct : c ^ 2 ^ m' = t := s26_pow_eq_of_uniqueInvolution hs.ht (hTJ hcU.1) hco
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hK hRD hRsyl hs.hz).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hbp2 : IsPGroup 2 (Subgroup.zpowers b) := hW2.to_le (Subgroup.zpowers_le.mpr hbW)
  have hnc : ¬ ∀ w ∈ M, b * w = w * b := by
    intro hcen
    obtain ⟨r₀, hrP, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
    have hinv : r₀ * b * r₀⁻¹ = b⁻¹ :=
      Q3CL.Thompson.conj_eq_inv_of_mem_inf_W hΩ hW hMΩ hPD hPM hrP hrW (hPW ▸ hbU)
    have h1 : r₀ * b * r₀⁻¹ = b := by
      rw [← hcen r₀ (hPM.1 hrP)]
      group
    have h2 : b * b = 1 := by
      have : b = b⁻¹ := h1.symm.trans hinv
      calc b * b = b * b⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel b
    have h3 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hbo] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have h4 : 2 ^ 2 ≤ 2 ^ (m' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbNK : b ∈ Subgroup.normalizer (K : Set Y) :=
    hΩ.omega5 K hK M hMΩ (Ne.symm hMK) z hs.hz b hbM hnc hbp2 (hWab b hbW z hzW)
  have hbNJ : b ∈ Subgroup.normalizer (J : Set Y) :=
    hΩ.omega5 J hJΩ M hMΩ (Ne.symm hMJ) t hs.ht b hbM hnc hbp2 (hWab b hbW t htW)
  have hTc : Nat.card T = 2 ^ (m' + 2) := by
    rw [hTcard, hccard]
    ring
  exact ⟨b, c, m', hm, hbo, hco, hbu, hct, hbW, hcW, hcU.1,
    mem_normalizer_iff_conjSub_eq.mp hbNK, mem_normalizer_iff_conjSub_eq.mp hbNJ,
    hWab b hbW c hcW, hTc⟩

theorem TightStd8R.s26Act_of_dich_of_ne_top (hD : TightS26DichR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hX₀ : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W) {P M : Subgroup Y}
    (hPD : P ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W)
    (hMΩ : M ∈ CoreAssembly.conjClass (tightCore Rd)) (hPM : IsSylow2In P M)
    (hMK : M ≠ tightCore Rd) (hMJ : M ≠ J) {u : Y} (hu : IsUniqueInvolution M u) :
    ∃ ε : ℕ, ε ≤ 1 ∧
      ∀ x ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
        ⁅u * t ^ ε, x⁆ ∈
          oddCoreOf (omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  classical
  obtain ⟨b, c, m, hm, hbo, hco, hbu, hct, -, -, hcT, hbK, hbJ, hbc, hTc⟩ :=
    hs.s26_setup hPD hMΩ hPM hMK hMJ hu
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hTJ : T ≤ J := hs.hT.2.1
  have hbX : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K :=
    conjSub_omegaNbrGen_of_conjSub_eq hΩ.conjInvariant hbK
  set X : Subgroup Y := omegaNbrGen Ω K with hXdef
  have hbN : b ∈ Subgroup.normalizer (X : Set Y) := mem_normalizer_iff_conjSub_eq.mpr hbX
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have hcJ : c ∈ J := hTJ hcT
  have hcX : c ∈ X := hJX hcJ
  have htX : t ∈ X := hJX hs.ht.mem
  have huN : u ∈ Subgroup.normalizer (X : Set Y) :=
    hbu ▸ (Subgroup.normalizer (X : Set Y)).pow_mem hbN _
  have htN : t ∈ Subgroup.normalizer (X : Set Y) := Subgroup.le_normalizer htX
  let β : MulAut (↥X ⧸ classicalInvolutionOddCore ↥X) := s26Act X ⟨b, hbN⟩
  let ū : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  let tbar : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  have hβū : β ū = ū := by
    refine s26Act_mk X ⟨b, hbN⟩ ⟨c, hcX⟩ ⟨c, hcX⟩ ?_
    show c = b * c * b⁻¹
    rw [hbc]
    group
  have hb2 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set Y))) ^ 2 ^ (m + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hbo]
    exact pow_orderOf_eq_one b
  have hβ2 : β ^ 2 ^ (m + 1) = 1 := by
    rw [← map_pow, hb2, map_one]
  have hβu : β ^ 2 ^ m = s26Act X ⟨u, huN⟩ := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hbu
  have hūt : ū ^ 2 ^ m = tbar := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ m =
      ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
    rw [← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hct
  have ht1 : tbar ≠ 1 := by
    intro h1
    have h2 : (⟨t, htX⟩ : ↥X) ∈ classicalInvolutionOddCore ↥X := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : t ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨htX, h2⟩
    obtain ⟨k, hk⟩ := T8.exists_orderOf_eq_two_pow hs.ht.sq
    exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h3
      (IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])))
  have hū2 : ū ^ 2 ^ (m + 1) = 1 := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ (m + 1) = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 2 ^ (m + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hco]
      exact pow_orderOf_eq_one c
    rw [this]
    rfl
  have hord : orderOf ū = 2 ^ (m + 1) :=
    orderOf_eq_prime_pow (by rw [hūt]; exact ht1) hū2
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hJ' : (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      xFam Ω K := ⟨J.subgroupOf X, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩
  have hūJ' : ū ∈ (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    ⟨⟨c, hcX⟩, hcJ, rfl⟩
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hs.hT.1 hTJ
  have hT' : IsSylow2In (T.subgroupOf X) (J.subgroupOf X) := hTsyl.subgroupOf hJX
  have hTbar := isSylow2In_map_mk hNodd hT'
  have hTbarc : Nat.card ↥((T.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥X))) = 2 ^ (m + 2) := by
    rw [natCard_map_mk_of_isPGroup_gen hNodd hT'.2.1, ← hTc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTJ.trans hJX)).toEquiv
  have hdich : β ^ 2 ^ m = 1 ∨ β ^ 2 ^ m = MulAut.conj tbar := by
    have := hD (XQuot Ω K) (hs.natCard_xQuot_lt_of_ne_top hX₀) (xFam Ω K) h.xFam
      xQuot_oddCore_eq_bot omegaGen_xFam (aEmpty_xFam h)
      (hs.dEdgeless_xFam_S4_of_not_le hKX hS4) hs.top_not_mem_xFam
      (hs.exists_muIsoZ2_xFam_S4_of_not_le hKX hS4) _ hJ' ū hūJ' m hm hord
      ⟨_, hTbar, hTbarc⟩ β hβū hβ2
    rwa [hūt] at this
  have hact : s26Act X ⟨t, htN⟩ = MulAut.conj tbar := s26Act_eq_conj X ⟨t, htX⟩
  rw [hβu] at hdich
  rcases hdich with h0 | h0
  · refine ⟨0, by norm_num, fun x hx => ?_⟩
    have := s26_comm_mem_oddCore_of_act_eq_one X ⟨u, huN⟩ h0 hx
    simpa using this
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have h1 : s26Act X (⟨u, huN⟩ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, h0, hact, ← map_mul]
      have : tbar * tbar = 1 := by
        show ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) *
          ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1
        rw [← QuotientGroup.mk_mul]
        have : (⟨t, htX⟩ : ↥X) * ⟨t, htX⟩ = 1 := Subtype.ext hs.ht.sq
        rw [this]
        rfl
      rw [this, map_one]
    have := s26_comm_mem_oddCore_of_act_eq_one X
      ⟨u * t, (Subgroup.normalizer (X : Set Y)).mul_mem huN htN⟩ h1 hx
    simpa using this

theorem TightStd8R.comm_u_T_of_ne_top (hD : TightS26DichR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hX : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W) {P M : Subgroup Y}
    (hPD : P ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W)
    (hMΩ : M ∈ CoreAssembly.conjClass (tightCore Rd)) (hPM : IsSylow2In P M)
    (hMK : M ≠ tightCore Rd) (hMJ : M ≠ J) {u : Y} (hu : IsUniqueInvolution M u) :
    ∀ x ∈ T, x * u = u * x := by
  obtain ⟨ε, hε, hact⟩ := hs.s26Act_of_dich_of_ne_top hD hX hKX hS4 hPD hMΩ hPM hMK hMJ hu
  have hΩ := hs.hyp
  have hW := hs.hW.1
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup Y), s ∈ Subgroup.normalizer (W : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have huW : u ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hMΩ hPD hPM hu).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hWS : W ≤ (S : Subgroup Y) := hs.hW.2.1
  have hJX := le_omegaNbrGen hs.hJ
  have htε : t ^ ε ∈ (S : Subgroup Y) := (S : Subgroup Y).pow_mem (hWS htW) ε
  intro x hx
  have hxX := hJX (hTJ hx)
  have hc := hact x hxX
  have hvS : u * t ^ ε ∈ (S : Subgroup Y) := (S : Subgroup Y).mul_mem (hWS huW) htε
  have hcS : ⁅u * t ^ ε, x⁆ ∈ (S : Subgroup Y) := by
    rw [commutatorElement_def]
    exact (S : Subgroup Y).mul_mem ((S : Subgroup Y).mul_mem
      ((S : Subgroup Y).mul_mem hvS (hTS hx)) ((S : Subgroup Y).inv_mem hvS))
      ((S : Subgroup Y).inv_mem (hTS hx))
  have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅u * t ^ ε, x⁆) :=
    (S.isPGroup').to_le ((Subgroup.zpowers_le).mpr hcS)
  have hc1 : ⁅u * t ^ ε, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc hc2
  have hcomm : (u * t ^ ε) * x = x * (u * t ^ ε) := by
    rw [commutatorElement_def] at hc1
    calc (u * t ^ ε) * x = (u * t ^ ε * x * (u * t ^ ε)⁻¹ * x⁻¹) * (x * (u * t ^ ε)) := by
          group
      _ = x * (u * t ^ ε) := by rw [hc1, one_mul]
  have htx : t ^ ε * x = x * t ^ ε := by
    interval_cases ε
    · simp
    · rw [pow_one]
      exact hs.ht.commute_of_mem (hTJ hx)
  have h2 : (u * x) * t ^ ε = (x * u) * t ^ ε := by
    calc (u * x) * t ^ ε = u * (x * t ^ ε) := by rw [mul_assoc]
      _ = u * (t ^ ε * x) := by rw [htx]
      _ = (u * t ^ ε) * x := by rw [mul_assoc]
      _ = x * (u * t ^ ε) := hcomm
      _ = (x * u) * t ^ ε := by rw [mul_assoc]
  exact (mul_right_cancel h2).symm

theorem TightStd8R.not_muIsoS4_of (hD : TightS26DichR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hX : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    ¬ MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W := by
  intro hS4
  obtain ⟨φ⟩ := hS4
  have hΩ := hs.hyp
  have hW := hs.hW.1
  have c := Q3CL.T8.ctxOf hs.partIHypG hW
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, hnot⟩ := hs.exists_third_S4 φ
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
  have hcent := hs.comm_u_T_of_ne_top hD hX hKX ⟨φ⟩ hPD hMΩ hPM hMK hMJ hu
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup Y), s ∈ Subgroup.normalizer (W : Set Y) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let σ : Rep (CoreAssembly.conjClass (tightCore Rd)) W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let ρP : Rep (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hrel : σ.r * u * σ.r⁻¹ = t * u :=
    c.conj_involution σ ρP (fun h => hMJ h.symm) hnot hs.ht hu
  have hcomm : σ.r * u = u * σ.r := hcent t' ht'
  have hcu : σ.r * u * σ.r⁻¹ = u := by
    rw [hcomm]
    group
  rw [hcu] at hrel
  apply hs.ht.ne_one
  have : t * u = 1 * u := by rw [← hrel, one_mul]
  exact mul_right_cancel this

theorem tightC26_2R_of (hD : TightS26DichR r n) (hLC : TightLambdaCommR r n) :
    TightC26_2R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc
  exact hs.not_muIsoS4_of hD (hs.omegaNbrGen_ne_top hdisc)
    (hs.not_le_omegaNbrGen (tightSecNbrGenR_of_comm hLC) hdisc)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
