module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UAct
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UAction
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Basic

variable {G : Type} [Group G]

theorem s26_exists_gen [Finite G] {U : Subgroup G} (hcyc : IsCyclic ↥U) (h2 : IsPGroup 2 ↥U)
    (h4 : 4 ≤ Nat.card ↥U) :
    ∃ (b : G) (n : ℕ), 1 ≤ n ∧ b ∈ U ∧ orderOf b = 2 ^ (n + 1) ∧ Nat.card ↥U = 2 ^ (n + 1) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hord : orderOf g = Nat.card ↥U := orderOf_eq_card_of_forall_mem_zpowers hg
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl
    · rw [pow_zero] at hm
      omega
    · rw [pow_one] at hm
      omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨(g : G), n, by omega, g.2, ?_, hm⟩
  rw [Subgroup.orderOf_coe, hord, hm]

theorem s26_pow_eq_of_uniqueInvolution {M : Subgroup G} {u b : G} (hu : IsUniqueInvolution M u)
    (hb : b ∈ M) {n : ℕ} (ho : orderOf b = 2 ^ (n + 1)) : b ^ 2 ^ n = u := by
  have h0 : b ^ 2 ^ (n + 1) = 1 := by
    rw [← ho]
    exact pow_orderOf_eq_one b
  have h1 : (b ^ 2 ^ n) * (b ^ 2 ^ n) = 1 := by
    rw [← pow_two, ← pow_mul, ← pow_succ]
    exact h0
  have h2 : b ^ 2 ^ n ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero n two_ne_zero) ?_
    rw [ho]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hu.unique (b ^ 2 ^ n) (M.pow_mem hb _) h1 with h | h
  · exact absurd h h2
  · exact h

end Basic


section Setup

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem s26_setup {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) {P M : Subgroup G} (hPD : P ∈ DSet Ω W) (hMΩ : M ∈ Ω)
    (hPM : P ≤ M) (hMK : M ≠ K) (hMJ : M ≠ J) {u : G} (hu : IsUniqueInvolution M u) :
    ∃ (b c : G) (n : ℕ), 1 ≤ n ∧ orderOf b = 2 ^ (n + 1) ∧ orderOf c = 2 ^ (n + 1) ∧
      b ^ 2 ^ n = u ∧ c ^ 2 ^ n = t ∧ b ∈ W ∧ c ∈ W ∧ c ∈ T ∧ conjSub b K = K ∧
      conjSub b J = J ∧ b * c = c * b ∧ u ∈ W ∧ t ∈ W ∧
      (Nat.card SL(2, GaloisField p f)).factorization 2 = n + 2 := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have hPsyl : IsSylow2In P M := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hMΩ hPD.1 hPM
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  obtain ⟨hPW, -, hPcyc, hP4, hPcard⟩ := inf_W_of_mem_D hp hq hΩ hW hPD hMΩ hPsyl
  obtain ⟨-, -, hTcyc, hT4, hTcard⟩ := inf_W_of_mem_D hp hq hΩ hW hTD hJΩ hTsyl
  have hPT : Nat.card P = Nat.card T := by
    rw [hΩ.natCard_isSylow2In hMΩ hPsyl, hΩ.natCard_isSylow2In hJΩ hTsyl]
  have hcardUT : Nat.card ↥(T ⊓ W) = Nat.card ↥(P ⊓ W) := by omega
  obtain ⟨b, n, hn, hbU, hbo, hbcard⟩ := s26_exists_gen hPcyc hW2.to_inf_right hP4
  obtain ⟨c, n', hn', hcU, hco, hccard⟩ := s26_exists_gen hTcyc hW2.to_inf_right hT4
  have hnn : n' = n := by
    rw [hccard, hbcard] at hcardUT
    have := Nat.pow_right_injective (le_refl 2) hcardUT
    omega
  subst hnn
  have hbW : b ∈ W := hbU.2
  have hcW : c ∈ W := hcU.2
  have hbM : b ∈ M := hPM hbU.1
  have hbu : b ^ 2 ^ n' = u := s26_pow_eq_of_uniqueInvolution hu hbM hbo
  have hct : c ^ 2 ^ n' = t := s26_pow_eq_of_uniqueInvolution hs.ht (hTJ hcU.1) hco
  have hzW : z ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW hK hRD hRsyl hs.hz).2
  have htW : t ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hbp2 : IsPGroup 2 (Subgroup.zpowers b) := hW2.to_le (Subgroup.zpowers_le.mpr hbW)
  have hnc : ¬ ∀ w ∈ M, b * w = w * b := by
    intro hcen
    obtain ⟨r, hrP, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hPD
    have hinv : r * b * r⁻¹ = b⁻¹ :=
      conj_eq_inv_of_mem_inf_W hp hq hΩ hW hMΩ hPD hPsyl hrP hrW (hPW ▸ hbU)
    have h1 : r * b * r⁻¹ = b := by
      rw [← hcen r (hPM hrP)]
      group
    have h2 : b * b = 1 := by
      have : b = b⁻¹ := h1.symm.trans hinv
      calc b * b = b * b⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel b
    have h3 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hbo] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have h4 : 2 ^ 2 ≤ 2 ^ (n' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbNK : b ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK M hMΩ (Ne.symm hMK) z hs.hz b hbM hnc hbp2 (hWab b hbW z hzW)
  have hbNJ : b ∈ Subgroup.normalizer (J : Set G) :=
    hΩ.omega5 J hJΩ M hMΩ (Ne.symm hMJ) t hs.ht b hbM hnc hbp2 (hWab b hbW t htW)
  have hfac : (Nat.card SL(2, GaloisField p f)).factorization 2 = n' + 2 := by
    have h1 : Nat.card P = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 :=
      hΩ.natCard_isSylow2In hMΩ hPsyl
    have h2 : Nat.card P = 2 ^ (n' + 2) := by
      rw [hPcard, hbcard]
      ring
    rw [h1] at h2
    exact Nat.pow_right_injective (le_refl 2) h2
  exact ⟨b, c, n', hn, hbo, hco, hbu, hct, hbW, hcW, hcU.1, conjSub_eq_of_mem_normalizer hbNK,
    conjSub_eq_of_mem_normalizer hbNJ, hWab b hbW c hcW, hbu ▸ W.pow_mem hbW _,
    htW, hfac⟩

end Setup


section Normalizer

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem s26_conjSub_mem_omegaNbr (hΩ : HypOmegaMod p f Ω) {K J' : Subgroup G} {b : G}
    (hb : conjSub b K = K) (hJ' : J' ∈ omegaNbr Ω K) : conjSub b J' ∈ omegaNbr Ω K := by
  obtain ⟨hJΩ, hJK, R', hR', hR'J, hR'N⟩ := hJ'
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hb
  refine ⟨hΩ.conjInvariant b J' hJΩ, ?_, conjSub b R', conjSub_mem_RSet hΩ hR' b,
    conjSub_mono hR'J, ?_⟩
  · intro h
    apply hJK
    have h2 : conjSub b⁻¹ (conjSub b J') = conjSub b⁻¹ K := by rw [h]
    rw [conjSub_inv_conjSub] at h2
    calc J' = conjSub b⁻¹ K := h2
      _ = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have hy := hR'N hx
    have e : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hy) (Subgroup.inv_mem _ hbN)

theorem s26_conjSub_omegaNbrGen_le (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) ≤ omegaNbrGen Ω K := by
  show (omegaNbrGen Ω K).map (MulAut.conj b).toMonoidHom ≤ omegaNbrGen Ω K
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun M' hM' => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) (conjSub b M')
    (s26_conjSub_mem_omegaNbr hΩ hb hM')

theorem s26_conjSub_omegaNbrGen (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := by
  have h1 := s26_conjSub_omegaNbrGen_le hΩ hb
  have hb' : conjSub b⁻¹ K = K := by
    calc conjSub b⁻¹ K = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  have h2 := s26_conjSub_omegaNbrGen_le (Ω := Ω) hΩ hb'
  refine le_antisymm h1 ?_
  have := conjSub_mono (n := b) h2
  rwa [conjSub_conjSub_inv] at this

end Normalizer


section Dichotomy

variable {p f : ℕ} [Fact p.Prime]

theorem s26_dich_of_lie (hL : S26Aut164L p) (hU : S26Aut164U p) {Y : Type} [Group Y]
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ) (hadm : StatedLieAdmissible t k p e)
    (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hcase : (t = .PSL ∧ k = 3 ∧ p ^ e % 4 = 3) ∨ (t = .PSU ∧ k = 3 ∧ p ^ e % 4 = 1))
    {R : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    {s : (modelUniv t k p e Fact.out).K} (hs : s ∈ R) {n : ℕ} (hn : 1 ≤ n)
    (hord : orderOf (ψ s) = 2 ^ (n + 1))
    (hmax : t = .PSU → (Nat.card SL(2, GaloisField p e)).factorization 2 = n + 2)
    (β : MulAut Y) (hβs : β (ψ s) = ψ s) (hβ : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ψ s ^ 2 ^ n) := by
  rcases hcase with ⟨rfl, rfl, h4⟩ | ⟨rfl, rfl, h4⟩
  · exact hL e hadm h4 Y ψ hker hsurj R hR s hs n hn hord β hβs hβ
  · exact hU e hadm h4 Y ψ hker hsurj R hR s hs n hn hord (hmax rfl) β hβs hβ

theorem s26_dich_of_sysData (hL : S26Aut164L p) (hU : S26Aut164U p) {Y : Type} [Group Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemData p f Y Φ) (hD1 : D.card = 1) (i : Fin D.card)
    (hcase : (D.tag i = .PSL ∧ D.rank i = 3 ∧ p ^ f % 4 = 3) ∨
      (D.tag i = .PSU ∧ D.rank i = 3 ∧ p ^ f % 4 = 1))
    {J' : Subgroup Y} (hJ' : J' ∈ Φ) {ū : Y} (hū : ū ∈ J') {n : ℕ} (hn : 1 ≤ n)
    (hord : orderOf ū = 2 ^ (n + 1))
    (hmax : (Nat.card SL(2, GaloisField p f)).factorization 2 = n + 2)
    (β : MulAut Y) (hβ : β ū = ū) (hβ2 : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ū ^ 2 ^ n) := by
  have : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  obtain ⟨i', R', hR', hJR'⟩ := D.fundamental J' hJ'
  obtain rfl : i' = i := Subsingleton.elim _ _
  have hsurj : Function.Surjective (D.hom i') := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ j : Fin D.card, (D.hom j).range ≤ (D.hom i').range := by
      intro j
      rw [Subsingleton.elim j i']
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  rw [hJR'] at hū
  obtain ⟨s, hsR, hsū⟩ := Subgroup.mem_map.mp hū
  have hexp : D.exp i' = f := by
    rcases D.exp_eq i' with h | ⟨hT, -⟩
    · exact h
    · exfalso
      rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (h1.symm.trans hT) (by decide)
      · exact absurd (h1.symm.trans hT) (by decide)
  have hcase' : (D.tag i' = .PSL ∧ D.rank i' = 3 ∧ p ^ D.exp i' % 4 = 3) ∨
      (D.tag i' = .PSU ∧ D.rank i' = 3 ∧ p ^ D.exp i' % 4 = 1) := by
    rw [hexp]
    exact hcase
  have key := s26_dich_of_lie hL hU (D.tag i') (D.rank i') (D.exp i') (D.admissible i')
    (D.hom i') (D.ker_le_center i') hsurj hcase' hR' hsR hn (by rw [hsū]; exact hord)
    (fun _ => by rw [hexp]; exact hmax) β (by rw [hsū]; exact hβ) hβ2
  rw [hsū] at key
  exact key

end Dichotomy


section Main

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C26_3_S4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        (SectionLieType p f Ω (omegaNbrGen Ω K) .PSL 3 ∧ p ^ f % 4 = 3) ∨
        (SectionLieType p f Ω (omegaNbrGen Ω K) .PSU 3 ∧ p ^ f % 4 = 1)

variable {p f}

theorem s26Act_of_sec (h3 : C26_3_S4 p f) (hL : S26Aut164L p) (hU : S26Aut164U p) :
    S26Act p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu
  obtain ⟨b, c, n, hn, hbo, hco, hbu, hct, hbW, hcW, hcT, hbK, hbJ, hbc, huW, htW, hfac⟩ :=
    s26_setup hs hPD hMΩ hPM hMK hMJ hu
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hTJ : T ≤ J := hs.hT.2.1
  have hbX : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := s26_conjSub_omegaNbrGen hΩ hbK
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hbN : b ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbX
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hcJ : c ∈ J := hTJ hcT
  have hcX : c ∈ X := hJX hcJ
  have htX : t ∈ X := hJX hs.ht.mem
  have huN : u ∈ Subgroup.normalizer (X : Set G) :=
    hbu ▸ (Subgroup.normalizer (X : Set G)).pow_mem hbN _
  have htN : t ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer htX
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
  have hb2 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 ^ (n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hbo]
    exact pow_orderOf_eq_one b
  have hβ2 : β ^ 2 ^ (n + 1) = 1 := by
    rw [← map_pow, hb2, map_one]
  have hβu : β ^ 2 ^ n = s26Act X ⟨u, huN⟩ := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hbu
  have hūt : ū ^ 2 ^ n = tbar := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ n =
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
    exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h3
      (isPGroup_zpowers_of_mul_self_eq_one hs.ht.sq hs.ht.ne_one))
  have hū2 : ū ^ 2 ^ (n + 1) = 1 := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ (n + 1) = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 2 ^ (n + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hco]
      exact pow_orderOf_eq_one c
    rw [this]
    rfl
  have hord : orderOf ū = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hūt]; exact ht1) hū2
  have hJ' : (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      oddQuotientFamily (restrictFamily Ω X) := ⟨J.subgroupOf X, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩
  have hūJ' : ū ∈ (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    ⟨⟨c, hcX⟩, hcJ, rfl⟩
  have hdich : β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj tbar := by
    rcases h3 G Ω K J S R T W z t hs hdisc hS4 with ⟨⟨D, hD1, i, hit, hir⟩, h4⟩ |
        ⟨⟨D, hD1, i, hit, hir⟩, h4⟩
    · have := s26_dich_of_sysData hL hU D hD1 i (Or.inl ⟨hit, hir, h4⟩) hJ' hūJ' hn hord hfac β
        hβū hβ2
      rwa [hūt] at this
    · have := s26_dich_of_sysData hL hU D hD1 i (Or.inr ⟨hit, hir, h4⟩) hJ' hūJ' hn hord hfac β
        hβū hβ2
      rwa [hūt] at this
  have hact : s26Act X ⟨t, htN⟩ = MulAut.conj tbar := s26Act_eq_conj X ⟨t, htX⟩
  rw [hβu] at hdich
  rcases hdich with h | h
  · refine ⟨0, by norm_num, fun x hx => ?_⟩
    have := s26_comm_mem_oddCore_of_act_eq_one X ⟨u, huN⟩ h hx
    simpa using this
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have h1 : s26Act X (⟨u, huN⟩ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, h, hact, ← map_mul]
      have : tbar * tbar = 1 := by
        show ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) *
          ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1
        rw [← QuotientGroup.mk_mul]
        have : (⟨t, htX⟩ : ↥X) * ⟨t, htX⟩ = 1 := Subtype.ext hs.ht.sq
        rw [this]
        rfl
      rw [this, map_one]
    have := s26_comm_mem_oddCore_of_act_eq_one X
      ⟨u * t, (Subgroup.normalizer (X : Set G)).mul_mem huN htN⟩ h1 hx
    simpa using this

theorem c26_2_u_of_sec (h3 : C26_3_S4 p f) (hL : S26Aut164L p) (hU : S26Aut164U p) :
    C26_2_u p f :=
  c26_2_u_of_act (s26Act_of_sec h3 hL hU)

end Main

end CFSG.ClassicalInvolution.Asc77
