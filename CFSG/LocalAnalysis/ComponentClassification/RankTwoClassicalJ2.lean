module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Orb
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.RankThree.PartTwo.KFacts.KS14 (cE25 gensE25 chkMult5_parts)
open scoped commutatorElement

@[expose] def StdAt (y : GJ) : Prop :=
  ∀ V Λ : Subgroup GJ, IsPGroup 2 V → 4 ≤ Nat.card V → V ≤ centralizer ({y} : Set GJ) →
    y ∈ Λ → Nat.card Λ = 60 → V ≤ centralizer (Λ : Set GJ) →
    ∃ c ∈ ⁅centralizer ({y} : Set GJ), centralizer ({y} : Set GJ)⁆, ∃ v ∈ V,
      c * v * c⁻¹ ∉ centralizer (Λ : Set GJ)

@[expose] def J2StdFacts : Prop := ∀ y : GJ, orderOf y = 5 → StdAt y

theorem centralizer_map_conj (S : Subgroup GJ) (u : GJ) :
    centralizer ((S.map (MulAut.conj u).toMonoidHom : Subgroup GJ) : Set GJ) =
      (centralizer (S : Set GJ)).map (MulAut.conj u).toMonoidHom := by
  set e := MulAut.conj u
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h s hs
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e s) ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    change e s * e y = e y * e s
    rw [← map_mul, ← map_mul, h s hs]

theorem map_conj_centralizer_singleton (y u : GJ) :
    (centralizer ({y} : Set GJ)).map (MulAut.conj u).toMonoidHom =
      centralizer ({u * y * u⁻¹} : Set GJ) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulAut.conj_symm_apply]
  constructor
  · intro h
    calc x * (u * y * u⁻¹) = u * ((u⁻¹ * x * u) * y) * u⁻¹ := by group
      _ = u * (y * (u⁻¹ * x * u)) * u⁻¹ := by rw [h]
      _ = u * y * u⁻¹ * x := by group
  · intro h
    calc u⁻¹ * x * u * y = u⁻¹ * (x * (u * y * u⁻¹)) * u := by group
      _ = u⁻¹ * (u * y * u⁻¹ * x) * u := by rw [h]
      _ = y * (u⁻¹ * x * u) := by group

theorem StdAt.of_conj {y : GJ} (u : GJ) (h : StdAt (u * y * u⁻¹)) : StdAt y := by
  intro V Λ hV2 hV4 hVy hyΛ hΛ hVΛ
  have hcardV : Nat.card (V.map (MulAut.conj u).toMonoidHom) = Nat.card V :=
    card_map_of_injective (MulAut.conj u).injective
  have hcardΛ : Nat.card (Λ.map (MulAut.conj u).toMonoidHom) = Nat.card Λ :=
    card_map_of_injective (MulAut.conj u).injective
  have hC := map_conj_centralizer_singleton y u
  have hCΛ := centralizer_map_conj Λ u
  obtain ⟨c, hc, v', hv', hcv⟩ := h (V.map (MulAut.conj u).toMonoidHom)
    (Λ.map (MulAut.conj u).toMonoidHom) (hV2.map _) (by rw [hcardV]; exact hV4)
    (by rw [← hC]; exact map_mono hVy) ⟨y, hyΛ, rfl⟩ (by rw [hcardΛ]; exact hΛ)
    (by rw [hCΛ]; exact map_mono hVΛ)
  rw [← hC, ← map_commutator] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨v, hv, rfl⟩ := hv'
  refine ⟨c₀, hc₀, v, hv, fun hmem => hcv ?_⟩
  rw [hCΛ]
  refine ⟨c₀ * v * c₀⁻¹, hmem, ?_⟩
  simp [map_mul, map_inv]

theorem j2StdCheck_parts (hc : j2StdCheck = true) :
    j2StdElts = true ∧ j2StdHChk = true ∧ j2StdP5 = true ∧ j2StdOrb = true := by
  simp only [j2StdCheck, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

theorem j2StdElts_parts (h : j2StdElts = true) :
    okA j2StdZ1 = true ∧ okA j2StdZ2 = true ∧ eqA 315 (powArr 315 j2StdZ1 5) (idA 315) = true ∧
    eqA 315 j2StdZ1 (idA 315) = false ∧ eqA 315 (powArr 315 j2StdZ2 5) (idA 315) = true ∧
    eqA 315 j2StdZ2 (idA 315) = false ∧
    (∀ k < j2StdC1.size, okA j2StdC1[k]! = true ∧ commA j2StdC1[k]! j2StdZ1 = true) ∧
    (∀ k < j2StdC2.size, okA j2StdC2[k]! = true ∧ commA j2StdC2[k]! j2StdZ2 = true) ∧
    okA j2StdA1 = true ∧ okA j2StdB1 = true ∧ okA j2StdA2 = true ∧ okA j2StdB2 = true ∧
    commA j2StdA1 j2StdZ1 = true ∧ commA j2StdB1 j2StdZ1 = true ∧ commA j2StdA2 j2StdZ1 = true ∧
    commA j2StdB2 j2StdZ1 = true ∧ (∀ k < j2StdCH.size, okA j2StdCH[k]! = true) ∧
    (∀ k < j2StdH.size, okA j2StdH[k]! = true) ∧
    enumOK 315 j2StdC1 keyPts cStdC1 = true ∧ cStdC1.pts.size = 300 ∧
    enumOK 315 j2StdC2 keyPts cStdC2 = true ∧ cStdC2.pts.size = 50 ∧
    enumOK 315 j2StdH keyPts cStdH = true ∧ cStdH.pts.size = 60 ∧
    enumOK 315 j2StdCH keyPts cStdCH = true ∧ cStdCH.pts.size = 10 := by
  simp only [j2StdElts, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    CFSG.Monster.B.Co2.allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩,
    h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun k hk => by simpa using h7 k hk,
    fun k hk => by simpa using h8 k hk, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩

theorem j2StdHChk_parts (h : j2StdHChk = true) :
    (∀ k < cStdC1.pts.size, isTwoA cStdC1.pts[k]! = true → inCert cStdH cStdC1.pts[k]! = true) ∧
      conjGenOK cStdH j2StdH j2StdSW = true := by
  simp only [j2StdHChk, Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨fun k hk h2 => ?_, h.2⟩
  rcases h.1 k hk with h1 | h1
  · rw [h1] at h2
    exact absurd h2 (by decide)
  · exact h1

theorem j2StdP5_parts (h : j2StdP5 = true) :
    j2StdW.size = 24 ∧ j2StdConj.size = 24 ∧ j2StdJ.size = 24 ∧ j2StdK.size = 24 ∧
    (∀ i < 24, okA j2StdConj[i]! = true ∧ okA j2StdW[i]! = true ∧
      eqA 315 (conjA 315 j2StdConj[i]! j2StdW[i]!) (powArr 315 (j2StdZ j2StdJ[i]!) j2StdK[i]!) =
        true ∧ (j2StdK[i]! = 1 ∨ j2StdK[i]! = 2)) ∧
    (∀ k < cE25.pts.size, eqA 315 cE25.pts[k]! (idA 315) = true ∨
      j2StdW.any (eqA 315 cE25.pts[k]!) = true) := by
  simp only [j2StdP5, Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => by simpa [and_assoc] using h5 i hi, h6⟩

theorem j2StdOrb_spec (hE : j2StdElts = true) (h : j2StdOrb = true)
    (g : GJ) :
    ∃ t, Rep 315 t g.1 ∧ (commA t j2StdZ1 = true → inCert cStdC1 t = true) ∧
      (commA t j2StdZ2 = true → inCert cStdC2 t = true) ∧
      (commA t j2StdH[0]! = true → commA t j2StdH[1]! = true → inCert cStdCH t = true) := by
  obtain ⟨hz1, hz2, -, -, -, -, hC1, hC2, -, -, -, -, -, -, -, -, hCHok, hHok, hen1, hsz1, hen2,
    hsz2, -, -, henCH, hszCH⟩ := j2StdElts_parts hE
  simp only [j2StdOrb, Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff] at h
  obtain ⟨⟨⟨o1, o2⟩, oH⟩, hcomm⟩ := h
  have hHs : j2StdH.size = 2 := rfl
  have hH0 : j2StdH[0]! = j2StdH0 := by simp [j2StdH]
  have hH1 : j2StdH[1]! = j2StdH1 := by simp [j2StdH]
  have rH0 : Rep 315 j2StdH0 (eltOf j2StdH[0]! (hHok 0 (by rw [hHs]; norm_num))).1 :=
    (congrArg (fun t => Rep 315 t (eltOf j2StdH[0]! (hHok 0 (by rw [hHs]; norm_num))).1) hH0).mp
      (rep_eltOf _)
  have rH1 : Rep 315 j2StdH1 (eltOf j2StdH[1]! (hHok 1 (by rw [hHs]; norm_num))).1 :=
    (congrArg (fun t => Rep 315 t (eltOf j2StdH[1]! (hHok 1 (by rw [hHs]; norm_num))).1) hH1).mp
      (rep_eltOf _)
  set x0 := eltOf j2StdH[0]! (hHok 0 (by rw [hHs]; norm_num))
  set x1 := eltOf j2StdH[1]! (hHok 1 (by rw [hHs]; norm_num))
  have e1 : centralizer ({eltOf j2StdZ1 hz1} : Set GJ) = subOf j2StdC1 :=
    cent_eq_subOf hen1 (fun k hk => okA_spec (hC1 k hk).1)
      (fun k hk => by
        rw [mem_centralizer_singleton_iff]
        exact (commute_of_commA (rep_gElt _ _ k hk) (rep_eltOf hz1) (hC1 k hk).2).eq)
      (by simp [hsz1]) (card_cent_single (rep_eltOf hz1) o1)
  have e2 : centralizer ({eltOf j2StdZ2 hz2} : Set GJ) = subOf j2StdC2 :=
    cent_eq_subOf hen2 (fun k hk => okA_spec (hC2 k hk).1)
      (fun k hk => by
        rw [mem_centralizer_singleton_iff]
        exact (commute_of_commA (rep_gElt _ _ k hk) (rep_eltOf hz2) (hC2 k hk).2).eq)
      (by simp [hsz2]) (card_cent_single (rep_eltOf hz2) o2)
  have eH : centralizer ({x0, x1} : Set GJ) = subOf j2StdCH :=
    cent_eq_subOf henCH (fun k hk => okA_spec (hCHok k hk))
      (fun k hk => by
        rw [mem_centralizer_iff]
        rintro y (rfl | rfl)
        · exact (commute_of_commA (rep_gElt _ _ k hk) rH0 (hcomm k hk).1).eq.symm
        · exact (commute_of_commA (rep_gElt _ _ k hk) rH1 (hcomm k hk).2).eq.symm)
      (by simp [hszCH]) (card_cent_pair rH0 rH1 oH)
  obtain ⟨a, ha, b, hb, c, hc, hg⟩ := exists_cperm g
  have ht : Rep 315 (prod3 315 autLevels a b c) g.1 := hg ▸ rep_prod3 ha hb hc
  refine ⟨_, ht, fun h1 => ?_, fun h1 => ?_, fun h1 h2 => ?_⟩
  · refine inCert_of_mem hen1 ht ?_
    rw [← e1, mem_centralizer_singleton_iff]
    exact (commute_of_commA ht (rep_eltOf hz1) h1).eq
  · refine inCert_of_mem hen2 ht ?_
    rw [← e2, mem_centralizer_singleton_iff]
    exact (commute_of_commA ht (rep_eltOf hz2) h1).eq
  · refine inCert_of_mem henCH ht ?_
    rw [← eH, mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (commute_of_commA ht rH0 (hH0 ▸ h1)).eq.symm
    · exact (commute_of_commA ht rH1 (hH1 ▸ h2)).eq.symm

theorem centralizer_pow_eq {z : GJ} (hz : z ^ 5 = 1) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    centralizer ({z ^ k} : Set GJ) = centralizer ({z} : Set GJ) := by
  rcases hk with rfl | rfl
  · rw [pow_one]
  · apply le_antisymm
    · intro x hx
      rw [mem_centralizer_singleton_iff] at hx ⊢
      have h3 : (z ^ 2) ^ 3 = z := by
        rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, hz, one_mul]
      have := (Commute.pow_right (show Commute x (z ^ 2) from hx) 3).eq
      rwa [h3] at this
    · intro x hx
      rw [mem_centralizer_singleton_iff] at hx ⊢
      exact (Commute.pow_right (show Commute x z from hx) 2).eq


theorem centralizer_eq_subOf {t : Array ℕ} {z : GJ} (hz : Rep 315 t z.1)
    {gs : Array (Array ℕ)} {c : CFSG.Monster.B.Fischer.ArrCert}
    (henum : enumOK 315 gs keyPts c = true) (hok : ∀ k < gs.size, okA gs[k]! = true)
    (hgen : ∀ k < gs.size, commA gs[k]! t = true)
    (hscan : ∀ g : GJ, ∃ s, Rep 315 s g.1 ∧ (commA s t = true → inCert c s = true)) :
    centralizer ({z} : Set GJ) = subOf gs := by
  apply le_antisymm
  · intro g hg
    obtain ⟨s, hs, hsc⟩ := hscan g
    exact mem_of_inCert henum hs
      (hsc (commA_of_commute hs hz (mem_centralizer_singleton_iff.mp hg)))
  · refine subOf_le_of gs (fun k hk => okA_spec (hok k hk)) fun k hk => ?_
    rw [mem_centralizer_singleton_iff]
    exact (commute_of_commA (rep_gElt _ _ k hk) hz (hgen k hk)).eq

theorem keyPts_lt : ∀ p ∈ keyPts, p < 315 := by decide

section Base

variable (hc : j2StdCheck = true)
include hc

theorem stdAt_z2 {z : GJ} (hz : Rep 315 j2StdZ2 z.1) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    StdAt (z ^ k) := by
  obtain ⟨hE, -, -, hS⟩ := j2StdCheck_parts hc
  obtain ⟨-, -, -, -, h5, -, -, hC2, -, -, -, -, -, -, -, -, -, -, -, -, hen2, hsz2, -⟩ :=
    j2StdElts_parts hE
  have hz5 : z ^ 5 = 1 := eq_of_rep (rep_pow hz 5) rep_one h5
  have hC : centralizer ({z ^ k} : Set GJ) = subOf j2StdC2 := by
    rw [centralizer_pow_eq hz5 hk]
    refine centralizer_eq_subOf hz hen2 (fun k hk => (hC2 k hk).1) (fun k hk => (hC2 k hk).2)
      fun g => ?_
    obtain ⟨t, ht, -, h2, -⟩ := j2StdOrb_spec hE hS g
    exact ⟨t, ht, h2⟩
  have hcard : Nat.card (subOf j2StdC2) = 50 := by
    rw [card_subOf keyPts_lt hen2 (fun k hk => okA_spec (hC2 k hk).1), hsz2]
  intro V Λ hV2 hV4 hVy _ _ _
  exfalso
  rw [hC] at hVy
  have hdvd := card_dvd_of_le hVy
  rw [hcard] at hdvd
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  rw [hn] at hdvd hV4
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at hV4
  have h4 : 2 ^ 2 ∣ 50 := (Nat.pow_dvd_pow 2 hn2).trans hdvd
  norm_num at h4

theorem stdAt_z1 {z : GJ} (hz : Rep 315 j2StdZ1 z.1) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    StdAt (z ^ k) := by
  obtain ⟨hE, hHC, -, hS⟩ := j2StdCheck_parts hc
  obtain ⟨-, -, h5, -, -, -, hC1, -, hA1, hB1, hA2, hB2, hcA1, hcB1, hcA2, hcB2, hCH, hHok, hen1,
    hsz1, -, -, henH, hszH, henCH, hszCH⟩ := j2StdElts_parts hE
  obtain ⟨htwo, hsimp⟩ := j2StdHChk_parts hHC
  have hz5 : z ^ 5 = 1 := eq_of_rep (rep_pow hz 5) rep_one h5
  have hspec1 : ∀ k < j2StdC1.size, validA 315 j2StdC1[k]! = true ∧ inP j2StdC1[k]! = true :=
    fun k hk => okA_spec (hC1 k hk).1
  have hspecH : ∀ k < j2StdH.size, validA 315 j2StdH[k]! = true ∧ inP j2StdH[k]! = true :=
    fun k hk => okA_spec (hHok k hk)
  have hspecCH : ∀ k < j2StdCH.size, validA 315 j2StdCH[k]! = true ∧ inP j2StdCH[k]! = true :=
    fun k hk => okA_spec (hCH k hk)
  have hC : centralizer ({z ^ k} : Set GJ) = subOf j2StdC1 := by
    rw [centralizer_pow_eq hz5 hk]
    refine centralizer_eq_subOf hz hen1 (fun k hk => (hC1 k hk).1) (fun k hk => (hC1 k hk).2)
      fun g => ?_
    obtain ⟨t, ht, h1, -, -⟩ := j2StdOrb_spec hE hS g
    exact ⟨t, ht, h1⟩
  set C := centralizer ({z ^ k} : Set GJ) with hCdef
  set HJ := subOf j2StdH with hHJ
  have hHsz : j2StdH.size = 2 := by simp [j2StdH]
  have h0 : 0 < j2StdH.size := by rw [hHsz]; norm_num
  have h1 : 1 < j2StdH.size := by rw [hHsz]; norm_num
  have hrepC : ∀ {t u : Array ℕ} (ht : okA t = true) (hu : okA u = true),
      Rep 315 (commutatorA 315 t u) (⁅eltOf t ht, eltOf u hu⁆ : GJ).1 := by
    intro t u ht hu
    have hr := rep_commutatorA (okA_spec ht).1 (okA_spec hu).1
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_eltOf ht),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_eltOf hu)] at hr
    simpa [commutatorElement_def] using hr
  have hmem : ∀ {t : Array ℕ} (ht : okA t = true), commA t j2StdZ1 = true → eltOf t ht ∈ C :=
    fun ht htc => by
      rw [hCdef, centralizer_pow_eq hz5 hk, mem_centralizer_singleton_iff]
      exact (commute_of_commA (rep_eltOf ht) hz htc).eq
  have hg0 : gElt j2StdH hspecH 0 h0 = ⁅eltOf j2StdA1 hA1, eltOf j2StdB1 hB1⁆ := by
    have r0 := rep_gElt _ hspecH 0 h0
    rw [show j2StdH[0]! = j2StdH0 by simp [j2StdH]] at r0
    exact Subtype.ext (r0.unique (hrepC hA1 hB1))
  have hg1 : gElt j2StdH hspecH 1 h1 = ⁅eltOf j2StdA2 hA2, eltOf j2StdB2 hB2⁆ := by
    have r1 := rep_gElt _ hspecH 1 h1
    rw [show j2StdH[1]! = j2StdH1 by simp [j2StdH]] at r1
    exact Subtype.ext (r1.unique (hrepC hA2 hB2))
  have hHC' : HJ ≤ ⁅C, C⁆ := by
    refine subOf_le_of j2StdH hspecH fun i hi => ?_
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · rw [hg0]
      exact commutator_mem_commutator (hmem hA1 hcA1) (hmem hB1 hcB1)
    · rw [hg1]
      exact commutator_mem_commutator (hmem hA2 hcA2) (hmem hB2 hcB2)
  have h2H : ∀ x ∈ C, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ HJ := by
    intro x hx h2
    rw [hC] at hx
    obtain ⟨i, hi, hr⟩ := exists_rep_subOf keyPts_lt hen1 hx
    have hiTwo : isTwoA cStdC1.pts[i]! = true := (isTwoA_iff hr).2 (pow128 h2)
    exact mem_of_inCert henH hr (htwo i hi hiTwo)
  have hsimpH : IsSimpleGroup ↥HJ := by
    have hcl := isSimpleGroup_of_conjGenOK keyPts_lt henH (by rw [hszH]; norm_num) hsimp
    exact (Subgroup.subgroupOfEquivOfLe (closure_le_P hspecH)).isSimpleGroup
  have hCH' : centralizer (HJ : Set GJ) ≤ subOf j2StdCH := by
    intro g hg
    obtain ⟨t, ht, -, -, h3⟩ := j2StdOrb_spec hE hS g
    have hc0 := mem_centralizer_iff.mp hg _ (gElt_mem j2StdH hspecH 0 h0)
    have hc1 := mem_centralizer_iff.mp hg _ (gElt_mem j2StdH hspecH 1 h1)
    exact mem_of_inCert henCH ht (h3 (commA_of_commute ht (rep_gElt _ _ 0 h0) hc0.symm)
      (commA_of_commute ht (rep_gElt _ _ 1 h1) hc1.symm))
  have hcardCH : Nat.card (subOf j2StdCH) = 10 := by
    rw [card_subOf keyPts_lt henCH hspecCH, hszCH]
  intro V Λ hV2 hV4 hVy _ hΛ hVΛ
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra h
    push Not at h
    have hVb : V = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (h x hx)
    rw [hVb, card_bot] at hV4
    norm_num at hV4
  have hvH : v ∈ HJ := by
    refine h2H v (hVy hv) ?_
    obtain ⟨n, hn⟩ := hV2 ⟨v, hv⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  set v' : ↥HJ := ⟨v, hvH⟩
  have hNn : (normalClosure ({v'} : Set ↥HJ)).Normal := normalClosure_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure ({v'} : Set ↥HJ)) with
    hbot | htop
  · apply hv1
    have h := subset_normalClosure (Set.mem_singleton v')
    rw [hbot] at h
    simpa [v'] using congrArg Subtype.val (mem_bot.mp h)
  · have hle : normalClosure ({v'} : Set ↥HJ) ≤ (centralizer (Λ : Set GJ)).subgroupOf HJ := by
      rw [normalClosure, closure_le]
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact hcon c (hHC' c.2) v hv
    rw [htop] at hle
    have hHΛ : HJ ≤ centralizer (Λ : Set GJ) := fun x hx =>
      mem_subgroupOf.mp (hle (mem_top ⟨x, hx⟩))
    have hcard := card_le_of_le ((le_centralizer_iff.mp hHΛ).trans hCH')
    rw [hΛ, hcardCH] at hcard
    norm_num at hcard

end Base

theorem j2StdFacts_of_check (hc : j2StdCheck = true) :
    J2StdFacts := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro y hy
  obtain ⟨hE, -, hP5, -⟩ := j2StdCheck_parts hc
  obtain ⟨hz1, hz2, -⟩ := j2StdElts_parts hE
  obtain ⟨hW24, -, -, -, hdat, hcov⟩ := j2StdP5_parts hP5
  obtain ⟨hx5, hy5, -, -, -, -, -, henE, hszE⟩ := chkMult5_parts
  have hgsz : gensE25.size = 2 := by simp [gensE25]
  have hspecE : ∀ k < gensE25.size, validA 315 gensE25[k]! = true ∧ inP gensE25[k]! = true := by
    intro k hk
    rw [hgsz] at hk
    interval_cases k
    · simpa [gensE25] using okA_spec hx5
    · simpa [gensE25] using okA_spec hy5
  have hcard5 : Nat.card (subOf gensE25) = 25 := by
    rw [card_subOf keyPts_lt henE hspecE, hszE]
  have hP5p : IsPGroup 5 ↥(subOf gensE25) := IsPGroup.of_card (n := 2) (by rw [hcard5]; norm_num)
  have hidx : ¬ 5 ∣ (subOf gensE25).index := by
    have h := (subOf gensE25).index_mul_card
    rw [hcard5, card_GJ] at h
    have h' : (subOf gensE25).index = 24192 := by omega
    rw [h']
    norm_num
  have hzy : IsPGroup 5 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨S, hS⟩ := hzy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GJ (hP5p.toSylow hidx) S
  have hyS : y ∈ ((g • hP5p.toSylow hidx : Sylow 5 GJ) : Set GJ) := by
    rw [hg]
    exact hS (mem_zpowers y)
  rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hyS
  change g⁻¹ * y * g ∈ ((hP5p.toSylow hidx : Subgroup GJ)) at hyS
  rw [IsPGroup.toSylow_coe] at hyS
  set w := g⁻¹ * y * g with hwdef
  have hw1 : w ≠ 1 := by
    intro h1
    have hy1 : y = 1 := by
      calc y = g * w * g⁻¹ := by rw [hwdef]; group
        _ = 1 := by rw [h1]; group
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  obtain ⟨i, hi, hri⟩ := exists_rep_subOf keyPts_lt henE hyS
  rcases hcov i hi with hid | hany
  · exact absurd (eq_of_rep hri rep_one hid) hw1
  rw [Array.any_eq_true] at hany
  obtain ⟨j, hj, hej⟩ := hany
  have hj24 : j < 24 := hW24 ▸ hj
  obtain ⟨hcj, -, hconj, hkj⟩ := hdat j hj24
  have hrw : Rep 315 j2StdW[j]! w.1 := by
    rw [getElem!_pos j2StdW j hj]
    exact rep_of_eqA hri hej
  set c := eltOf j2StdConj[j]! hcj
  have hu : ∀ z : GJ, Rep 315 (j2StdZ j2StdJ[j]!) z.1 →
      (c * g⁻¹) * y * (c * g⁻¹)⁻¹ = z ^ j2StdK[j]! := by
    intro z hz
    have h1 : c * w * c⁻¹ = z ^ j2StdK[j]! :=
      eq_of_rep (rep_conj (rep_eltOf hcj) (okA_spec hcj).1 hrw) (rep_pow hz _) hconj
    rw [← h1, hwdef]
    group
  by_cases hJ : j2StdJ[j]! = 0
  · have hz : Rep 315 (j2StdZ j2StdJ[j]!) (eltOf j2StdZ1 hz1).1 := by
      simp only [j2StdZ, hJ, ↓reduceIte]
      exact rep_eltOf hz1
    refine StdAt.of_conj (c * g⁻¹) ?_
    rw [hu _ hz]
    exact stdAt_z1 hc (rep_eltOf hz1) hkj
  · have hz : Rep 315 (j2StdZ j2StdJ[j]!) (eltOf j2StdZ2 hz2).1 := by
      simp only [j2StdZ, hJ, ↓reduceIte]
      exact rep_eltOf hz2
    refine StdAt.of_conj (c * g⁻¹) ?_
    rw [hu _ hz]
    exact stdAt_z2 hc (rep_eltOf hz2) hkj

theorem mem_P_of_commute {v y : Equiv.Perm (Fin 315)} (hv : v ∈ R) (hv2 : v ^ 2 = 1)
    (hy : y ∈ P) (hy5 : orderOf y = 5) (hvy : v * y = y * v) : v ∈ P := by
  rcases mem_P_or_coset hv with h | h
  · exact h
  exfalso
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [mul_one] at h
    exact permU_not_mem (by simpa using P.inv_mem h)
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  obtain ⟨hcl, -, hC⟩ := outer_classes
  obtain ⟨c, hcP, rfl⟩ := hcl v h hvo
  have hy' : c⁻¹ * y * c ∈ CFSG.Sporadic.Schreier.centralizerIn P permU := by
    rw [CFSG.Sporadic.Schreier.mem_centralizerIn]
    refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hcP) hy) hcP, ?_⟩
    calc c⁻¹ * y * c * permU = c⁻¹ * (y * (c * permU * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * permU * c⁻¹) * y) * c := by rw [← hvy]
      _ = permU * (c⁻¹ * y * c) := by group
  rw [hC] at hy'
  have hdvd : orderOf (⟨c⁻¹ * y * c, hy'⟩ : ↥centOuterChain.originalSubgroup) ∣ 336 := by
    rw [← centOuter_facts.2.1]
    exact orderOf_dvd_natCard _
  have ho : orderOf (c⁻¹ * y * c) = orderOf y := by
    have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective y
    simpa [MulAut.conj_apply] using this
  rw [Subgroup.orderOf_mk, ho, hy5] at hdvd
  norm_num at hdvd

end CFSG.ComponentClassification.RankTwoClassical.J2Std
