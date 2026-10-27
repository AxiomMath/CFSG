module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo.KFacts.KS14 (cE25 gensE25 chkMult5_parts)
open scoped commutatorElement

@[expose] def SimpleIn {X₀ : Type*} [Group X₀] (x : X₀) : Prop :=
  ∃ H : Subgroup X₀, H ≤ ⁅centralizer ({x} : Set X₀), centralizer ({x} : Set X₀)⁆ ∧
    Nat.card H = 60 ∧ IsSimpleGroup ↥H

@[expose] def A4cd {X₀ : Type*} [Group X₀] (V Λ : Subgroup X₀) : Prop :=
  (∀ z ∈ Λ, orderOf z = 3 → ∀ β : MulAut X₀, (∃ k : ℕ, β ^ 5 ^ k = 1) → β z = z → β = 1) ∧
    (∃ f ∈ centralizer (Λ : Set X₀), orderOf f = 3 ∧ f ∈ normalizer (V : Set X₀) ∧
      f ∉ centralizer (V : Set X₀))

private theorem map_centralizer_singleton {X₀ X₁ : Type*} [Group X₀] [Group X₁] (e : X₀ ≃* X₁)
    (x : X₀) :
    (centralizer ({x} : Set X₀)).map e.toMonoidHom = centralizer ({e x} : Set X₁) := by
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply e.injective
    rw [map_mul, map_mul, h]

theorem SimpleIn.of_equiv {X₀ X₁ : Type*} [Group X₀] [Group X₁] (e : X₀ ≃* X₁) {x : X₀}
    (h : SimpleIn (e x)) : SimpleIn x := by
  obtain ⟨H, hH, hcard, hsimp⟩ := h
  have hC := map_centralizer_singleton e x
  refine ⟨H.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := hH hy
    rw [← hC, ← map_commutator] at hy'
    obtain ⟨w, hw, rfl⟩ := hy'
    simpa using hw
  · rw [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard]
  · exact (H.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.isSimpleGroup

theorem A4cd.of_equiv {X₀ X₁ : Type*} [Group X₀] [Group X₁] (e : X₀ ≃* X₁)
    {V Λ : Subgroup X₀} (h : A4cd (V.map e.toMonoidHom) (Λ.map e.toMonoidHom)) : A4cd V Λ := by
  obtain ⟨hc, f, hfΛ, hf3, hfN, hfV⟩ := h
  refine ⟨fun z hz hz3 β hβ hβz => ?_, e.symm f, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hβ
    have h1 := hc (e z) ⟨z, hz, rfl⟩ (by rw [MulEquiv.orderOf_eq, hz3]) (MulAut.congr e β)
      ⟨k, by rw [← map_pow, hk, map_one]⟩ (by simp [MulAut.congr_apply, hβz])
    apply (MulAut.congr e).injective
    rw [h1, map_one]
  · rw [RankTwoClassical.centralizer_map_equiv e Λ] at hfΛ
    obtain ⟨f₀, hf₀, rfl⟩ := hfΛ
    simpa using hf₀
  · rw [MulEquiv.orderOf_eq]
    exact hf3
  · rw [← map_equiv_normalizer_eq V e] at hfN
    obtain ⟨f₀, hf₀, rfl⟩ := hfN
    simpa using hf₀
  · intro hmem
    apply hfV
    rw [RankTwoClassical.centralizer_map_equiv e V]
    exact ⟨e.symm f, hmem, by simp⟩

private theorem exists_mem_map_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K) (hA : IsPGroup p A) (hB : IsPGroup p B)
    (hcard : Nat.card A = Nat.card B) (hidx : ¬ p ∣ (B.subgroupOf K).index) :
    ∃ c ∈ K, A.map (MulAut.conj c).toMonoidHom = B := by
  have hA' : IsPGroup p (A.subgroupOf K) := hA.comap_of_injective _ K.subtype_injective
  have hB' : IsPGroup p (B.subgroupOf K) := hB.comap_of_injective _ K.subtype_injective
  have hcA : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  have hcB : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv
  have hidxA : ¬ p ∣ (A.subgroupOf K).index := by
    have h1 := (A.subgroupOf K).index_mul_card
    have h2 := (B.subgroupOf K).index_mul_card
    have hpos : 0 < Nat.card B := Nat.card_pos
    rw [hcA, hcard] at h1
    rw [hcB] at h2
    rwa [Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K (hA'.toSylow hidxA) (hB'.toSylow hidx)
  refine ⟨c, c.2, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  · intro b hb
    have hbS : (⟨b, hBK hb⟩ : K) ∈ ((c • hA'.toSylow hidxA : Sylow p K) : Set K) := by
      rw [hc]
      simpa [mem_subgroupOf] using hb
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hbS
    change c⁻¹ * ⟨b, hBK hb⟩ * c ∈ (hA'.toSylow hidxA : Subgroup K) at hbS
    rw [IsPGroup.toSylow_coe, mem_subgroupOf] at hbS
    refine ⟨_, hbS, ?_⟩
    simp [mul_assoc]
  · exact ((card_map_of_injective (f := (MulAut.conj (c : G)).toMonoidHom)
      (MulAut.conj (c : G)).injective).trans hcard).le

private theorem commutator_closure_le {G : Type*} [Group G] {S : Set G} {N : Subgroup G}
    (hN : closure S ≤ normalizer (N : Set G)) (hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N) :
    ⁅closure S, closure S⁆ ≤ N := by
  have hconj : ∀ g ∈ closure S, ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (mem_normalizer_iff.mp (hN hg) n).mp hn
  have h1 : ∀ s ∈ S, ∀ b ∈ closure S, ⁅s, b⁆ ∈ N := by
    intro s hs b hb
    induction hb using closure_induction with
    | mem t ht => exact hc s hs t ht
    | one => simp
    | mul b₁ b₂ hb₁ _ ih₁ ih₂ =>
      have e : ⁅s, b₁ * b₂⁆ = ⁅s, b₁⁆ * (b₁ * ⁅s, b₂⁆ * b₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ih₁ (hconj b₁ hb₁ _ ih₂)
    | inv b hb' ih =>
      have e : ⁅s, b⁻¹⁆ = b⁻¹ * ⁅s, b⁆⁻¹ * b⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj _ (inv_mem hb') _ (inv_mem ih)
  rw [commutator_le]
  intro a ha b hb
  induction ha using closure_induction with
  | mem s hs => exact h1 s hs b hb
  | one => simp
  | mul a₁ a₂ ha₁ _ ih₁ ih₂ =>
    have e : ⁅a₁ * a₂, b⁆ = a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₁, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hconj a₁ ha₁ _ ih₂) ih₁
  | inv a ha' ih =>
    have e : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj _ (inv_mem ha') _ (inv_mem ih)

private theorem mem_of_pow_eq_one_of_coprime {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {n : ℕ} (hn : Nat.Coprime n N.index) {g : G} (hg : g ^ n = 1) : g ∈ N := by
  have h1 : orderOf (g : G ⧸ N) ∣ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one])
  have h2 : orderOf (g : G ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have h3 := (Nat.Coprime.coprime_dvd_left h1 hn).eq_one_of_dvd h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

theorem j2A4Check_parts (hc : j2A4Check = true) : j2A4Elts = true ∧ j2A4Orb = true := by
  simpa only [j2A4Check, Bool.and_eq_true] using hc

theorem j2A4Elts_parts (h : j2A4Elts = true) :
    okA j2A4R1 = true ∧ okA j2A4R2 = true ∧ okA j2A4F = true ∧ okA j2A4Z3 = true ∧
    (∀ k < j2A4CR.size, okA j2A4CR[k]! = true) ∧
    (∀ k < j2A4L.size, okA j2A4L[k]! = true) ∧
    (∀ k < j2A4C3.size, okA j2A4C3[k]! = true) ∧
    enumOK 315 j2A4RGens keyPts cA4R = true ∧ cA4R.pts.size = 4 ∧
    enumOK 315 j2A4CR keyPts cA4CR = true ∧
    enumOK 315 j2A4L keyPts cA4L = true ∧ cA4L.pts.size = 60 ∧
    enumOK 315 j2A4C3 keyPts cA4C3 = true ∧ cA4C3.pts.size = 36 ∧
    inCert cStdH j2A4R1 = true ∧ inCert cStdH j2A4R2 = true ∧
    (∀ k < j2A4CR.size, ∀ l < j2A4L.size,
      inCert cA4L (conjA 315 j2A4CR[k]! j2A4L[l]!) = true) ∧
    (∀ k < j2A4CR.size, ∀ l < j2A4CR.size,
      inCert cA4L (commutatorA 315 j2A4CR[k]! j2A4CR[l]!) = true) ∧
    eqA 315 (powArr 315 j2A4F 3) (idA 315) = true ∧ eqA 315 j2A4F (idA 315) = false ∧
    (∀ k < j2A4L.size, commA j2A4F j2A4L[k]! = true) ∧
    inCert cA4R (conjA 315 j2A4F j2A4R1) = true ∧ inCert cA4R (conjA 315 j2A4F j2A4R2) = true ∧
    (commA j2A4F j2A4R1 && commA j2A4F j2A4R2) = false ∧
    eqA 315 (powArr 315 j2A4Z3 3) (idA 315) = true ∧ eqA 315 j2A4Z3 (idA 315) = false ∧
    inCert cA4L j2A4Z3 = true := by
  simp only [j2A4Elts, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    CFSG.Monster.B.Co2.allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    -⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩,
    h26⟩, h27⟩, h28⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, fun k hk => (h5 k hk).1.1, fun k hk => (h6 k hk).1,
    fun k hk => (h7 k hk).1, h8, h9, h10, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28⟩

theorem j2A4Orb_spec (hE : j2A4Elts = true) (h : j2A4Orb = true)
    (g : GJ) :
    ∃ t, Rep 315 t g.1 ∧
      (commA t j2A4R1 = true → commA t j2A4R2 = true → inCert cA4CR t = true) ∧
      (commA t j2A4Z3 = true → inCert cA4C3 t = true) := by
  simp only [j2A4Elts, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    CFSG.Monster.B.Co2.allLt_iff] at hE
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, -⟩, h7⟩, -⟩, -⟩, h10⟩,
    h11⟩, -⟩, -⟩, h14⟩, h15⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  simp only [j2A4Orb, Bool.and_eq_true] at h
  obtain ⟨oR, o3⟩ := h
  have eR : centralizer ({eltOf j2A4R1 h1, eltOf j2A4R2 h2} : Set GJ) = subOf j2A4CR :=
    cent_eq_subOf h10 (fun k hk => okA_spec (h5 k hk).1.1)
      (fun k hk => by
        rw [mem_centralizer_iff]
        rintro y (rfl | rfl)
        · exact (commute_of_commA (rep_gElt _ _ k hk) (rep_eltOf h1) (h5 k hk).1.2).eq.symm
        · exact (commute_of_commA (rep_gElt _ _ k hk) (rep_eltOf h2) (h5 k hk).2).eq.symm)
      (by simp [h11]) (card_cent_pair (rep_eltOf h1) (rep_eltOf h2) oR)
  have e3 : centralizer ({eltOf j2A4Z3 h4} : Set GJ) = subOf j2A4C3 :=
    cent_eq_subOf h14 (fun k hk => okA_spec (h7 k hk).1)
      (fun k hk => by
        rw [mem_centralizer_singleton_iff]
        exact (commute_of_commA (rep_gElt _ _ k hk) (rep_eltOf h4) (h7 k hk).2).eq)
      (by simp [h15]) (card_cent_single (rep_eltOf h4) o3)
  obtain ⟨a, ha, b, hb, c, hc, hg⟩ := exists_cperm g
  have ht : Rep 315 (prod3 315 autLevels a b c) g.1 := hg ▸ rep_prod3 ha hb hc
  refine ⟨_, ht, fun c1 c2 => ?_, fun c3 => ?_⟩
  · refine inCert_of_mem h10 ht ?_
    rw [← eR, mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (commute_of_commA ht (rep_eltOf h1) c1).eq.symm
    · exact (commute_of_commA ht (rep_eltOf h2) c2).eq.symm
  · refine inCert_of_mem h14 ht ?_
    rw [← e3, mem_centralizer_singleton_iff]
    exact (commute_of_commA ht (rep_eltOf h4) c3).eq

theorem stdH_facts (hc : j2StdCheck = true) {z : GJ}
    (hz : Rep 315 j2StdZ1 z.1) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    centralizer ({z ^ k} : Set GJ) = subOf j2StdC1 ∧
    subOf j2StdH ≤ ⁅centralizer ({z ^ k} : Set GJ), centralizer ({z ^ k} : Set GJ)⁆ ∧
    Nat.card (subOf j2StdH) = 60 ∧ IsSimpleGroup ↥(subOf j2StdH) ∧
    ∀ x ∈ centralizer ({z ^ k} : Set GJ), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ subOf j2StdH := by
  obtain ⟨hE, hHC, -, hS⟩ := j2StdCheck_parts hc
  obtain ⟨-, -, h5, -, -, -, hC1, -, hA1, hB1, hA2, hB2, hcA1, hcB1, hcA2, hcB2, -, hHok, hen1,
    -, -, -, henH, hszH, -, -⟩ := j2StdElts_parts hE
  obtain ⟨htwo, hsimp⟩ := j2StdHChk_parts hHC
  have hz5 : z ^ 5 = 1 := eq_of_rep (rep_pow hz 5) rep_one h5
  have hspecH : ∀ k < j2StdH.size, validA 315 j2StdH[k]! = true ∧ inP j2StdH[k]! = true :=
    fun k hk => okA_spec (hHok k hk)
  have hC : centralizer ({z ^ k} : Set GJ) = subOf j2StdC1 := by
    rw [centralizer_pow_eq hz5 hk]
    refine centralizer_eq_subOf hz hen1 (fun k hk => (hC1 k hk).1) (fun k hk => (hC1 k hk).2)
      fun g => ?_
    obtain ⟨t, ht, h1, -, -⟩ := j2StdOrb_spec hE hS g
    exact ⟨t, ht, h1⟩
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
  have hmem : ∀ {t : Array ℕ} (ht : okA t = true), commA t j2StdZ1 = true →
      eltOf t ht ∈ centralizer ({z ^ k} : Set GJ) := fun ht htc => by
    rw [centralizer_pow_eq hz5 hk, mem_centralizer_singleton_iff]
    exact (commute_of_commA (rep_eltOf ht) hz htc).eq
  have hg0 : gElt j2StdH hspecH 0 h0 = ⁅eltOf j2StdA1 hA1, eltOf j2StdB1 hB1⁆ := by
    have r0 := rep_gElt _ hspecH 0 h0
    rw [show j2StdH[0]! = j2StdH0 by simp [j2StdH]] at r0
    exact Subtype.ext (r0.unique (hrepC hA1 hB1))
  have hg1 : gElt j2StdH hspecH 1 h1 = ⁅eltOf j2StdA2 hA2, eltOf j2StdB2 hB2⁆ := by
    have r1 := rep_gElt _ hspecH 1 h1
    rw [show j2StdH[1]! = j2StdH1 by simp [j2StdH]] at r1
    exact Subtype.ext (r1.unique (hrepC hA2 hB2))
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · refine subOf_le_of j2StdH hspecH fun i hi => ?_
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · rw [hg0]
      exact commutator_mem_commutator (hmem hA1 hcA1) (hmem hB1 hcB1)
    · rw [hg1]
      exact commutator_mem_commutator (hmem hA2 hcA2) (hmem hB2 hcB2)
  · rw [card_subOf keyPts_lt henH hspecH, hszH]
  · have hcl := isSimpleGroup_of_conjGenOK keyPts_lt henH (by rw [hszH]; norm_num) hsimp
    exact (Subgroup.subgroupOfEquivOfLe (closure_le_P hspecH)).isSimpleGroup
  · intro x hx h2
    rw [hC] at hx
    obtain ⟨i, hi, hr⟩ := exists_rep_subOf keyPts_lt hen1 hx
    have hiTwo : isTwoA cStdC1.pts[i]! = true := (isTwoA_iff hr).2 (pow128 h2)
    exact mem_of_inCert henH hr (htwo i hi hiTwo)

theorem simpleIn_z1 (hc : j2StdCheck = true) {z : GJ}
    (hz : Rep 315 j2StdZ1 z.1) {k : ℕ} (hk : k = 1 ∨ k = 2) : SimpleIn (z ^ k) := by
  obtain ⟨-, hHC', hcard, hsimp, -⟩ := stdH_facts hc hz hk
  exact ⟨_, hHC', hcard, hsimp⟩

theorem card_lt_of_le_z2 (hc : j2StdCheck = true) {z : GJ}
    (hz : Rep 315 j2StdZ2 z.1) {k : ℕ} (hk : k = 1 ∨ k = 2) {V : Subgroup GJ}
    (hV2 : IsPGroup 2 V) (hVz : V ≤ centralizer ({z ^ k} : Set GJ)) : Nat.card V < 4 := by
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
  rw [hC] at hVz
  have hdvd := card_dvd_of_le hVz
  rw [hcard] at hdvd
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  rw [hn] at hdvd ⊢
  by_contra h4
  push Not at h4
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at h4
  have h4' : 2 ^ 2 ∣ 50 := (Nat.pow_dvd_pow 2 hn2).trans hdvd
  norm_num at h4'

theorem exists_conj_z
    (hc : j2StdCheck = true) {y : GJ} (hy : orderOf y = 5) :
    ∃ (u z : GJ) (k : ℕ), (k = 1 ∨ k = 2) ∧ (Rep 315 j2StdZ1 z.1 ∨ Rep 315 j2StdZ2 z.1) ∧
      u * y * u⁻¹ = z ^ k := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
    exact ⟨c * g⁻¹, eltOf j2StdZ1 hz1, j2StdK[j]!, hkj, Or.inl (rep_eltOf hz1), hu _ hz⟩
  · have hz : Rep 315 (j2StdZ j2StdJ[j]!) (eltOf j2StdZ2 hz2).1 := by
      simp only [j2StdZ, hJ, ↓reduceIte]
      exact rep_eltOf hz2
    exact ⟨c * g⁻¹, eltOf j2StdZ2 hz2, j2StdK[j]!, hkj, Or.inr (rep_eltOf hz2), hu _ hz⟩

theorem simpleIn_of_le
    (hc : j2StdCheck = true) {x : GJ} (hx : orderOf x = 5) {V : Subgroup GJ}
    (hV2 : IsPGroup 2 V) (hV4 : 4 ≤ Nat.card V) (hVx : V ≤ centralizer ({x} : Set GJ)) :
    SimpleIn x := by
  obtain ⟨u, z, k, hk, hz, hu⟩ := exists_conj_z hc hx
  rcases hz with hz | hz
  · refine SimpleIn.of_equiv (MulAut.conj u) ?_
    show SimpleIn (u * x * u⁻¹)
    rw [hu]
    exact simpleIn_z1 hc hz hk
  · exfalso
    have hV' : V.map (MulAut.conj u).toMonoidHom ≤ centralizer ({z ^ k} : Set GJ) := by
      rw [← hu, ← map_conj_centralizer_singleton]
      exact map_mono hVx
    have h := card_lt_of_le_z2 hc hz hk (hV2.map _) hV'
    rw [card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective] at h
    omega

theorem exists_conj_std
    (hs : j2StdCheck = true) (hc : j2A4Check = true) {V Λ : Subgroup GJ} (hV2 : IsPGroup 2 V)
    (hV4 : 4 ≤ Nat.card V) (hΛ : Nat.card Λ = 60) (hper : ⁅Λ, Λ⁆ = Λ)
    (hVΛ : V ≤ centralizer (Λ : Set GJ)) :
    ∃ g : GJ, V.map (MulAut.conj g).toMonoidHom = subOf j2A4RGens ∧
      Λ.map (MulAut.conj g).toMonoidHom = subOf j2A4L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hE, hS⟩ := j2A4Check_parts hc
  obtain ⟨hR1, hR2, -, -, hCR, hL, -, henR, hszR, henCR, henL, hszL, -, -, hR1H, hR2H, hnorm,
    hcomm, -⟩ := j2A4Elts_parts hE
  obtain ⟨hEs, -, -, -⟩ := j2StdCheck_parts hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, henH, -⟩ :=
    j2StdElts_parts hEs
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Λ) 5 (by rw [hΛ]; norm_num)
  have hx5 : orderOf (x : GJ) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hVx : V ≤ centralizer ({(x : GJ)} : Set GJ) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hVΛ hv) x x.2).symm
  obtain ⟨u, z, k, hk, hz, hu⟩ := exists_conj_z hs hx5
  have hV' : V.map (MulAut.conj u).toMonoidHom ≤ centralizer ({z ^ k} : Set GJ) := by
    rw [← hu, ← map_conj_centralizer_singleton]
    exact map_mono hVx
  have hcV : Nat.card (V.map (MulAut.conj u).toMonoidHom) = Nat.card V :=
    card_map_of_injective (MulAut.conj u).injective
  rcases hz with hz | hz
  swap
  · exfalso
    have := card_lt_of_le_z2 hs hz hk (hV2.map _) hV'
    omega
  obtain ⟨-, -, hHcard, -, h2H⟩ := stdH_facts hs hz hk
  have hV₁H : V.map (MulAut.conj u).toMonoidHom ≤ subOf j2StdH := fun v hv =>
    h2H v (hV' hv) (two_of_mem (hV2.map _) hv)
  have hV₁4 : Nat.card (V.map (MulAut.conj u).toMonoidHom) = 4 := by
    obtain ⟨n, hn⟩ := (hV2.map (MulAut.conj u).toMonoidHom).exists_card_eq
    have hdvd := card_dvd_of_le hV₁H
    rw [hHcard, hn] at hdvd
    rw [← hcV, hn] at hV4
    rw [hn]
    have hn2 : 2 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> norm_num at hV4
    have hn3 : n ≤ 2 := by
      by_contra h
      push Not at h
      have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 h).trans hdvd
      norm_num at h8
    rw [show n = 2 by omega]
    norm_num
  have hRsz : j2A4RGens.size = 2 := by simp [j2A4RGens]
  have hR0 : j2A4RGens[0]! = j2A4R1 := by simp [j2A4RGens]
  have hR1' : j2A4RGens[1]! = j2A4R2 := by simp [j2A4RGens]
  have hspecR : ∀ k < j2A4RGens.size,
      validA 315 j2A4RGens[k]! = true ∧ inP j2A4RGens[k]! = true := by
    intro k hk
    rw [hRsz] at hk
    interval_cases k
    · rw [hR0]
      exact okA_spec hR1
    · rw [hR1']
      exact okA_spec hR2
  have hRcard : Nat.card (subOf j2A4RGens) = 4 := by
    rw [card_subOf keyPts_lt henR hspecR, hszR]
  have hR2p : IsPGroup 2 (subOf j2A4RGens) := IsPGroup.of_card (n := 2) (by rw [hRcard]; norm_num)
  have hRH : subOf j2A4RGens ≤ subOf j2StdH := by
    refine subOf_le_of j2A4RGens hspecR fun i hi => ?_
    have r := rep_gElt _ hspecR i hi
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · rw [hR0] at r
      exact mem_of_inCert henH r hR1H
    · rw [hR1'] at r
      exact mem_of_inCert henH r hR2H
  have hidx : ¬ 2 ∣ ((subOf j2A4RGens).subgroupOf (subOf j2StdH)).index := by
    have h1 := ((subOf j2A4RGens).subgroupOf (subOf j2StdH)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv, hRcard, hHcard] at h1
    have h15 : ((subOf j2A4RGens).subgroupOf (subOf j2StdH)).index = 15 := by omega
    rw [h15]
    norm_num
  obtain ⟨h, -, hh⟩ := exists_mem_map_conj_eq hV₁H hRH (hV2.map _) hR2p (by rw [hV₁4, hRcard])
    hidx
  have hmap : ∀ S : Subgroup GJ, (S.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj h).toMonoidHom = S.map (MulAut.conj (h * u)).toMonoidHom := by
    intro S
    rw [map_map]
    congr 1
  have hV₂ : V.map (MulAut.conj (h * u)).toMonoidHom = subOf j2A4RGens := by rw [← hmap, hh]
  refine ⟨h * u, hV₂, ?_⟩
  set Λ₂ := Λ.map (MulAut.conj (h * u)).toMonoidHom with hΛ₂
  have hΛ₂C : Λ₂ ≤ centralizer ((subOf j2A4RGens : Subgroup GJ) : Set GJ) := by
    rw [← le_centralizer_iff, ← hV₂, hΛ₂, centralizer_map_conj]
    exact map_mono hVΛ
  have h0 : 0 < j2A4RGens.size := by rw [hRsz]; norm_num
  have h1 : 1 < j2A4RGens.size := by rw [hRsz]; norm_num
  have hspecCR : ∀ k < j2A4CR.size,
      validA 315 j2A4CR[k]! = true ∧ inP j2A4CR[k]! = true := fun k hk => okA_spec (hCR k hk)
  have hspecL : ∀ k < j2A4L.size,
      validA 315 j2A4L[k]! = true ∧ inP j2A4L[k]! = true := fun k hk => okA_spec (hL k hk)
  have hΛ₂CR : Λ₂ ≤ subOf j2A4CR := by
    intro l hl
    obtain ⟨t, ht, h3, -⟩ := j2A4Orb_spec hE hS l
    have r0 := rep_gElt _ hspecR 0 h0
    have r1 := rep_gElt _ hspecR 1 h1
    rw [hR0] at r0
    rw [hR1'] at r1
    have hc0 := mem_centralizer_iff.mp (hΛ₂C hl) _ (gElt_mem j2A4RGens hspecR 0 h0)
    have hc1 := mem_centralizer_iff.mp (hΛ₂C hl) _ (gElt_mem j2A4RGens hspecR 1 h1)
    exact mem_of_inCert henCR ht (h3 (commA_of_commute ht r0 hc0.symm)
      (commA_of_commute ht r1 hc1.symm))
  have hCRcomm : ⁅subOf j2A4CR, subOf j2A4CR⁆ ≤ subOf j2A4L := by
    rw [subOf_eq_closure_gElt j2A4CR hspecCR]
    refine commutator_closure_le ?_ ?_
    · rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      have hle : subOf j2A4L ≤ (subOf j2A4L).comap
          (MulAut.conj (gElt j2A4CR hspecCR k hk)).toMonoidHom := by
        refine subOf_le_of j2A4L hspecL fun l hl => ?_
        rw [mem_comap]
        have r := rep_conj (rep_gElt _ hspecCR k hk) (hspecCR k hk).1 (rep_gElt _ hspecL l hl)
        simpa using mem_of_inCert henL r (hnorm k hk l hl)
      simpa using hle hv
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      have hr := rep_commutatorA (hspecCR k hk).1 (hspecCR l hl).1
      rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_gElt _ hspecCR k hk),
        CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_gElt _ hspecCR l hl)] at hr
      have hr' : Rep 315 (commutatorA 315 j2A4CR[k]! j2A4CR[l]!)
          (⁅gElt j2A4CR hspecCR k hk, gElt j2A4CR hspecCR l hl⁆ : GJ).1 := by
        simpa [commutatorElement_def] using hr
      exact mem_of_inCert henL hr' (hcomm k hk l hl)
  have hper₂ : ⁅Λ₂, Λ₂⁆ = Λ₂ := by rw [hΛ₂, ← map_commutator, hper]
  have hle : Λ₂ ≤ subOf j2A4L := by
    rw [← hper₂]
    exact (commutator_mono hΛ₂CR hΛ₂CR).trans hCRcomm
  have hcardL : Nat.card (subOf j2A4L) = 60 := by
    rw [card_subOf keyPts_lt henL hspecL, hszL]
  refine eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hcardL, hΛ₂, card_map_of_injective (f := (MulAut.conj (h * u)).toMonoidHom)
    (MulAut.conj (h * u)).injective, hΛ]

theorem a4cd_std
    (hc : j2A4Check = true) : A4cd (subOf j2A4RGens) (subOf j2A4L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE, hS⟩ := j2A4Check_parts hc
  obtain ⟨hR1, hR2, hF, hZ3, -, hL, hC3, henR, -, -, henL, hszL, henC3, hszC3, -, -, -, -,
    hF3, hF1, hFL, hFR1, hFR2, hFR, hZ33, hZ31, hZ3L⟩ := j2A4Elts_parts hE
  have hRsz : j2A4RGens.size = 2 := by simp [j2A4RGens]
  have hR0 : j2A4RGens[0]! = j2A4R1 := by simp [j2A4RGens]
  have hR1' : j2A4RGens[1]! = j2A4R2 := by simp [j2A4RGens]
  have hspecR : ∀ k < j2A4RGens.size,
      validA 315 j2A4RGens[k]! = true ∧ inP j2A4RGens[k]! = true := by
    intro k hk
    rw [hRsz] at hk
    interval_cases k
    · rw [hR0]
      exact okA_spec hR1
    · rw [hR1']
      exact okA_spec hR2
  have hspecL : ∀ k < j2A4L.size,
      validA 315 j2A4L[k]! = true ∧ inP j2A4L[k]! = true := fun k hk => okA_spec (hL k hk)
  have hspecC3 : ∀ k < j2A4C3.size,
      validA 315 j2A4C3[k]! = true ∧ inP j2A4C3[k]! = true := fun k hk => okA_spec (hC3 k hk)
  set f₀ := eltOf j2A4F hF with hf₀
  set l₃ := eltOf j2A4Z3 hZ3 with hl₃
  refine ⟨fun z hz hz3 β hβ hβz => ?_, f₀, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨k, hk⟩ := hβ
    have hin : β ∈ inner GJ := by
      refine mem_of_pow_eq_one_of_coprime ?_ hk
      have hle : (inner GJ).index ≤ 2 := outer_P.1
      have hpos : 0 < (inner GJ).index := by
        have := finite_outer_P
        exact Nat.card_pos
      refine Nat.Coprime.pow_left k ?_
      rcases (by omega : (inner GJ).index = 1 ∨ (inner GJ).index = 2) with h | h <;> rw [h] <;>
        norm_num
    obtain ⟨e, he⟩ := hin
    change MulAut.conj e = β at he
    have he5 : e ^ 5 ^ k = 1 := by
      have h1 : MulAut.conj (e ^ 5 ^ k) = 1 := by rw [map_pow, he, hk]
      have h2 : e ^ 5 ^ k ∈ center GJ := by
        rw [mem_center_iff]
        intro y
        have h3 := congrArg (fun σ : MulAut GJ => σ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc y * e ^ 5 ^ k = e ^ 5 ^ k * y * (e ^ 5 ^ k)⁻¹ * e ^ 5 ^ k := by rw [h3]
          _ = e ^ 5 ^ k * y := by group
      rw [center_P, mem_bot] at h2
      exact h2
    have hez : Commute e z := by
      have h1 : β z = z := hβz
      rw [← he, MulAut.conj_apply] at h1
      show e * z = z * e
      calc e * z = e * z * e⁻¹ * e := by group
        _ = z * e := by rw [h1]
    have hl3L : l₃ ∈ subOf j2A4L := mem_of_inCert henL (rep_eltOf hZ3) hZ3L
    have hl3 : orderOf l₃ = 3 := by
      refine orderOf_eq_prime (eq_of_rep (rep_pow (rep_eltOf hZ3) 3) rep_one hZ33) fun h1 => ?_
      have h2 := (eqA_iff (rep_eltOf hZ3) rep_one).2 (congrArg Subtype.val h1)
      rw [hZ31] at h2
      exact absurd h2 (by decide)
    have hcardL : Nat.card (subOf j2A4L) = 60 := by
      rw [card_subOf keyPts_lt henL hspecL, hszL]
    have hidx : ¬ 3 ∣ ((zpowers l₃).subgroupOf (subOf j2A4L)).index := by
      have h1 := ((zpowers l₃).subgroupOf (subOf j2A4L)).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hl3L)).toEquiv, Nat.card_zpowers,
        hl3, hcardL] at h1
      have h20 : ((zpowers l₃).subgroupOf (subOf j2A4L)).index = 20 := by omega
      rw [h20]
      norm_num
    obtain ⟨c, -, hcz⟩ := exists_mem_map_conj_eq (zpowers_le.mpr hz) (zpowers_le.mpr hl3L)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz3, pow_one]))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hl3, pow_one]))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hl3]) hidx
    have hl3mem : l₃ ∈ (zpowers z).map (MulAut.conj c).toMonoidHom := by
      rw [hcz]
      exact mem_zpowers l₃
    obtain ⟨w, hw, hwl⟩ := hl3mem
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
    have hcomm : Commute (c * e * c⁻¹) l₃ := by
      rw [← hwl]
      simpa using (hez.zpow_right m).map (MulAut.conj c).toMonoidHom
    obtain ⟨t, ht, -, h3⟩ := j2A4Orb_spec hE hS (c * e * c⁻¹)
    have hmemC3 : c * e * c⁻¹ ∈ subOf j2A4C3 :=
      mem_of_inCert henC3 ht (h3 (commA_of_commute ht (rep_eltOf hZ3) hcomm))
    have hcardC3 : Nat.card (subOf j2A4C3) = 36 := by
      rw [card_subOf keyPts_lt henC3 hspecC3, hszC3]
    have hpow : (c * e * c⁻¹) ^ 5 ^ k = 1 := by rw [conj_pow, he5, mul_one, mul_inv_cancel]
    have hord : orderOf (c * e * c⁻¹) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hpow
      have h2 := (subOf j2A4C3).orderOf_dvd_natCard hmemC3
      rw [hcardC3] at h2
      exact (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by norm_num))).eq_one_of_dvd
        h2
    have he1 : e = 1 := by
      have h1 := orderOf_eq_one_iff.mp hord
      calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    rw [← he, he1, map_one]
  ·
    rw [mem_centralizer_iff]
    intro l hl
    have hle : subOf j2A4L ≤ centralizer ({f₀} : Set GJ) := by
      refine subOf_le_of j2A4L hspecL fun k hk => ?_
      rw [mem_centralizer_singleton_iff]
      exact (commute_of_commA (rep_eltOf hF) (rep_gElt _ hspecL k hk) (hFL k hk)).symm.eq
    exact mem_centralizer_singleton_iff.mp (hle hl)
  ·
    refine orderOf_eq_prime (eq_of_rep (rep_pow (rep_eltOf hF) 3) rep_one hF3) fun h1 => ?_
    have h2 := (eqA_iff (rep_eltOf hF) rep_one).2 (congrArg Subtype.val h1)
    rw [hF1] at h2
    exact absurd h2 (by decide)
  ·
    refine mem_normalizer_of_conj_mem fun v hv => ?_
    have hle : subOf j2A4RGens ≤ (subOf j2A4RGens).comap (MulAut.conj f₀).toMonoidHom := by
      refine subOf_le_of j2A4RGens hspecR fun i hi => ?_
      rw [mem_comap]
      have r := rep_gElt _ hspecR i hi
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · rw [hR0] at r
        simpa using mem_of_inCert henR (rep_conj (rep_eltOf hF) (okA_spec hF).1 r) hFR1
      · rw [hR1'] at r
        simpa using mem_of_inCert henR (rep_conj (rep_eltOf hF) (okA_spec hF).1 r) hFR2
    simpa using hle hv
  ·
    intro hmem
    have h0 : 0 < j2A4RGens.size := by rw [hRsz]; norm_num
    have h1 : 1 < j2A4RGens.size := by rw [hRsz]; norm_num
    have r0 := rep_gElt _ hspecR 0 h0
    have r1 := rep_gElt _ hspecR 1 h1
    rw [hR0] at r0
    rw [hR1'] at r1
    have hc0 := mem_centralizer_iff.mp hmem _ (gElt_mem j2A4RGens hspecR 0 h0)
    have hc1 := mem_centralizer_iff.mp hmem _ (gElt_mem j2A4RGens hspecR 1 h1)
    rw [commA_of_commute (rep_eltOf hF) r0 hc0.symm,
      commA_of_commute (rep_eltOf hF) r1 hc1.symm] at hFR
    exact absurd hFR (by decide)

theorem a4_gJ
    (hs : j2StdCheck = true) (hc : j2A4Check = true)
    {V Λ : Subgroup GJ} (hV2 : IsPGroup 2 V) (hV4 : 4 ≤ Nat.card V) (hΛ : Nat.card Λ = 60)
    (hper : ⁅Λ, Λ⁆ = Λ) (hVΛ : V ≤ centralizer (Λ : Set GJ)) :
    (∀ x ∈ Λ, orderOf x = 5 → SimpleIn x) ∧ A4cd V Λ := by
  refine ⟨fun x hx hx5 => simpleIn_of_le hs hx5 hV2 hV4 fun v hv => ?_, ?_⟩
  · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hVΛ hv) x hx).symm
  obtain ⟨g, hgV, hgΛ⟩ := exists_conj_std hs hc hV2 hV4 hΛ hper hVΛ
  refine A4cd.of_equiv (MulAut.conj g) ?_
  rw [hgV, hgΛ]
  exact a4cd_std hc

theorem j2A4Facts_of_check
    (hs : j2StdCheck = true) (hc : j2A4Check = true) :
    J2A4Facts := by
  intro X _ hX V Λ hV2 hV4 hΛ hper hVΛ
  obtain ⟨φ⟩ := hX
  let e : X ≃* GJ := φ.trans nativeEquivP
  obtain ⟨ha, hcd⟩ := a4_gJ hs hc (V := V.map e.toMonoidHom) (Λ := Λ.map e.toMonoidHom)
    (hV2.map _) (by rw [card_map_of_injective (f := e.toMonoidHom) e.injective]; exact hV4)
    (by rw [card_map_of_injective (f := e.toMonoidHom) e.injective]; exact hΛ)
    (by rw [← map_commutator, hper])
    (by rw [RankTwoClassical.centralizer_map_equiv e Λ]; exact map_mono hVΛ)
  obtain ⟨hc', hd'⟩ := A4cd.of_equiv e hcd
  exact ⟨fun x hx hx5 => SimpleIn.of_equiv e (ha (e x) ⟨x, hx, rfl⟩
    (by rw [MulEquiv.orderOf_eq, hx5])), hc', hd'⟩

end CFSG.ComponentClassification.RankTwoClassical.J2Std
