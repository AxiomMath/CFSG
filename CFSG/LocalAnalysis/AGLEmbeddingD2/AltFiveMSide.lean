module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveHSide
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDichotomy
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairTools
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem exists_isPGroup_not_mem_of_pow_mem {Y : Type} [Group Y] [Finite Y] {q : ℕ}
    [hq : Fact q.Prime] {C : Subgroup Y} {ℓ : Y} (hℓC : ℓ ∉ C) {k : ℕ} (hk : ℓ ^ q ^ k ∈ C) :
    ∃ y ∈ Subgroup.zpowers ℓ, IsPGroup q (Subgroup.zpowers y) ∧ y ∉ C := by
  have hq1 : q ≠ 1 := hq.out.one_lt.ne'
  obtain ⟨a, b, hb, hnab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ℓ).ne' q hq1
  have hcop : Nat.Coprime b (q ^ a) :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hb)).symm
  obtain ⟨x, z, hxz⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hn : ℓ ^ ((q ^ a * b : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hnab, pow_orderOf_eq_one]
  set y : Y := ℓ ^ (x * (b : ℤ)) with hy
  set u : Y := ℓ ^ (z * ((q ^ a : ℕ) : ℤ)) with hu
  have hℓ : ℓ = y * u := by rw [hy, hu, ← zpow_add, hxz, zpow_one]
  have hyq : y ^ q ^ a = 1 := by
    rw [hy, ← zpow_natCast, ← zpow_mul,
      show x * (b : ℤ) * ((q ^ a : ℕ) : ℤ) = ((q ^ a * b : ℕ) : ℤ) * x by push_cast; ring,
      zpow_mul, hn, one_zpow]
  have hub : u ^ b = 1 := by
    rw [hu, ← zpow_natCast, ← zpow_mul,
      show z * ((q ^ a : ℕ) : ℤ) * (b : ℤ) = ((q ^ a * b : ℕ) : ℤ) * z by push_cast; ring,
      zpow_mul, hn, one_zpow]
  have huk : u ^ q ^ k ∈ C := by
    rw [hu, ← zpow_natCast, ← zpow_mul,
      show z * ((q ^ a : ℕ) : ℤ) * ((q ^ k : ℕ) : ℤ) = ((q ^ k : ℕ) : ℤ) * (z * ((q ^ a : ℕ) : ℤ))
        by ring, zpow_mul, zpow_natCast]
    exact C.zpow_mem hk _
  have hcop' : Nat.Coprime (q ^ k) b :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hb)
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop'
  have key : ∀ v : Y, v ^ b = 1 → v = (v ^ q ^ k) ^ s := by
    intro v hv
    calc v = v ^ (s * ((q ^ k : ℕ) : ℤ) + t * (b : ℤ)) := by rw [hst, zpow_one]
      _ = (v ^ q ^ k) ^ s * (v ^ b) ^ t := by
          rw [zpow_add, mul_comm s, mul_comm t, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (v ^ q ^ k) ^ s := by rw [hv, one_zpow, mul_one]
  have huC : u ∈ C := by
    rw [key u hub]
    exact C.zpow_mem huk s
  refine ⟨y, Subgroup.zpow_mem_zpowers ℓ _, isPGroup_zpowers_of_pow_eq_one hyq, fun hyC => ?_⟩
  exact hℓC (hℓ ▸ C.mul_mem hyC huC)

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem exists_threeElement_of_not_mem_centralizerBar (h : AGLPair p M H R) (hD1 : D1For G)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {W : Subgroup G} (hWK : W ≤ H ⊓ M) (hW : ⁅W, W⁆ = W) (hWM : W ≤ M)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) {w : W} {k : ℕ}
    (hw3 : w ^ 3 ^ k = 1) (hwC : w ∉ centralizerBar M hWM Lb) :
    ∃ y ∈ Lb, IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ Lb, y * l ≠ l * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hx : barElt M hWM w ∈ Lb ⊔ C :=
    h.le_sup_centralizer_component hD1 hα hSch hB3 hWK hW hLb (barElt_mem_barM hWM w)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hx
  obtain ⟨ℓ, hℓ, c, hc, hℓc⟩ := hx
  dsimp only at hℓc
  have hcomm : ℓ * c = c * ℓ := Subgroup.mem_centralizer_iff.mp hc ℓ hℓ
  have hℓC : ℓ ∉ C := by
    intro hℓC'
    apply hwC
    rw [mem_centralizerBar_iff, ← hℓc]
    exact C.mul_mem hℓC' hc
  have hpow : ℓ ^ 3 ^ k ∈ C := by
    have h1 : (ℓ * c) ^ 3 ^ k = 1 := by
      rw [hℓc, ← map_pow, hw3, map_one]
    rw [(show Commute ℓ c from hcomm).mul_pow] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact C.inv_mem (C.pow_mem hc _)
  obtain ⟨y, hyℓ, hy3, hyC⟩ := exists_isPGroup_not_mem_of_pow_mem hℓC hpow
  have hyL : y ∈ Lb := (Subgroup.zpowers_le.mpr hℓ) hyℓ
  refine ⟨y, hyL, hy3, ?_⟩
  by_contra hall
  push Not at hall
  exact hyC (Subgroup.mem_centralizer_iff.mpr fun l hl => (hall l hl).symm)

theorem three_le_pRank_of_two_components (h : AGLPair p M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L₀ L₁ L₂ : Subgroup G} (hL₀ : IsTwoPrimeComponent M L₀) (hL₁ : IsTwoPrimeComponent M L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hK₀ : L₀ ≤ H ⊓ M) (hK₁ : L₁ ≤ H ⊓ M)
    (hne : barM M L₀ ≠ barM M L₁)
    (hy₀ : ∃ y ∈ barM M L₀, IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ barM M L₀, y * l ≠ l * y)
    (hy₁ : ∃ y ∈ barM M L₁, IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ barM M L₁, y * l ≠ l * y) :
    3 ≤ Open.pRank 3 (H ⊓ M) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  obtain ⟨y₂, ⟨hy₂S, hy₂L⟩, hy₂3, l₂, hl₂, hl₂Q⟩ := hB3 L₂ hL₂
  have hy₂M : y₂ ∈ M := hL₂.le hy₂L
  set yb₂ : ↥M ⧸ CFSG.pCore 2 ↥M := mk ⟨y₂, hy₂M⟩
  have hyb₂K : yb₂ ∈ barM M (H ⊓ M) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hKeq ▸ ⟨hy₂M, hy₂S⟩))
  have hyb₂L : yb₂ ∈ barM M L₂ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy₂L)
  have hyb₂3 : IsPGroup 3 (Subgroup.zpowers yb₂) := by
    obtain ⟨k, hk⟩ := hy₂3 ⟨y₂, Subgroup.mem_zpowers _⟩
    have hk' : y₂ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
    have : (⟨y₂, hy₂M⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
    simp only [yb₂, ← map_pow, this, map_one]
  have hyb₂Z : ∃ l ∈ barM M L₂, yb₂ * l ≠ l * yb₂ := by
    have hlM : l₂ ∈ M := hL₂.le hl₂
    refine ⟨mk ⟨l₂, hlM⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl₂),
      fun he => ?_⟩
    apply hl₂Q
    have h1 : mk (⟨y₂, hy₂M⟩ * ⟨l₂, hlM⟩ * (⟨y₂, hy₂M⟩)⁻¹ * (⟨l₂, hlM⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change yb₂ * mk ⟨l₂, hlM⟩ * yb₂⁻¹ * (mk ⟨l₂, hlM⟩)⁻¹ = 1
      rw [he]
      group
    simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  have hne₂ : ∀ {L : Subgroup G}, IsTwoPrimeComponent M L → L ≤ H ⊓ M → barM M L₂ ≠ barM M L :=
    fun hL hLK he => hL₂.not_le_normalizer
      ((hL₂.toIsTwoPrimeComponent.eq_of_barM_eq hL he) ▸ (hKeq ▸ hLK).trans inf_le_right)
  obtain ⟨y₀, hy₀L, hy₀3, hy₀Z⟩ := hy₀
  obtain ⟨y₁, hy₁L, hy₁3, hy₁Z⟩ := hy₁
  let Lb : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := ![barM M L₀, barM M L₁, barM M L₂]
  let yb : Fin 3 → ↥M ⧸ CFSG.pCore 2 ↥M := ![y₀, y₁, yb₂]
  have hcomp : ∀ i, IsComponentOf (Lb i) ⊤ := by
    intro i
    fin_cases i
    exacts [hL₀.component, hL₁.component, hL₂.component]
  have hinj : Function.Injective Lb := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij hne | exact absurd hij.symm hne
      | exact absurd hij (hne₂ hL₀ hK₀).symm | exact absurd hij.symm (hne₂ hL₀ hK₀).symm
      | exact absurd hij (hne₂ hL₁ hK₁).symm | exact absurd hij.symm (hne₂ hL₁ hK₁).symm
  have hyA : ∀ i, yb i ∈ barM M (H ⊓ M) := by
    intro i
    fin_cases i
    exacts [barM_mono hK₀ hy₀L, barM_mono hK₁ hy₁L, hyb₂K]
  have hyL : ∀ i, yb i ∈ Lb i := by
    intro i
    fin_cases i
    exacts [hy₀L, hy₁L, hyb₂L]
  have hyq : ∀ i, IsPGroup 3 (Subgroup.zpowers (yb i)) := by
    intro i
    fin_cases i
    exacts [hy₀3, hy₁3, hyb₂3]
  have hyZ : ∀ i, ∃ l ∈ Lb i, yb i * l ≠ l * yb i := by
    intro i
    fin_cases i
    exacts [hy₀Z, hy₁Z, hyb₂Z]
  have h3 := le_pRank_of_components Nat.prime_three Lb hcomp hinj (barM M (H ⊓ M)) yb hyA hyL
    hyq hyZ
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  exact h3.trans (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)

end AGLPair

@[expose] def D2AltFiveResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) →
      ((∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
          ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
        ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
          barM M A ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) → False

theorem exists_orderOf_eq_three_alt {p : ℕ} (hp5 : 5 ≤ p) :
    ∃ a : alternatingGroup (Fin p), orderOf a = 3 := by
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin p)) := by
    have hcard := two_mul_nat_card_alternatingGroup (α := Fin p)
    rw [Nat.card_perm, show Nat.card (Fin p) = p by simp] at hcard
    have h3f : 3 ∣ Nat.factorial p := Nat.dvd_factorial (by norm_num) (by omega)
    rw [← hcard] at h3f
    exact (Nat.Coprime.dvd_mul_left (by norm_num)).mp h3f
  exact exists_prime_orderOf_dvd_card' 3 h3

theorem exists_three_pow_preimage {W Q : Type*} [Group W] [Finite W] [Group Q] (ψ : W →* Q)
    {a : Q} (ha : orderOf a = 3) {w₀ : W} (hw₀ : ψ w₀ = a) :
    ∃ (w : W) (k : ℕ), w ^ 3 ^ k = 1 ∧ ψ w ≠ 1 ∧ ∃ m : ℕ, ψ w = a ^ m := by
  obtain ⟨k, m, hm, hkm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w₀).ne' 3 (by norm_num)
  refine ⟨w₀ ^ m, k, ?_, ?_, m, by rw [map_pow, hw₀]⟩
  · rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  · rw [map_pow, hw₀]
    intro h1
    exact hm (ha ▸ orderOf_dvd_of_pow_eq_one h1)

theorem altFiveResidue_of_escape {G : Type} [Group G] [Finite G] (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hglob : AGLGlobal G) (hD1 : D1For G) (hNX : NoXBlockFor G) {p : ℕ} [Fact p.Prime]
    (hp5 : p = 5) {P : Sylow p G} {M A H : Subgroup G} (hesc : D2Escape p P M A H A)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) :
    ((∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
          ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
        ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
          barM M A ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) := by
  have hp5' : 5 ≤ p := hp5.ge
  have hdata : D2AltData p M H A A := hesc.altData_of_alt hglob hRbar hK e hp5'
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L :=
    fun L hL => hdata.pair.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  obtain ⟨c₀, c₁, s, g, W, ψ, hWM, hsc, hWK, hW, hXW, -, hsurj, hker, -, -, -, hcases⟩ :=
    hdata.carrying_dichotomy hD1 hα hB3 h84 hNX
  have hbarA : ∀ {c : G} (hc : c ∈ A), barElt M hWM ⟨c, hXW hc⟩ ∈ barM M A := fun hc =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc)
  rcases hcases with ⟨Lb, hLb, hS⟩ | ⟨L₀, L₁, hL₀, hL₁, hne, h0, h1, -, -, hc0, hc1, -, -⟩
  ·
    refine Or.inr ⟨Lb, hLb, ?_⟩
    rw [eq_bot_iff]
    rintro x ⟨⟨m, hmA, rfl⟩, hxC⟩
    have hmA' : (m : G) ∈ A := Subgroup.mem_subgroupOf.mp hmA
    set w : W := ⟨m, hXW hmA'⟩
    have hwC : w ∈ centralizerBar M hWM Lb := hxC
    have hψ : w ∈ ψ.ker := hS w hwC
    rw [hker] at hψ
    have hmN : (m : G) ∈ GLBPrimeCore p H := hψ
    have hm1 : (m : G) = 1 := by
      have hmp : (m : G) ^ p = 1 := hdata.elem.2 _ hmA'
      have hdvd1 : orderOf (m : G) ∣ p := orderOf_dvd_of_pow_eq_one hmp
      have hdvd2 : orderOf (m : G) ∣ Nat.card (GLBPrimeCore p H) :=
        Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H) hmN
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hdvd1 (glbPrimeCore_coprime p H)) hdvd2)
    have hm1' : m = 1 := Subtype.ext hm1
    rw [hm1', map_one]
    exact Subgroup.one_mem _
  ·
    obtain ⟨L₀', hL₀'c, hL₀'b, hL₀'w | hL₀'K⟩ := hdata.pair.exists_weakSBlock_or_le_inf hL₀
    · refine Or.inl ⟨L₀', hL₀'w, fun hle => ?_⟩
      exact hc0 ⟨c₀, hXW hsc.mem_zero⟩ rfl (hL₀'b ▸ hle (hbarA hsc.mem_zero))
    obtain ⟨L₁', hL₁'c, hL₁'b, hL₁'w | hL₁'K⟩ := hdata.pair.exists_weakSBlock_or_le_inf hL₁
    · refine Or.inl ⟨L₁', hL₁'w, fun hle => ?_⟩
      exact hc1 ⟨c₁, hXW hsc.mem_one⟩ rfl (hL₁'b ▸ hle (hbarA hsc.mem_one))
    exfalso
    obtain ⟨a, ha⟩ := exists_orderOf_eq_three_alt hp5'
    obtain ⟨w₀', hw₀'⟩ := hsurj (a, 1)
    obtain ⟨w₁', hw₁'⟩ := hsurj (1, a)
    have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
    have ha1' : a ≠ 1 := fun h' => by
      rw [h', orderOf_one] at ha
      exact absurd ha (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hoa : orderOf (a, (1 : alternatingGroup (Fin p))) = 3 :=
      orderOf_eq_prime (Prod.ext (by simpa using ha3) (by simp))
        (fun h' => ha1' (congrArg Prod.fst h'))
    have hoa' : orderOf ((1 : alternatingGroup (Fin p)), a) = 3 :=
      orderOf_eq_prime (Prod.ext (by simp) (by simpa using ha3))
        (fun h' => ha1' (congrArg Prod.snd h'))
    obtain ⟨w₀, k₀, hw₀3, hw₀1, m₀, hw₀m⟩ := exists_three_pow_preimage ψ hoa hw₀'
    obtain ⟨w₁, k₁, hw₁3, hw₁1, m₁, hw₁m⟩ := exists_three_pow_preimage ψ hoa' hw₁'
    have hw₀C : w₀ ∉ centralizerBar M hWM L₀ := fun hw => by
      have h0w := h0 w₀ hw
      apply hw₀1
      rw [hw₀m] at h0w ⊢
      exact Prod.ext h0w (by simp)
    have hw₁C : w₁ ∉ centralizerBar M hWM L₁ := fun hw => by
      have h1w := h1 w₁ hw
      apply hw₁1
      rw [hw₁m] at h1w ⊢
      exact Prod.ext (by simp) h1w
    have hy₀ := hdata.pair.exists_threeElement_of_not_mem_centralizerBar hD1 hα hSch hB3 hWK hW
      hWM hL₀ hw₀3 hw₀C
    have hy₁ := hdata.pair.exists_threeElement_of_not_mem_centralizerBar hD1 hα hSch hB3 hWK hW
      hWM hL₁ hw₁3 hw₁C
    obtain ⟨L₂, hL₂⟩ := hdata.pair.exists_weakSBlock h84 hNX
    have h3 := hdata.pair.three_le_pRank_of_two_components hB3 hL₀'c hL₁'c hL₂ hL₀'K hL₁'K
      (by rw [hL₀'b, hL₁'b]; exact hne) (hL₀'b ▸ hy₀) (hL₁'b ▸ hy₁)
    have h2 := hesc.pRank_three_inf_le_two_of_alt_five hglob hD1 hRbar hK e hp5
    omega

theorem d2AltFive_of_residue (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hres : D2AltFiveResidue) : D2AltFive := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  exact hres G hglob hD1 p hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩
    (altFiveResidue_of_escape hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hglob.toAGLGlobal hD1
      (hD2.noXBlockFor hglob.toD1Global) hp5 hesc hRbar hK e)

end CFSG.AGLEmbeddingD2
