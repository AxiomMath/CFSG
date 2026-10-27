module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoJConfig
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem stmtUnitaryToJConfig_of (hB : StmtUnitaryBorel) : StmtUnitaryToJConfig := by
  intro G _ _ p _ d hd T _ _ hTe P M H R U h hN
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKn, ⟨eT⟩, hC, hUK⟩ := h.socle
  obtain ⟨eTd⟩ := hTe
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set X₀ := ((H ⊓ M).subgroupOf H).map π with hX₀
  set Ub : Subgroup (H ⧸ primeComplementCore (G := H) p) := (Rbar : Subgroup _) ⊓ K with hUbdef
  set Zb := Ub ⊓ Subgroup.centralizer (Ub : Set _) with hZbdef
  obtain ⟨hn2, -, -, -, hD1, -, hCU, ⟨ψ, hψ, hψZ, -⟩, -, -, -⟩ :=
    hB Rbar X₀ K Ub Zb d hd hred hKn ⟨eT.trans eTd⟩ hC rfl rfl
  have hn0 : d.1.fieldExponent ≠ 0 := by omega
  have hZbcard := (isElemAbelian_range_galoisField hn0 ψ hψ).2
  rw [hψZ] at hZbcard
  have hZb1 : Zb ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZbcard
    have := Nat.one_lt_pow hn0 hp.one_lt
    omega
  have hZbp : IsPGroup p Zb := Rbar.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hph3 : D1PhaseThree p P M H R := h.ext.toPhaseThreeU h.glob
    (h.ext.primeCore_inf_eq_iff.mpr (primeComplementCore_eq_bot_of_dichotomy hD1 hZbp hZb1))
  have hUb : (U.subgroupOf H).map π = Ub := by rw [hUK, ← hRbar]
  have hne : U ≠ ⊥ := by
    rintro rfl
    apply hZb1
    rw [eq_bot_iff]
    intro z hz
    have hzU : z ∈ (((⊥ : Subgroup G).subgroupOf H).map π) := hUb ▸ hz.1
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot] at hzU
    exact hzU
  have hCX : Subgroup.centralizer (((U.subgroupOf H).map π :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) : Set _) ≤ (U.subgroupOf H).map π := by
    rw [hUb]
    exact hCU
  exact ⟨hph3, h.le_R, hne, hN, hph3.commutator_glbPrimeCore_le_twoCore h.le_R hN,
    (inf_le_inf_right _ inf_le_left).trans (inf_centralizer_le_sup_glbPrimeCore hCX)⟩

theorem stmtUnitaryTarget_of (hKU2 : KFactUnitarySylowStructure) (hKU10 : KFactUnitaryAutPCard)
    (hKU11 : KFactUnitaryOrder) (hKU12 : KFactUnitaryOuterSolvable) : StmtUnitaryTarget := by
  intro p _ d hp2 hd hn2 T _ _ hTe hTs
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨S⟩ : Nonempty (Sylow p T) := inferInstance
  obtain ⟨hScard, hScomm, -, E, -, hE, hEcard⟩ := hKU2 T p d hp2 hd hTe S
  have hsyl : ∀ S' : Sylow p T, Nat.card (S' : Subgroup T) = p ^ (3 * d.1.fieldExponent) :=
    fun S' =>
    (hKU2 T p d hp2 hd hTe S').1
  have hrank : 3 ≤ Open.pRank p (⊤ : Subgroup T) :=
    (show 3 ≤ 2 * d.1.fieldExponent by omega).trans
      (le_csSup (pRank_bddAbove p hp _) ⟨E, le_top, hE, hEcard⟩)
  have hnonab : ∃ x y : T, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    have hc : ⁅(S : Subgroup T), (S : Subgroup T)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ =>
        Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    have hcent : (S : Subgroup T) ⊓ Subgroup.centralizer ((S : Subgroup T) : Set T) =
        (S : Subgroup T) :=
      inf_eq_left.mpr fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    rw [hcent, hc] at hScomm
    rw [← hScomm, Subgroup.card_bot] at hScard
    have := Nat.one_lt_pow (by omega : 3 * d.1.fieldExponent ≠ 0) hp.one_lt
    omega
  refine ⟨⟨hTs, hnonab, hrank, hKU12 T p d hd hTe, ?_⟩, ⟨hsyl, hKU10 T p d hp2 hd hTe⟩⟩
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p)
      (n := 6 * d.1.fieldExponent)
      hp3 (by omega)
  have hℓp : ℓ ≠ p := by
    rintro rfl
    have h1 : ℓ ∣ ℓ ^ (6 * d.1.fieldExponent) := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    apply hprim 1 one_pos (by omega)
    rw [pow_one]
    exact (Nat.Prime.even_sub_one hp hp2).two_dvd
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have hp3' : p ≠ 3 := fun h => hℓp h.symm
    apply hprim 2 (by norm_num) (by omega)
    have h3 : ¬ 3 ∣ p := fun h => hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    rcases hmod with h | h
    · have : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
    · have : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
  have hfac : p ^ (6 * d.1.fieldExponent) - 1 =
      ((p ^ d.1.fieldExponent) ^ 3 + 1) * ((p ^ d.1.fieldExponent) ^ 3 - 1) := by
    have h6 : p ^ (6 * d.1.fieldExponent) = ((p ^ d.1.fieldExponent) ^ 3) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; ring_nf
    have h := Nat.sq_sub_sq ((p ^ d.1.fieldExponent) ^ 3) 1
    rw [one_pow] at h
    rw [h6, h]
  have hnd : ¬ ℓ ∣ (p ^ d.1.fieldExponent) ^ 3 - 1 := by
    rw [← pow_mul]
    exact hprim (d.1.fieldExponent * 3) (by omega) (by omega)
  have hℓq : ℓ ∣ (p ^ d.1.fieldExponent) ^ 3 + 1 := by
    rw [hfac] at hℓdvd
    exact ((Nat.Prime.dvd_mul hℓ).mp hℓdvd).resolve_right hnd
  refine ⟨ℓ, hℓ, hℓp, ?_, fun k hk hkB => hprim k hk ?_⟩
  · have hord := hKU11 T p d hd hTe
    have h1 : ℓ ∣ Nat.card T * Nat.gcd 3 (p ^ d.1.fieldExponent + 1) := by
      rw [hord]
      exact (hℓq.mul_left _).mul_right _
    rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h | h
    · exact h
    · exfalso
      have h3 := h.trans (Nat.gcd_dvd_left 3 _)
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3)
  · have hle := Nat.le_of_dvd (by positivity) hkB
    have h1 : p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent <
        p ^ (3 * d.1.fieldExponent) * p ^ (3 * d.1.fieldExponent) :=
      Nat.mul_lt_mul_of_pos_left
        ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.pow_le_pow_right hp.pos (by omega)))
        (by positivity)
    rw [← pow_add, show 3 * d.1.fieldExponent + 3 * d.1.fieldExponent =
      6 * d.1.fieldExponent by ring] at h1
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle h1)

theorem dvd_of_ppd_dvd_card_unitary {p ℓ n m : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hℓdvd : ℓ ∣ p ^ (6 * n) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ ℓ ∣ p ^ k - 1)
    (hℓK : ℓ ∣ (p ^ m) ^ 3 * ((p ^ m) ^ 3 + 1) * ((p ^ m) ^ 2 - 1)) : n ∣ m := by
  have := Fact.mk hℓ
  have hℓp : ℓ ≠ p := by
    rintro rfl
    have h1 : ℓ ∣ ℓ ^ (6 * n) := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓq : ¬ ℓ ∣ (p ^ m) ^ 3 := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow (hℓ.dvd_of_dvd_pow h)))
  have hq6 : p ^ (6 * m) - 1 = ((p ^ m) ^ 3 + 1) * ((p ^ m) ^ 3 - 1) := by
    have h6 : p ^ (6 * m) = ((p ^ m) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
    have h := Nat.sq_sub_sq ((p ^ m) ^ 3) 1
    rw [one_pow] at h
    rw [h6, h]
  have hℓ6 : ℓ ∣ p ^ (6 * m) - 1 := by
    rw [mul_assoc] at hℓK
    have h1 := Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq) hℓK
    rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
    · rw [hq6]
      exact h2.mul_right _
    · have h3 : (p ^ m) ^ 2 - 1 ∣ p ^ (6 * m) - 1 := by
        have h6 : p ^ (6 * m) = ((p ^ m) ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]; ring_nf
        rw [h6]
        simpa using Nat.sub_dvd_pow_sub_pow (x := (p ^ m) ^ 2) (y := 1) (n := 3)
      exact h2.trans h3
  have hp0 : (p : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
  have hpow : ∀ k, ℓ ∣ p ^ k - 1 ↔ (p : ZMod ℓ) ^ k = 1 := fun k =>
    CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k
  have hord : orderOf (p : ZMod ℓ) = 6 * n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨(hpow _).mp hℓdvd, fun k hk hk0 h => hprim k hk0 hk ((hpow k).mpr h)⟩
  have h6 : 6 * n ∣ 6 * m := hord ▸ orderOf_dvd_of_pow_eq_one ((hpow _).mp hℓ6)
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h6

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem unitary_elim_self (hKU2 : KFactUnitarySylowStructure) (hKU11 : KFactUnitaryOrder)
    (hKU12 : KFactUnitaryOuterSolvable)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d d' : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : 2 ≤ d.1.fieldExponent) (hd' : IsUnitaryIndex p d')
    {T : Type} [Group T] [Finite T] (hTe : Nonempty (T ≃* CatGroup d)) (hTs : IsSimpleGroup T)
    {L₀ : Type} [Group L₀] [Finite L₀] (hL₀ : IsSimpleGroup L₀) (e' : L₀ ≃* CatGroup d')
    (hdata : JStarElimDataOf L₀ p (p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T) :
    Nonempty (L₀ ≃* T) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨eT⟩ := hTe
  obtain ⟨A, J, hA, hJA, hcardA, φ, hs, -⟩ := hdata
  obtain ⟨q', hq'p, hq'd, hm, hm1⟩ := hd'.exists_eq
  have hnab : ∀ (L : Type) [Group L] [Finite L] (d₁ : TauCeti.ValidLieTypeIndex),
      IsUnitaryIndex p d₁ → 1 ≤ d₁.1.fieldExponent → Nonempty (L ≃* CatGroup d₁) →
      ∃ x y : L, x * y ≠ y * x := by
    intro L _ _ d₁ hd₁ hn₁ he₁
    obtain ⟨S⟩ : Nonempty (Sylow p L) := inferInstance
    obtain ⟨hScard, hScomm, -⟩ := hKU2 L p d₁ hp2 hd₁ he₁ S
    by_contra hcomm
    push Not at hcomm
    have hc : ⁅(S : Subgroup L), (S : Subgroup L)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ =>
        Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    have hcent : (S : Subgroup L) ⊓ Subgroup.centralizer ((S : Subgroup L) : Set L) =
        (S : Subgroup L) :=
      inf_eq_left.mpr fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    rw [hcent, hc] at hScomm
    rw [← hScomm, Subgroup.card_bot] at hScard
    have := Nat.one_lt_pow (by omega : 3 * d₁.1.fieldExponent ≠ 0) hp.one_lt
    omega
  have hTnab := hnab T d hd (by omega) ⟨eT⟩
  have hTperf : Group.IsPerfect T := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T) with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hTnab
      have h1 : (⊤ : Subgroup T) ≤ Subgroup.centralizer ((⊤ : Subgroup T) : Set T) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
      exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
    · exact htop
  have hL₀nab := hnab L₀ d' hd' (by omega) ⟨e'⟩
  have hZ : Subgroup.center L₀ = ⊥ :=
    CFSG.ComponentClassification.BMCase.center_eq_bot_of_isSimpleGroup hL₀nab
  have hinjc : Function.Injective (MulAut.conj : L₀ →* MulAut L₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : x ∈ Subgroup.center L₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut L₀ => f y) (MonoidHom.mem_ker.mp hx)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rwa [hZ] at hxZ
  have hlt : d'.1.fieldExponent < 2 * d.1.fieldExponent := by
    obtain ⟨S⟩ : Nonempty (Sylow p L₀) := inferInstance
    have hS := (hKU2 L₀ p d' hp2 hd' ⟨e'⟩ S).1
    have hS'A : (S : Subgroup L₀).map MulAut.conj ≤ A :=
      (Subgroup.map_le_range _ _).trans hA
    have hdvd := hcardA _ hS'A (S.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective hinjc, hS] at hdvd
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent <
        p ^ (3 * d.1.fieldExponent) * p ^ (3 * d.1.fieldExponent) :=
      Nat.mul_lt_mul_of_pos_left
        ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.pow_le_pow_right hp.pos (by omega)))
        (by positivity)
    rw [← pow_add] at h2
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h1 h2)
    omega
  obtain ⟨k, hk⟩ := (hKU12 L₀ p d' hd' ⟨e'⟩).solvable
  set Jk := derivedSeries J k with hJk
  have hJkInn : Jk.map J.subtype ≤ inner L₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries
      ((QuotientGroup.mk' (inner L₀)).comp J.subtype) k ⟨x, hx, rfl⟩
    have : (inner L₀).Normal := inner_normal L₀
    rw [hk, Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hφk : Jk.map φ = ⊤ := by
    rw [hJk, map_derivedSeries_eq hs, Group.IsPerfect.derivedSeries_eq_top]
  have hTdvd : Nat.card T ∣ Nat.card L₀ := by
    have h1 : Nat.card T ∣ Nat.card Jk := by
      refine Subgroup.card_dvd_of_surjective (f := φ.comp Jk.subtype) fun t => ?_
      obtain ⟨x, hx, hxt⟩ : t ∈ Jk.map φ := hφk ▸ Subgroup.mem_top t
      exact ⟨⟨x, hx⟩, hxt⟩
    have h2 : Nat.card Jk ∣ Nat.card (inner L₀) := by
      rw [← Subgroup.card_map_of_injective J.subtype_injective]
      exact Subgroup.card_dvd_of_le hJkInn
    have h3 : Nat.card (inner L₀) = Nat.card L₀ :=
      Nat.card_congr (MonoidHom.ofInjective hinjc).symm.toEquiv
    exact (h1.trans h2).trans h3.dvd
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p)
      (n := 6 * d.1.fieldExponent) hp3 (by omega)
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    by_cases hp3' : p = 3
    · subst hp3'
      have h1 : 3 ∣ 3 ^ (6 * d.1.fieldExponent) := dvd_pow_self 3 (by omega)
      have h2 := Nat.dvd_sub h1 hℓdvd
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at h2
      omega
    · apply hprim 2 (by norm_num) (by omega)
      have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
        have h3 : ¬ 3 ∣ p := fun h =>
          hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
        omega
      have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      rcases hmod with h | h
      · have : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
        omega
      · have : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
        omega
  have hℓT : ℓ ∣ Nat.card T := by
    have hfac : p ^ (6 * d.1.fieldExponent) - 1 =
        ((p ^ d.1.fieldExponent) ^ 3 + 1) * ((p ^ d.1.fieldExponent) ^ 3 - 1) := by
      have h6 : p ^ (6 * d.1.fieldExponent) = ((p ^ d.1.fieldExponent) ^ 3) ^ 2 := by
        rw [← pow_mul, ← pow_mul]; ring_nf
      have h := Nat.sq_sub_sq ((p ^ d.1.fieldExponent) ^ 3) 1
      rw [one_pow] at h
      rw [h6, h]
    have hnd : ¬ ℓ ∣ (p ^ d.1.fieldExponent) ^ 3 - 1 := by
      rw [← pow_mul]
      exact hprim (d.1.fieldExponent * 3) (by omega) (by omega)
    have hℓq : ℓ ∣ (p ^ d.1.fieldExponent) ^ 3 + 1 := by
      rw [hfac] at hℓdvd
      exact ((Nat.Prime.dvd_mul hℓ).mp hℓdvd).resolve_right hnd
    have h1 : ℓ ∣ Nat.card T * Nat.gcd 3 (p ^ d.1.fieldExponent + 1) := by
      rw [hKU11 T p d hd ⟨eT⟩]
      exact (hℓq.mul_left _).mul_right _
    rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h | h
    · exact h
    · exfalso
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
        (h.trans (Nat.gcd_dvd_left 3 _)))
  have hℓL : ℓ ∣ (p ^ d'.1.fieldExponent) ^ 3 * ((p ^ d'.1.fieldExponent) ^ 3 + 1) *
      ((p ^ d'.1.fieldExponent) ^ 2 - 1) := by
    rw [← hKU11 L₀ p d' hd' ⟨e'⟩]
    exact (hℓT.trans hTdvd).mul_right _
  have hnm : d.1.fieldExponent ∣ d'.1.fieldExponent :=
    dvd_of_ppd_dvd_card_unitary hp hℓ (by omega) hℓdvd hprim hℓL
  have hmn : d'.1.fieldExponent = d.1.fieldExponent := by
    obtain ⟨c, hc⟩ := hnm
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  obtain ⟨q, hqp, hqd, hn', -⟩ := hd.exists_eq
  have hdd : d' = d := by
    apply Subtype.ext
    rw [hq'd, hqd]
    congr 1
    exact TauCeti.PrimePower.ext (hq'p.trans hqp.symm) (by omega)
  subst hdd
  exact ⟨e'.trans eT.symm⟩

theorem stmtUnitaryElim_of (hEL : KFactJStarElimUnitaryLie) (hEA : KFactJStarElimUnitaryAlt)
    (hES : KFactJStarElimUnitarySpor) (hKU2 : KFactUnitarySylowStructure)
    (hKU11 : KFactUnitaryOrder) (hKU12 : KFactUnitaryOuterSolvable) : StmtUnitaryElim := by
  intro p _ d hp2 hd hn T _ _ hTe hTs L₀ _ _ hL₀ hlist hdata
  obtain ⟨eT⟩ := hTe
  have hdata' := hdata.congr_target eT
  rcases hlist with ⟨d', hd'l, ⟨e'⟩⟩ | he' | ⟨s, hs, ⟨e'⟩⟩
  · by_cases hU : IsUnitaryIndex p d'
    · exact unitary_elim_self hKU2 hKU11 hKU12 hp2 hd hn hU ⟨eT⟩ hTs hL₀ e' hdata
    · exact (hEL p d hp2 hd hn L₀ hL₀ d' hd'l hU ⟨e'⟩ hdata').elim
  · exact (hEA p d hp2 hd hn L₀ he' hdata').elim
  · exact (hES p d hp2 hd hn L₀ s hs ⟨e'⟩ hdata').elim

end CFSG.AGLEmbedding
