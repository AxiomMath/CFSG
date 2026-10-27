module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Apply
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Aux
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankF smallRankR smallRankIsQ8D8 Lemma630Iii)

variable {G : Type} [Group G] [Finite G]

theorem coprime_rankThreePrimeCore' {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    Nat.Coprime p (Nat.card (rankThreePrimeCore p C)) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
    hp C

theorem sup_subgroupOf_normal {Y : Type} [Group Y] (X O Q : Subgroup Y) (hOX : O ≤ X)
    (hQX : Q ≤ X) (hO : (O.subgroupOf X).Normal) (hQ : (Q.subgroupOf X).Normal) :
    ((O ⊔ Q).subgroupOf X).Normal := by
  refine ⟨fun n hn w => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨o, ho, t, ht, hnot⟩ := mul_decomp_of_mem_sup X O Q hOX hQX hO hQ hn n.2
  have hwO : (w : Y) * o * (w : Y)⁻¹ ∈ O := by
    have := hO.conj_mem (⟨o, hOX ho⟩ : ↥X) (Subgroup.mem_subgroupOf.mpr ho) w
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hwQ : (w : Y) * t * (w : Y)⁻¹ ∈ Q := by
    have := hQ.conj_mem (⟨t, hQX ht⟩ : ↥X) (Subgroup.mem_subgroupOf.mpr ht) w
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hrw : (w : Y) * (n : Y) * (w : Y)⁻¹ =
      ((w : Y) * o * (w : Y)⁻¹) * ((w : Y) * t * (w : Y)⁻¹) := by
    rw [hnot]
    group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hrw]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwO) (Subgroup.mem_sup_right hwQ)

theorem s62L630Iii_of_kfacts (hI : KFactI2026) (h5 : StepFiveFPF) (h9 : StepNineFPF) :
    S62L630Iii := by
  intro G _ _ p P M x z hS hx hz hP614 T₀ hT hcov hL628 f hf hf2 hcore hL629
  have hsetting : L630Setting G p P M x z T₀ f :=
    ⟨hS, hx, hz, hP614, hT, hcov, hL628, hf, hf2, hcore, hL629⟩
  have hp5 : p = 5 := by
    have h1 := hS.p_ge
    have h2 := hL628.1
    omega
  subst hp5
  have hf5 : Nat.Prime 5 := by norm_num
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact (Nat.Prime 5) := ⟨hf5⟩
  have hFe : IsElemAbelian f (smallRankF 5 f x) := hL629.2.2.2.1
  have hFc : Nat.card (smallRankF 5 f x) = f ^ 4 := hL629.2.2.2.2.1
  have hloc : rankThreeLocalRank f G ≤ 3 := hL629.2.2.1
  have hFM : smallRankF 5 f x ⊓ M = ⊥ := smallRankF_inf_eq_bot hf hf2 hL628.2.2.2
  have hFne : smallRankF 5 f x ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFc
    have h4 : 2 ≤ f ^ 4 := le_trans hf.two_le (Nat.le_self_pow (by norm_num) f)
    rw [← hFc] at h4
    norm_num at h4
  have hC_z : centralizer ({z} : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.centralizer_singleton_le hS hz
  have hzN : z ∈ normalizer ((smallRankF 5 f x : Subgroup G) : Set G) :=
    central_mem_normalizer_smallRankF hf5 hf hx.mem hz.centralizes
  have hzF : z ∉ centralizer ((smallRankF 5 f x : Subgroup G) : Set G) := by
    intro hzC
    apply hFne
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    exact eq_one_of_mem_smallRankF_comm hC_z hFM ha (mem_centralizer_iff.mp hzC a ha)
  set F : Subgroup G := smallRankF 5 f x with hFdef
  set N : Subgroup G := normalizer ((F : Subgroup G) : Set G) with hNdef
  have hCF_le_N : centralizer (F : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hCx_le_N : centralizer ({x} : Set G) ≤ N := fun g hg =>
    mem_normalizer_smallRankF hf5 hf hg
  set ψ : N →* MulAut F := Subgroup.normalizerMonoidHom F with hψdef
  have hψapp : ∀ (g : N) (a : F), ((ψ g a : F) : G) = (g : G) * (a : G) * (g : G)⁻¹ :=
    fun g a => rfl
  have hker : ∀ g : N, ψ g = 1 ↔ (g : G) ∈ centralizer (F : Set G) := by
    intro g
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro a ha
      have h1 : (g : G) * a * (g : G)⁻¹ = a := by
        have := hψapp g ⟨a, ha⟩
        rw [h, MulAut.one_apply] at this
        exact this.symm
      calc (a : G) * (g : G) = ((g : G) * (a : G) * (g : G)⁻¹) * (g : G) := by rw [h1]
        _ = (g : G) * (a : G) := by group
    · intro hg
      ext a
      rw [hψapp, MulAut.one_apply]
      have hc : (a : G) * g = g * a := (mem_centralizer_iff.mp hg) a a.2
      calc (g : G) * (a : G) * (g : G)⁻¹ = ((a : G) * (g : G)) * (g : G)⁻¹ := by rw [← hc]
        _ = (a : G) := by group
  obtain ⟨hPX, hPcard, hSX, hSO, hSP, hSQ8⟩ :=
    stepApplyI2026_holds G 5 P M x z T₀ f hsetting hzN
  have hcomm : ∀ a b : F, a * b = b * a := fun a b => hFe.1.is_comm.comm a b
  have hexp : ∀ e : F, e ^ f = 1 := fun e => by
    apply Subtype.ext
    simpa using hFe.2 e e.2
  obtain ⟨hscal, hinv⟩ := hI f F hf hf2 hcomm hexp hFc _ _ _ hPX hPcard hSX hSO hSP hSQ8
  haveI : Finite (MulAut F) := Finite.of_injective (fun e : MulAut F => e.toEquiv)
    (fun a b h => MulEquiv.ext fun y => congrArg (fun e : F ≃ F => e y) h)
  have hOX : rankThreePrimeCore 2 ψ.range ≤ ψ.range := rankThreePrimeCore_le_self 2 ψ.range
  have hQX : pCoreOf 2 ψ.range ≤ ψ.range := pCoreOf_le_self 2 ψ.range
  have hOn : ((rankThreePrimeCore 2 ψ.range).subgroupOf ψ.range).Normal :=
    rankThreePrimeCore_subgroupOf_normal Nat.prime_two ψ.range
  have hQn : ((pCoreOf 2 ψ.range).subgroupOf ψ.range).Normal := pCoreOf_subgroupOf_normal 2 ψ.range
  have hOodd : ¬ 2 ∣ Nat.card (rankThreePrimeCore 2 ψ.range) := by
    intro h
    have h2 := coprime_rankThreePrimeCore' Nat.prime_two ψ.range
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h2
    exact h2 h
  have hK0n : (((rankThreePrimeCore 2 ψ.range) ⊔ pCoreOf 2 ψ.range).subgroupOf ψ.range).Normal :=
    sup_subgroupOf_normal ψ.range _ _ hOX hQX hOn hQn
  have hfree : ∀ g : N, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf (ψ g) = q →
      ∀ a : F, ψ g a = a → a = 1 := by
    intro g q hq hq2 hord a hfix
    by_contra ha
    by_cases hq35 : q = 3 ∨ q = 5
    · have hgn : ψ g ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hord
        exact hq.one_lt.ne' hord.symm
      have hpow : (ψ g) ^ q = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      have hgqC : (g : G) ^ q ∈ centralizer (F : Set G) := by
        have h1 : ψ (g ^ q) = 1 := by rw [map_pow, hpow]
        have h2 := (hker (g ^ q)).mp h1
        rw [Subgroup.coe_pow] at h2
        exact h2
      have hgC : (g : G) ∉ centralizer (F : Set G) := fun h => hgn ((hker g).mpr h)
      have hgae : (g : G) * (a : G) * (g : G)⁻¹ = a := by
        rw [← hψapp, hfix]
      have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
      rcases hq35 with rfl | rfl
      · exact h9 G 5 P M x z T₀ f hsetting (g : G) g.2 hgqC hgC (a : G) a.2 ha' hgae
      · exact h5 G 5 P M x z T₀ f hsetting (g : G) g.2 hgqC hgC (a : G) a.2 ha' hgae
    · have hwX : ψ g ∈ ψ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
      have hwodd : Odd (orderOf (ψ g)) := by
        rw [hord]
        exact hq.odd_of_ne_two hq2
      have hwK : ψ g ∈ rankThreePrimeCore 2 ψ.range ⊔ pCoreOf 2 ψ.range := by
        by_contra hwK
        have hW : (⟨ψ g, hwX⟩ : ψ.range) ∉
            ((rankThreePrimeCore 2 ψ.range ⊔ pCoreOf 2 ψ.range).subgroupOf ψ.range) := by
          rw [Subgroup.mem_subgroupOf]
          exact hwK
        haveI : Fact q.Prime := ⟨hq⟩
        have hpowW : (⟨ψ g, hwX⟩ : ψ.range) ^ q = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          show ψ g ^ q = 1
          rw [← hord]
          exact pow_orderOf_eq_one _
        have hne1 : (QuotientGroup.mk (⟨ψ g, hwX⟩ : ψ.range) :
            ψ.range ⧸
              ((rankThreePrimeCore 2 ψ.range ⊔ pCoreOf 2 ψ.range).subgroupOf ψ.range)) ≠ 1 := by
          rw [Ne, QuotientGroup.eq_one_iff]
          exact hW
        have hordQ : orderOf (QuotientGroup.mk (⟨ψ g, hwX⟩ : ψ.range) :
            ψ.range ⧸
              ((rankThreePrimeCore 2 ψ.range ⊔ pCoreOf 2 ψ.range).subgroupOf ψ.range)) = q := by
          apply orderOf_eq_prime _ hne1
          rw [← QuotientGroup.mk_pow, hpowW]
          rfl
        have hdivQ : q ∣ Nat.card (ψ.range ⧸
            ((rankThreePrimeCore 2 ψ.range ⊔ pCoreOf 2 ψ.range).subgroupOf ψ.range)) := by
          rw [← hordQ]
          exact orderOf_dvd_natCard _
        have h720 := card_dvd_of_isInvolvedIn (hinv hK0n)
        have hq720 : q ∣ 720 := hdivQ.trans h720
        rcases prime_eq_two_three_or_five hq hq720 with h | h | h
        · exact hq2 h
        · exact hq35 (Or.inl h)
        · exact hq35 (Or.inr h)
      have hwO : ψ g ∈ rankThreePrimeCore 2 ψ.range :=
        mem_of_odd_of_mem_sup ψ.range _ _ hOX hQX hOn hQn hOodd (pCoreOf_isPGroup 2 ψ.range) hwX
          hwK hwodd
      obtain ⟨k, hk⟩ := hscal (ψ g) hwO
      have hw1 : ψ g = 1 := scalar_eq_one hf hexp (ψ g) hk ha hfix
      rw [hw1, orderOf_one] at hord
      exact hq.one_lt.ne' hord.symm
  unfold Lemma630Iii
  intro a ha ha1 g hg
  have hgN : g ∈ N := hg.1
  have hgc : g * a = a * g := mem_centralizer_singleton_iff.mp hg.2
  have hfixg : ψ ⟨g, hgN⟩ ⟨a, ha⟩ = ⟨a, ha⟩ := by
    apply Subtype.ext
    show (g : G) * (a : G) * (g : G)⁻¹ = (a : G)
    calc (g : G) * (a : G) * (g : G)⁻¹ = ((a : G) * (g : G)) * (g : G)⁻¹ := by rw [hgc]
      _ = (a : G) := by group
  have hne1 : (⟨a, ha⟩ : F) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := two_pow_mem_ker_of_fixed ψ hfree ⟨g, hgN⟩ hfixg hne1
  refine ⟨n, ?_⟩
  have hmem := (hker (⟨g, hgN⟩ ^ 2 ^ n)).mp hn
  simpa using hmem

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
