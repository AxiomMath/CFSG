module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
import CFSG.LocalAnalysis.AGLEmbedding.ReeArith
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] def StmtReeTarget : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d → ∀ (T : Type) [Group T] [Finite T],
    Nonempty (T ≃* CatGroup d) → IsSimpleGroup T →
    JStarTarget 3 (3 ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T ∧
    JStarTargetCard 3 (3 * d.1.fieldExponent) (3 ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T

theorem stmtReeTarget_of (hKR2 : KFactReeSylowCenterTorus) (hKR7 : KFactReeAutPCard)
    (hKR8 : KFactReeOrder) (hKR9 : KFactReeOuterSolvable) : StmtReeTarget := by
  intro d hd T _ _ hTe hTs
  have hn3 : 3 ≤ d.1.fieldExponent := hd.three_le_fieldExponent
  set n := d.1.fieldExponent with hn
  have hcard : Nat.card T = (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) := hKR8 T d hd hTe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ S : Sylow 3 T, Nat.card (S : Subgroup T) = 3 ^ (3 * n) :=
    card_sylow_of_card_ree (by omega) hcard
  have hq1 : 1 < 3 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
  have hrank : 3 ≤ Open.pRank 3 (⊤ : Subgroup T) := by
    obtain ⟨S⟩ : Nonempty (Sylow 3 T) := inferInstance
    obtain ⟨ψ, hψ, hψZ, -⟩ := hKR2 T d hd hTe S
    obtain ⟨hZel, hZcard⟩ := isElemAbelian_range_galoisField (by omega) ψ hψ
    exact hn3.trans (le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨_, le_top, hZel, hZcard⟩)
  have hnonab : ∃ x y : T, x * y ≠ y * x := nonabelian_of_card_ree (by omega) hcard
  refine ⟨⟨hTs, hnonab, hrank, hKR9 T d hd hTe, ?_⟩, ⟨hsyl, hKR7 T d hd hTe⟩⟩
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := 3) (n := 6 * n)
      le_rfl (by omega)
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ (6 * n) := dvd_pow_self 3 (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at h2
    omega
  have hfac : 3 ^ (6 * n) - 1 = ((3 ^ n) ^ 3 + 1) * ((3 ^ n) ^ 3 - 1) := by
    have h6 : 3 ^ (6 * n) = ((3 ^ n) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
    have h := Nat.sq_sub_sq ((3 ^ n) ^ 3) 1
    rw [one_pow] at h
    rw [h6, h]
  have hnd : ¬ ℓ ∣ (3 ^ n) ^ 3 - 1 := by
    rw [← pow_mul]
    exact hprim (n * 3) (by omega) (by omega)
  have hℓq : ℓ ∣ (3 ^ n) ^ 3 + 1 := by
    rw [hfac] at hℓdvd
    exact ((Nat.Prime.dvd_mul hℓ).mp hℓdvd).resolve_right hnd
  refine ⟨ℓ, hℓ, hℓ3, ?_, fun k hk hkB => hprim k hk ?_⟩
  · rw [hcard]
    exact (hℓq.mul_left _).mul_right _
  · have hle := Nat.le_of_dvd (by positivity) hkB
    have h1 : 3 ^ (3 * n) * n < 3 ^ (3 * n) * 3 ^ (3 * n) :=
      Nat.mul_lt_mul_of_pos_left
        ((Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
        (by positivity)
    rw [← pow_add, show 3 * n + 3 * n = 6 * n by ring] at h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (lt_of_le_of_lt hle h1)

@[expose] def StmtReeElim : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d → ∀ (T : Type) [Group T] [Finite T],
    Nonempty (T ≃* CatGroup d) → IsSimpleGroup T →
    JStarElimOf 3 (3 ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem ree_elim_self (hKR8 : KFactReeOrder) (hKR9 : KFactReeOuterSolvable)
    {d d' : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (hd' : IsReeGTwoIndex 3 d')
    {T : Type} [Group T] [Finite T] (hTe : Nonempty (T ≃* CatGroup d)) (hTs : IsSimpleGroup T)
    {L₀ : Type} [Group L₀] [Finite L₀] (hL₀ : IsSimpleGroup L₀) (e' : L₀ ≃* CatGroup d')
    (hdata : JStarElimDataOf L₀ 3 (3 ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T) :
    Nonempty (L₀ ≃* T) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eT⟩ := hTe
  set n := d.1.fieldExponent with hn
  set n' := d'.1.fieldExponent with hn'
  have hn3 : 3 ≤ n := hd.three_le_fieldExponent
  have hn'3 : 3 ≤ n' := hd'.three_le_fieldExponent
  obtain ⟨A, J, hA, hJA, hcardA, φ, hs, -⟩ := hdata
  have hcardL₀ := hKR8 L₀ d' hd' ⟨e'⟩
  have hcardT := hKR8 T d hd ⟨eT⟩
  have hTnab : ∃ x y : T, x * y ≠ y * x := nonabelian_of_card_ree (by omega) hcardT
  have hTperf : Group.IsPerfect T := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T) with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hTnab
      have h1 : (⊤ : Subgroup T) ≤ Subgroup.centralizer ((⊤ : Subgroup T) : Set T) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
      exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
    · exact htop
  have hL₀nab : ∃ x y : L₀, x * y ≠ y * x := nonabelian_of_card_ree (by omega) hcardL₀
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
  have hlt : n' < 2 * n := by
    obtain ⟨S⟩ : Nonempty (Sylow 3 L₀) := inferInstance
    have hS := card_sylow_of_card_ree (by omega) hcardL₀ S
    have hS'A : (S : Subgroup L₀).map MulAut.conj ≤ A :=
      (Subgroup.map_le_range _ _).trans hA
    have hdvd := hcardA _ hS'A (S.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective hinjc, hS] at hdvd
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : 3 ^ (3 * n) * n < 3 ^ (3 * n) * 3 ^ (3 * n) :=
      Nat.mul_lt_mul_of_pos_left
        ((Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
        (by positivity)
    rw [← pow_add] at h2
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (lt_of_le_of_lt h1 h2)
    omega
  obtain ⟨k, hk⟩ := (hKR9 L₀ d' hd' ⟨e'⟩).solvable
  set Jk := derivedSeries J k with hJk
  have hJkInn : Jk.map J.subtype ≤ inner L₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries ((QuotientGroup.mk' (inner L₀)).comp J.subtype)
      k ⟨x, hx, rfl⟩
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
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := 3) (n := 6 * n)
      le_rfl (by omega)
  have hℓT : ℓ ∣ Nat.card T := by
    have hq6 : 3 ^ (6 * n) - 1 = ((3 ^ n) ^ 3 + 1) * ((3 ^ n) ^ 3 - 1) := by
      have h6 : 3 ^ (6 * n) = ((3 ^ n) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
      have h := Nat.sq_sub_sq ((3 ^ n) ^ 3) 1
      rw [one_pow] at h
      rw [h6, h]
    have hnd : ¬ ℓ ∣ (3 ^ n) ^ 3 - 1 := by
      rw [← pow_mul]
      exact hprim (n * 3) (by omega) (by omega)
    have hℓdvd' := hℓdvd
    rw [hq6] at hℓdvd'
    rw [hcardT]
    exact ((((Nat.Prime.dvd_mul hℓ).mp hℓdvd').resolve_right hnd).mul_left _).mul_right _
  have hℓL := hℓT.trans hTdvd
  rw [hcardL₀] at hℓL
  have hnn' : n ∣ n' := dvd_of_ppd_dvd_card_ree hℓ (by omega) hℓdvd hprim hℓL
  have hnn : n' = n := by
    obtain ⟨c, hc⟩ := hnn'
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  obtain ⟨-, m, -, hm, hme⟩ := hd.exists_eq
  obtain ⟨-, m', -, hm', hme'⟩ := hd'.exists_eq
  have hdd : d' = d := by
    apply Subtype.ext
    rw [hm, hm']
    have : m' = m := by
      have h1 : n' = 2 * m' + 1 := hme'
      have h2 : n = 2 * m + 1 := hme
      omega
    rw [this]
  subst hdd
  exact ⟨e'.trans eT.symm⟩

theorem stmtReeElim_of (hEL : KFactJStarElimReeLie) (hEA : KFactJStarElimReeAlt)
    (hES : KFactJStarElimReeSpor) (hKR8 : KFactReeOrder) (hKR9 : KFactReeOuterSolvable) :
    StmtReeElim := by
  intro d hd T _ _ hTe hTs L₀ _ _ hL₀ hlist hdata
  obtain ⟨eT⟩ := hTe
  have hdata' := hdata.congr_target eT
  rcases hlist with ⟨d', hd'l, ⟨e'⟩⟩ | he' | ⟨s, hs, ⟨e'⟩⟩
  · by_cases hR : IsReeGTwoIndex 3 d'
    · exact ree_elim_self hKR8 hKR9 hd hR ⟨eT⟩ hTs hL₀ e' hdata
    · exact (hEL d hd L₀ hL₀ d' hd'l hR ⟨e'⟩ hdata').elim
  · exact (hEA d hd L₀ he' hdata').elim
  · exact (hES d hd L₀ s hs ⟨e'⟩ hdata').elim

end CFSG.AGLEmbedding
