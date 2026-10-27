module

import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Basic

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

omit [Finite X] in
theorem inf_centralizer_eq_center_map_of_omega {R E K : Subgroup X} {z : X}
    (hER : E ≤ R) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (hz : z ∈ Subgroup.center X)
    (hC : ∀ c ∈ R ⊓ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ Subgroup.zpowers z) :
    E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype := by
  have hzZ : z ∈ (Subgroup.center E).map E.subtype := by
    rw [hZE]
    exact Subgroup.mem_zpowers z
  refine le_antisymm (fun e he => ?_) ?_
  · rw [hZE]
    by_cases he1 : e = 1
    · rw [he1]
      exact Subgroup.one_mem _
    · exact hC e ⟨hER he.1, he.2⟩ (orderOf_eq_prime (hEp e he.1) he1)
  · rw [hZE]
    exact Subgroup.zpowers_le.mpr ⟨Subgroup.map_subtype_le _ hzZ,
      Subgroup.center_le_centralizer _ hz⟩

theorem exists_mem_inf_not_mem_centralizer (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hZK : IsPGroup p (Subgroup.center K)) (hKp : p ∣ Nat.card (K ⧸ Subgroup.center K)) :
    ∃ k ∈ (R : Subgroup X) ⊓ K, k ∉ Subgroup.centralizer (K : Set X) := by
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' p hKp
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hxZ : x ^ p ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hxb ▸ pow_orderOf_eq_one _
  obtain ⟨m, hm⟩ := hZK ⟨x ^ p, hxZ⟩
  have hxm : (x : X) ^ (p ^ (m + 1)) = 1 := by
    have h1 : (x ^ p) ^ (p ^ m) = 1 := by
      have := congrArg (fun y : Subgroup.center K => (y : K)) hm
      simpa using this
    have h2 : x ^ (p ^ (m + 1)) = 1 := by rw [pow_succ', pow_mul]; exact h1
    simpa using congrArg Subtype.val h2
  have hQ : IsPGroup p (Subgroup.zpowers (x : X)) := by
    refine IsPGroup.of_card (n := (orderOf (x : X)).factorization p) ?_
    rw [Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hxm)
    rw [hj, Nat.Prime.factorization_pow (Fact.out : p.Prime)]
    simp
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup R hQ
  refine ⟨g⁻¹ * x * g, ⟨hg _ (Subgroup.mem_zpowers _), ?_⟩, fun hC => ?_⟩
  · simpa using ‹K.Normal›.conj_mem (x : X) x.2 g⁻¹
  · have hxC : (x : X) ∈ Subgroup.centralizer (K : Set X) := by
      have h1 := (inferInstance : (Subgroup.centralizer (K : Set X)).Normal).conj_mem _ hC g
      have h2 : g * (g⁻¹ * (x : X) * g) * g⁻¹ = x := by group
      rwa [h2] at h1
    have hxz : x ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC k k.2)
    rw [(QuotientGroup.eq_one_iff x).mpr hxz, orderOf_one] at hxb
    exact (Fact.out : p.Prime).one_lt.ne hxb

theorem three_le_pRank_of_card_sq {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y}
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) {y : Y}
    (hyC : y ∈ Subgroup.centralizer (A : Set Y)) (hyp : y ^ p = 1) (hyA : y ∉ A) :
    3 ≤ Open.pRank p (⊤ : Subgroup Y) := by
  have hp := (Fact.out : p.Prime)
  have hE := CFSG.AGLEmbedding.isElemAbelian_sup_zpowers_of_mem_centralizer hA hyC hyp
  have hlt : A < A ⊔ Subgroup.zpowers y := lt_of_le_of_ne le_sup_left fun h =>
    hyA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hPG : IsPGroup p (A ⊔ Subgroup.zpowers y : Subgroup Y) :=
    fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPG
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hAcard, hm, pow_lt_pow_iff_right₀ hp.one_lt] at hcard
  exact (show 3 ≤ m by omega).trans (le_csSup (pRank_bddAbove p hp _) ⟨_, le_top, hE, hm⟩)

theorem three_le_pRank_mulAut_of_inf_sup_le (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hZK : IsPGroup p (Subgroup.center K)) (hKp : p ∣ Nat.card (K ⧸ Subgroup.center K))
    {z : X} (hz : z ∈ Subgroup.center X)
    (hC : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ Subgroup.zpowers z)
    {E : Subgroup X} (hER : E ≤ (R : Subgroup X)) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (hEY : E ⊓ (K ⊔ Subgroup.centralizer (K : Set X)) ≤ (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  have hp := (Fact.out : p.Prime)
  have hEC := inf_centralizer_eq_center_map_of_omega hER hEexp hEZ hz hC
  set ρ : X →* MulAut K := MulAut.conjNormal (H := K) with hρ
  have hker : ρ.ker = Subgroup.centralizer (K : Set X) :=
    CFSG.AGLEmbedding.ker_conjNormal_eq_centralizer K
  have hAel : IsElemAbelian p (E.map ρ) :=
    CFSG.AGLEmbedding.isElemAbelian_map_conjNormal hEexp hEC e
  have hAcard : Nat.card (E.map ρ) = p ^ 2 := CFSG.AGLEmbedding.card_map_conjNormal hEcard hEC e
  obtain ⟨k, hkRK, hkC⟩ := exists_mem_inf_not_mem_centralizer R hZK hKp
  have hSne : ((R : Subgroup X) ⊓ K).map ρ ≠ ⊥ := by
    intro h
    apply hkC
    have hk : ρ k ∈ ((R : Subgroup X) ⊓ K).map ρ := Subgroup.mem_map_of_mem _ hkRK
    rw [h, Subgroup.mem_bot] at hk
    rw [← hker]
    exact hk
  have hSn : (R : Subgroup X).map ρ ≤
      Subgroup.normalizer ((((R : Subgroup X) ⊓ K).map ρ : Subgroup (MulAut K)) :
        Set (MulAut K)) := by
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.le_normalizer_map ρ
      ⟨r, le_normalizer_inf_of_normal_right (R : Subgroup X) K hr, rfl⟩
  obtain ⟨y, hyS, hyp, hyc⟩ := exists_orderOf_eq_prime_commute (R.isPGroup'.map ρ)
    (Subgroup.map_mono inf_le_left) hSn hSne
  obtain ⟨w, ⟨-, hwK⟩, hwy⟩ := Subgroup.mem_map.mp hyS
  have hyp' : y ^ p = 1 := hyp ▸ pow_orderOf_eq_one y
  have hyC : y ∈ Subgroup.centralizer ((E.map ρ : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e₀, he₀, rfl⟩
    exact (hyc _ ⟨e₀, hER he₀, rfl⟩).eq
  refine three_le_pRank_of_card_sq hAel hAcard hyC hyp' ?_
  rintro ⟨e₀, he₀, hρe⟩
  have hmem : w⁻¹ * e₀ ∈ Subgroup.centralizer (K : Set X) := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hwy, hρe, inv_mul_cancel]
  have hC₀ : e₀ ∈ Subgroup.centralizer (K : Set X) := by
    have := hEY ⟨he₀, by simpa using Subgroup.mul_mem_sup hwK hmem⟩
    rw [← hEC] at this
    exact this.2
  have hy1 : y = 1 := by
    rw [← hρe, ← MonoidHom.mem_ker, hker]
    exact hC₀
  rw [hy1, orderOf_one] at hyp
  exact hp.one_lt.ne hyp

end Basic

end CFSG.LocalAnalysis.RankThreeTheoremC
