module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExDef
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Universal.Unitary

section Generic

variable {p : ℕ} [hp : Fact p.Prime] {S : Type} [Group S] [Finite S]

theorem pRank_top_le_of_sylow_card (P : Sylow p S) {k : ℕ}
    (hP : Nat.card (P : Subgroup S) = p ^ k) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ k := by
  rw [← (CFSG.SectionRank.pRank_sylow P).1]
  refine CFSG.SectionRank.pRank_le hp.out.one_lt fun E hE _ => ?_
  calc Nat.card E ≤ Nat.card (P : Subgroup S) := Subgroup.card_le_of_le hE
    _ = p ^ k := hP

theorem pRank_top_le_of_nonab {G : Type} [Group G] [Finite G] (π : G →* S)
    (hπ : Function.Surjective π) {U : Subgroup G} (hU : IsPGroup p U) (hidx : ¬ p ∣ U.index)
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) {k : ℕ} (hcard : Nat.card U = p ^ (k + 1)) {u v : G}
    (hu : u ∈ U) (hv : v ∈ U) (huv : u * v ≠ v * u) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ k := by
  have hp1 := hp.out.one_lt
  set P₀ : Sylow p S := (hU.toSylow hidx).mapSurjective hπ with hP₀
  have hP₀coe : (P₀ : Subgroup S) = U.map π := by
    rw [hP₀, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  have hcP : Nat.card (P₀ : Subgroup S) = p ^ (k + 1) := by
    rw [hP₀coe, card_map_eq_of_injOn_subgroup π hinj, hcard]
  rw [← (CFSG.SectionRank.pRank_sylow P₀).1]
  refine CFSG.SectionRank.pRank_le hp1 fun E hE hEa => ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card E = p ^ m :=
    IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by simpa using hEa.2 g g.2)⟩
  have hle : Nat.card E ≤ p ^ (k + 1) := hcP ▸ Subgroup.card_le_of_le hE
  by_cases hm3 : m = k + 1
  · exfalso
    have hEP : E = (P₀ : Subgroup S) :=
      Subgroup.eq_of_le_of_card_ge hE (by rw [hcP, hm, hm3])
    apply huv
    have hπuv : π u * π v = π v * π u := by
      have h1 : π u ∈ (P₀ : Subgroup S) := by rw [hP₀coe]; exact Subgroup.mem_map_of_mem _ hu
      have h2 : π v ∈ (P₀ : Subgroup S) := by rw [hP₀coe]; exact Subgroup.mem_map_of_mem _ hv
      rw [← hEP] at h1 h2
      have := hEa.1.is_comm.comm ⟨π u, h1⟩ ⟨π v, h2⟩
      simpa using congrArg Subtype.val this
    have hq : π (u * v) = π (v * u) := by rw [map_mul, map_mul, hπuv]
    have hmem : (v * u)⁻¹ * (u * v) ∈ U := mul_mem (inv_mem (mul_mem hv hu)) (mul_mem hu hv)
    have h1 : (v * u)⁻¹ * (u * v) = 1 :=
      hinj _ hmem (by rw [map_mul, map_inv, ← hq, map_mul]; simp)
    exact (inv_mul_eq_one.mp h1).symm
  · have hm2 : m ≤ k := by
      by_contra h
      have h3 : k + 1 ≤ m := by omega
      have : p ^ (k + 1) ≤ p ^ m := Nat.pow_le_pow_right hp1.le h3
      have hm' : p ^ m ≤ p ^ (k + 1) := hm ▸ hle
      have : p ^ m = p ^ (k + 1) := le_antisymm hm' this
      exact hm3 ((Nat.pow_right_injective hp1) this)
    rw [hm]
    exact Nat.pow_le_pow_right hp1.le hm2

theorem pRank_top_le_two_of_heis_nonab {G : Type} [Group G] [Finite G] (π : G →* S)
    (hπ : Function.Surjective π) {U : Subgroup G} (hU : IsPGroup p U) (hidx : ¬ p ∣ U.index)
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) (hcard : Nat.card U = p ^ 3) {u v : G} (hu : u ∈ U)
    (hv : v ∈ U) (huv : u * v ≠ v * u) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 :=
  pRank_top_le_of_nonab π hπ hU hidx hinj (k := 2) hcard hu hv huv

end Generic

section L3

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem pRank_le_two_statedSL_three_prime (hK : Nat.card K = p) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSL 3 K)) : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 := by
  have hK1 : Nat.card K = p ^ 1 := by rw [hK, pow_one]
  haveI : CharP K p := charP_of_card_eq_prime_pow (le_refl 1) hK1
  let φ := specialLinearGroupEquivStatedSL 3 K
  let π : Matrix.SpecialLinearGroup (Fin 3) K →* S :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSL 3 K))).comp φ.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp φ.surjective)
  have hU : IsPGroup p (Usl K) := isPGroup_Usl hK1
  have hidx : ¬ p ∣ (Usl K).index := not_dvd_index_Usl hK1 le_rfl
  have hinj : ∀ u ∈ Usl K, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    refine φ.injective ?_
    rw [map_one]
    refine eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 ?_
    exact e.symm.injective (hπu.trans (map_one e.symm).symm)
  have hcard : Nat.card (Usl K) = p ^ 3 := by rw [card_Usl, hK]
  have hne : uSL (1 : K) 0 0 * uSL 0 0 1 ≠ uSL 0 0 1 * uSL (1 : K) 0 0 := by
    intro h
    rw [uSL_mul, uSL_mul] at h
    have := (uSL_injective h).2.1
    simp at this
  exact pRank_top_le_two_of_heis_nonab π hπ hU hidx hinj hcard (uSL_mem_Usl _ _ _)
    (uSL_mem_Usl _ _ _) hne

variable {f : ℕ}

theorem three_le_pRank_centralizer_of_statedSL_three_of_three_le (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {S : Type} [Group S] [Finite S] (e : S ≃* StatedProj (StatedSL 3 K))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    have := pRank_le_two_statedSL_three_prime (by rw [hK, pow_one]) e
    omega
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  let φ := specialLinearGroupEquivStatedSL 3 K
  let π : Matrix.SpecialLinearGroup (Fin 3) K →* StatedProj (StatedSL 3 K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))).comp φ.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hU : IsPGroup p (Usl K) := isPGroup_Usl hK
  have hidx : ¬ p ∣ (Usl K).index := not_dvd_index_Usl hK hf
  have hinj : ∀ u ∈ Usl K, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    exact φ.injective (by
      rw [map_one]
      exact eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 hπu)
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  have hZ : p ^ 2 ≤ Nat.card (Zsl K) := by
    rw [card_Zsl_eq, hK]
    exact Nat.pow_le_pow_right hp.out.pos hf2
  have hZc : ∀ z ∈ Zsl K, ∀ u ∈ Usl K, z * u = u * z := by
    rintro _ ⟨β, rfl⟩ _ ⟨a, b, c, rfl⟩
    rw [uSL_mul, uSL_mul]
    congr 1 <;> ring
  have hZexp : ∀ z ∈ Zsl K, z ^ p = 1 := by
    rintro _ ⟨β, rfl⟩
    rw [uSL_zero_pow, CharP.cast_eq_zero, zero_mul, uSL_zero]
  have key := three_le_pRank_centralizer_of_heis π hπ hU hidx Zsl_le_Usl hZc hZexp hZ hinj
    h3' (x := e x) (by rw [← map_pow, hx, map_one])
  exact key.trans (pRank_centralizer_le_of_mulEquiv hp1 e x)


end L3


section U3

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]

theorem pRank_le_two_statedSU_three_prime (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ 1) ^ 2)
    {S : Type} [Group S] [Finite S] (e : S ≃* StatedProj (StatedSU 3 (p ^ 1) K)) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2 := by
  haveI : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * 1) (by omega) (by rw [hK, pow_mul'])
  have H : SUInv (CFSG.LieType.BorelTits.unitaryInvolution K p 1) := suInv_unitary hK hp2
  let φ := equivStatedSU hK 3
  let π : SU (CFSG.LieType.BorelTits.unitaryInvolution K p 1) 3 →* S :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ 1) K))).comp φ.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp φ.surjective)
  have hU : IsPGroup p (Usu H) := isPGroup_Usu hK H
  have hidx : ¬ p ∣ (Usu H).index := not_dvd_index_Usu hK le_rfl H
  have hinj : ∀ u ∈ Usu H, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    refine φ.injective ?_
    rw [map_one]
    refine eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 ?_
    exact e.symm.injective (hπu.trans (map_one e.symm).symm)
  have hcard : Nat.card (Usu H) = p ^ 3 := by rw [card_Usu_unitary hK H, pow_one]
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hσζ : CFSG.LieType.BorelTits.unitaryInvolution K p 1 (ζ : K) = -ζ := by
    have := ζ.2
    rw [mem_traceZero] at this
    linear_combination this
  have hne : xSU H 1 * xSU H (ζ : K) ≠ xSU H (ζ : K) * xSU H 1 := by
    intro h
    rw [xSU_mul, xSU_mul, add_comm (ζ : K) 1] at h
    have h' := congrArg Subtype.val (xSU_mul_zSU_injective H h).2
    simp only [coe_gamSU, map_one, hσζ] at h'
    have h2 := H.two_ne_zero
    apply hζ
    have h6 := (div_left_inj' h2).mp h'
    have h4 : (2 : K) * 2 * (ζ : K) = 0 := by linear_combination h6
    exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero h2 h2)
  exact pRank_top_le_two_of_heis_nonab π hπ hU hidx hinj hcard (xSU_mem_Usu H _)
    (xSU_mem_Usu H _) hne

theorem three_le_pRank_centralizer_of_statedSU_three_of_three_le (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    have := pRank_le_two_statedSU_three_prime hp2 hK e
    omega
  haveI : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by omega) (by rw [hK, pow_mul'])
  have H : SUInv (CFSG.LieType.BorelTits.unitaryInvolution K p f) := suInv_unitary hK hp2
  let φ := equivStatedSU hK 3
  let π : SU (CFSG.LieType.BorelTits.unitaryInvolution K p f) 3 →*
      StatedProj (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))).comp
      φ.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hU : IsPGroup p (Usu H) := isPGroup_Usu hK H
  have hidx : ¬ p ∣ (Usu H).index := not_dvd_index_Usu hK hf H
  have hinj : ∀ u ∈ Usu H, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    exact φ.injective (by
      rw [map_one]
      exact eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 hπu)
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))) := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  have hZ : p ^ 2 ≤ Nat.card (Zsu H) := by
    rw [card_Zsu_eq, CFSG.LieType.Steinberg.card_traceZero hK]
    exact Nat.pow_le_pow_right hp.out.pos hf2
  have hZc : ∀ z ∈ Zsu H, ∀ u ∈ Usu H, z * u = u * z := by
    rintro _ ⟨β, rfl⟩ u hu
    have := zSU_comm_of_mem_Usu H hu β
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hZexp : ∀ z ∈ Zsu H, z ^ p = 1 := by
    rintro _ ⟨β, rfl⟩
    have hβ : p • β = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul]
    rw [zSU_pow, hβ, zSU_zero]
  have key := three_le_pRank_centralizer_of_heis π hπ hU hidx (Zsu_le_Usu H) hZc hZexp hZ hinj
    h3' (x := e x) (by rw [← map_pow, hx, map_one])
  exact key.trans (pRank_centralizer_le_of_mulEquiv hp1 e x)


end U3


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
