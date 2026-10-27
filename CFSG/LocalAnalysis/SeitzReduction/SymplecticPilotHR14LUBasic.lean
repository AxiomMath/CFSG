module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphBasic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor)

section Fixed

variable {G : Type} [Group G]

theorem normalizerMonoidHom_mul_self {M : Subgroup G} {w : G} (hw : w * w = 1)
    (hN : w ∈ normalizer (M : Set G)) :
    M.normalizerMonoidHom ⟨w, hN⟩ * M.normalizerMonoidHom ⟨w, hN⟩ = 1 := by
  rw [← map_mul, show (⟨w, hN⟩ : normalizer (M : Set G)) * ⟨w, hN⟩ = 1 from Subtype.ext hw,
    map_one]

theorem mul_self_inv_conj_eq_one {t : G} (htt : t * t = 1) (g : G) :
    (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
  calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [htt]; group

theorem map_fixedSubgroup_conj_le_centralizer {M : Subgroup G} {t g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (M : Set G)) :
    (fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)).map
        ((MulAut.conj g).toMonoidHom.comp M.subtype) ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * t * g) * (x : G) * (g⁻¹ * t * g)⁻¹ = x := by
    have h := congrArg Subtype.val
      (show M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ x = x from hx)
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * (x : G) * g⁻¹ * t =
      g * ((g⁻¹ * t * g) * (x : G) * (g⁻¹ * t * g)⁻¹) * g⁻¹ * t := by rw [h1]
    _ = t * (g * (x : G) * g⁻¹) := by group

theorem card_map_fixedSubgroup_conj {M : Subgroup G} {t g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (M : Set G)) :
    Nat.card ((fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)).map
        ((MulAut.conj g).toMonoidHom.comp M.subtype)) =
      Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) :=
  Subgroup.card_map_of_injective ((MulAut.conj g).injective.comp M.subtype_injective)

theorem exists_mulAut_mul_eq_of_congr {X P : Type*} [Group X] [Group P] (ε : X ≃* P)
    {θ θ' : MulAut X} {γ : MulAut P} (h : γ * MulAut.congr ε θ = MulAut.congr ε θ' * γ) :
    ∃ β : MulAut X, β * θ = θ' * β := by
  refine ⟨(MulAut.congr ε).symm γ, (MulAut.congr ε).injective ?_⟩
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]

theorem symm_trans_mul_congr {X Y : Type*} [Group X] [Group Y] (θ₁ θ₂ : Y ≃* X)
    (β : MulAut Y) :
    (θ₁.symm.trans θ₂ : MulAut X) * MulAut.congr θ₁ β = MulAut.congr θ₂ β * θ₁.symm.trans θ₂ := by
  ext x
  simp [MulAut.congr_apply]

theorem normalizerMonoidHom_one_conj {M : Subgroup G} {t : G} (htM : t ∈ normalizer (M : Set G)) :
    ∃ hg : (1 : G)⁻¹ * t * 1 ∈ normalizer (M : Set G),
      M.normalizerMonoidHom ⟨(1 : G)⁻¹ * t * 1, hg⟩ = M.normalizerMonoidHom ⟨t, htM⟩ := by
  have he : (1 : G)⁻¹ * t * 1 = t := by group
  have hg : (1 : G)⁻¹ * t * 1 ∈ normalizer (M : Set G) := by rw [he]; exact htM
  refine ⟨hg, ?_⟩
  have hs : (⟨(1 : G)⁻¹ * t * 1, hg⟩ : normalizer (M : Set G)) = ⟨t, htM⟩ := Subtype.ext he
  rw [hs]

end Fixed

section Orders

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem card_fixedSubgroup_conj_dvd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (M : Set G)) :
    Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
  have : NeZero n := ⟨by omega⟩
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hKc
  have h1 := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer hset.2.2.2.1
    (e.trans (F4Pilot.spProjEquiv n K)) ht hKt (map_fixedSubgroup_conj_le_centralizer hg)
  rw [card_map_fixedSubgroup_conj] at h1
  have h2 := E6Pilot.card_mulAut_dvd_card_mul_card_outer (StatedProj (StatedSp n K))
  have h3 := (SymplecticHigher.outer_card_dvd Nat.prime_two hf hKc (by omega)).2 hn
  rw [gcd_two_two_pow_sub_one hf, mul_one] at h3
  have hP : Nat.card (StatedProj (StatedSp n K)) = Nat.card (StatedSp n K) :=
    (Nat.card_congr (F4Pilot.spProjEquiv n K).toEquiv).symm
  rw [← hP]
  exact h1.trans (Nat.mul_dvd_mul_left 2 (h2.trans (Nat.mul_dvd_mul_left _ h3)))

theorem factorization_card_fixedSubgroup_conj_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (M : Set G)) :
    (Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))).factorization 2 ≤
      f * n ^ 2 + 1 + f.factorization 2 := by
  have h := factorization_card_le_of_le_centralizer_sp hset.2.2.2.1 hn hKc e ht hKt
    (map_fixedSubgroup_conj_le_centralizer hg)
  rwa [card_map_fixedSubgroup_conj] at h

omit [Finite K] in
theorem card_fixedSubgroup_dvd_of_mem (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (htM : t ∈ normalizer (M : Set G)) :
    Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨t, htM⟩)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
  obtain ⟨hg, he⟩ := normalizerMonoidHom_one_conj htM
  rw [← he]
  exact card_fixedSubgroup_conj_dvd hset hn hKc e ht hKt hg

theorem factorization_card_fixedSubgroup_le_of_mem (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (htM : t ∈ normalizer (M : Set G)) :
    (Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨t, htM⟩))).factorization 2 ≤
      f * n ^ 2 + 1 + f.factorization 2 := by
  obtain ⟨hg, he⟩ := normalizerMonoidHom_one_conj htM
  rw [← he]
  exact factorization_card_fixedSubgroup_conj_le hset hn hKc e ht hKt hg

end Orders

section PPD

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_two_mul_card_statedSp_mul_of_ppd {n f : ℕ} (hf : 1 ≤ f)
    (hKc : Nat.card K = 2 ^ f) {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hfk : f < k)
    (hk : ∀ i, 1 ≤ i → i ≤ n → ¬ k ∣ 2 * f * i) :
    ¬ p ∣ 2 * (Nat.card (StatedSp n K) * f) := by
  intro hdvd
  have hk0 : 0 < k := by omega
  have hpk := LinearPilot.index_lt_of_isPrimitivePrimeDivisor hp hk0
  have hpr := hp.prime
  have hp2 : ¬ p ∣ 2 := fun h =>
    hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h)
  have hpf : ¬ p ∣ f := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hpow : ¬ p ∣ (2 ^ f) ^ (n ^ 2) := fun h => by
    rw [← pow_mul] at h
    exact hp2 (hpr.dvd_of_dvd_pow h)
  have hprod : ¬ p ∣ ∏ j ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * j) - 1) := by
    rw [Prime.dvd_finsetProd_iff hpr.prime]
    rintro ⟨j, hj, hpj⟩
    rw [← pow_mul] at hpj
    have hj' := Finset.mem_Icc.1 hj
    have h1 := (hp.dvd_sub_one_iff hk0 (f * (2 * j))).1 hpj
    exact hk j hj'.1 hj'.2 (by rw [show 2 * f * j = f * (2 * j) by ring]; exact h1)
  rw [SymplecticFlag.card_statedSp, hKc] at hdvd
  rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
  · exact hp2 h
  rcases (Nat.Prime.dvd_mul hpr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hpr).1 h with h | h
    · exact hpow h
    · exact hprod h
  · exact hpf h

end PPD

end CFSG.SeitzReduction.SymplecticPilot
