module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank

open CFSG.Open Subgroup
open scoped Pointwise

theorem isCatalogGroup_of_isKGroup_simple {K : Type} [Group K] [IsSimpleGroup K]
    (hK : CFSG.IsKGroup K) : IsCatalogGroup K :=
  hK.inCatalog_of_surjective ⊤ (Subgroup.topEquiv (G := K)).toMonoidHom
    (Subgroup.topEquiv (G := K)).surjective

theorem exists_sylow_map_eq_of_pow_eq_one {K : Type} [Group K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] (φ : MulAut K) {n : ℕ} (hφ : φ ^ (p ^ n) = 1) :
    ∃ P : Sylow p K, ∀ g : K, g ∈ (P : Subgroup K) → φ g ∈ (P : Subgroup K) := by
  classical
  let H : Subgroup (MulAut K) := Subgroup.zpowers φ
  have hH : IsPGroup p H := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφ, one_zpow]
  have h1 := hH.card_modEq_card_fixedPoints (Sylow p K)
  have h2 := card_sylow_modEq_one p K
  have h3 : Nat.card (MulAction.fixedPoints H (Sylow p K)) ≡ 1 [MOD p] := h1.symm.trans h2
  have hne : (MulAction.fixedPoints H (Sylow p K)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at h3
    have h0 : Nat.card (↥(∅ : Set (Sylow p K))) = 0 := by simp
    rw [h0] at h3
    have h4 : (0 : ℕ) = 1 := by
      unfold Nat.ModEq at h3
      rwa [Nat.zero_mod, Nat.mod_eq_of_lt hp.out.one_lt] at h3
    exact absurd h4 (by norm_num)
  obtain ⟨P, hP⟩ := hne
  refine ⟨P, fun g hg => ?_⟩
  have hφH : φ ∈ H := Subgroup.mem_zpowers φ
  have hfix : (⟨φ, hφH⟩ : H) • P = P := hP ⟨φ, hφH⟩
  have h6 : (⟨φ, hφH⟩ : H) • g ∈ (⟨φ, hφH⟩ : H) • (P : Subgroup K) :=
    Subgroup.smul_mem_pointwise_smul g _ _ hg
  have h5 : ((⟨φ, hφH⟩ : H) • (P : Subgroup K) : Subgroup K) = (P : Subgroup K) := by
    have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hfix
    simpa [Sylow.pointwise_smul_def] using this
  rw [h5] at h6
  exact h6

theorem map_eq_self_of_pow_eq_one_of_card_three {K : Type} [Group K] [Finite K] {P : Subgroup K}
    (hP : Nat.card P = 3) (φ : MulAut K) {n : ℕ} (hφ : φ ^ (3 ^ n) = 1)
    (hmap : ∀ g : K, g ∈ P → φ g ∈ P) : ∀ g ∈ P, φ g = g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg
  by_cases hg1 : g = 1
  · subst hg1
    simp
  have hg3 : g ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨g, hg⟩)
    rw [hP] at h
    exact congrArg Subtype.val h
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hzp : Subgroup.zpowers g = P := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hg)
    rw [hP, Nat.card_zpowers, hord]
  have hφgP : φ g ∈ Subgroup.zpowers g := hzp ▸ hmap g hg
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hφgP
  have hφg1 : φ g ≠ 1 := fun h => hg1 (φ.injective (by rw [h, map_one]))
  have hjmod : g ^ (j % 3) = φ g := by
    rw [← hj]
    have := zpow_mod_orderOf g j
    rw [hord] at this
    simpa using this
  have hr0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
  have hr3 : j % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcase : φ g = g ∨ φ g = g⁻¹ := by
    generalize j % 3 = r at hjmod hr0 hr3
    interval_cases r
    · exact absurd (by simpa using hjmod.symm) hφg1
    · left; simpa using hjmod.symm
    · right
      have : g ^ (2 : ℤ) = g⁻¹ := by
        have : g ^ (2 : ℤ) * g = 1 := by
          rw [← zpow_add_one]
          simpa using hg3
        exact eq_inv_of_mul_eq_one_left this
      rw [← hjmod, this]
  rcases hcase with h | h
  · exact h
  · exfalso
    have h2 : (φ ^ 2) g = g := by
      rw [pow_two, MulAut.mul_apply, h, map_inv, h, inv_inv]
    have h2m : ∀ m : ℕ, ((φ ^ 2) ^ m) g = g := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, h2]
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have hφn : (φ ^ (3 ^ n)) g = g⁻¹ := by
      rw [hm, pow_succ, pow_mul, MulAut.mul_apply, h, map_inv, h2m]
    rw [hφ, MulAut.one_apply] at hφn
    have hsq : g ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hφn
    apply hg1
    calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg3, hsq]; simp

theorem kFactOutThreePrimeSimple_of_innerAction (hIA : KFactInnerAction) :
    KFactOutThreePrimeSimple := by
  intro K _ _ hK hs hnab ⟨P₀, hP₀, hP₀idx⟩ φ ⟨n, hφ⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_of_pow_eq_one (p := 3) φ hφ
  have hP₀pg : IsPGroup 3 P₀ := IsPGroup.of_card (n := 1) (by rw [hP₀, pow_one])
  let P₀' : Sylow 3 K := hP₀pg.toSylow hP₀idx
  have hcard₀ : Nat.card (P₀' : Subgroup K) = 3 := by
    have : (P₀' : Subgroup K) = P₀ := IsPGroup.toSylow_coe hP₀pg hP₀idx
    rw [this, hP₀]
  have hcard : Nat.card (P : Subgroup K) = 3 := by
    rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity P₀', hcard₀]
  have hfix : ∀ g ∈ (P : Subgroup K), φ g = g :=
    map_eq_self_of_pow_eq_one_of_card_three hcard φ hφ hP
  haveI : IsCyclic (P : Subgroup K) := isCyclic_of_prime_card (p := 3) hcard
  have hne : (P : Subgroup K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hcomm : IsMulCommutative (P : Subgroup K) := inferInstance
  obtain ⟨g, -, hg⟩ := hIA 3 Nat.prime_three (by norm_num) K hs hnab
    (isCatalogGroup_of_isKGroup_simple hK) P hne hcomm φ ⟨n, hφ⟩ (by
      intro g hg
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix g hg])
  exact ⟨g, hg⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank
