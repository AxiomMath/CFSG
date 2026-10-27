module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRepCentral
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_kline_three_cyc (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hp3 : p = 3) (hR3 : IsPGroup 3 R)
    (hZ3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ζ ^ 3 = 1 → ζ = 1)
    {z w : G} (hzR : z ∈ R) (hzo : orderOf z = 3)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    (hRz : ∀ y ∈ R, y * z = z * y) (hwR : w ∈ R) (hwo : orderOf w = 3)
    (hRw : ∀ y ∈ R, y * w = w * y) (hwz : w ∉ Subgroup.zpowers z)
    (hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z)
    (hrk : ∀ E : Subgroup G, E ≤ R → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hfus : ∀ i : ℕ, ∃ n ∈ M, n * z * n⁻¹ = z * w ^ i)
    (hinv : ∃ s ∈ M, s * z * s⁻¹ = z ∧ s * w * s⁻¹ = w⁻¹)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      mbar M z (h.le_M hzR) ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hE : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      mbar M z (h.le_M hzR) ∈ barM M L → ∀ v ∈ barM M L, v ^ 3 = 1 →
        v * mbar M z (h.le_M hzR) = mbar M z (h.le_M hzR) * v →
        v ∈ Subgroup.zpowers (mbar M z (h.le_M hzR))) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hRM : R ≤ M := h.le_M
  set S := pCoreOf 2 H with hS
  have hzM : z ∈ M := hRM hzR
  set zb := mbar M z hzM with hzb
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by rw [hzb, ← mbar_pow, ← mbar_one]; congr 1
  have hnC : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨L₀, hL₀⟩ := h.exists_weakSBlock h84 hD2
  obtain ⟨L', hL', r, hrR, hrM, hrL, hrc⟩ := exists_rep_mem_R hzM hz3 hCz hsyl hL₀ (hin L₀ hL₀)
  obtain ⟨hr3, hrc'⟩ := D1PhaseThree.rep_central h hR3 hZ3 hzR hz3 hRz hwR hw3 hRw hwz hrk
    hnC hL' hrR hrL hrc
  have hrΩ := hΩ r hrR hrc' hr3
  have hwzc : Commute w z := hRz w hwR
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, r = w ^ a * z ^ b := by
    have hN : Subgroup.zpowers w ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hwzc.zpow_right n).eq.symm
    have hr' : r ∈ (Subgroup.zpowers w : Set G) * (Subgroup.zpowers z : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]; exact hrΩ
    obtain ⟨x, hx, y, hy, hxy⟩ := hr'
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨a, b, hxy.symm⟩
  obtain ⟨s, hsM, hsz, hsw⟩ := hinv
  by_cases hb : b % 3 = 0
  ·
    have hzb' : z ^ b = 1 := by
      rw [← zpow_mod_three hzo, hb, zpow_zero]
    have hrw : r = w ^ a := by rw [hab, hzb', mul_one]
    exact h.false_of_rep_inv hp hp2 hzM hz hCz hL' hrM hr3 hrL hrc hsM hsz (by
      rw [hrw, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsw, inv_zpow])
  obtain ⟨i, hi⟩ := exists_mul_pow_mem_zpowers hwo hzo hwzc hab hb
  obtain ⟨n, hnM, hnz⟩ := hfus i
  set L₁ := L' with hL₁
  have hzL₁ : zb ∈ barM M L₁ := by
    have hA : IsComponentOf (barM M (L'.map (MulAut.conj n⁻¹).toMonoidHom)) ⊤ :=
      (hL'.toIsTwoPrimeComponent.map_conj (M.inv_mem hnM)).component
    have hzA : zb ∈ barM M (L'.map (MulAut.conj n⁻¹).toMonoidHom) := by
      rw [barM_map_conj (M.inv_mem hnM) L']
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hi
      have hzr : n * z * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hzM) (M.inv_mem hnM)
      refine ⟨mbar M (n * z * n⁻¹) hzr, ?_, ?_⟩
      · have e : mbar M (n * z * n⁻¹) hzr = (mbar M r hrM) ^ k := by
          rw [← mbar_zpow hrM k]
          congr 1
          rw [hnz, ← hk]
        rw [e]
        exact Subgroup.zpow_mem _ hrL k
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzb, mbar]
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (by simp [mul_assoc])
    have := h.barM_eq_of_mem_component hp hp2 hzM hz hCz hA hzA hL'
    rw [hL₁, this]
    exact hzA
  have huniq : ∀ L : Subgroup G, IsWeakSBlock M S L → barM M L = barM M L₁ := by
    intro L hL
    have hA : IsComponentOf (barM M L₁) ⊤ := hL'.component
    rw [h.barM_eq_of_mem_component hp hp2 hzM hz hCz hA hzL₁ hL]
  have hKN : ∀ (g : G) (hgM : g ∈ M), g ∈ Subgroup.normalizer (S : Set G) →
      mbar M g hgM ∈ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgM hgS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (barM M L₁).map (MulAut.conj (mbar M g hgM)).toMonoidHom = barM M L₁
    rw [← barM_map_conj hgM L₁]
    exact huniq _ (hL'.map_conj hgM hgS)
  have hwL₁ : mbar M w (hRM hwR) ∈ barM M L₁ := by
    obtain ⟨x, hxM, hxz⟩ := hfus 1
    rw [pow_one] at hxz
    have hzw : z * w ∈ M := M.mul_mem hzM (hRM hwR)
    have hzwb : mbar M (z * w) hzw ∈ barM M (L₁.map (MulAut.conj x).toMonoidHom) := by
      rw [barM_map_conj hxM L₁]
      refine ⟨zb, hzL₁, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hzb, ← mbar_conj hzM hxM]
      congr 1
    by_cases hB : barM M (L₁.map (MulAut.conj x).toMonoidHom) = barM M L₁
    · rw [hB] at hzwb
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzL₁) hzwb
      rw [← mbar_inv hzM, ← mbar_mul (M.inv_mem hzM) hzw] at this
      convert this using 2
      group
    · exfalso
      have hc1 : mbar M (z * w) hzw ∈ Subgroup.centralizer (barM M L₁ : Set _) :=
        le_centralizer_of_component_ne (hL'.toIsTwoPrimeComponent.map_conj hxM).component
          hL'.component hB hzwb
      have hsC : s ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc s * z = s * z * s⁻¹ * s := by group
            _ = z * s := by rw [hsz])
      have hsS : s ∈ Subgroup.normalizer (S : Set G) :=
        localGroup_le_normalizer_pCoreOf 2 H (hCz hsC)
      have hsN := hKN s hsM hsS
      have hc2 : mbar M s hsM * mbar M (z * w) hzw * (mbar M s hsM)⁻¹ ∈
          Subgroup.centralizer (barM M L₁ : Set _) := by
        have h1 := conj_mem_centralizer_map (g := mbar M s hsM) hc1
        have h2 : (barM M L₁).map (MulAut.conj (mbar M s hsM)).toMonoidHom = barM M L₁ := by
          rw [← barM_map_conj hsM L₁]
          exact huniq _ (hL'.map_conj hsM hsS)
        rwa [h2] at h1
      have hzw' : mbar M s hsM * mbar M (z * w) hzw * (mbar M s hsM)⁻¹ =
          mbar M (z * w⁻¹) (M.mul_mem hzM (M.inv_mem (hRM hwR))) := by
        rw [← mbar_conj hzw hsM]
        congr 1
        calc s * (z * w) * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by group
          _ = z * w⁻¹ := by rw [hsz, hsw]
      rw [hzw'] at hc2
      have hz2 := Subgroup.mul_mem _ hc1 hc2
      rw [← mbar_mul hzw (M.mul_mem hzM (M.inv_mem (hRM hwR)))] at hz2
      have e : z * w * (z * w⁻¹) = z ^ 2 := by
        calc z * w * (z * w⁻¹) = z * (w * z) * w⁻¹ := by group
          _ = z * (z * w) * w⁻¹ := by rw [hwzc.eq]
          _ = z ^ 2 := by rw [pow_two]; group
      have hz2' : mbar M (z ^ 2) (M.pow_mem hzM 2) ∈ Subgroup.centralizer (barM M L₁ : Set _) := by
        convert hz2 using 2
        exact e.symm
      have hz4 := Subgroup.mul_mem _ hz2' hz2'
      rw [← mbar_mul (M.pow_mem hzM 2) (M.pow_mem hzM 2)] at hz4
      apply hnC L₁ hL'
      convert hz4 using 2
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul, pow_one]
  have hwz' := hE L₁ hL' hzL₁ (mbar M w (hRM hwR)) hwL₁
    (by rw [← mbar_pow, ← mbar_one]; congr 1)
    (by rw [hzb, ← mbar_mul, ← mbar_mul]; congr 1)
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hwz'
  apply hwz
  have hzc : z ^ c ∈ R := R.zpow_mem hzR c
  have heq : mbar M (z ^ c) (hRM hzc) = mbar M w (hRM hwR) := by
    rw [mbar_zpow hzM c]; exact hc
  rw [← eq_of_mbar_eq_p hp hp2 hRM hR3 hzc hwR heq]
  exact Subgroup.zpow_mem_zpowers z c

end CFSG.AGLEmbedding
