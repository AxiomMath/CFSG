module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBlockFacts
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRepCentral
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBCenter
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique
import CFSG.LocalAnalysis.AGLEmbedding.Sp48OrbitOne
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_kline_three (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hKA : CitedBlockToralThreeAut) (hp3 : p = 3) (hR3 : IsPGroup 3 R)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
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
    (hR27 : 3 ^ 3 ≤ Nat.card R)
    (hfus : ∀ i : ℕ, ∃ n ∈ M, n * z * n⁻¹ = z * w ^ i)
    (hinv : ∃ s ∈ M, s * z * s⁻¹ = z ∧ s * w * s⁻¹ = w⁻¹) : False := by
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
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hperf' : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y) := fun Y hY hYp => hperf Y (hKeq ▸ hY) hYp
  have hnC : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  have hzN : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    mem_normalizer_barM hzM (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hz hz3
      hCz hL)
  have hfix : ∀ L : Subgroup G, ∀ l ∈ barM M L, zb * l * zb⁻¹ = l →
      l ∈ blockPL M S L := fun L l hl hl' =>
    h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz l hl hl'
  have hin : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL => (hK G M S L h.isKGroup.1 h.asc81bHyp hL (h.nineThree h93 hL)
      (h.nineThree_not_one h85 hD2 hL).1 (h.not_isSylowTwoOf_inf h85 hD2 hL) hperf' zb
      (hzN L hL) hzb3 (hnC L hL) (hfix L)).1
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
  set X := barM M R with hX
  have hXp : IsPGroup 3 X := (hR3.comap_subtype (K := M)).map _
  have hXN : X ≤ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    have hgR : g ∈ R := Subgroup.mem_subgroupOf.mp hg
    exact hKN g hgM (localGroup_le_normalizer_pCoreOf 2 H (h.le_H hgR))
  have hXC : X ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    have hgR : g ∈ R := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    show mbar M g hgM * mbar M z hzM = mbar M z hzM * mbar M g hgM
    rw [← mbar_mul, ← mbar_mul]
    congr 1
    exact hRz g hgR
  have hXinf : X ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
    by_contra hne
    have hNi : X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer
        (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) : Set _) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer
          (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
        mem_normalizer_centralizer (hXN hx)
      constructor
      · rintro ⟨hyX, hyC⟩
        exact ⟨X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx),
          (Subgroup.mem_normalizer_iff.mp hxC y).mp hyC⟩
      · rintro ⟨hyX, hyC⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxC y).mpr hyC⟩
        have := X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx
        simpa [mul_assoc] using this
    obtain ⟨c, ⟨hcX, hcC⟩, hcZ, hco⟩ :=
      exists_mem_inf_centralizer_orderOf_eq hXp inf_le_left hNi hne
    obtain ⟨⟨g, hgM⟩, hg, rfl⟩ := hcX
    have hgR : g ∈ R := Subgroup.mem_subgroupOf.mp hg
    change orderOf (mbar M g hgM) = 3 at hco
    have hgc : ∀ y ∈ R, y * g = g * y := by
      intro y hy
      refine commute_of_mbar_p hp hp2 hRM hR3 hy hgR ?_
      exact (Subgroup.mem_centralizer_iff.mp hcZ (mbar M y (hRM hy))
        ⟨⟨y, hRM hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    have hcb3 : mbar M g hgM ^ 3 = 1 := by
      rw [← hco]; exact pow_orderOf_eq_one _
    have hg3 : g ^ 3 = 1 := eq_of_mbar_eq_p hp hp2 hRM hR3 (R.pow_mem hgR 3) R.one_mem (by
      rw [mbar_pow (hRM hgR) 3, mbar_one]; exact hcb3)
    have hgΩ := hΩ g hgR hgc hg3
    have hgL : mbar M g hgM ∈ barM M L₁ := by
      have hle : barM M (Subgroup.zpowers w ⊔ Subgroup.zpowers z) ≤ barM M L₁ := by
        rw [barM_sup ((Subgroup.zpowers_le).mpr (hRM hwR)) ((Subgroup.zpowers_le).mpr hzM),
          barM_zpowers (hRM hwR), barM_zpowers hzM]
        exact sup_le ((Subgroup.zpowers_le).mpr hwL₁) ((Subgroup.zpowers_le).mpr hzL₁)
      exact hle ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hgΩ, rfl⟩
    have h1 := hZ3 L₁ hL' _ hgL hcC hcb3
    have h2 : orderOf (mbar M g hgM) = 1 := by rw [h1]; exact orderOf_one
    omega
  have hcard := hKA G M S L₁ h.isKGroup.1 h.asc81bHyp hL' (h.nineThree h93 hL')
    (h.nineThree_not_one h85 hD2 hL').1 (h.not_isSylowTwoOf_inf h85 hD2 hL') hperf' zb
    (hzN L₁ hL') hzb3 (hnC L₁ hL') (hfix L₁) X hXp hXN hXC hXinf
  rw [hX, card_barM_of_isPGroup hp hp2 hRM hR3] at hcard
  omega

end CFSG.AGLEmbedding
