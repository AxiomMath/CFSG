module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBCenter
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique
import CFSG.LocalAnalysis.AGLEmbedding.Sp48OrbitOne

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_kline_unique (h : D1PhaseThree p P M H R) (hR : IsPGroup p R)
    {Lb : Subgroup G} (hLb : IsWeakSBlock M (pCoreOf 2 H) Lb)
    (huniq : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → barM M L = barM M Lb)
    (hZ : ∀ ζ ∈ barM M Lb, ζ ∈ Subgroup.centralizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ p = 1 → ζ = 1)
    {z w : G} (hzR : z ∈ R) (hzo : orderOf z = p)
    (hbound : ∀ X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup p X →
      X ≤ Subgroup.normalizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      X ≤ Subgroup.centralizer ({mbar M z (h.le_M hzR)} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      X ⊓ Subgroup.centralizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ →
      Nat.card X ≤ p ^ 2)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow p ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    (hin : mbar M z (h.le_M hzR) ∈
      barM M Lb ⊔ Subgroup.centralizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hRz : ∀ y ∈ R, y * z = z * y) (hwR : w ∈ R) (hwo : orderOf w = p)
    (hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z)
    (hR3 : p ^ 3 ≤ Nat.card R)
    (hfus : ∀ i : ℕ, ∃ n ∈ M, n * z * n⁻¹ = z * w ^ i)
    (hinv : ∃ s ∈ M, s * z * s⁻¹ = z ∧ s * w * s⁻¹ ∈ Subgroup.zpowers w ∧ s * w * s⁻¹ ≠ w) :
    False := by
  have hp := h.prime
  have hp2 := h.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hRM : R ≤ M := h.le_M
  set S := pCoreOf 2 H with hS
  set B := barM M Lb with hB
  have hzM : z ∈ M := hRM hzR
  set zb := mbar M z hzM with hzb
  have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hwp : w ^ p = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  have hz : IsPGroup p (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzp)
  have hzbp : zb ^ p = 1 := by rw [hzb, ← mbar_pow, ← mbar_one]; congr 1
  have hnC : zb ∉ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hLb
  have hKN : ∀ (g : G) (hgM : g ∈ M), g ∈ H →
      mbar M g hgM ∈ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgM hgH
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (barM M Lb).map (MulAut.conj (mbar M g hgM)).toMonoidHom = barM M Lb
    rw [← barM_map_conj hgM Lb]
    exact huniq _ (hLb.map_conj hgM (localGroup_le_normalizer_pCoreOf 2 H hgH))
  have hKC : ∀ (g : G) (hgM : g ∈ M), g ∈ H → ∀ c ∈ Subgroup.centralizer (B : Set _),
      mbar M g hgM * c * (mbar M g hgM)⁻¹ ∈ Subgroup.centralizer (B : Set _) := by
    intro g hgM hgH c hc
    have h1 := conj_mem_centralizer_map (g := mbar M g hgM) hc
    have h2 : B.map (MulAut.conj (mbar M g hgM)).toMonoidHom = B := by
      rw [← barM_map_conj hgM Lb]
      exact huniq _ (hLb.map_conj hgM (localGroup_le_normalizer_pCoreOf 2 H hgH))
    rwa [h2] at h1
  obtain ⟨y, hyK, r, hrR, hrM, hrL, hrc⟩ := exists_rep_mem_R_p hp hp2 hzM hzp hsyl hin
  have hyB : barM M (Lb.map (MulAut.conj y).toMonoidHom) = B :=
    huniq _ (hLb.map_conj hyK.1 (localGroup_le_normalizer_pCoreOf 2 H (hCz hyK.2)))
  rw [hyB] at hrL hrc
  set rb := mbar M r hrM with hrb
  have hpelt : ∀ x (hx : x ∈ R), ∃ k : ℕ, (mbar M x (hRM hx)) ^ p ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
    exact ⟨k, by rw [← mbar_pow, ← mbar_one]; congr 1; simpa using congrArg Subtype.val hk⟩
  obtain ⟨k₀, hk₀⟩ := hpelt r hrR
  have hconjrep : ∀ (g : G) (hgM : g ∈ M), g ∈ H → g * z * g⁻¹ = z →
      g * r * g⁻¹ ∈ R → g * r * g⁻¹ = r := by
    intro g hgM hgH hgz hgr
    have hgb := hKN g hgM hgH
    have hmem : mbar M g hgM * rb * (mbar M g hgM)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hgb rb).mp hrL
    have hgzb : mbar M g hgM * zb * (mbar M g hgM)⁻¹ = zb := by
      rw [hzb, ← mbar_conj hzM hgM]; congr 1
    have hc : (mbar M g hgM * rb * (mbar M g hgM)⁻¹)⁻¹ * zb ∈
        Subgroup.centralizer (B : Set _) := by
      have e : (mbar M g hgM * rb * (mbar M g hgM)⁻¹)⁻¹ * zb =
          mbar M g hgM * (rb⁻¹ * zb) * (mbar M g hgM)⁻¹ := by
        conv_lhs => rw [← hgzb]
        group
      rw [e]; exact hKC g hgM hgH _ hrc
    obtain ⟨k₁, hk₁⟩ := hpelt _ hgr
    have hk₁' : (mbar M g hgM * rb * (mbar M g hgM)⁻¹) ^ p ^ k₁ = 1 := by
      rw [hrb, ← mbar_conj hrM hgM]; exact hk₁
    have heq := rep_unique_p hZ hmem hrL hk₁' hk₀ hc hrc
    rw [hrb, ← mbar_conj hrM hgM] at heq
    exact eq_of_mbar_eq_p hp hp2 hRM hR hgr hrR heq
  have hrcen : ∀ g ∈ R, g * r = r * g := by
    intro g hg
    have hgr : g * r * g⁻¹ ∈ R := R.mul_mem (R.mul_mem hg hrR) (R.inv_mem hg)
    have := hconjrep g (hRM hg) (h.le_H hg) (by rw [hRz g hg, mul_inv_cancel_right]) hgr
    calc g * r = g * r * g⁻¹ * g := by group
      _ = r * g := by rw [this]
  have hrzc : Commute rb zb := by
    show rb * zb = zb * rb
    rw [hrb, hzb, ← mbar_mul, ← mbar_mul]
    congr 1
    exact hRz r hrR
  have hrbp : rb ^ p = 1 := rep_pow_p hZ hrL hk₀ hzbp hrzc hrc
  have hrp : r ^ p = 1 := eq_of_mbar_eq_p hp hp2 hRM hR (R.pow_mem hrR p) R.one_mem (by
    rw [mbar_pow (hRM hrR) p, mbar_one]; exact hrbp)
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hnC
    simp only [show (⟨1, hrM⟩ : M) = 1 from rfl, map_one, inv_one, one_mul] at hrc
    exact hrc
  have hro : orderOf r = p := orderOf_eq_prime hrp hr1
  have hrΩ := hΩ r hrR hrcen hrp
  obtain ⟨s, hsM, hsz, hsw, hsw1⟩ := hinv
  have hsC : s ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [hsz])
  have hsH : s ∈ H := hCz hsC
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hsw
  have hrw : r ∉ Subgroup.zpowers w := by
    intro hrw
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hrw
    have hsr : s * w ^ a * s⁻¹ ∈ R := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hm, ← zpow_mul]
      exact Subgroup.zpow_mem _ hwR _
    have h1 := hconjrep s hsM hsH hsz hsr
    have hwin := mem_zpowers_of_zpow_ne_one hp hwo hr1
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hwin
    apply hsw1
    rw [← hc, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1]
  obtain ⟨k, j, hkj⟩ := exists_pow_eq_mul hp hwo hzo hro (hRz w hwR) (hrcen w hwR).symm hrΩ hrw
  obtain ⟨n, hnM, hnz⟩ := hfus (j % (p : ℤ)).toNat
  have hwj : w ^ ((j % (p : ℤ)).toNat : ℕ) = w ^ j := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero))]
    have := zpow_mod_orderOf w j
    rwa [hwo] at this
  rw [hwj, ← hkj] at hnz
  have hzB : zb ∈ B := by
    have hA : IsComponentOf (barM M (Lb.map (MulAut.conj n⁻¹).toMonoidHom)) ⊤ :=
      (hLb.toIsTwoPrimeComponent.map_conj (M.inv_mem hnM)).component
    have hzA : zb ∈ barM M (Lb.map (MulAut.conj n⁻¹).toMonoidHom) := by
      rw [barM_map_conj (M.inv_mem hnM) Lb]
      have hzr : n * z * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hzM) (M.inv_mem hnM)
      refine ⟨mbar M (n * z * n⁻¹) hzr, ?_, ?_⟩
      · have e : mbar M (n * z * n⁻¹) hzr = rb ^ k := by
          rw [hrb, ← mbar_zpow hrM k]
          congr 1
        rw [e]
        exact Subgroup.zpow_mem _ hrL k
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzb, mbar]
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (by simp [mul_assoc])
    have heqA := h.barM_eq_of_mem_component hp hp2 hzM hz hCz hA hzA hLb
    rw [hB, heqA]
    exact hzA
  have hwB : mbar M w (hRM hwR) ∈ B := by
    obtain ⟨x, hxM, hxz⟩ := hfus 1
    rw [pow_one] at hxz
    have hzw : z * w ∈ M := M.mul_mem hzM (hRM hwR)
    have hzwb : mbar M (z * w) hzw ∈ barM M (Lb.map (MulAut.conj x).toMonoidHom) := by
      rw [barM_map_conj hxM Lb]
      refine ⟨zb, hzB, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hzb, ← mbar_conj hzM hxM]
      congr 1
    by_cases hBx : barM M (Lb.map (MulAut.conj x).toMonoidHom) = B
    · rw [hBx] at hzwb
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzB) hzwb
      rw [← mbar_inv hzM, ← mbar_mul (M.inv_mem hzM) hzw] at this
      convert this using 2
      group
    · exfalso
      have hc1 : mbar M (z * w) hzw ∈ Subgroup.centralizer (B : Set _) :=
        le_centralizer_of_component_ne (hLb.toIsTwoPrimeComponent.map_conj hxM).component
          hLb.component hBx hzwb
      have hc2 := hKC s hsM hsH _ hc1
      have hzwm : s * (z * w) * s⁻¹ = z * w ^ m := by
        calc s * (z * w) * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by group
          _ = z * w ^ m := by rw [hsz, hm]
      rw [← mbar_conj hzw hsM] at hc2
      have hc3 : mbar M (z * w ^ m) (M.mul_mem hzM (M.zpow_mem (hRM hwR) m)) ∈
          Subgroup.centralizer (B : Set _) := by
        convert hc2 using 2
        exact hzwm.symm
      have hc4 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hc1) hc3
      rw [← mbar_inv hzw, ← mbar_mul (M.inv_mem hzw)] at hc4
      have e : (z * w)⁻¹ * (z * w ^ m) = w ^ (m - 1) := by
        rw [zpow_sub, zpow_one]
        have hc := (hRz w hwR).symm
        calc (z * w)⁻¹ * (z * w ^ m) = w⁻¹ * (z⁻¹ * z) * w ^ m := by group
          _ = w ^ m * w⁻¹ := by rw [inv_mul_cancel, mul_one, ← zpow_neg_one,
              ((Commute.refl w).zpow_zpow (-1) m).eq, zpow_neg_one]
      have hwm1 : mbar M (w ^ (m - 1)) (M.zpow_mem (hRM hwR) _) ∈
          Subgroup.centralizer (B : Set _) := by
        convert hc4 using 2
        exact e.symm
      have hne : w ^ (m - 1) ≠ 1 := by
        intro h1
        apply hsw1
        rw [← hm, show m = (m - 1) + 1 by ring, zpow_add, h1, one_mul, zpow_one]
      obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_zpow_ne_one hp hwo hne)
      have hwC : mbar M w (hRM hwR) ∈ Subgroup.centralizer (B : Set _) := by
        have := Subgroup.zpow_mem _ hwm1 c
        rw [← mbar_zpow] at this
        convert this using 2
        exact hc.symm
      apply hnC
      have := Subgroup.mul_mem _ hc1 (Subgroup.inv_mem _ hwC)
      rw [← mbar_inv (hRM hwR), ← mbar_mul hzw (M.inv_mem (hRM hwR))] at this
      convert this using 2
      group
  set X := barM M R with hX
  have hXp : IsPGroup p X := (hR.comap_subtype (K := M)).map _
  have hXN : X ≤ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    exact hKN g hgM (h.le_H (Subgroup.mem_subgroupOf.mp hg))
  have hXC : X ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    have hgR : g ∈ R := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    show mbar M g hgM * mbar M z hzM = mbar M z hzM * mbar M g hgM
    rw [← mbar_mul, ← mbar_mul]
    congr 1
    exact hRz g hgR
  have hXinf : X ⊓ Subgroup.centralizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
    by_contra hne
    have hNi : X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer
        (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) : Set _) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hxC := mem_normalizer_centralizer (hXN hx)
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
    change orderOf (mbar M g hgM) = p at hco
    have hgc : ∀ y ∈ R, y * g = g * y := by
      intro y hy
      refine commute_of_mbar_p hp hp2 hRM hR hy hgR ?_
      exact (Subgroup.mem_centralizer_iff.mp hcZ (mbar M y (hRM hy))
        ⟨⟨y, hRM hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    have hcbp : mbar M g hgM ^ p = 1 := by rw [← hco]; exact pow_orderOf_eq_one _
    have hgp : g ^ p = 1 := eq_of_mbar_eq_p hp hp2 hRM hR (R.pow_mem hgR p) R.one_mem (by
      rw [mbar_pow (hRM hgR) p, mbar_one]; exact hcbp)
    have hgΩ := hΩ g hgR hgc hgp
    have hgL : mbar M g hgM ∈ B := by
      have hle : barM M (Subgroup.zpowers w ⊔ Subgroup.zpowers z) ≤ B := by
        rw [barM_sup ((Subgroup.zpowers_le).mpr (hRM hwR)) ((Subgroup.zpowers_le).mpr hzM),
          barM_zpowers (hRM hwR), barM_zpowers hzM]
        exact sup_le ((Subgroup.zpowers_le).mpr hwB) ((Subgroup.zpowers_le).mpr hzB)
      exact hle ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hgΩ, rfl⟩
    have h1 := hZ _ hgL hcC hcbp
    have h2 : orderOf (mbar M g hgM) = 1 := by rw [h1]; exact orderOf_one
    rw [hco] at h2
    exact hp.one_lt.ne' h2
  have hcard := hbound X hXp hXN hXC hXinf
  rw [hX, card_barM_of_isPGroup hp hp2 hRM hR] at hcard
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.AGLEmbedding
