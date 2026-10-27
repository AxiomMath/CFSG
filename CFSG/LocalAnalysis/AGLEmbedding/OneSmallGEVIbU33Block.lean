module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Inner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1PhaseThree.exists_block_u33_three_ib (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (hc : D1IbCubeThreeData p P M H R Rbar K z) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) (hShape : KFactSmallSylowShape) (hOrb3 : KFactSmallOrbitsCube)
    (hcov : ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → V ≤ Subgroup.normalizer (L : Set G))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    (hfusZ : ∀ r ∈ R, r ∉ d1LiftX p H R K → (∀ s ∈ R, r * s = s * r) → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹) :
    ∃ L₁ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, h.le_M hc.elt.1⟩ ∈ barM M L₁ := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set T := d1LiftX 3 H R K with hT
  have hRM : R ≤ M := h.le_M
  have hzR : z ∈ R := hc.elt.1
  have hzM : z ∈ M := hRM hzR
  set zb := mk ⟨z, hzM⟩ with hzb
  have hzo : orderOf z = 3 := hc.elt.2.1
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  obtain ⟨V, hVHM, hVp, hzV, hVN⟩ := hcov
  have hblkA : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL => h.zbar_mem_sup_of_cover hSch hVHM hVp hzV hzM hL (hVN L hL)
  obtain ⟨L₀, hL₀⟩ := h.exists_weakSBlock h84 hD2
  obtain ⟨L₁, hL₁, r, hrR, hrM, hrL, hrc⟩ :=
    exists_rep_mem_R hzM hz3 hCz hsyl hL₀ (hblkA L₀ hL₀)
  obtain ⟨c₀, hc₀Z, i₀, hr⟩ := hc.rep_mem_center rfl h hShape hOrb3 hCz hL₁ hrR hrL hrc
  have hzC₁ := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL₁
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hzC₁
    have e : (mk ⟨1, hrM⟩)⁻¹ * zb = zb := by
      have : (⟨1, hrM⟩ : M) = 1 := rfl
      rw [this, map_one, inv_one, one_mul]
    rwa [e] at hrc
  have hrT : r ∉ T := by
    intro hrT
    obtain ⟨n, hnM, hnz, hnr⟩ := hinv r hrT hr1
    exact h.false_of_rep_inv hp hp2 hzM hz hCz hL₁ hrM (hc.exp r hrR) hrL hrc hnM hnz hnr
  have hrZ : ∀ s ∈ R, r * s = s * r := by
    intro s hs
    rw [hr]
    have h1 := hc.centerOf_le_centralizer hc₀Z hs
    have h2 : z ^ i₀ * s = s * z ^ i₀ := (Commute.pow_left (hc.commute_z hs).symm i₀).eq
    calc c₀ * z ^ i₀ * s = c₀ * (z ^ i₀ * s) := by group
      _ = c₀ * (s * z ^ i₀) := by rw [h2]
      _ = c₀ * s * z ^ i₀ := by group
      _ = s * c₀ * z ^ i₀ := by rw [h1]
      _ = s * (c₀ * z ^ i₀) := by group
  obtain ⟨-, n, hnN, hrn⟩ := hfusZ r hrR hrT hrZ
  have hnM : n ∈ M := h.toD1Escape.normalizer_le hnN
  have hnzo : orderOf (n * z * n⁻¹) = 3 := by
    rw [← hzo]; exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
  have hzr : n * z * n⁻¹ ∈ Subgroup.zpowers r :=
    mem_zpowers_of_mem_zpowers_of_prime hp hnzo hrn hr1
  have hnzM : n * z * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hzM) (M.inv_mem hnM)
  have hnzL : mk ⟨n * z * n⁻¹, hnzM⟩ ∈ barM M L₁ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzr
    have : (⟨n * z * n⁻¹, hnzM⟩ : M) = (⟨r, hrM⟩ : M) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem _ hrL k
  have hAc' : IsComponentOf (barM M (L₁.map (MulAut.conj n⁻¹).toMonoidHom)) ⊤ :=
    (hL₁.toIsTwoPrimeComponent.map_conj (M.inv_mem hnM)).component
  have hzA' : zb ∈ barM M (L₁.map (MulAut.conj n⁻¹).toMonoidHom) := by
    rw [barM_map_conj (M.inv_mem hnM) L₁]
    refine ⟨mk ⟨n * z * n⁻¹, hnzM⟩, hnzL, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hzb]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])
  exact ⟨L₁, hL₁, (h.barM_eq_of_mem_component hp hp2 hzM hz hCz hAc' hzA' hL₁) ▸ hzA'⟩

theorem D1PhaseThree.exists_center_mem_block_u33 (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (hc : D1IbCubeThreeData p P M H R Rbar K z)
    (hcent : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p), W ≤ d1X0 p M H →
      ⁅W, W⁆ = W → W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {L₁ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hzL₁ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, h.le_M hc.elt.1⟩ ∈ barM M L₁)
    (hall : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L₁)
    (hmove : ∃ x ∈ (P : Subgroup G), x ∈ Subgroup.normalizer (R : Set G) ∧ x ∉ R ∧
      x * z * x⁻¹ ∉ Subgroup.zpowers z) :
    ∃ t ∈ centerOf (d1LiftX p H R K), t ≠ 1 ∧ ∃ htM : t ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∈ barM M L₁ := by
  subst hp3
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set T := d1LiftX 3 H R K with hT
  have hRM : R ≤ M := h.le_M
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hzR : z ∈ R := hc.elt.1
  have hzM : z ∈ M := hRM hzR
  set zb := mk ⟨z, hzM⟩ with hzb
  set A := barM M L₁ with hA
  obtain ⟨x, hxP, hxN, -, hxz⟩ := hmove
  have hxM : x ∈ M := h.sylow_le hxP
  have hwR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzR
  have hwc : ∀ s ∈ R, x * z * x⁻¹ * s = s * (x * z * x⁻¹) := by
    intro s hs
    have hs' : x⁻¹ * s * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) s).mp hs
      simpa using this
    have h1 := hc.commute_z hs'
    calc x * z * x⁻¹ * s = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by rw [h1]
      _ = s * (x * z * x⁻¹) := by group
  obtain ⟨t, htT, j, hwt⟩ := hc.dec _ hwR
  have htR : t ∈ R := hTR htT
  have htZ : t ∈ centerOf T := by
    refine hc.mem_centerOf_of_comm htT fun s hs => ?_
    have hts : t = x * z * x⁻¹ * (z ^ j)⁻¹ := by rw [hwt]; group
    have h2 : (z ^ j)⁻¹ * s = s * (z ^ j)⁻¹ :=
      ((Commute.pow_left (hc.commute_z hs).symm j).inv_left).eq
    rw [hts]
    calc x * z * x⁻¹ * (z ^ j)⁻¹ * s = x * z * x⁻¹ * ((z ^ j)⁻¹ * s) := by group
      _ = x * z * x⁻¹ * (s * (z ^ j)⁻¹) := by rw [h2]
      _ = (x * z * x⁻¹ * s) * (z ^ j)⁻¹ := by group
      _ = s * (x * z * x⁻¹) * (z ^ j)⁻¹ := by rw [hwc s hs]
      _ = s * (x * z * x⁻¹ * (z ^ j)⁻¹) := by group
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hxz
    rw [hwt, one_mul]
    exact Subgroup.npow_mem_zpowers z j
  have htM : t ∈ M := hRM htR
  have hwM : x * z * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hxM hzM) (M.inv_mem hxM)
  refine ⟨t, htZ, ht1, htM, ?_⟩
  have hte : mk ⟨t, htM⟩ = mk ⟨x * z * x⁻¹, hwM⟩ * (zb ^ j)⁻¹ := by
    rw [hzb, ← map_pow, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [hwt]; group
  by_cases hxA : mk ⟨x, hxM⟩ ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · have hwA : mk ⟨x * z * x⁻¹, hwM⟩ ∈ A := by
      have he : mk ⟨x * z * x⁻¹, hwM⟩ = mk ⟨x, hxM⟩ * zb * (mk ⟨x, hxM⟩)⁻¹ := by
        rw [hzb, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [he]
      exact (Subgroup.mem_normalizer_iff.mp hxA zb).mp hzL₁
    rw [hte]
    exact A.mul_mem hwA (A.inv_mem (A.pow_mem hzL₁ j))
  exfalso
  set L₂ := L₁.map (MulAut.conj x).toMonoidHom with hL₂
  have hL₂c : IsTwoPrimeComponent M L₂ := hL₁.toIsTwoPrimeComponent.map_conj hxM
  have hL₂S : L₂ ≤ Subgroup.normalizer (S : Set G) := by
    by_contra hns
    have he := hall L₂ ⟨hL₂c, hns⟩
    rw [barM_map_conj hxM L₁] at he
    exact hxA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hL₂H : L₂ ≤ H := by
    have := hL₂S
    rwa [h.normalizer_twoCore_H] at this
  have hL₂M : L₂ ≤ M := hL₂c.le
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set W := (L₂.subgroupOf H).map π with hW
  have hWX : W ≤ d1X0 3 M H := Subgroup.map_mono fun y hy =>
    Subgroup.mem_subgroupOf.mpr
      ⟨hL₂H (Subgroup.mem_subgroupOf.mp hy), hL₂M (Subgroup.mem_subgroupOf.mp hy)⟩
  have hWp : ⁅W, W⁆ = W := by
    have h1 : ⁅L₂.subgroupOf H, L₂.subgroupOf H⁆ = L₂.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL₂H, hL₂c.perfect]
    rw [hW, ← Subgroup.map_commutator, h1]
  have hWC := hcent W hWX hWp
  obtain ⟨l, hl, hlz⟩ := hzL₁
  have hq : ((l⁻¹ * ⟨z, hzM⟩ : M) : G) ∈ pCoreOf 2 M :=
    coe_mem_pCoreOf_two_of_mk_eq_one _ (by rw [map_mul, map_inv, hlz, inv_mul_cancel])
  have hqx : x * ((l : G)⁻¹ * z) * x⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M hxM) _).mp
      (by simpa using hq)
  have hqN : x * ((l : G)⁻¹ * z) * x⁻¹ ∈ GLBPrimeCore 3 H := h.twoCore_M_le_glbPrimeCore hqx
  have hlx : x * l * x⁻¹ ∈ L₂ :=
    ⟨l, Subgroup.mem_subgroupOf.mp hl, by simp [MulAut.conj_apply]⟩
  have hlxH : x * l * x⁻¹ ∈ H := hL₂H hlx
  have hqxH : x * ((l : G)⁻¹ * z) * x⁻¹ ∈ H := glbPrimeCore_le 3 H hqN
  have hwH : x * z * x⁻¹ ∈ H := by
    have : x * z * x⁻¹ = (x * l * x⁻¹) * (x * ((l : G)⁻¹ * z) * x⁻¹) := by group
    rw [this]
    exact H.mul_mem hlxH hqxH
  have hπw : π ⟨x * z * x⁻¹, hwH⟩ ∈ W := by
    have h1 : (⟨x * z * x⁻¹, hwH⟩ : H) =
        ⟨x * l * x⁻¹, hlxH⟩ * ⟨x * ((l : G)⁻¹ * z) * x⁻¹, hqxH⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have h2 : π ⟨x * ((l : G)⁻¹ * z) * x⁻¹, hqxH⟩ = 1 :=
      (mk'_primeComplementCore_eq_one_iff 3 _).mpr hqN
    rw [h1, map_mul, h2, mul_one]
    exact ⟨⟨x * l * x⁻¹, hlxH⟩, Subgroup.mem_subgroupOf.mpr hlx, rfl⟩
  obtain ⟨t', ⟨ht'R, ht'K⟩, ht't⟩ := htT
  have htH : t ∈ H := ht't ▸ t'.2
  have hzH : z ∈ H := hc.elt.2.2.1
  have ht'e : t' = ⟨t, htH⟩ := Subtype.ext ht't
  have hte' : (⟨t, htH⟩ : H) = ⟨x * z * x⁻¹, hwH⟩ * (⟨z, hzH⟩ ^ j)⁻¹ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hwt]
      group)
  have hπtC : π ⟨t, htH⟩ ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hte', map_mul, map_inv, map_pow]
    exact Subgroup.mul_mem _ (hWC hπw) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc.elt.2.2.2 j))
  have hπtK : π ⟨t, htH⟩ ∈ K := ht'e ▸ ht'K
  have hπt1 : π ⟨t, htH⟩ = 1 := by
    have hcen : (⟨π ⟨t, htH⟩, hπtK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hπtC k k.2)
    rw [hc.data.center, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have := hc.mk_eq_iff (a := ⟨t, htH⟩) (b := 1) htR R.one_mem (by rw [hπt1, map_one])
  exact ht1 (congrArg Subtype.val this)

end CFSG.AGLEmbedding
