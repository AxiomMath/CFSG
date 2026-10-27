module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.le_or_le_of_l34 (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {Y : Subgroup G} (hHM : H ⊓ M ≤ Y) (hYH : Y ≤ H) : Y ≤ M ∨ H ≤ Y := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨hp3, hL⟩)
  obtain ⟨T, hT, -, -, -, -, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hRKp : IsPGroup p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) := Rbar.isPGroup'.to_le inf_le_left
  have h2 : 2 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hp hd.cfg.red.ne_two hRKp
      hd.noncyclic
  have hN : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H :=
    hd.cfg.red.normalizer_le_of_mem_centralizer hzbR (fun h => hzbK h.2) hzbp
      (Subgroup.centralizer_le inf_le_right hzbc) inf_le_left h2
  have htop : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ⊔ K = ⊤ := by
    rw [← hT₁]
    exact Sylow.normalizer_sup_eq_top T₁
  set Yb := (Y.subgroupOf H).map π with hYdef
  have hXY : d1X0 p M H ≤ Yb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hHM (Subgroup.mem_subgroupOf.mp hx))
  have hΓY : GLBCore p 1 (T₁ : Subgroup K) ≤ Yb.subgroupOf K := by
    rw [← hY]
    exact Subgroup.comap_mono hXY
  have hcoreM : ∀ h : H, π h = 1 → (h : G) ∈ M := fun h h1 =>
    hd.cfg.ext.primeCore_le ((mk'_primeComplementCore_eq_one_iff p h).mp h1)
  have hcoreY : ∀ h : H, π h = 1 → (h : G) ∈ Y := fun h h1 =>
    hHM ⟨h.2, hcoreM h h1⟩
  rcases (hUE K p (Or.inl ⟨hp3, hL⟩) T₁ hΓT).1 (Yb.subgroupOf K) hΓY with hYK | hYK
  · left
    intro j hj
    have hjH : j ∈ H := hYH hj
    have hjY : π ⟨j, hjH⟩ ∈ Yb := ⟨⟨j, hjH⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    have hjt : π ⟨j, hjH⟩ ∈ K ⊔ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [sup_comm, htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_left.mp hjt
    have hnX : n ∈ d1X0 p M H := hN hn
    have hkY : k ∈ Yb := by
      have e : k = π ⟨j, hjH⟩ * n⁻¹ := by rw [← hkn]; group
      rw [e]
      exact Yb.mul_mem hjY (Yb.inv_mem (hXY hnX))
    have hkX : k ∈ d1X0 p M H := by
      have h1 : (⟨k, hk⟩ : K) ∈ Yb.subgroupOf K := Subgroup.mem_subgroupOf.mpr hkY
      rw [hYK, ← hY] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hjX : π ⟨j, hjH⟩ ∈ d1X0 p M H := hkn ▸ (d1X0 p M H).mul_mem hkX hnX
    obtain ⟨m, hm, hmj⟩ := hjX
    have hm' : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
    have h1 : π (m⁻¹ * ⟨j, hjH⟩) = 1 := by rw [map_mul, map_inv, hmj, inv_mul_cancel]
    have := hcoreM _ h1
    have e : j = (m : G) * ((m⁻¹ * ⟨j, hjH⟩ : H) : G) := by simp
    rw [e]
    exact M.mul_mem hm' this
  · right
    have hKY : K ≤ Yb := fun k hk => by
      have h1 : (⟨k, hk⟩ : K) ∈ Yb.subgroupOf K := hYK ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    have hYtop : Yb = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le (hN.trans hXY) hKY
    intro h hh
    have hmem : π ⟨h, hh⟩ ∈ Yb := hYtop ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjh⟩ := hmem
    have h1 : π (j⁻¹ * ⟨h, hh⟩) = 1 := by rw [map_mul, map_inv, hjh, inv_mul_cancel]
    have hjY : (j : G) ∈ Y := Subgroup.mem_subgroupOf.mp hj
    have e : h = (j : G) * ((j⁻¹ * ⟨h, hh⟩ : H) : G) := by simp
    rw [e]
    exact Y.mul_mem hjY (hcoreY _ h1)

section Shared

variable {M H : Subgroup G}

omit [Finite G] in
theorem twoCore_le_twoCore_inf_of_le (hHM : pCoreOf 2 H ≤ M) :
    pCoreOf 2 H ≤ pCoreOf 2 (H ⊓ M) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (_root_.le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hHM)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)

omit [Finite G] in
theorem inf_normalizer_twoCore_inf_of_le_or_le (hHM : pCoreOf 2 H ≤ M)
    (hY : ∀ {Y : Subgroup G}, H ⊓ M ≤ Y → Y ≤ H → Y ≤ M ∨ H ≤ Y)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := by
  have hle : H ⊓ M ≤ H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) :=
    le_inf inf_le_left (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))
  refine le_antisymm ?_ hle
  rcases hY hle inf_le_left with h | h
  · exact le_inf inf_le_left h
  · exfalso
    apply hS
    refine le_antisymm ?_ (twoCore_le_twoCore_inf_of_le hHM)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left)
      (h.trans inf_le_right)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M))

omit [Finite G] in
theorem isTwoRadicalIn_twoCore_inf_of_le_or_le (hHM : pCoreOf 2 H ≤ M)
    (hY : ∀ {Y : Subgroup G}, H ⊓ M ≤ Y → Y ≤ H → Y ≤ M ∨ H ≤ Y)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) : IsTwoRadicalIn H (pCoreOf 2 (H ⊓ M)) := by
  refine ⟨(CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left,
    fun hbot => hS ?_, ?_⟩
  · have h1 := twoCore_le_twoCore_inf_of_le hHM
    rw [hbot, le_bot_iff] at h1
    rw [hbot, h1]
  · rw [inf_normalizer_twoCore_inf_of_le_or_le hHM hY hS]

omit [Finite G] in
theorem cgsIn_twoCore_inf_of_le_or_le (hHM : pCoreOf 2 H ≤ M)
    (hY : ∀ {Y : Subgroup G}, H ⊓ M ≤ Y → Y ≤ H → Y ≤ M ∨ H ≤ Y)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    cgsIn H (pCoreOf 2 (H ⊓ M)) = H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) := by
  have hrad := isTwoRadicalIn_twoCore_inf_of_le_or_le hHM hY hS
  refine le_antisymm ?_ (inf_normalizer_le_cgsIn hrad.2.1)
  rw [inf_normalizer_twoCore_inf_of_le_or_le hHM hY hS]
  refine iSup_le fun C => iSup_le fun hCU => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hNC : H ⊓ M ≤ H ⊓ Subgroup.normalizer (C : Set G) := by
    refine le_inf inf_le_left ?_
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := pCoreOf 2 (H ⊓ M)) (C.subgroupOf (pCoreOf 2 (H ⊓ M)))
    rw [Subgroup.map_subgroupOf_eq_of_le hCU] at h1
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)).trans h1
  rcases hY hNC inf_le_left with h | h
  · exact le_inf inf_le_left h
  · exact absurd (h.trans inf_le_right) (hPU C hCU hC1 hchar)

omit [Finite G] in
theorem asc81bHyp_twoCore_inf_of_le_or_le (hHM : pCoreOf 2 H ≤ M)
    (hY : ∀ {Y : Subgroup G}, H ⊓ M ≤ Y → Y ≤ H → Y ≤ M ∨ H ≤ Y) (hcH : CharTwo H)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    Asc81bHyp H (pCoreOf 2 (H ⊓ M)) where
  twoRadical := isTwoRadicalIn_twoCore_inf_of_le_or_le hHM hY hS
  charTwo := hcH
  cgs := cgsIn_twoCore_inf_of_le_or_le hHM hY hS hPU

end Shared

theorem D1OneSmallData.inf_normalizer_twoCore_inf (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M :=
  inf_normalizer_twoCore_inf_of_le_or_le hd.cfg.ext.twoCore_le
    (fun hHM hYH => hd.le_or_le_of_l34 hUE hp3 hL hHM hYH) hS

theorem D1OneSmallData.isTwoRadicalIn_twoCore_inf (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) : IsTwoRadicalIn H (pCoreOf 2 (H ⊓ M)) :=
  isTwoRadicalIn_twoCore_inf_of_le_or_le hd.cfg.ext.twoCore_le
    (fun hHM hYH => hd.le_or_le_of_l34 hUE hp3 hL hHM hYH) hS

theorem D1OneSmallData.asc81bHyp_twoCore_inf (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    Asc81bHyp H (pCoreOf 2 (H ⊓ M)) :=
  asc81bHyp_twoCore_inf_of_le_or_le hd.cfg.ext.twoCore_le
    (fun hHM hYH => hd.le_or_le_of_l34 hUE hp3 hL hHM hYH)
    (hd.cfg.ext.charTwo_of_isCharTwoType hd.cfg.glob.charTwo).2 hS hPU

end CFSG.AGLEmbedding
