module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSFactor
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSAbs

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

theorem card_specialLinearGroup_fin_four_eq_sixS {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) = 20160 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem card_specialLinearGroup_fin_six_eq_sixS {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 6) K) = 20158709760 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem not_sq_card_dvd_card_of_mulEquiv_projectiveSL_six_sixS {G : Type} [Group G] {L : Subgroup G}
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) :
    ¬ Nat.card (Matrix.SpecialLinearGroup (Fin (6 - 2)) K) ^ 2 ∣ Nat.card L := by
  have hL : Nat.card L = 20158709760 := by
    rw [Nat.card_congr e.toEquiv, ← card_specialLinearGroup_fin_six_eq_sixS hK]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨proj_injective_of_natCard_eq_two hK,
      LinearFlag.proj_surjective 6 K⟩)).symm
  rw [hL, show (6 - 2 : ℕ) = 4 from rfl, card_specialLinearGroup_fin_four_eq_sixS hK]
  decide

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def rootTorusSixG {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n} (hij : i ≠ j) : G :=
  ((e.symm (xab hij (1 : K) * xab hij.symm 1) : L) : G)

theorem rootTorus_le_and_card_sixS {n : ℕ} {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    {i j : Fin n} (hij : i ≠ j) :
    zpowers (xab hij (1 : K) * xab hij.symm 1) ≤ rootSL2 i j ∧
      Nat.card (zpowers (xab hij (1 : K) * xab hij.symm 1)) = Nat.card K + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(zpowers_le).2 (mul_mem (xab_mem_rootSL2 hij 1)
    (by rw [rootSL2_comm]; exact xab_mem_rootSL2 hij.symm 1)), ?_⟩
  rw [Nat.card_zpowers, hK, orderOf_eq_prime (xab_mul_xab_pow_three_sixS hij)
    (xab_mul_xab_ne_one_sixS hK hij)]

omit [Finite G] in
theorem modelToG_zpowers_rootTorus_sixS {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n} (hij : i ≠ j) :
    modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) = zpowers (rootTorusSixG e hij) := by
  rw [modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
theorem centralizer_modelToG_rootTorus_sixS {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n} (hij : i ≠ j) :
    centralizer (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) : Set G) =
      centralizer ({rootTorusSixG e hij} : Set G) := by
  rw [modelToG_zpowers_rootTorus_sixS, centralizer_zpowers_eq]

section WZero

variable {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
  (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
  (htC : t ∈ centralizer (L : Set G)) {c : Fin 6} {W₁ : Subgroup G}
  (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
  (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
  (htW₁ : t ∈ normalizer (W₁ : Set G))
  (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
include hK hW₁c hW₁2 hW₁t htW₁ hLW htC ht

omit [Finite G] [CharP K 2] ht htC hW₁2 htW₁ hLW in
theorem card_vOne_sixS :
    Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 5 ∧
      Nat.card W₁ = Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 6)) := by simp
  have h5 : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 5 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  exact ⟨h5, by rw [hW₁c, h5]; norm_num⟩

theorem wZero_facts_sixS {i j : Fin 6} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j) :
    Nat.card (W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) : Subgroup G) = 2 ^ 6 ∧
    W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) ⊓ centralizer ({t} : Set G) =
      modelToG e (pointRadOn c (({c}ᶜ : Finset (Fin 6)) \ {i, j})) ∧
    ∃ yG ∈ modelToG e (blockSL (K := K) (({i, j} : Finset (Fin 6))ᶜ)),
      yG ∈ normalizer ((W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) : Subgroup G) : Set G) ∧
      W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) ⊓ centralizer ({yG} : Set G) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  obtain ⟨hX₀, hX₀c⟩ := rootTorus_le_and_card_sixS hK hij
  set X₀ := zpowers (xab hij (1 : K) * xab hij.symm 1) with hX₀def
  set xG : G := rootTorusSixG e hij with hxG
  have hCX := centralizer_modelToG_rootTorus_sixS (G := G) e hij
  have hcsub : ({i, j} : Finset (Fin 6)) ⊆ {c}ᶜ := by
    intro m hm
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    rcases Finset.mem_insert.1 hm with h | h
    · exact hci h
    · exact hcj (Finset.mem_singleton.1 h)
  have hyX : xab hij (1 : K) * xab hij.symm 1 ∈ X₀ := mem_zpowers _
  have hxB : xab hij (1 : K) * xab hij.symm 1 ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
    blockSL_mono hcsub (by rw [← rootSL2_eq]; exact hX₀ hyX)
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
  have hxt : xG * t = t * xG := hLt xG (e.symm _).2
  have hx3G : xG ^ 3 = 1 := by
    rw [hxG, rootTorusSixG, ← Subgroup.coe_pow, ← map_pow, xab_mul_xab_pow_three_sixS hij, map_one,
      Subgroup.coe_one]
  obtain ⟨hV₁card, hWV⟩ := card_vOne_sixS hK e hW₁c hW₁t
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ hWV
  set S₀ : Finset (Fin 6) := ({c}ᶜ : Finset (Fin 6)) \ {i, j} with hS₀
  have hS₀card : S₀.card = 3 := by
    rw [hS₀, Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hij]
  have hcS₀ : c ∉ S₀ := fun h => by simp [hS₀] at h
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c S₀) := by
    rw [hW₁t, hxG, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hij hci hcj _ hX₀ hX₀c]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c S₀)) = 2 ^ 3 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c hcS₀, hS₀card]
  have hS₀sub : insert c S₀ ⊆ ({i, j} : Finset (Fin 6))ᶜ := by
    intro m hm
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 hm with rfl | hm
    · simp [hci, hcj]
    · exact (Finset.mem_sdiff.1 hm).2
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hS₀eq⟩ := Finset.card_eq_three.1 hS₀card
  have hdS₀ : ∀ {d : Fin 6}, d ∈ S₀ → c ≠ d := fun hd h => hcS₀ (h ▸ hd)
  have hc1 : c ≠ d₁ := hdS₀ (by rw [hS₀eq]; simp)
  have hc2 : c ≠ d₂ := hdS₀ (by rw [hS₀eq]; simp)
  have hc3 : c ≠ d₃ := hdS₀ (by rw [hS₀eq]; simp)
  set y : LinearFlag.projectiveSL 6 K := LinearFlag.proj 6 K (singerThree d₁ d₂ d₃) with hydef
  set yG : G := ((e.symm y : L) : G) with hyG
  have hYz : modelToG e (zpowers y) = zpowers yG := by
    rw [modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCY : centralizer (modelToG e (zpowers y) : Set G) = centralizer ({yG} : Set G) := by
    rw [hYz, centralizer_zpowers_eq]
  have hyS₀ : y ∈ blockSL (K := K) S₀ := by
    rw [hS₀eq]
    exact proj_mem_blockSL (singerThree_mem_blockSpecialLinear d₁ d₂ d₃)
  have hyD : yG ∈ modelToG e (blockSL (K := K) (({i, j} : Finset (Fin 6))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono ((Finset.subset_insert c S₀).trans hS₀sub) hyS₀)
  have hyN : yG ∈ normalizer (W₁ : Set G) :=
    hLW (symm_mem_modelToG e (blockSL_mono (fun m hm => (Finset.mem_sdiff.1 hm).1) hyS₀))
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hyx : yG * xG = xG * yG := by
    have hdisj : Disjoint S₀ ({i, j} : Finset (Fin 6)) := Finset.sdiff_disjoint
    have h := (commute_blockSL_of_disjoint hdisj y hyS₀ _
      (by rw [← rootSL2_eq]; exact hX₀ hyX)).eq
    have h' : e.symm y * e.symm (xab hij (1 : K) * xab hij.symm 1) =
        e.symm (xab hij (1 : K) * xab hij.symm 1) * e.symm y := by
      rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  refine ⟨?_, ?_, yG, hyD, mem_normalizer_inf_centralizer hyN hyx, ?_⟩
  · rw [card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hxN hxt hx3G, hV₀, hV₀card]
    norm_num
  · rw [inf_right_comm, hV₀]
  · refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hxt hyt ?_
    rw [hV₀, ← hCY, modelToG_inf_centralizer_eq, hS₀eq,
      pointRadOn_inf_centralizer_singerThree hK h12 h13 h23 hc1 hc2 hc3, modelToG,
      Subgroup.map_bot, Subgroup.map_bot]

end WZero

section Root

variable
  (hset : SeitzSetting G L)
  {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
  (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
  (htC : t ∈ centralizer (L : Set G)) {c : Fin 6} {W₁ : Subgroup G}
  (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
  (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
  (htW₁ : t ∈ normalizer (W₁ : Set G))
  (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
include hset hK hW₁c hW₁2 hW₁t htW₁ hLW htC ht

theorem wZero_le_and_rootSL2_le_centralizer_sixS {i j : Fin 6} (hij : i ≠ j) (hci : c ≠ i)
    (hcj : c ≠ j)
    (hswap : ∀ htX : t ∈ centralizer (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) :
      Set G), LinearTwoSwapKindAt e t i j (zpowers (xab hij (1 : K) * xab hij.symm 1)) htX) :
    W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) ≤
        centralizerPerfectCore (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1))) ∧
      modelToG e (rootSL2 (K := K) i j) ≤
        centralizer ((W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hX₀, hX₀c⟩ := rootTorus_le_and_card_sixS hK hij
  have htX : t ∈ centralizer (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) : Set G) :=
    centralizer_le (modelToG_le e _) htC
  obtain ⟨A, -, -, -, -, hDE⟩ :=
    exists_swap_factor_of_swap hset hK e (by norm_num) htC ht hij hX₀ hX₀c htX (hswap htX)
  obtain ⟨-, -, yG, hyD, hyW₀, hy0⟩ :=
    wZero_facts_sixS hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hij hci hcj
  have hWc : ∀ v ∈ W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G),
      ∀ w ∈ W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G), v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv.1 hw.1
  have hW₀X : W₁ ⊓ centralizer ({rootTorusSixG e hij} : Set G) ≤
      centralizer (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) : Set G) := by
    rw [centralizer_modelToG_rootTorus_sixS]
    exact inf_le_right
  have hW₀E := le_centralizerPerfectCore_of_inf_centralizer_eq_bot hWc hW₀X (hDE hyD) hyW₀ hy0
  have hJ := rootSL2_le_centralizer_of_swap hset hK e (by norm_num) htC ht hij hX₀ hX₀c htX
    (hswap htX) (not_sq_card_dvd_card_of_mulEquiv_projectiveSL_six_sixS hK e)
  refine ⟨hW₀E, fun x hx => mem_centralizer_iff.2 fun w hw => ?_⟩
  exact (mem_centralizer_iff.1 (hJ hx)) w (hW₀E hw)

theorem root_bound_sixS {i j : Fin 6} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (hswap : ∀ htX : t ∈ centralizer (modelToG e (zpowers (xab hij (1 : K) * xab hij.symm 1)) :
      Set G), LinearTwoSwapKindAt e t i j (zpowers (xab hij (1 : K) * xab hij.symm 1)) htX) :
    Nat.card W₁ ≤
      4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hij (1 : K)) : L) : G)} : Set G) :
        Subgroup G) := by
  obtain ⟨hW₀c, -, -⟩ := wZero_facts_sixS hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hij hci hcj
  obtain ⟨-, hJ⟩ := wZero_le_and_rootSL2_le_centralizer_sixS hset hK e ht htC hW₁c hW₁2 hW₁t
    htW₁ hLW hij hci hcj hswap
  have hcsub : ({i, j} : Finset (Fin 6)) ⊆ {c}ᶜ := by
    intro m hm
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    rcases Finset.mem_insert.1 hm with h | h
    · exact hci h
    · exact hcj (Finset.mem_singleton.1 h)
  set xG : G := ((e.symm (xab hij (1 : K)) : L) : G) with hxG
  set yG : G := rootTorusSixG e hij with hyG
  have hxB : xab hij (1 : K) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
    blockSL_mono hcsub (by rw [← rootSL2_eq]; exact xab_mem_rootSL2 hij 1)
  have hyB : xab hij (1 : K) * xab hij.symm 1 ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
    blockSL_mono hcsub (by
      rw [← rootSL2_eq]
      exact mul_mem (xab_mem_rootSL2 hij 1)
        (by rw [rootSL2_comm]; exact xab_mem_rootSL2 hij.symm 1))
  have hxW : xG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
  have hyW : yG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hyB)
  have hx2 : xG * xG = 1 := by
    rw [hxG, ← Subgroup.coe_mul, ← map_mul, xab_mul_self_of_charTwo hij 1, map_one,
      Subgroup.coe_one]
  have hy3 : yG ^ 3 = 1 := by
    rw [hyG, rootTorusSixG, ← Subgroup.coe_pow, ← map_pow, xab_mul_xab_pow_three_sixS hij, map_one,
      Subgroup.coe_one]
  have hxy : xG * yG * xG⁻¹ = yG⁻¹ := by
    have h := congrArg (fun z => ((e.symm z : L) : G)) (xab_conj_xab_mul_xab_sixS (K := K) hij)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hxG, hyG, rootTorusSixG]
    simpa only [map_mul, Subgroup.coe_mul] using h
  have hCy : W₁ ⊓ centralizer ({yG} : Set G) ≤ centralizer ({xG} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2
      ((mem_centralizer_iff.1 (hJ (symm_mem_modelToG e (xab_mem_rootSL2 hij 1)))) w hw)
  have h1 := card_mul_card_le_sq_of_inv hW₁2 hxW hyW hx2 hy3 hxy hCy
  rw [hW₀c, hW₁c] at h1
  rw [hW₁c]
  by_contra hcon
  push Not at hcon
  have hlt : Nat.card (W₁ ⊓ centralizer ({xG} : Set G) : Subgroup G) < 2 ^ 8 := by omega
  have h2 : Nat.card (W₁ ⊓ centralizer ({xG} : Set G) : Subgroup G) ^ 2 < (2 ^ 8) ^ 2 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  omega

omit
  [Finite G] [CharP K 2] hset hW₁c hW₁2 htW₁ hLW htC ht in
theorem xab_not_mem_centralizer_vOne_sixS {i j : Fin 6} (hij : i ≠ j) (hci : c ≠ i)
    (hcj : c ≠ j) :
    ((e.symm (xab hij (1 : K)) : L) : G) ∉
      centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  intro hC
  have hv : ((e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single i (1 : K)))) : L) : G) ∈
      W₁ ⊓ centralizer ({t} : Set G) := by
    rw [hW₁t]
    exact symm_mem_modelToG e (proj_pointRadElem_mem_pointRadical c _)
  have h1 := (mem_centralizer_iff.1 hC) _ hv
  have h2 : e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single i (1 : K)))) *
      e.symm (xab hij 1) =
      e.symm (xab hij 1) * e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single i (1 : K)))) :=
    Subtype.ext h1
  rw [← map_mul, ← map_mul] at h2
  have h3 := e.symm.injective h2
  rw [← proj_pointRadElem_single_eq_xab_sixS hij] at h3
  have h4 := eq_zero_of_proj_pointRadElem_commute_sixS hK hci (s := Pi.single j 1)
    (Pi.single_eq_of_ne hcj 1) (Pi.single_eq_of_ne hij 1) h3.symm
  have h5 := congrFun h4 j
  rw [Pi.single_eq_same, Pi.zero_apply] at h5
  exact one_ne_zero h5

theorem key_sixS
    (hall : ∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX)
    {h : G} (hh : h ∈ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6)))) (hh2 : h * h = 1) :
    Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
      Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  obtain ⟨hV₁card, hWV⟩ := card_vOne_sixS hK e hW₁c hW₁t
  have hroot : ∀ (i j : Fin 6) (hij : i ≠ j), c ≠ i → c ≠ j →
      Nat.card W₁ ≤ 4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hij (1 : K)) : L) : G)} :
        Set G) : Subgroup G) := by
    intro i j hij hci hcj
    obtain ⟨hX₀, hX₀c⟩ := rootTorus_le_and_card_sixS hK hij
    exact root_bound_sixS hset hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hij hci hcj
      (hall i j hij _ hX₀ hX₀c)
  have hxN : ∀ x ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)),
      ((e.symm x : L) : G) ∈ normalizer (W₁ : Set G) := fun x hx => hLW (symm_mem_modelToG e hx)
  have hx2 : ∀ (i j : Fin 6) (hij : i ≠ j),
      ((e.symm (xab hij (1 : K)) : L) : G) * ((e.symm (xab hij (1 : K)) : L) : G) = 1 :=
    fun i j hij => by
      rw [← Subgroup.coe_mul, ← map_mul, xab_mul_self_of_charTwo hij 1, map_one, Subgroup.coe_one]
  obtain ⟨_, ⟨h', hh'B, rfl⟩, rfl⟩ := hh
  change ((e.symm h' : L) : G) * ((e.symm h' : L) : G) = 1 at hh2
  change Nat.card (W₁ ⊓ centralizer ({((e.symm h' : L) : G) * t} : Set G) : Subgroup G) ≤ _
  have hh'2 : h' * h' = 1 := by
    have h1 : e.symm (h' * h') = e.symm 1 := by
      rw [map_mul, map_one]
      exact Subtype.ext hh2
    exact e.symm.injective h1
  have hcard5 : ({c}ᶜ : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  obtain ⟨k, P, g, hgB, hPout, hg⟩ :=
    exists_conj_eq_elt_of_mem_blockSL_mem_sixS (by omega) hh'B hh'2
  set gG : G := ((e.symm g : L) : G) with hgG
  have hgW : gG ∈ normalizer (W₁ : Set G) := hxN g hgB
  have hgt : gG * t = t * gG := hLt gG (e.symm g).2
  have hconj : gG * ((e.symm h' : L) : G) * gG⁻¹ = ((e.symm (P.elt K) : L) : G) := by
    rw [← hg, map_mul, map_mul, map_inv]
    rfl
  rw [← card_inf_centralizer_conj_mul_eq_sixS hgW hgt, hconj]
  have hk : 2 * k ≤ 5 := by
    rw [← InvPlacement.card_outer_sixS P, ← hcard5]
    exact Finset.card_le_card hPout
  have hcout : ∀ m ∈ P.outer, c ≠ m := fun m hm h => by
    have := hPout hm
    rw [← h] at this
    simp at this
  have hcu : ∀ a, c ≠ P.u a := fun a => hcout _ (P.u_mem_outer a)
  have hcw : ∀ a, c ≠ P.w a := fun a => hcout _ (P.w_mem_outer a)
  have hxabB : ∀ a, xab (P.u_ne_w a a) (1 : K) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
    fun a => xab_mem_blockSL _ (by simpa using (hcu a).symm) (by simpa using (hcw a).symm) 1
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  ·
    rw [InvPlacement.elt_eq_one_sixS, map_one, Subgroup.coe_one, one_mul]
  ·
    rw [InvPlacement.elt_eq_xab_sixS]
    exact card_inf_centralizer_mul_le_of_root hW₁2 ht2 htW₁ hWV (hxN _ (hxabB 0))
      (hLt _ (e.symm _).2) (hx2 _ _ _) (hroot _ _ _ (hcu 0) (hcw 0))
      (xab_not_mem_centralizer_vOne_sixS hK e hW₁t _ (hcu 0) (hcw 0))
  ·
    rw [InvPlacement.elt_eq_xab_mul_xab_sixS, map_mul, Subgroup.coe_mul]
    have hu01 : P.u 0 ≠ P.u 1 := P.u_injective.ne (by decide)
    have hw01 : P.w 0 ≠ P.w 1 := P.w_injective.ne (by decide)
    have hdisj : Disjoint ({P.u 0, P.w 0} : Finset (Fin 6)) {P.u 1, P.w 1} := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hu01
      · exact P.u_ne_w 0 1
      · exact (P.u_ne_w 1 0).symm
      · exact hw01
    have hcomm : xab (P.u_ne_w 0 0) (1 : K) * xab (P.u_ne_w 1 1) 1 =
        xab (P.u_ne_w 1 1) 1 * xab (P.u_ne_w 0 0) 1 :=
      (commute_blockSL_of_disjoint hdisj _ (xab_mem_blockSL _ (by simp) (by simp) 1) _
        (xab_mem_blockSL _ (by simp) (by simp) 1)).eq
    have hcommG : ((e.symm (xab (P.u_ne_w 0 0) (1 : K)) : L) : G) *
        ((e.symm (xab (P.u_ne_w 1 1) (1 : K)) : L) : G) =
        ((e.symm (xab (P.u_ne_w 1 1) (1 : K)) : L) : G) *
          ((e.symm (xab (P.u_ne_w 0 0) (1 : K)) : L) : G) := by
      rw [← Subgroup.coe_mul, ← map_mul, hcomm, map_mul, Subgroup.coe_mul]
    have hV : 4 * Nat.card (W₁ ⊓ centralizer ({t} : Set G) ⊓
        centralizer ({((e.symm (xab (P.u_ne_w 0 0) (1 : K)) : L) : G) *
          ((e.symm (xab (P.u_ne_w 1 1) (1 : K)) : L) : G)} : Set G) : Subgroup G) ≤
        Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
      rw [hV₁card]
      set z : LinearFlag.projectiveSL 6 K := xab (P.u_ne_w 0 0) (1 : K) * xab (P.u_ne_w 1 1) 1
        with hz
      have hzG : ((e.symm (xab (P.u_ne_w 0 0) (1 : K)) : L) : G) *
          ((e.symm (xab (P.u_ne_w 1 1) (1 : K)) : L) : G) = ((e.symm z : L) : G) := by
        rw [hz, map_mul, Subgroup.coe_mul]
      have hZ : modelToG e (zpowers z) = zpowers ((e.symm z : L) : G) := by
        rw [modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      have hcen : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({((e.symm z : L) : G)} : Set G) =
          modelToG e (pointRadical c ⊓ centralizer ({z} : Set (LinearFlag.projectiveSL 6 K))) := by
        rw [hW₁t, ← centralizer_zpowers_eq, ← hZ, modelToG_inf_centralizer_eq,
          centralizer_zpowers_eq]
      have hle := pointRadical_inf_centralizer_xab_mul_xab_le_sixS (K := K) hK (P.u_ne_w 0 0)
        (P.u_ne_w 1 1) (P.u_ne_w 0 1) (P.u_ne_w 1 0).symm hw01 (hcu 0) (hcw 0) (hcu 1) (hcw 1)
      rw [← hz] at hle
      have hcS : c ∉ ({c}ᶜ : Finset (Fin 6)) \ {P.u 0, P.u 1} := by simp
      have hcard3 : (({c}ᶜ : Finset (Fin 6)) \ {P.u 0, P.u 1}).card = 3 := by
        have hsub : ({P.u 0, P.u 1} : Finset (Fin 6)) ⊆ {c}ᶜ := by
          intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · simpa using (hcu 0).symm
          · simpa using (hcu 1).symm
        rw [Finset.card_sdiff_of_subset hsub, hcard5, Finset.card_pair hu01]
      rw [hzG, hcen, natCard_modelToG_eq]
      have h8 := Subgroup.card_le_of_le hle
      rw [card_pointRadOn hK c hcS, hcard3] at h8
      omega
    exact card_inf_centralizer_mul_mul_le_of_root_pair_sixS hW₁2 ht2 htW₁ hWV (hxN _ (hxabB 0))
      (hxN _ (hxabB 1)) (hLt _ (e.symm _).2) (hLt _ (e.symm _).2) hcommG (hx2 _ _ _) (hx2 _ _ _)
      (hroot _ _ _ (hcu 0) (hcw 0)) (hroot _ _ _ (hcu 1) (hcw 1)) hV

end Root

end CFSG.SeitzReduction.LinearPilot
