module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePRad
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSAbs

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

theorem modelToG_zpowers (x : LinearFlag.projectiveSL n K) :
    modelToG e (zpowers x) = zpowers ((e.symm x : L) : G) := by
  rw [modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem modelToG_inf_centralizer_singleton (A : Subgroup (LinearFlag.projectiveSL n K))
    (x : LinearFlag.projectiveSL n K) :
    modelToG e A ⊓ centralizer ({((e.symm x : L) : G)} : Set G) =
      modelToG e (A ⊓ centralizer ({x} : Set (LinearFlag.projectiveSL n K))) := by
  rw [← centralizer_zpowers_eq, ← modelToG_zpowers, modelToG_inf_centralizer_eq,
    centralizer_zpowers_eq]

theorem coe_symm_mul (x y : LinearFlag.projectiveSL n K) :
    ((e.symm (x * y) : L) : G) = ((e.symm x : L) : G) * ((e.symm y : L) : G) := by
  rw [map_mul, Subgroup.coe_mul]

end Transport

theorem eq_zpowers_xab_mul_xab_symm {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    X₀ = zpowers (xab hab (1 : K) * xab hab.symm 1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set y : LinearFlag.projectiveSL n K := xab hab (1 : K) * xab hab.symm 1 with hy
  have hyR : y ∈ rootSL2 a b := xab_mul_xab_symm_mem_rootSL2 hab 1 1
  have hy3 : orderOf y = 3 := orderOf_xab_mul_xab_symm hn hab
  have hR := card_rootSL2_two hK hn hab
  have hidx : (X₀.subgroupOf (rootSL2 (K := K) a b)).index = 2 := by
    have h1 := Subgroup.card_mul_index (X₀.subgroupOf (rootSL2 (K := K) a b))
    rw [Nat.card_congr (X₀.subgroupOfEquivOfLe hX₀).toEquiv, hX₀c, hK, hR] at h1
    omega
  have hy2 : y ^ 2 ∈ X₀ := by
    have h1 := Subgroup.sq_mem_of_index_two hidx ⟨y, hyR⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hyX : y ∈ X₀ := by
    have h1 : y ^ 2 * y = 1 := by
      rw [← pow_succ, show 2 + 1 = orderOf y from hy3.symm, pow_orderOf_eq_one]
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem hy2
  refine (Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hyX) ?_).symm
  rw [hX₀c, Nat.card_zpowers, hy3, hK]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem wZero_data_five {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {c : Fin 5} {W₁ : Subgroup G}
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {p q r s : Fin 5} (hpq : p ≠ q) (hrs : r ≠ s) (hcp : c ≠ p) (hcq : c ≠ q)
    (hS : ({c}ᶜ : Finset (Fin 5)) \ {p, q} = {r, s}) :
    Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} :
        Set G) : Subgroup G) = 2 ^ 4 ∧
      W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} : Set G) ⊓
        centralizer ({t} : Set G) = modelToG e (pointRadOn c {r, s}) ∧
      (((e.symm (xab hpq (1 : K)) : L) : G) ∈
          centralizer ((W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} :
            Set G) : Subgroup G) : Set G) →
        Nat.card W₁ ≤
          4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K)) : L) : G)} : Set G) :
            Subgroup G)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hrS : r ∈ ({c}ᶜ : Finset (Fin 5)) \ {p, q} := by rw [hS]; simp
  have hsS : s ∈ ({c}ᶜ : Finset (Fin 5)) \ {p, q} := by rw [hS]; simp
  have hcr : c ≠ r := fun h => by simp [← h] at hrS
  have hcs : c ≠ s := fun h => by simp [← h] at hsS
  have hpqc : ({p, q} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    rcases Finset.mem_insert.1 hj with h | h
    · exact hcp h
    · exact hcq (Finset.mem_singleton.1 h)
  set y : LinearFlag.projectiveSL 5 K := xab hpq (1 : K) * xab hpq.symm 1 with hy
  have hyR : y ∈ rootSL2 p q := xab_mul_xab_symm_mem_rootSL2 hpq 1 1
  have hy3 : orderOf y = 3 := orderOf_xab_mul_xab_symm (by norm_num) hpq
  have hX₀ : zpowers y ≤ rootSL2 p q := (zpowers_le).2 hyR
  have hX₀c : Nat.card (zpowers y) = Nat.card K + 1 := by rw [Nat.card_zpowers, hy3, hK]
  set yG : G := ((e.symm y : L) : G) with hyG
  have hyB : y ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    blockSL_mono hpqc (by rw [← rootSL2_eq]; exact hyR)
  have hyN : yG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hyB)
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hy3G : yG ^ 3 = 1 := by
    rw [hyG, ← Subgroup.coe_pow, ← map_pow, ← hy3, pow_orderOf_eq_one, map_one,
      Subgroup.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ (by rw [hW₁c, hV₁card]; norm_num)
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({yG} : Set G) =
      modelToG e (pointRadOn c {r, s}) := by
    rw [hW₁t, hyG, modelToG_inf_centralizer_singleton, ← centralizer_zpowers_eq, pointRadical,
      pointRadOn_inf_centralizer hpq hcp hcq _ hX₀ hX₀c, hS]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c {r, s})) = 2 ^ 2 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c (by simp [hcr, hcs]), Finset.card_pair hrs]
  have hW₀c : Nat.card (W₁ ⊓ centralizer ({yG} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hyN hyt hy3G, hV₀, hV₀card]
    norm_num
  refine ⟨hW₀c, by rw [inf_right_comm, hV₀], fun hj => ?_⟩
  set xG : G := ((e.symm (xab hpq (1 : K)) : L) : G) with hxG
  set x'G : G := ((e.symm (xab hpq.symm (1 : K)) : L) : G) with hx'G
  have hxB : xab hpq (1 : K) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    xab_mem_blockSL hpq (hpqc (by simp)) (hpqc (by simp)) 1
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
  have hx2 : xG * xG = 1 := by
    rw [hxG, ← Subgroup.coe_mul, ← map_mul, ← xab_add, CharTwo.add_self_eq_zero, xab_zero,
      map_one, Subgroup.coe_one]
  have hx'2 : x'G * x'G = 1 := by
    rw [hx'G, ← Subgroup.coe_mul, ← map_mul, ← xab_add, CharTwo.add_self_eq_zero, xab_zero,
      map_one, Subgroup.coe_one]
  have hyx : yG = xG * x'G := by rw [hyG, hy, coe_symm_mul]
  have hxi : xG⁻¹ = xG := inv_eq_of_mul_eq_one_right hx2
  have hx'i : x'G⁻¹ = x'G := inv_eq_of_mul_eq_one_right hx'2
  have hxy : xG * yG * xG⁻¹ = yG⁻¹ := by
    rw [hyx, mul_inv_rev, hxi, hx'i, ← mul_assoc, hx2, one_mul]
  have hCy : W₁ ⊓ centralizer ({yG} : Set G) ≤ centralizer ({xG} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hj) w hw
  have h2 := card_mul_card_le_sq_of_inv hW₁2 hxN hyN hx2 hy3G hxy hCy
  rw [hW₁c, hW₀c] at h2
  rw [hW₁c]
  by_contra hlt
  have h3 : Nat.card (W₁ ⊓ centralizer ({xG} : Set G) : Subgroup G) ≤ 63 := by omega
  have h4 := Nat.pow_le_pow_left h3 2
  omega

theorem root_data_five (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G))
    (hcore : ∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      modelToG e (rootSL2 (K := K) a b) ≤
        centralizer (centralizerPerfectCore (modelToG e X₀) : Set G))
    {c : Fin 5} {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {p q r s : Fin 5} (hpq : p ≠ q) (hrs : r ≠ s) (hcp : c ≠ p) (hcq : c ≠ q)
    (hS : ({c}ᶜ : Finset (Fin 5)) \ {p, q} = {r, s}) :
    modelToG e (rootSL2 (K := K) p q) ≤
        centralizer ((W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} :
          Set G) : Subgroup G) : Set G) ∧
      Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} :
        Set G) : Subgroup G) = 2 ^ 4 ∧
      Nat.card W₁ ≤
        4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K)) : L) : G)} : Set G) :
          Subgroup G) ∧
      W₁ ⊓ centralizer ({((e.symm (xab hpq (1 : K) * xab hpq.symm 1) : L) : G)} : Set G) ⊓
        centralizer ({t} : Set G) = modelToG e (pointRadOn c {r, s}) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  obtain ⟨hW₀c, hV₀, hroot⟩ := wZero_data_five hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hpq hrs hcp hcq
    hS
  have hrS : r ∈ ({c}ᶜ : Finset (Fin 5)) \ {p, q} := by rw [hS]; simp
  have hsS : s ∈ ({c}ᶜ : Finset (Fin 5)) \ {p, q} := by rw [hS]; simp
  have hcr : c ≠ r := fun h => by simp [← h] at hrS
  have hcs : c ≠ s := fun h => by simp [← h] at hsS
  have hrsc : ({r, s} : Finset (Fin 5)) ⊆ {c}ᶜ := by rw [← hS]; exact Finset.sdiff_subset
  have hrspq : ({r, s} : Finset (Fin 5)) ⊆ ({p, q} : Finset (Fin 5))ᶜ := by
    intro j hj
    rw [← hS] at hj
    exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2
  have hdisj : Disjoint ({r, s} : Finset (Fin 5)) ({p, q} : Finset (Fin 5)) :=
    Finset.disjoint_left.2 fun j hj hj' => (Finset.mem_compl.1 (hrspq hj)) hj'
  set y : LinearFlag.projectiveSL 5 K := xab hpq (1 : K) * xab hpq.symm 1 with hy
  set y' : LinearFlag.projectiveSL 5 K := xab hrs (1 : K) * xab hrs.symm 1 with hy'
  have hyR : y ∈ rootSL2 p q := xab_mul_xab_symm_mem_rootSL2 hpq 1 1
  have hy'R : y' ∈ rootSL2 r s := xab_mul_xab_symm_mem_rootSL2 hrs 1 1
  have hy3 : orderOf y = 3 := orderOf_xab_mul_xab_symm (by norm_num) hpq
  have hy'3 : orderOf y' = 3 := orderOf_xab_mul_xab_symm (by norm_num) hrs
  have hX₀ : zpowers y ≤ rootSL2 p q := (zpowers_le).2 hyR
  have hX₀c : Nat.card (zpowers y) = Nat.card K + 1 := by rw [Nat.card_zpowers, hy3, hK]
  have hY₀ : zpowers y' ≤ rootSL2 r s := (zpowers_le).2 hy'R
  have hY₀c : Nat.card (zpowers y') = Nat.card K + 1 := by rw [Nat.card_zpowers, hy'3, hK]
  set yG : G := ((e.symm y : L) : G) with hyG
  set y'G : G := ((e.symm y' : L) : G) with hy'G
  have hCX : centralizer (modelToG e (zpowers y) : Set G) = centralizer ({yG} : Set G) := by
    rw [modelToG_zpowers, centralizer_zpowers_eq]
  have hy'B : y' ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    blockSL_mono hrsc (by rw [← rootSL2_eq]; exact hy'R)
  have hy'N : y'G ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hy'B)
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hy't : y'G * t = t * y'G := hLt y'G (e.symm y').2
  have hyy' : y'G * yG = yG * y'G := by
    have h := (commute_blockSL_of_disjoint hdisj y' (by rw [← rootSL2_eq]; exact hy'R) y
      (by rw [← rootSL2_eq]; exact hyR)).eq
    have h' : e.symm y' * e.symm y = e.symm y * e.symm y' := by rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  have hy'W₀ : y'G ∈ normalizer ((W₁ ⊓ centralizer ({yG} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_centralizer hy'N hyy'
  have hy'0 : W₁ ⊓ centralizer ({yG} : Set G) ⊓ centralizer ({y'G} : Set G) = ⊥ := by
    refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hyt hy't ?_
    rw [show W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({yG} : Set G) =
        W₁ ⊓ centralizer ({yG} : Set G) ⊓ centralizer ({t} : Set G) from inf_right_comm _ _ _,
      hV₀, hy'G, modelToG_inf_centralizer_singleton, ← centralizer_zpowers_eq,
      pointRadOn_inf_centralizer hrs hcr hcs _ hY₀ hY₀c, Finset.sdiff_self, pointRadOn_empty,
      modelToG, Subgroup.map_bot, Subgroup.map_bot]
  have htX : t ∈ centralizer (modelToG e (zpowers y) : Set G) :=
    centralizer_le (modelToG_le e _) htC
  obtain ⟨-, hDX, hDq, -⟩ := neighbour_hyps_linear_two hset hK e (by norm_num) htC ht hpq hX₀
    hX₀c rfl htX rfl
  have hDE : modelToG e (blockSL (K := K) (({p, q} : Finset (Fin 5))ᶜ)) ≤
      centralizerPerfectCore (modelToG e (zpowers y)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDX (Subgroup.isPerfect_iff.mp hDq.1)
  have hy'D : y'G ∈ modelToG e (blockSL (K := K) (({p, q} : Finset (Fin 5))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono hrspq (by rw [← rootSL2_eq]; exact hy'R))
  have hWc : ∀ v ∈ W₁ ⊓ centralizer ({yG} : Set G), ∀ w ∈ W₁ ⊓ centralizer ({yG} : Set G),
      v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 (Subgroup.mem_inf.1 hv).1 (Subgroup.mem_inf.1 hw).1
  have hW₀X : W₁ ⊓ centralizer ({yG} : Set G) ≤ centralizer (modelToG e (zpowers y) : Set G) := by
    rw [hCX]; exact inf_le_right
  have hW₀E := le_centralizerPerfectCore_of_inf_centralizer_eq_bot hWc hW₀X (hDE hy'D) hy'W₀ hy'0
  have h1 : modelToG e (rootSL2 (K := K) p q) ≤
      centralizer ((W₁ ⊓ centralizer ({yG} : Set G) : Subgroup G) : Set G) :=
    (hcore p q hpq _ hX₀ hX₀c).trans (centralizer_le hW₀E)
  exact ⟨h1, hW₀c, hroot (h1 (symm_mem_modelToG e (xab_mem_rootSL2 hpq 1))), hV₀⟩

end CFSG.SeitzReduction.LinearPilot
