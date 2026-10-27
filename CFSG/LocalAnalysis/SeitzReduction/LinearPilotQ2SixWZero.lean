module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

section Model

variable {n : ℕ} {K : Type*} [Field K]

theorem vecMul_pointRadMat (i : Fin n) (r s : Fin n → K) :
    r ᵥ* pointRadMat i s = r + r i • Function.update s i 0 := by
  rw [pointRadMat, vecMul_add, vecMul_one, vecMul_vecMulVec, dotProduct_single, mul_one]

@[expose] def singerThree (d₁ d₂ d₃ : Fin n) : SpecialLinearGroup (Fin n) K :=
  pointRadElem d₁ (Pi.single d₂ 1) * pointRadElem d₂ (Pi.single d₃ 1) *
    pointRadElem d₃ (Pi.single d₁ 1)

theorem pointRadElem_single_mem_blockSpecialLinear (i j : Fin n) :
    pointRadElem (K := K) i (Pi.single j 1) ∈ blockSpecialLinear {i, j} :=
  pointRadSL_le_blockSpecialLinear i {j}
    ⟨Pi.single j 1, fun k hk => Pi.single_eq_of_ne (by simpa using hk) 1, rfl⟩

theorem singerThree_mem_blockSpecialLinear (d₁ d₂ d₃ : Fin n) :
    singerThree (K := K) d₁ d₂ d₃ ∈ blockSpecialLinear {d₁, d₂, d₃} := by
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact blockSpecialLinear_mono (by intro j; simp; tauto)
      (pointRadElem_single_mem_blockSpecialLinear d₁ d₂)
  · exact blockSpecialLinear_mono (by intro j; simp; tauto)
      (pointRadElem_single_mem_blockSpecialLinear d₂ d₃)
  · exact blockSpecialLinear_mono (by intro j; simp; tauto)
      (pointRadElem_single_mem_blockSpecialLinear d₃ d₁)

theorem eq_zero_of_vecMul_singerThree_apply {d₁ d₂ d₃ : Fin n} (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃)
    (h23 : d₂ ≠ d₃) {r : Fin n → K} (hr : ∀ j, j ≠ d₁ → j ≠ d₂ → j ≠ d₃ → r j = 0)
    (h1 : (r ᵥ* ((singerThree d₁ d₂ d₃ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) d₁ = r d₁)
    (h2 : (r ᵥ* ((singerThree d₁ d₂ d₃ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) d₂ = r d₂)
    (h3 : (r ᵥ* ((singerThree d₁ d₂ d₃ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) d₃ = r d₃) : r = 0 := by
  have hu : ∀ {i j : Fin n}, i ≠ j →
      Function.update (Pi.single j (1 : K) : Fin n → K) i 0 = Pi.single j 1 := fun {i j} hij =>
    Function.update_eq_self_iff.2 (Pi.single_eq_of_ne (M := fun _ => K) hij (1 : K)).symm
  have hB : ((singerThree d₁ d₂ d₃ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      pointRadMat d₁ (Pi.single d₂ 1) * pointRadMat d₂ (Pi.single d₃ 1) *
        pointRadMat d₃ (Pi.single d₁ 1) := rfl
  rw [hB, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_pointRadMat, vecMul_pointRadMat,
    vecMul_pointRadMat, hu h12, hu h23, hu (Ne.symm h13)] at h1 h2 h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h12, h13, h23,
    Ne.symm h12, Ne.symm h13, Ne.symm h23, ite_true, ite_false, mul_one, mul_zero,
    add_zero] at h1 h2 h3
  have e1 : r d₁ = 0 := by linear_combination h2
  have e2 : r d₂ = 0 := by linear_combination h3 - e1
  have e3 : r d₃ = 0 := by linear_combination h1 - e1 - e2
  funext j
  by_cases hj1 : j = d₁
  · rw [hj1, e1]; rfl
  by_cases hj2 : j = d₂
  · rw [hj2, e2]; rfl
  by_cases hj3 : j = d₃
  · rw [hj3, e3]; rfl
  exact hr j hj1 hj2 hj3

theorem pointRadOn_inf_centralizer_singerThree (hK : Nat.card K = 2) {c d₁ d₂ d₃ : Fin n}
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) (hc1 : c ≠ d₁) (hc2 : c ≠ d₂) (hc3 : c ≠ d₃) :
    pointRadOn (K := K) c {d₁, d₂, d₃} ⊓
      centralizer ((zpowers (LinearFlag.proj n K (singerThree d₁ d₂ d₃)) :
        Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hvc⟩
  obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hv
  set B := singerThree (K := K) d₁ d₂ d₃ with hBdef
  have hcomm : LinearFlag.proj n K B * LinearFlag.proj n K (pointRadElem c r) =
      LinearFlag.proj n K (pointRadElem c r) * LinearFlag.proj n K B :=
    (mem_centralizer_iff.1 hvc) _ (mem_zpowers _)
  have hsub : ({d₁, d₂, d₃} : Finset (Fin n)) ⊆ {c}ᶜ := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    simp only [Finset.mem_compl, Finset.mem_singleton]
    rcases hj with rfl | rfl | rfl
    · exact Ne.symm hc1
    · exact Ne.symm hc2
    · exact Ne.symm hc3
  have hBmem : B ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin n)) :=
    blockSpecialLinear_mono hsub (singerThree_mem_blockSpecialLinear d₁ d₂ d₃)
  have hconj : B⁻¹ * pointRadElem c r * B = pointRadElem c r := by
    apply proj_injective_of_natCard_eq_two (n := n) hK
    rw [map_mul, map_mul, map_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hformula := conj_pointRadElem_of_mem_blockSpecialLinear (inv_mem hBmem) r
  rw [inv_inv, hconj] at hformula
  have hrc : r c = 0 := hr c (by simp [hc1, hc2, hc3])
  have h' := update_eq_update_of_pointRadElem_eq hformula
  have hev : ∀ j, j ≠ c →
      (r ᵥ* ((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) j = r j := by
    intro j hj
    have h2 := congrFun h' j
    rw [Function.update_of_ne hj, Function.update_of_ne hj,
      Function.update_eq_self_iff.2 hrc.symm] at h2
    exact h2.symm
  have hr0 : r = 0 := eq_zero_of_vecMul_singerThree_apply h12 h13 h23
    (fun j hj1 hj2 hj3 => hr j (by simp [hj1, hj2, hj3])) (hev d₁ (Ne.symm hc1))
    (hev d₂ (Ne.symm hc2)) (hev d₃ (Ne.symm hc3))
  rw [Subgroup.mem_bot, hr0, pointRadElem_zero, map_one]

end Model

section Wzero

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_wZero_lSix (hW : LinearTwoWOneAtInput 6) (hset : SeitzSetting G L) {K : Type}
    [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin 6} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    ∃ W₀ : Subgroup G, Nat.card W₀ = 2 ^ 6 ∧ (∀ w ∈ W₀, w * w = 1) ∧
      W₀ ≤ centralizer (modelToG e X₀ : Set G) ∧ t ∈ normalizer (W₀ : Set G) ∧
      W₀ ⊓ centralizer ({t} : Set G) ≤
        modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)) ∧
      Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 3 ∧
      ∃ y ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)),
        y ∈ normalizer (W₀ : Set G) ∧ W₀ ⊓ centralizer ({y} : Set G) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard4 : (({a, b} : Finset (Fin 6))ᶜ).card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨c, hc⟩ : (({a, b} : Finset (Fin 6))ᶜ).Nonempty := Finset.card_pos.1 (by omega)
  have hca : c ≠ a := fun h => by simp [h] at hc
  have hcb : c ≠ b := fun h => by simp [h] at hc
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htW₁, hLW₁⟩ := hW G L hset K hK e t ht hKt c
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hcsub : ({a, b} : Finset (Fin 6)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact (Finset.mem_compl.1 hc) hj
  obtain ⟨x, hxX, -, -, -, hx1, hxm, -⟩ := exists_lift_torusQ1 hX₀ hX₀c
  rw [hK] at hxm
  have hX₀z : X₀ = zpowers x :=
    eq_zpowers_of_card_eq_prime (p := 3) (by rw [hX₀c, hK]) hxX hx1 hxm
  set xG : G := ((e.symm x : L) : G) with hxG
  have hXz : modelToG e X₀ = zpowers xG := by
    rw [hX₀z, modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCX : centralizer (modelToG e X₀ : Set G) = centralizer ({xG} : Set G) := by
    rw [hXz, centralizer_zpowers_eq]
  have hxB : x ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
    blockSL_mono hcsub (by rw [← rootSL2_eq]; exact hX₀ hxX)
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW₁ (symm_mem_modelToG e hxB)
  have hxt : xG * t = t * xG := hLt xG (e.symm x).2
  have hx3G : xG ^ 3 = 1 := by
    rw [hxG, ← Subgroup.coe_pow, ← map_pow, hxm, map_one, Subgroup.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 6)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 5 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ (by rw [hW₁c, hV₁card]; norm_num)
  set S₀ : Finset (Fin 6) := ({c}ᶜ : Finset (Fin 6)) \ {a, b} with hS₀
  have hS₀card : S₀.card = 3 := by
    rw [hS₀, Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hab]
  have hcS₀ : c ∉ S₀ := fun h => hcc (Finset.mem_sdiff.1 h).1
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c S₀) := by
    rw [hW₁t, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hab hca hcb _ hX₀ hX₀c]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c S₀)) = 2 ^ 3 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c hcS₀, hS₀card]
  have hS₀sub : insert c S₀ ⊆ ({a, b} : Finset (Fin 6))ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact Finset.mem_compl.1 hc
    · exact (Finset.mem_sdiff.1 hj).2
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
  have hyD : yG ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono ((Finset.subset_insert c S₀).trans hS₀sub) hyS₀)
  have hyN : yG ∈ normalizer (W₁ : Set G) :=
    hLW₁ (symm_mem_modelToG e (blockSL_mono (fun j hj => (Finset.mem_sdiff.1 hj).1) hyS₀))
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hyx : yG * xG = xG * yG := by
    have hdisj : Disjoint S₀ ({a, b} : Finset (Fin 6)) := Finset.sdiff_disjoint
    have h := (commute_blockSL_of_disjoint hdisj y hyS₀ x (by rw [← rootSL2_eq]; exact hX₀ hxX)).eq
    have h' : e.symm y * e.symm x = e.symm x * e.symm y := by rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  refine ⟨W₁ ⊓ centralizer ({xG} : Set G), ?_, fun w hw => hW₁2 w (Subgroup.mem_inf.1 hw).1,
    hCX ▸ inf_le_right, mem_normalizer_inf_centralizer htW₁ hxt.symm, ?_, ?_, yG, hyD,
    mem_normalizer_inf_centralizer hyN hyx, ?_⟩
  · rw [card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hxN hxt hx3G, hV₀, hV₀card]
    norm_num
  · rw [inf_right_comm, hV₀]
    exact modelToG_mono e ((pointRadOn_le_blockSL c S₀).trans (blockSL_mono hS₀sub))
  · rw [inf_right_comm, hV₀, hV₀card]
  · refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hxt hyt ?_
    rw [hV₀, ← hCY, modelToG_inf_centralizer_eq, hS₀eq,
      pointRadOn_inf_centralizer_singerThree hK h12 h13 h23 hc1 hc2 hc3, modelToG,
      Subgroup.map_bot, Subgroup.map_bot]

end Wzero

section Layer

variable {G : Type} [Group G] [Finite G]

theorem map_le_of_normal_of_inf_centralizer_eq_bot {H W₀ : Subgroup G} {M : Subgroup H}
    [M.Normal] {y : G} (hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v) (hW₀H : W₀ ≤ H) (hyH : y ∈ H)
    (hyW₀ : y ∈ normalizer (W₀ : Set G)) (hW₀y : W₀ ⊓ centralizer ({y} : Set G) = ⊥)
    {N : Subgroup (H ⧸ M)} (hN : N.Normal) (hyN : QuotientGroup.mk' M ⟨y, hyH⟩ ∈ N) :
    (W₀.subgroupOf H).map (QuotientGroup.mk' M) ≤ N := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨w', hw', hw'eq⟩ :=
    exists_commutator_eq_of_inf_centralizer_eq_bot hWc hyW₀ hW₀y (mem_subgroupOf.1 hw)
  have hw'H : w' ∈ H := hW₀H hw'
  have hweq : w = ⟨w', hw'H⟩ * ⟨y, hyH⟩ * ⟨w', hw'H⟩⁻¹ * ⟨y, hyH⟩⁻¹ :=
    Subtype.ext hw'eq.symm
  rw [hweq, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact N.mul_mem (hN.conj_mem _ hyN _) (N.inv_mem hyN)

variable {L : Subgroup G}

theorem map_wZero_le_of_normal_lSix (hW : LinearTwoWOneAtInput 6) (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {a b : Fin 6}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    ∃ W₀ : Subgroup G, Nat.card W₀ = 2 ^ 6 ∧ (∀ w ∈ W₀, w * w = 1) ∧
      W₀ ≤ centralizer (modelToG e X₀ : Set G) ∧ t ∈ normalizer (W₀ : Set G) ∧
      W₀ ⊓ centralizer ({t} : Set G) ≤
        modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)) ∧
      Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 3 ∧
      Nat.card ((W₀.subgroupOf (centralizer (modelToG e X₀ : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = 2 ^ 6 ∧
      ∀ N : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
          oddCore (centralizer (modelToG e X₀ : Set G))), N.Normal →
        ((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ N →
        (W₀.subgroupOf (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ N := by
  obtain ⟨W₀, hW₀c, hW₀2, hW₀X, htW₀, hV₀D, hV₀c, y, hyD, hyW₀, hW₀y⟩ :=
    exists_wZero_lSix hW hset hK e ht hKt hab hX₀ hX₀c
  have hDX : modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)) ≤
      centralizer (modelToG e X₀ : Set G) := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := (mem_modelToG e).1 hd
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
    have h := (mem_centralizer_iff.1 (blockSL_compl_le_centralizer hX₀ hd₀)) x hx
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, h]
  have hyH : y ∈ centralizer (modelToG e X₀ : Set G) := hDX hyD
  have hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₀2 hv hw
  refine ⟨W₀, hW₀c, hW₀2, hW₀X, htW₀, hV₀D, hV₀c, ?_, fun N hN hDN => ?_⟩
  · rw [card_map_mk_oddCore_of_mul_self (fun x hx => Subtype.ext (hW₀2 _ (mem_subgroupOf.1 hx))),
      Nat.card_congr (subgroupOfEquivOfLe hW₀X).toEquiv, hW₀c]
  · exact map_le_of_normal_of_inf_centralizer_eq_bot hWc hW₀X hyH hyW₀ hW₀y hN
      (hDN ⟨⟨y, hyH⟩, mem_subgroupOf.2 hyD, rfl⟩)

end Layer

end CFSG.SeitzReduction.LinearPilot
