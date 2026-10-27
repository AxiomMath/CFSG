module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSFactor
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

theorem xab_mul_proj_pointRadElem_ne {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) {c d d' : Fin n} (hdd' : d ≠ d') (hcd : c ≠ d) (hcd' : c ≠ d') :
    xab hdd' (1 : K) * LinearFlag.proj n K (pointRadElem c (Pi.single d 1)) ≠
      LinearFlag.proj n K (pointRadElem c (Pi.single d 1)) * xab hdd' 1 := by
  intro h
  rw [xab, ← map_mul, ← map_mul] at h
  have h1 := proj_injective_of_natCard_eq_two hK h
  have h3 : ((SpecialLinearGroup.transvection hdd' (1 : K) * pointRadElem c (Pi.single d 1) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c d' =
      ((pointRadElem c (Pi.single d 1) * SpecialLinearGroup.transvection hdd' 1 :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c d' := by rw [h1]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_pointRadElem] at h3
  change ((1 + single d d' (1 : K) : Matrix (Fin n) (Fin n) K) *
      pointRadMat c (Pi.single d (1 : K))) c d' =
    (pointRadMat c (Pi.single d (1 : K)) * (1 + single d d' (1 : K) : Matrix (Fin n) (Fin n) K))
      c d' at h3
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
    Matrix.add_apply] at h3
  simp [pointRadMat_apply, hcd, hcd'] at h3
  exact hcd h3.symm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem swapPart_five_of_swap
    (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (c : Fin 5)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {a b d d' : Fin 5} (hab : a ≠ b) (hdd' : d ≠ d') (hca : c ≠ a) (hcb : c ≠ b)
    (hS : ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'})
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (hswap : ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) :
    ∃ A X : Subgroup G,
      A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      (∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) ∧
      t ∈ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
      W₁ ⊓ centralizer (modelToG e X₀ : Set G) ⊓ A ≠ ⊥ ∧
      zpowers ((e.symm (xab hdd' 1) : L) : G) ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom ∧
      zpowers ((e.symm (xab hdd' 1) : L) : G) ≤
        normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
      IsPGroup 2 X ∧ X ≤ A ∧
      X ≤ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
      X ⊓ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) ⊓ A : Subgroup G) : Set G) = ⊥ ∧
      4 < 2 * Nat.card X ^ 2 ∧
      W₁ ⊓ centralizer (modelToG e X₀ : Set G) ⊓ centralizer ({t} : Set G) =
        modelToG e (pointRadOn c {d, d'}) ∧
      Nat.card (W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) = 2 ^ 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hcsub : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    rcases Finset.mem_insert.1 hj with h | h
    · exact hca h
    · exact hcb (Finset.mem_singleton.1 h)
  have hdS : d ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hd'S : d' ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hcd : c ≠ d := fun h => by simp [← h] at hdS
  have hcd' : c ≠ d' := fun h => by simp [← h] at hd'S
  have hdab : d ∉ ({a, b} : Finset (Fin 5)) := (Finset.mem_sdiff.1 hdS).2
  have hd'ab : d' ∉ ({a, b} : Finset (Fin 5)) := (Finset.mem_sdiff.1 hd'S).2
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
  have hxB : x ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    blockSL_mono hcsub (by rw [← rootSL2_eq]; exact hX₀ hxX)
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
  have hxt : xG * t = t * xG := hLt xG (e.symm x).2
  have hx3G : xG ^ 3 = 1 := by
    rw [hxG, ← Subgroup.coe_pow, ← map_pow, hxm, map_one, Subgroup.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ (by rw [hW₁c, hV₁card]; norm_num)
  have hcS₀ : c ∉ ({d, d'} : Finset (Fin 5)) := by simp [hcd, hcd']
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c {d, d'}) := by
    rw [hW₁t, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hab hca hcb _ hX₀ hX₀c, hS]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c {d, d'})) = 2 ^ 2 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c hcS₀, Finset.card_pair hdd']
  set W₀ : Subgroup G := W₁ ⊓ centralizer (modelToG e X₀ : Set G) with hW₀
  have hW₀' : W₀ = W₁ ⊓ centralizer ({xG} : Set G) := by rw [hW₀, hCX]
  have hW₀2 : ∀ w ∈ W₀, w * w = 1 := fun w hw => hW₁2 w (Subgroup.mem_inf.1 hw).1
  have hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₀2 hv hw
  have hW₀c : Nat.card W₀ = 2 ^ 4 := by
    rw [hW₀', card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hxN hxt hx3G, hV₀, hV₀card]
    norm_num
  have hW₀X : W₀ ≤ centralizer (modelToG e X₀ : Set G) := inf_le_right
  have htW₀ : t ∈ normalizer (W₀ : Set G) := by
    rw [hW₀']; exact mem_normalizer_inf_centralizer htW₁ hxt.symm
  have hV₀' : W₀ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadOn c {d, d'}) := by
    rw [hW₀', inf_right_comm, hV₀]
  obtain ⟨Y₀, hY₀, -, hY₀c⟩ := exists_torusQ1 (K := K) (n := 5) hdd'
  obtain ⟨y, hyY, -, -, -, hy1, hym, -⟩ := exists_lift_torusQ1 hY₀ hY₀c
  rw [hK] at hym
  have hY₀z : Y₀ = zpowers y :=
    eq_zpowers_of_card_eq_prime (p := 3) (by rw [hY₀c, hK]) hyY hy1 hym
  set yG : G := ((e.symm y : L) : G) with hyG
  have hYz : modelToG e Y₀ = zpowers yG := by
    rw [hY₀z, modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCY : centralizer (modelToG e Y₀ : Set G) = centralizer ({yG} : Set G) := by
    rw [hYz, centralizer_zpowers_eq]
  have hyS₀ : y ∈ blockSL (K := K) {d, d'} := by
    rw [← rootSL2_eq]
    exact hY₀ hyY
  have hdd'sub : ({d, d'} : Finset (Fin 5)) ⊆ ({a, b} : Finset (Fin 5))ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · exact hdab
    · rw [Finset.mem_singleton.1 hj']; exact hd'ab
  have hdd'c : ({d, d'} : Finset (Fin 5)) ⊆ ({c}ᶜ : Finset (Fin 5)) := by
    rw [← hS]; exact Finset.sdiff_subset
  have hyD : yG ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono hdd'sub hyS₀)
  have hyN : yG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e (blockSL_mono hdd'c hyS₀))
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hdisj : Disjoint ({d, d'} : Finset (Fin 5)) ({a, b} : Finset (Fin 5)) :=
    Finset.disjoint_left.2 fun j hj hj' => (Finset.mem_compl.1 (hdd'sub hj)) hj'
  have hyx : yG * xG = xG * yG := by
    have h := (commute_blockSL_of_disjoint hdisj y hyS₀ x
      (by rw [← rootSL2_eq]; exact hX₀ hxX)).eq
    have h' : e.symm y * e.symm x = e.symm x * e.symm y := by rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  have hyW₀ : yG ∈ normalizer (W₀ : Set G) := by
    rw [hW₀']; exact mem_normalizer_inf_centralizer hyN hyx
  have hy0 : W₀ ⊓ centralizer ({yG} : Set G) = ⊥ := by
    rw [hW₀']
    refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hxt hyt ?_
    rw [hV₀, ← hCY, modelToG_inf_centralizer_eq, pointRadOn_inf_centralizer hdd' hcd hcd' _ hY₀
      hY₀c, Finset.sdiff_self, pointRadOn_empty, modelToG, Subgroup.map_bot, Subgroup.map_bot]
  set uG : G := ((e.symm (xab hdd' 1) : L) : G) with huG
  have hu_dd' : xab hdd' (1 : K) ∈ blockSL (K := K) {d, d'} :=
    xab_mem_blockSL hdd' (by simp) (by simp) 1
  have huD : uG ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono hdd'sub hu_dd')
  have huN : uG ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e (blockSL_mono hdd'c hu_dd'))
  have hut : uG * t = t * uG := hLt uG (e.symm (xab hdd' 1)).2
  have hux : uG * xG = xG * uG := by
    have h := (commute_blockSL_of_disjoint hdisj (xab hdd' 1) hu_dd' x
      (by rw [← rootSL2_eq]; exact hX₀ hxX)).eq
    have h' : e.symm (xab hdd' 1) * e.symm x = e.symm x * e.symm (xab hdd' 1) := by
      rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  have huW₀ : uG ∈ normalizer (W₀ : Set G) := by
    rw [hW₀']; exact mem_normalizer_inf_centralizer huN hux
  have hu2 : uG * uG = 1 := by
    rw [huG, ← Subgroup.coe_mul, ← map_mul, xab_mul_self_of_charTwo, map_one, Subgroup.coe_one]
  have huC : uG ∉ centralizer (W₀ : Set G) := by
    intro hC
    set v₀ : LinearFlag.projectiveSL 5 K := LinearFlag.proj 5 K (pointRadElem c (Pi.single d 1))
      with hv₀
    have hv₀P : v₀ ∈ pointRadOn (K := K) c {d, d'} := by
      refine ⟨pointRadElem c (Pi.single d 1), ⟨Pi.single d 1, fun j hj => ?_, rfl⟩, rfl⟩
      exact Pi.single_eq_of_ne (fun hjd => hj (by rw [hjd]; simp)) 1
    have hvW₀ : ((e.symm v₀ : L) : G) ∈ W₀ := by
      have h1 : ((e.symm v₀ : L) : G) ∈ modelToG e (pointRadOn (K := K) c {d, d'}) :=
        symm_mem_modelToG e hv₀P
      rw [← hV₀'] at h1
      exact (Subgroup.mem_inf.1 h1).1
    have h1 := (mem_centralizer_iff.1 hC) _ hvW₀
    have h2 : e.symm v₀ * e.symm (xab hdd' 1) = e.symm (xab hdd' 1) * e.symm v₀ :=
      Subtype.ext h1
    apply xab_mul_proj_pointRadElem_ne hK hdd' hcd hcd'
    rw [← hv₀]
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  have htX : t ∈ centralizer (modelToG e X₀ : Set G) := centralizer_le (modelToG_le e X₀) htC
  obtain ⟨A, hEX, hinf, hcomm, hA16, hDE⟩ :=
    exists_swap_factor_of_swap_five hset hK e htC ht hab hX₀ hX₀c htX (hswap htX)
  have hW₀E : W₀ ≤ centralizerPerfectCore (modelToG e X₀) :=
    le_centralizerPerfectCore_of_inf_centralizer_eq_bot hWc hW₀X (hDE hyD) hyW₀ hy0
  rw [hEX] at hW₀E hDE
  obtain ⟨X, hE1, huA, huW₀', hX2, hXA, hXW₀, hXE, hk⟩ := swapData_five ht2 hinf hcomm hW₀E hW₀2
    (by rw [hW₀c]; norm_num) htW₀ (by rw [hV₀', hV₀card]; norm_num) (hDE hyD) hyW₀ hy0 hA16
    (hDE huD) hut huW₀ huC hu2
  exact ⟨A, X, hinf, hcomm, htW₀, hE1, huA, huW₀', hX2, hXA, hXW₀, hXE, hk, hV₀', hW₀c⟩

end CFSG.SeitzReduction.LinearPilot
