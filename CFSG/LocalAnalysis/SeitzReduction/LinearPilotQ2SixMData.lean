module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift HasBLift)

theorem exists_not_mem_of_card_lt_fin {n : ℕ} (S : Finset (Fin n)) (h : S.card < n) :
    ∃ x : Fin n, x ∉ S := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := S) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; exact h)
  exact ⟨x, hx⟩

theorem exists_pair_ne_ne_of_three_le {n : ℕ} (hn : 3 ≤ n) (c : Fin n) :
    ∃ a b : Fin n, a ≠ b ∧ c ≠ a ∧ c ≠ b := by
  classical
  obtain ⟨a, ha⟩ := exists_not_mem_of_card_lt_fin {c} (by rw [Finset.card_singleton]; omega)
  obtain ⟨b, hb⟩ := exists_not_mem_of_card_lt_fin {c, a}
    ((Finset.card_le_two).trans_lt (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb
  exact ⟨a, b, Ne.symm hb.2, Ne.symm ha, Ne.symm hb.1⟩

theorem exists_linTv_path {n : ℕ} (hn : 5 ≤ n) (c : Fin n)
    (p q : {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c}) :
    ∃ r : {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c},
      (p.1.2 ≠ r.1.1 ∧ p.1.1 ≠ r.1.2) ∧ (r.1.2 ≠ q.1.1 ∧ r.1.1 ≠ q.1.2) := by
  classical
  obtain ⟨b, hb⟩ := exists_not_mem_of_card_lt_fin {c, p.1.1, q.1.1}
    ((Finset.card_le_three).trans_lt (by omega))
  obtain ⟨a, ha⟩ := exists_not_mem_of_card_lt_fin {c, p.1.2, q.1.2, b}
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb
  exact ⟨⟨(a, b), ha.2.2.2, ha.1, hb.1⟩, ⟨Ne.symm ha.2.1, Ne.symm hb.2.1⟩,
    ⟨hb.2.2, ha.2.2.1⟩⟩

section Transvections

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def linTv (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n}
    (hij : i ≠ j) : G :=
  ((e.symm (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hij (1 : K))) : L) : G)

theorem linTv_mem (e : L ≃* LinearFlag.projectiveSL n K) {c i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ c) (hj : j ≠ c) :
    linTv e hij ∈ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) :=
  symm_mem_modelToG e (proj_transvection_mem_blockSL hij (by simpa using hi) (by simpa using hj) 1)

theorem linTv_mul_self [CharP K 2] (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n}
    (hij : i ≠ j) : linTv e hij * linTv e hij = 1 := by
  have h : Matrix.SpecialLinearGroup.transvection hij (1 : K) *
      Matrix.SpecialLinearGroup.transvection hij (1 : K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.transvection_add, one_add_one_eq_two, CharTwo.two_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  rw [linTv, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h, map_one, map_one, Subgroup.coe_one]

theorem linTv_ne_one (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n} (hij : i ≠ j) :
    linTv e hij ≠ 1 := by
  intro h
  have h1 : e.symm (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hij (1 : K))) = 1 :=
    Subtype.ext h
  rw [EmbeddingLike.map_eq_one_iff, LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center,
    Matrix.SpecialLinearGroup.transvection_mem_center_iff] at h1
  exact one_ne_zero h1

theorem linTv_commute (e : L ≃* LinearFlag.projectiveSL n K) {i j k l : Fin n} (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) :
    linTv e hij * linTv e hkl = linTv e hkl * linTv e hij := by
  have h := (Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli (1 : K) (1 : K)).eq
  rw [linTv, linTv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, h]

theorem modelToG_blockSL_le_closure_linTv (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) :
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
      closure (Set.range fun p : {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c} =>
        linTv e p.2.1) := by
  rw [modelToG, blockSL_eq_closure, MonoidHom.map_closure, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨_, ⟨i, j, hij, c', hi, hj, rfl⟩, rfl⟩, rfl⟩
  rcases eq_zero_or_eq_one_of_natCard_eq_two hK c' with rfl | rfl
  · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one, map_one, map_one]
    exact one_mem _
  · apply Subgroup.subset_closure
    exact ⟨⟨(i, j), hij, by simpa using hi, by simpa using hj⟩, rfl⟩

end Transvections

section Levi

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem nonempty_levi_mulEquiv_of_card {m : ℕ} (hm : n = m + 1)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) :
    Nonempty (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≃*
      Matrix.SpecialLinearGroup (Fin m) K) := by
  have hcard : (({c}ᶜ : Finset (Fin n))).card = m := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  exact ⟨(linearModelToGEquiv e _).symm.trans
    (blockSLEquivOfEquiv (K := K) (by rw [hcard]; omega) (Finset.equivFinOfCardEq hcard)).symm⟩

theorem isSimpleGroup_levi_compl (hK : Nat.card K = 2) (hn : 4 ≤ n)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) :
    IsSimpleGroup (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))) ∧
      ∃ a b : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))), a * b ≠ b * a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) with hL₁
  have hcard : (({c}ᶜ : Finset (Fin n))).card = n - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hq : CFSG.IsQuasisimple L₁ := isQuasisimple_map_blockSL e (by rw [hcard]; omega)
    (by rw [hcard]; omega) (Or.inl (by rw [hcard]; omega))
  obtain ⟨φ⟩ := nonempty_levi_mulEquiv_of_card (K := K) (m := n - 1) (by omega) e c
  have hZSL : center (Matrix.SpecialLinearGroup (Fin (n - 1)) K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  have hZ : center L₁ = ⊥ := F4Pilot.center_eq_bot_congr φ.symm hZSL
  have hsL : IsSimpleGroup L₁ := by
    have : IsSimpleGroup (L₁ ⧸ center L₁) := hq.2.1
    exact (quotientCenterMulEquiv hZ).symm.isSimpleGroup
  refine ⟨hsL, ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center L₁) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center L₁) b
  exact ⟨a', b', fun h => hab (by rw [← map_mul, h, map_mul])⟩

theorem levi_inf_eq_bot_of_abelian (hK : Nat.card K = 2) (hn : 4 ≤ n)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) {W : Subgroup G}
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W : Set G)) :
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ⊓ W = ⊥ := by
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) with hL₁
  obtain ⟨hsimp, a, b, hab⟩ := isSimpleGroup_levi_compl hK hn e c
  have hnor : ((L₁ ⊓ W).subgroupOf L₁).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxL, hxW⟩ := Subgroup.mem_inf.1 hx
    simp only [coe_mul, coe_inv]
    exact Subgroup.mem_inf.2 ⟨L₁.mul_mem (L₁.mul_mem g.2 hxL) (L₁.inv_mem g.2),
      (mem_normalizer_iff.1 (hLW g.2) x).1 hxW⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L₁ ⊓ W).subgroupOf L₁) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : L₁) ∈ (L₁ ⊓ W).subgroupOf L₁ :=
      mem_subgroupOf.2 hx
    rw [h] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hx'))
  · exfalso
    have hle : ∀ x : L₁, (x : G) ∈ W := fun x => by
      have hx' : x ∈ (L₁ ⊓ W).subgroupOf L₁ := h ▸ mem_top _
      exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 hx')).2
    exact hab (Subtype.ext (hWc _ (hle a) _ (hle b)))

theorem seitzLeviBar_facts (hK : Nat.card K = 2) (hn : 4 ≤ n)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) {W : Subgroup G}
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W : Set G))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (htN : t ∈ normalizer (W : Set G)) :
    IsSimpleGroup (seitzLeviBar e c W) ∧ CFSG.Open.IsQuasisimple (seitzLeviBar e c W) ∧
      center (seitzLeviBar e c W) = ⊥ ∧
      Nonempty (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≃* seitzLeviBar e c W) ∧
      seitzLeviBar e c W ≤ centralizer
        ({QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩} :
          Set (seitzBar W)) := by
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) with hL₁
  obtain ⟨hsimp, a, b, hab⟩ := isSimpleGroup_levi_compl hK hn e c
  have hinf := levi_inf_eq_bot_of_abelian hK hn e c hWc hLW
  have hinf' : L₁.subgroupOf (normalizer (W : Set G)) ⊓ W.subgroupOf (normalizer (W : Set G)) =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hx' : (x : G) ∈ L₁ ⊓ W := Subgroup.mem_inf.2 ⟨mem_subgroupOf.1 h1, mem_subgroupOf.1 h2⟩
    rw [hinf] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
  set ψ : L₁ ≃* seitzLeviBar e c W := (subgroupOfEquivOfLe hLW).symm.trans
    (F4Pilot.mapMkEquivOfInfEqBot (W.subgroupOf (normalizer (W : Set G)))
      (L₁.subgroupOf (normalizer (W : Set G))) hinf') with hψ
  have hsB : IsSimpleGroup (seitzLeviBar e c W) := ψ.symm.isSimpleGroup
  have hnB : ∃ a b : seitzLeviBar e c W, a * b ≠ b * a :=
    ⟨ψ a, ψ b, fun h => hab (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨hq, hZ⟩ := open_isQuasisimple_and_center_of_isSimpleGroup hnB
  refine ⟨hsB, hq, hZ, ⟨ψ⟩, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_iff.1 htC) l (modelToG_le e _ (mem_subgroupOf.1 hl))

end Levi

section ModuleData

theorem card_inf_centralizer_eq_of_pointRadical {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {c : Fin n} {W : Subgroup G}
    (hWt : W ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c)) :
    Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ (n - 1) := by
  have hcc : c ∉ ({c}ᶜ : Finset (Fin n)) := by simp
  rw [hWt, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
    Finset.card_singleton, Fintype.card_fin]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem exists_swapModuleData_of_swapType_of_dvd
    (hset : SeitzSetting G L)
    (hn : 5 ≤ n) (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c : Fin n} {W : Subgroup G} (hWc : Nat.card W = 2 ^ (2 * (n - 1)))
    (hW2 : ∀ w ∈ W, w * w = 1)
    (hWt : W ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W : Set G))
    (hfact : ∀ k, k ∣ 2 ^ (2 * (n - 1)) →
      Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) K) ∣ (k - 1).factorial → 2 ^ (n - 1) ≤ k)
    (hsw : LinearTwoSwapTypeAtNOne e t c W htN) :
    ∃ X : Subgroup G, ⁅X, X⁆ = X ∧ X ≤ normalizer (W : Set G) ∧
      W ≤ normalizer (X : Set G) ∧ ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ W ∧
      X ⊓ X.map (MulAut.conj t).toMonoidHom ≤ W ∧
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
        (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W ∧
      W ⊓ centralizer (X : Set G) ≠ ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set N := normalizer (W : Set G) with hNdef
  set q := QuotientGroup.mk' (W.subgroupOf N) with hq
  set π := QuotientGroup.mk' (oddCore (seitzBar W)) with hπ
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) with hL₁
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    mul_comm_of_forall_mul_self_eq_one hW2 ha hb
  have htW : t ∉ W := fun h => by
    have h' : t ∈ W ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hWt] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h')
  have hs : orderOf (q ⟨t, htN⟩) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have h1 : (⟨t, htN⟩ : N) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [h1, map_one]
    · intro h1
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact htW h1
  have hs2 : q ⟨t, htN⟩ * q ⟨t, htN⟩ = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hVc := card_inf_centralizer_eq_of_pointRadical hK e hWt
  have hcardW : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hWc, hVc, ← pow_mul, mul_comm]
  have hNV := normalizer_pointRadical_inf_le hset (by omega) hK e ht hKt c
  have hCs := centralizer_mk_le_sup_of_normalizer_inf_le ht2 hW2 hcardW hWt htN hLW hNV
  obtain ⟨-, hLq, hLZ, ⟨ψL⟩, hLs⟩ := seitzLeviBar_facts hK (by omega) e c hWab hLW htC htN
  obtain ⟨φS⟩ := nonempty_levi_mulEquiv_of_card (K := K) (m := n - 2 + 1) (by omega) e c
  obtain ⟨φ1⟩ := nonempty_levi_mulEquiv_of_card (K := K) (m := n - 1) (by omega) e c
  have hschurL : OddSchurTrivial ((L₁.subgroupOf N).map q) :=
    (SeitzQ2.oddSchurTrivial_specialLinearGroup (n - 2) K).of_mulEquiv (φS.symm.trans ψL)
  have hLp : ⁅(L₁.subgroupOf N).map q, (L₁.subgroupOf N).map q⁆ = (L₁.subgroupOf N).map q :=
    isPerfect_iff.mp ⟨hLq.1⟩
  obtain ⟨Kc, hKc, hDKK, -, hcomm, hZ, ⟨χ⟩⟩ := hsw
  have hcomm' : ⁅Kc, Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom⁆ = ⊥ := hcomm
  have hDKK' : ((L₁.subgroupOf N).map q).map π ≤
      Kc ⊔ Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom := by
    rw [← seitzLeviHat_eq_map_map]
    exact hDKK
  have hKL : Nonempty (Kc ≃* ((L₁.subgroupOf N).map q).map π) := by
    rw [← seitzLeviHat_eq_map_map]
    exact ⟨χ⟩
  obtain ⟨hBsup, -, hinfO, hmapA, ⟨ψ⟩, hconjA⟩ :=
    exists_lift_swap_of_le_sup hs hLs hLq hLZ hCs hschurL hKc hcomm' hKL
  set A := oddCoreLift Kc with hAdef
  have hAp : ⁅A, A⁆ = A := F4Pilot.commutator_oddCoreLift Kc
  have hAc : Nat.card A = Nat.card ((L₁.subgroupOf N).map q) := Nat.card_congr ψ.toEquiv
  have hAc' : Nat.card A = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) K) := by
    rw [hAc, ← Nat.card_congr ψL.toEquiv, Nat.card_congr φ1.toEquiv]
  have : IsSimpleGroup L₁ := (isSimpleGroup_levi_compl hK (by omega) e c).1
  have : IsSimpleGroup A := (ψ.trans ψL.symm).isSimpleGroup
  have hsimp : ∀ M : Subgroup (seitzBar W), M ≤ A → A ≤ normalizer (M : Set (seitzBar W)) →
      M = ⊥ ∨ M = A := by
    intro M hMA hAM
    have hn : (M.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hMA).2 hAM
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf A) with h | h
    · left
      rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hMA] at h
      exact h
    · right
      rw [subgroupOf_eq_top] at h
      exact le_antisymm hMA h
  have hKcp : ⁅Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom,
      Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom⁆ =
        Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom := by
    rw [← map_commutator, isPerfect_iff.mp hKc.1.1]
  have hπAs : (A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom).map π =
      Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom := by
    rw [hconjA]
    exact F4Pilot.map_oddCoreLift hKcp
  have hOK : oddCore (seitzBar W) ≤ centralizer (A : Set (seitzBar W)) :=
    le_centralizer_iff.1 (hBsup.mono le_sup_left)
  have hAcomm : ⁅A, A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator (isPerfect_iff.mpr hAp)
    have h1 : ⁅A, A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom⁆ ≤ oddCore (seitzBar W) := by
      have h2 : (⁅A, A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom⁆).map π = ⊥ := by
        rw [map_commutator, hmapA, hπAs]
        exact hcomm'
      have h3 := (Subgroup.map_eq_bot_iff _).1 h2
      rwa [hπ, QuotientGroup.ker_mk'] at h3
    exact commutator_eq_bot_iff_le_centralizer.2 (h1.trans hOK)
  have hKinf : Kc ⊓ Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hzc : (⟨z, hz1⟩ : Kc) ∈ center Kc := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm' k.2) z hz2).symm
    rw [hZ, mem_bot] at hzc
    exact mem_bot.2 (congrArg Subtype.val hzc)
  have hAinf : A ⊓ A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h1 : π x ∈ Kc ⊓ Kc.map (MulAut.conj (π (q ⟨t, htN⟩))).toMonoidHom :=
      ⟨hmapA ▸ mem_map_of_mem π hx1, hπAs ▸ mem_map_of_mem π hx2⟩
    rw [hKinf, mem_bot] at h1
    have hxO : x ∈ oddCore (seitzBar W) := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hinfO.le ⟨hx1, hxO⟩
  have hLbA : (L₁.subgroupOf N).map q ≤ A ⊔ A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom := by
    have hLM := F4Pilot.le_oddCoreLift_of_perfect hLp hDKK'
    refine hLM.trans (F4Pilot.perfect_le_of_forall_exists_commute
      (F4Pilot.commutator_oddCoreLift _) (sup_le (F4Pilot.oddCoreLift_mono le_sup_left)
        (hconjA ▸ F4Pilot.oddCoreLift_mono le_sup_right)) fun a ha => ?_)
    have hπa : π a ∈ (A ⊔ A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom).map π := by
      rw [Subgroup.map_sup, hmapA, hπAs]
      exact F4Pilot.oddCoreLift_le_comap _ ha
    obtain ⟨m, hm, hma⟩ := hπa
    refine ⟨m, hm, m⁻¹ * a, by group, fun b hb => ?_⟩
    have hz : m⁻¹ * a ∈ oddCore (seitzBar W) := by
      rw [← QuotientGroup.ker_mk' (oddCore (seitzBar W)), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hma, inv_mul_cancel]
    exact mem_centralizer_iff.1 (hBsup hb) _ hz
  obtain ⟨hXp, hXN, hWX, hXY, hXYW, hLX⟩ := barLift_swap_facts htN hAp hAcomm hAinf hLW hLbA
  refine ⟨barLift A, hXp, hXN, hWX, hXY, hXYW, hLX, ?_⟩
  have hinfL := levi_inf_eq_bot_of_abelian hK (by omega) e c hWab hLW
  obtain ⟨a₀, b₀, hab₀, hca₀, hcb₀⟩ := exists_pair_ne_ne_of_three_le (by omega) c
  have hb1 : 2 ^ (n - 1) ≠ 1 := (Nat.one_lt_two_pow (by omega)).ne'
  have hWc' : Nat.card W = 2 ^ (n - 1) * 2 ^ (n - 1) := by
    rw [hWc, ← pow_add]
    congr 1
    omega
  have hfact' : ∀ k, k ∣ Nat.card W → Nat.card A ∣ (k - 1).factorial → 2 ^ (n - 1) ≤ k :=
    fun k hk hA => hfact k (hWc ▸ hk) (hAc' ▸ hA)
  refine ne_bot_inf_centralizer_barLift_of_dvd htN hWab hW2 hWc' hb1 rfl hs2 hAp hsimp hfact'
    hAcomm hAinf (ι := {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c})
    (fun p => linTv e p.2.1) (fun p => hLW (linTv_mem e p.2.1 p.2.2.1 p.2.2.2))
    (fun p => hLbA (mem_barImg_of_mem (linTv_mem e p.2.1 p.2.2.1 p.2.2.2) _))
    (fun p => (mem_centralizer_singleton_iff.1
      (hLs (mem_barImg_of_mem (linTv_mem e p.2.1 p.2.2.1 p.2.2.2) _))).symm)
    (fun p => linTv_mul_self e p.2.1)
    (fun p hp => linTv_ne_one e p.2.1 (by
      have h := mem_inf.2 ⟨linTv_mem e p.2.1 p.2.2.1 p.2.2.2, hp⟩
      rw [hinfL, mem_bot] at h
      exact h))
    (fun p r => p.1.2 ≠ r.1.1 ∧ p.1.1 ≠ r.1.2)
    (fun p r hpr => linTv_commute e p.2.1 r.2.1 hpr.1 (Ne.symm hpr.2))
    (exists_linTv_path hn c) ⟨(a₀, b₀), hab₀, Ne.symm hca₀, Ne.symm hcb₀⟩ ?_
  rw [hAc]
  apply Subgroup.card_le_of_le
  set S' : Set N := Set.range fun p : {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c} =>
    (⟨linTv e p.2.1, hLW (linTv_mem e p.2.1 p.2.2.1 p.2.2.2)⟩ : N) with hS'
  have h1 : (closure S').map N.subtype = closure (Set.range fun p :
      {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c} => (linTv e p.2.1 : G)) := by
    rw [MonoidHom.map_closure, hS', ← Set.range_comp]
    rfl
  have h2 : (closure S').map q = closure (Set.range fun p :
      {p : Fin n × Fin n // p.1 ≠ p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c} =>
        q ⟨linTv e p.2.1, hLW (linTv_mem e p.2.1 p.2.2.1 p.2.2.2)⟩) := by
    rw [MonoidHom.map_closure, hS', ← Set.range_comp]
    rfl
  rw [← h2]
  apply map_mono
  intro l hl
  have hl' : (l : G) ∈ (closure S').map N.subtype :=
    h1 ▸ modelToG_blockSL_le_closure_linTv hK e c (mem_subgroupOf.1 hl)
  obtain ⟨m, hm, hml⟩ := hl'
  have hml' : m = l := Subtype.ext hml
  rw [← hml']
  exact hm

omit [CharP K 2] in
theorem two_pow_le_of_dvd_factorial_six (hK : Nat.card K = 2) : ∀ k, k ∣ 2 ^ (2 * (6 - 1)) →
    Nat.card (Matrix.SpecialLinearGroup (Fin (6 - 1)) K) ∣ (k - 1).factorial →
      2 ^ (6 - 1) ≤ k := by
  intro k _ h
  have h' : 9999360 ∣ (k - 1).factorial := by
    have h5 := card_specialLinearGroup_five_of_card_two hK
    rw [h5] at h
    exact h
  exact thirty_two_le_of_dvd_factorial h'

omit [CharP K 2] in
theorem two_pow_le_of_dvd_factorial_five (hK : Nat.card K = 2) : ∀ k, k ∣ 2 ^ (2 * (5 - 1)) →
    Nat.card (Matrix.SpecialLinearGroup (Fin (5 - 1)) K) ∣ (k - 1).factorial →
      2 ^ (5 - 1) ≤ k := by
  intro k hk h
  have h' : 20160 ∣ (k - 1).factorial := by
    have h4 := card_specialLinearGroup_four_of_card_two hK
    rw [h4] at h
    exact h
  exact sixteen_le_of_dvd_factorial hk h'

end ModuleData

end CFSG.SeitzReduction.LinearPilot
