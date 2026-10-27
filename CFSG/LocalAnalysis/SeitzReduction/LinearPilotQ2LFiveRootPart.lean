module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootStep
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootLift

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)

theorem eq_one_of_mul_self_of_odd_card_group {M : Type*} [Group M] [Finite M]
    (hM : Odd (Nat.card M)) {x : M} (hx : x * x = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
  have hodd : orderOf x ∣ Nat.card M := orderOf_dvd_natCard x
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd (Odd.of_dvd_nat hM hodd) (by decide)

theorem mem_normalizer_sup_of_left_right {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem transvection_eq_pointRadElem {n : ℕ} {K : Type*} [Field K] {c j : Fin n} (hcj : c ≠ j)
    (b : K) : SpecialLinearGroup.transvection hcj b = pointRadElem c (Pi.single j b) := by
  apply Subtype.ext
  ext i l
  rw [coe_pointRadElem, pointRadMat_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_apply, Matrix.single_apply]
  congr 1
  by_cases hi : i = c
  · subst hi
    by_cases hl : l = i
    · subst hl
      simp [Ne.symm hcj]
    · simp only [hl, ne_eq, not_false_eq_true, and_self, ite_true, true_and, Pi.single_apply]
      by_cases hlj : l = j
      · subst hlj; simp
      · simp [hlj, Ne.symm hlj]
  · have h1 : ¬ (c = i ∧ j = l) := fun h => hi h.1.symm
    have h2 : ¬ (i = c ∧ l ≠ c) := fun h => hi h.1
    rw [ite_eq_right h1, ite_eq_right h2]

theorem xab_mem_pointRadical {n : ℕ} {K : Type*} [Field K] {c j : Fin n} (hcj : c ≠ j) (b : K) :
    xab hcj b ∈ pointRadical (K := K) c := by
  refine ⟨_, ⟨Pi.single j b, fun m hm => ?_, rfl⟩, ?_⟩
  · have hmc : m = c := by simpa using hm
    rw [hmc, Pi.single_apply, ite_eq_right hcj]
  · rw [xab, transvection_eq_pointRadElem]

theorem exists_equiv_fin_three_of_compl_pair {a b c d d' : Fin 5} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) (hdd' : d ≠ d') (hS : ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'}) :
    ∃ eN : ({a, b}ᶜ : Finset (Fin 5)) ≃ Fin 3,
      ((eN.symm 0 : ({a, b}ᶜ : Finset (Fin 5))) : Fin 5) = c ∧
      ((eN.symm 1 : ({a, b}ᶜ : Finset (Fin 5))) : Fin 5) = d ∧
      ((eN.symm 2 : ({a, b}ᶜ : Finset (Fin 5))) : Fin 5) = d' := by
  have hdS : d ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hd'S : d' ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hcd : c ≠ d := fun h =>
    Finset.mem_compl.1 (Finset.mem_sdiff.1 hdS).1 (Finset.mem_singleton.2 h.symm)
  have hcd' : c ≠ d' := fun h =>
    Finset.mem_compl.1 (Finset.mem_sdiff.1 hd'S).1 (Finset.mem_singleton.2 h.symm)
  have hcN : c ∈ ({a, b}ᶜ : Finset (Fin 5)) := by simp [hca, hcb]
  have hdN : d ∈ ({a, b}ᶜ : Finset (Fin 5)) := Finset.mem_compl.2 (Finset.mem_sdiff.1 hdS).2
  have hd'N : d' ∈ ({a, b}ᶜ : Finset (Fin 5)) := Finset.mem_compl.2 (Finset.mem_sdiff.1 hd'S).2
  let f : Fin 3 → ({a, b}ᶜ : Finset (Fin 5)) := ![⟨c, hcN⟩, ⟨d, hdN⟩, ⟨d', hd'N⟩]
  have hfinj : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢
    · exact hcd hij'
    · exact hcd' hij'
    · exact hcd hij'.symm
    · exact hdd' hij'
    · exact hcd' hij'.symm
    · exact hdd' hij'.symm
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      Finset.card_pair hab]
  exact ⟨(Equiv.ofBijective f hfbij).symm, rfl, rfl, rfl⟩

section WZero

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem card_wZero_of_wOne (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b c : Fin 5} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW₁ : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)) :
    Nat.card (W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) = 2 ^ 4 ∧
      W₁ ⊓ centralizer (modelToG e X₀ : Set G) ⊓ centralizer ({t} : Set G) =
        modelToG e (pointRadOn (K := K) c (({c}ᶜ : Finset (Fin 5)) \ {a, b})) ∧
      Nat.card (modelToG e (pointRadOn (K := K) c (({c}ᶜ : Finset (Fin 5)) \ {a, b}))) = 2 ^ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hcsub : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    intro hjc
    rcases Finset.mem_insert.1 hj with h | h
    · exact hca (hjc ▸ h)
    · exact hcb (hjc ▸ Finset.mem_singleton.1 h)
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
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW₁ (symm_mem_modelToG e hxB)
  have hxt : xG * t = t * xG := hLt xG (e.symm x).2
  have hx3G : xG ^ 3 = 1 := by
    rw [hxG, ← Subgroup.coe_pow, ← map_pow, hxm, map_one, Subgroup.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ (by rw [hW₁c, hV₁card]; norm_num)
  set S₀ : Finset (Fin 5) := ({c}ᶜ : Finset (Fin 5)) \ {a, b} with hS₀
  have hS₀card : S₀.card = 2 := by
    rw [hS₀, Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hab]
  have hcS₀ : c ∉ S₀ := fun h => hcc (Finset.mem_sdiff.1 h).1
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c S₀) := by
    rw [hW₁t, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hab hca hcb _ hX₀ hX₀c]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c S₀)) = 2 ^ 2 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c hcS₀, hS₀card]
  refine ⟨?_, ?_, hV₀card⟩
  · rw [hCX, card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hxN hxt hx3G, hV₀, hV₀card]
    norm_num
  · rw [inf_right_comm, hCX, hV₀]

end WZero

theorem lFiveFieldPartInput_holds :
    LFiveFieldPartInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c d d' hdd' hca hcb hS W₁
    hW₁c hW₁2 hW₁t htW₁ hLW
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hdS : d ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hd'S : d' ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hcd : c ≠ d := fun h =>
    Finset.mem_compl.1 (Finset.mem_sdiff.1 hdS).1 (Finset.mem_singleton.2 h.symm)
  have hcd' : c ≠ d' := fun h =>
    Finset.mem_compl.1 (Finset.mem_sdiff.1 hd'S).1 (Finset.mem_singleton.2 h.symm)
  have hcN : c ∈ ({a, b}ᶜ : Finset (Fin 5)) := by simp [hca, hcb]
  have hdN : d ∈ ({a, b}ᶜ : Finset (Fin 5)) := Finset.mem_compl.2 (Finset.mem_sdiff.1 hdS).2
  have hd'N : d' ∈ ({a, b}ᶜ : Finset (Fin 5)) := Finset.mem_compl.2 (Finset.mem_sdiff.1 hd'S).2
  obtain ⟨hZ, Kc, hKcomp, hDK, hsN, hτ, hmodel⟩ := hfk
  obtain ⟨hcore, -, q, hqs, hqc, hqo, -, hqapp, -⟩ := neighbourCore_field_linear_two
    (X := modelToG e X₀) (D := modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5)))) hset hK
    e le_rfl htC ht hab hX₀ hX₀c rfl htX rfl hKcomp hDK hsN hτ hmodel
  obtain ⟨eN, he0, he1, he2⟩ := exists_equiv_fin_three_of_compl_pair hab hca hcb hdd' hS
  obtain ⟨F, _, _, _, hF4, ι, σ, -, -, -, ψ, hψD, hψτ⟩ :=
    exists_mulEquiv_fieldKind_two_of_equiv hset hK e le_rfl htC ht hab hX₀ hX₀c htX hZ hDK hsN
      hτ hmodel eN
  let p : centralizerPerfectCore (modelToG e X₀) →* LinearFlag.projectiveSL 3 F :=
    ψ.toMonoidHom.comp q
  have hps : Function.Surjective p := ψ.surjective.comp hqs
  have hpq : ∀ y, p y = 1 → q y = 1 := fun y h => ψ.injective (h.trans (map_one ψ).symm)
  have hpker : p.ker = q.ker := by
    ext y
    refine ⟨hpq y, fun h => ?_⟩
    rw [MonoidHom.mem_ker] at h ⊢
    change ψ (q y) = 1
    rw [h, map_one]
  have hc' : ∀ y : centralizerPerfectCore (modelToG e X₀), p y = 1 →
      ∀ y' : centralizerPerfectCore (modelToG e X₀), y * y' = y' * y := fun y hy y' =>
    ((Subgroup.mem_center_iff.1 (hqc (hpq y hy))) y').symm
  have hkodd : Odd (Nat.card p.ker) := by rw [hpker]; exact hqo
  have hodd' : ∀ y : centralizerPerfectCore (modelToG e X₀), p y = 1 → y * y = 1 →
      y = 1 := by
    intro y hy hyy
    have h := eq_one_of_mul_self_of_odd_card_group hkodd (x := ⟨y, hy⟩) (Subtype.ext hyy)
    exact congrArg Subtype.val h
  have htP : t ∈ normalizer (centralizerPerfectCore (modelToG e X₀) : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  have hpt : ∀ (y : G) (hy : y ∈ centralizerPerfectCore (modelToG e X₀)),
      p ⟨t * y * t⁻¹, (mem_normalizer_iff.1 htP y).1 hy⟩ =
        (LinearFlag.fieldAut 3 F σ).toMonoidHom (p ⟨y, hy⟩) := by
    intro y hy
    have hqt : q ⟨t * y * t⁻¹, (mem_normalizer_iff.1 htP y).1 hy⟩ =
        Kc.normalizerMonoidHom ⟨_, hsN⟩ (q ⟨y, hy⟩) := by
      apply Subtype.ext
      have e1 : (⟨t * y * t⁻¹, F4Pilot.centralizerPerfectCore_le_centralizer _
          ((mem_normalizer_iff.1 htP y).1 hy)⟩ : centralizer (modelToG e X₀ : Set G)) =
          (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G)) *
            ⟨y, F4Pilot.centralizerPerfectCore_le_centralizer _ hy⟩ *
            (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹ :=
        Subtype.ext rfl
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply, hqapp, hqapp]
      change QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))
        (⟨t * y * t⁻¹, F4Pilot.centralizerPerfectCore_le_centralizer _
          ((mem_normalizer_iff.1 htP y).1 hy)⟩ : centralizer (modelToG e X₀ : Set G)) = _
      rw [e1, map_mul, map_mul, map_inv]
    change ψ (q _) = LinearFlag.fieldAut 3 F σ (ψ (q _))
    rw [hqt, hψτ]
  have hDC : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5))) ≤
      centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e ((blockSL_le_centralizer_blockSL_of_disjoint
      (disjoint_compl_left : Disjoint ({a, b}ᶜ : Finset (Fin 5)) {a, b})).trans
        (centralizer_le hX₀))
  have hDP : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5))) ≤
      centralizerPerfectCore (modelToG e X₀) :=
    F4Pilot.le_centralizerPerfectCore (modelToG_perfect e (commutator_blockSL_eq_of_three_le
      (by rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]))) hDC
  have hroot : ∀ (i j : Fin 3) (hij : i ≠ j) {x y : Fin 5} (hxy : x ≠ y)
      (hx : ((eN.symm i : ({a, b}ᶜ : Finset (Fin 5))) : Fin 5) = x)
      (hy : ((eN.symm j : ({a, b}ᶜ : Finset (Fin 5))) : Fin 5) = y),
      ∃ hP : ((e.symm (xab hxy 1) : L) : G) ∈
        centralizerPerfectCore (modelToG e X₀),
        p ⟨_, hP⟩ = LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij 1) := by
    intro i j hij x y hxy hx hy
    subst hx
    subst hy
    have heq : ((e.symm (xab hxy 1) : L) : G) = ((e.symm (LinearFlag.proj 5 K
        (blockSLEquiv ({a, b}ᶜ : Finset (Fin 5)) eN
          (SpecialLinearGroup.transvection hij (1 : K)))) : L) : G) := by
      rw [coe_blockSLEquiv_transvection _ eN hij hxy, xab_def]
    have hmem : ((e.symm (xab hxy 1) : L) : G) ∈
        centralizerPerfectCore (modelToG e X₀) :=
      hDP (symm_mem_modelToG e (xab_mem_blockSL hxy (eN.symm i).2 (eN.symm j).2 1))
    refine ⟨hmem, ?_⟩
    have h1 : (⟨_, hmem⟩ : centralizerPerfectCore (modelToG e X₀)) = ⟨_, heq ▸ hmem⟩ :=
      Subtype.ext heq
    have h2 : ∀ (hz : ((e.symm (LinearFlag.proj 5 K (blockSLEquiv ({a, b}ᶜ : Finset (Fin 5)) eN
        (SpecialLinearGroup.transvection hij (1 : K)))) : L) : G) ∈
          centralizerPerfectCore (modelToG e X₀)),
        p ⟨_, hz⟩ = LinearFlag.proj 3 F (SpecialLinearGroup.map ι
          (SpecialLinearGroup.transvection hij (1 : K))) := by
      intro hz
      have hzC := F4Pilot.centralizerPerfectCore_le_centralizer _ hz
      have hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨_, hzC⟩ ∈
          Kc := by
        rw [← hqapp ⟨_, hz⟩]
        exact (q ⟨_, hz⟩).2
      have hq' : q ⟨_, hz⟩ = ⟨_, hk⟩ := Subtype.ext (hqapp _)
      change ψ (q ⟨_, hz⟩) = _
      rw [hq']
      exact hψD _ hzC hk
    rw [h1, h2, specialLinear_map_transvection, map_one]
  obtain ⟨hv₁P, hpv₁⟩ := hroot 0 1 (by decide) hcd he0 he1
  obtain ⟨hv₂P, hpv₂⟩ := hroot 0 2 (by decide) hcd' he0 he2
  obtain ⟨huP, hpu⟩ := hroot 1 2 (by decide) hdd' he1 he2
  rw [transvection_zero_one_eq_unipU_three] at hpv₁
  rw [transvection_zero_two_eq_unipU_three] at hpv₂
  rw [transvection_one_two_eq_unipU_three] at hpu
  have hW₀P : W₁ ⊓ centralizer (modelToG e X₀ : Set G) ≤ centralizerPerfectCore (modelToG e X₀) :=
    wZero_le_centralizerPerfectCore_of_wOne hset hK e ht hKt hab hca hcb hX₀ hX₀c hW₁2 hW₁t htW₁
      hLW
  have hW₀2 : ∀ w ∈ W₁ ⊓ centralizer (modelToG e X₀ : Set G), w * w = 1 :=
    fun w hw => hW₁2 w (Subgroup.mem_inf.1 hw).1
  obtain ⟨hW₀card, hV₀eq, hV₀card⟩ := card_wZero_of_wOne hK e ht hKt hab hca hcb hX₀ hX₀c hW₁c
    hW₁2 hW₁t htW₁ hLW
  have hW₁V : ∀ {j : Fin 5} (hcj : c ≠ j), j ∈ ({a, b}ᶜ : Finset (Fin 5)) →
      ((e.symm (xab hcj (1 : K)) : L) : G) ∈ W₁ ⊓ centralizer (modelToG e X₀ : Set G) := by
    intro j hcj hjN
    have h1 : ((e.symm (xab hcj (1 : K)) : L) : G) ∈ W₁ ⊓ centralizer ({t} : Set G) := by
      rw [hW₁t]
      exact symm_mem_modelToG e (xab_mem_pointRadical hcj 1)
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h1).1,
      hDC (symm_mem_modelToG e (xab_mem_blockSL hcj hcN hjN 1))⟩
  have hv₁W₀ := hW₁V hcd hdN
  have hv₂W₀ := hW₁V hcd' hd'N
  have hv₁t : t * ((e.symm (xab hcd (1 : K)) : L) : G) =
      ((e.symm (xab hcd (1 : K)) : L) : G) * t :=
    ((mem_centralizer_iff.1 htC) _ (e.symm (xab hcd (1 : K))).2).symm
  have hpW₀ : ∀ (w : G) (hw : w ∈ W₁ ⊓ centralizer (modelToG e X₀ : Set G)),
      p ⟨w, hW₀P hw⟩ ∈ projRad F 0 := by
    intro w hw
    have hc₁ : (⟨_, hv₁P⟩ : centralizerPerfectCore (modelToG e X₀)) * ⟨w, hW₀P hw⟩ =
        ⟨w, hW₀P hw⟩ * ⟨_, hv₁P⟩ :=
      Subtype.ext (mul_comm_of_forall_mul_self_eq_one hW₀2 hv₁W₀ hw)
    have hc₂ : (⟨_, hv₂P⟩ : centralizerPerfectCore (modelToG e X₀)) * ⟨w, hW₀P hw⟩ =
        ⟨w, hW₀P hw⟩ * ⟨_, hv₂P⟩ :=
      Subtype.ext (mul_comm_of_forall_mul_self_eq_one hW₀2 hv₂W₀ hw)
    refine mem_projRad_zero_of_commute hF4 ?_ ?_
    · rw [← hpv₁, ← map_mul, ← map_mul, hc₁]
    · rw [← hpv₂, ← map_mul, ← map_mul, hc₂]
  have hpWeq : ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
      (centralizerPerfectCore (modelToG e X₀))).map p = projRad F 0 := by
    have hle : ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
        (centralizerPerfectCore (modelToG e X₀))).map p ≤ projRad F 0 := by
      rintro _ ⟨y, hy, rfl⟩
      exact hpW₀ y (mem_subgroupOf.1 hy)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hinj : Function.Injective (p.comp ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
        (centralizerPerfectCore (modelToG e X₀))).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      have hy1 : p (y : centralizerPerfectCore (modelToG e X₀)) = 1 := hy
      have hyy : (y : centralizerPerfectCore (modelToG e X₀)) * y = 1 :=
        Subtype.ext (hW₀2 _ (mem_subgroupOf.1 y.2))
      exact Subgroup.mem_bot.2 (Subtype.ext (hodd' _ hy1 hyy))
    have hcardsub : Nat.card ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
        (centralizerPerfectCore (modelToG e X₀))) = 2 ^ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hW₀P).toEquiv, hW₀card]
    have hrange : ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
        (centralizerPerfectCore (modelToG e X₀))).map p =
        (p.comp ((W₁ ⊓ centralizer (modelToG e X₀ : Set G)).subgroupOf
          (centralizerPerfectCore (modelToG e X₀))).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [card_projRad, hF4, hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      hcardsub]
    norm_num
  set T₀ : Subgroup G := involutionsOver p (projRootU F) hc' hodd'
    (fun u hu => mul_self_of_mem_projRootU hu) with hT₀def
  have hT₀N : T₀ ≤ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) :
      Set G) := by
    refine involutionsOver_le_normalizer hW₀2 fun y hy w hw => ?_
    obtain ⟨hyP, hpy, -⟩ := hy
    have hywP : y * w * y⁻¹ ∈ centralizerPerfectCore (modelToG e X₀) :=
      mul_mem (mul_mem hyP (hW₀P hw)) (inv_mem hyP)
    have hr : p ⟨y * w * y⁻¹, hywP⟩ ∈ projRad F 0 := by
      have e1 : (⟨y * w * y⁻¹, hywP⟩ : centralizerPerfectCore (modelToG e X₀)) =
          ⟨y, hyP⟩ * ⟨w, hW₀P hw⟩ * (⟨y, hyP⟩ : centralizerPerfectCore (modelToG e X₀))⁻¹ :=
        Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (projRootU_le_normalizer hpy) _).1 (hpW₀ w hw)
    rw [← hpWeq] at hr
    obtain ⟨w', hw', hw'eq⟩ := hr
    exact ⟨w', mem_subgroupOf.1 hw', w'.2, hywP, hw'eq.symm⟩
  have htT₀ : t ∈ normalizer (T₀ : Set G) :=
    mem_normalizer_involutionsOver ht2 htP (fun u hu => fieldAut_mem_projRootU σ hu) hpt
  have hT₀v : ∀ y ∈ T₀, y * ((e.symm (xab hcd (1 : K)) : L) : G) =
      ((e.symm (xab hcd (1 : K)) : L) : G) * y → y = 1 := by
    refine fun y hy hyv => eq_one_of_mem_involutionsOver_of_commute hv₁P (fun u hu h => ?_) hy hyv
    rw [hpv₁] at h
    exact eq_one_of_mem_projRootU_of_commute hu h
  have hT₀inf : T₀ ⊓ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) :
      Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyC⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_bot.2 (hT₀v y hyT ((mem_centralizer_iff.1 hyC _ hv₁W₀).symm))
  have hT₀card : 4 ≤ Nat.card T₀ := by
    let g : T₀ → projRootU F := fun y => ⟨p ⟨y, y.2.1⟩, y.2.2.1⟩
    have hg : Function.Surjective g := by
      rintro ⟨r, hr⟩
      obtain ⟨y, hyT, hyP, hpy⟩ := exists_mem_involutionsOver_of_surjective (hc := hc')
        (hodd := hodd') (hU2 := fun u hu => mul_self_of_mem_projRootU hu) hps hkodd hr
      exact ⟨⟨y, hyT⟩, Subtype.ext hpy⟩
    have h := Nat.card_le_card_of_surjective g hg
    rw [card_projRootU, hF4] at h
    exact h
  have huu : ((e.symm (xab hdd' (1 : K)) : L) : G) * ((e.symm (xab hdd' (1 : K)) : L) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, ← xab_add, CharTwo.add_self_eq_zero, xab_zero, map_one,
      Subgroup.coe_one]
  have huT₀ : ((e.symm (xab hdd' (1 : K)) : L) : G) ∈ T₀ :=
    ⟨huP, by rw [hpu]; exact mem_projRootU.2 ⟨1, rfl⟩, huu⟩
  have htW₀ : t ∈ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) :
      Set G) := mem_normalizer_inf_of_mem htW₁ (le_normalizer htX)
  have hT₀NC : T₀ ≤ normalizer ((centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) :
      Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_centralizer_of_mem_normalizer (hT₀N hy)
  refine ⟨centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ⊔ T₀, T₀,
    le_sup_left, Subgroup.mem_sup_right huT₀,
    mem_normalizer_sup_of_left_right (mem_normalizer_centralizer_of_mem_normalizer htW₀) htT₀, ?_,
    isPGroup_involutionsOver, le_sup_right, hT₀N, htT₀, ?_⟩
  ·
    intro htR
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hT₀NC] at htR
    obtain ⟨c', hc', τ, hτ', hcτ⟩ := Set.mem_mul.1 htR
    have hτW := (mem_normalizer_iff.1 (hT₀N hτ') _).1 hv₁W₀
    have hcτv : c' * (τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹) =
        (τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹) * c' :=
      ((mem_centralizer_iff.1 hc') _ hτW).symm
    have hτv : τ * ((e.symm (xab hcd (1 : K)) : L) : G) =
        ((e.symm (xab hcd (1 : K)) : L) : G) * τ := by
      have h1 : t * ((e.symm (xab hcd (1 : K)) : L) : G) * t⁻¹ =
          ((e.symm (xab hcd (1 : K)) : L) : G) := by rw [hv₁t, mul_inv_cancel_right]
      rw [← hcτ] at h1
      have h2 : c' * τ * ((e.symm (xab hcd (1 : K)) : L) : G) * (c' * τ)⁻¹ =
          τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹ := by
        calc c' * τ * ((e.symm (xab hcd (1 : K)) : L) : G) * (c' * τ)⁻¹ =
            c' * (τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹) * c'⁻¹ := by group
          _ = τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹ := by
            rw [hcτv, mul_inv_cancel_right]
      rw [h2] at h1
      calc τ * ((e.symm (xab hcd (1 : K)) : L) : G) =
          τ * ((e.symm (xab hcd (1 : K)) : L) : G) * τ⁻¹ * τ := by group
        _ = ((e.symm (xab hcd (1 : K)) : L) : G) * τ := by rw [h1]
    have hτ1 := hT₀v τ hτ' hτv
    rw [hτ1, mul_one] at hcτ
    have hle : W₁ ⊓ centralizer (modelToG e X₀ : Set G) ≤ centralizer ({t} : Set G) := by
      intro w hw
      rw [mem_centralizer_singleton_iff]
      have h := (mem_centralizer_iff.1 hc') w hw
      rw [hcτ] at h
      exact h
    rw [inf_eq_left.2 hle] at hV₀eq
    rw [hV₀eq, hV₀card] at hW₀card
    norm_num at hW₀card
  · rw [hT₀inf, Subgroup.card_bot]
    omega

end CFSG.SeitzReduction.LinearPilot
