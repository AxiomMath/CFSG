module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionInner
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectV

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Steinberg.Adjoint

@[expose] def xiVF : Fin 10 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def xiVP : Fin 7 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 0], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 2, 1]]

@[expose] def xiVP' : Fin 7 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1]]

@[expose] def xiVD : Fin 3 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1]]

@[expose] def xiVD' : Fin 3 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0]]

@[expose] def xiVLand : Fin 3 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![1, 1, 1, 2, 1, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def xiVAll : Fin 30 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1], ![1, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 0]]

theorem xiVAll_check : Function.Injective xiVAll ∧
    ∀ i, twistedE6TwoRootB (xiVAll i) = true ∧ 0 < height (xiVAll i) := by
  decide +kernel

theorem xiV_central_check :
    (∀ i, twistedE6TwoRootB (xiVF i) = true ∧ permLattice TwistTag.E6.perm (xiVF i) = xiVF i ∧
      twistedE6ClassCentralB (xiVF i) TwistedE6Pilot.vReprRoots = true) ∧
    (∀ j, twistedE6TwoRootB (xiVP j) = true ∧ permLattice TwistTag.E6.perm (xiVP j) = xiVP' j ∧
      twistedE6ClassCentralB (xiVP j) TwistedE6Pilot.vReprRoots = true ∧
      twistedE6TwoRootB (xiVP' j) = true ∧ twistedE6ClassCentralB (xiVP' j) TwistedE6Pilot.vReprRoots = true) ∧
    (∀ l, twistedE6TwoRootB (xiVD l) = true ∧ twistedE6TwoRootB (xiVD' l) = true ∧
      permLattice TwistTag.E6.perm (xiVD l) = xiVD' l) := by
  decide +kernel

theorem xiVLand_check : ∀ l : Fin 3,
    xiVD l + twistedE6ClassRootA = xiVLand l ∧ xiVD' l + twistedE6ClassRootA' = xiVLand l ∧
    twistedE6TwoRootB (xiVLand l) = true ∧
    twistedE6TwoRootB (xiVD l + twistedE6ClassRootB) = false ∧
    twistedE6TwoRootB (xiVD' l + twistedE6ClassRootB) = false ∧
    twistedE6TwoRootB (xiVD l + twistedE6ClassRootA') = false ∧
    twistedE6TwoRootB (xiVD' l + twistedE6ClassRootA) = false ∧
    twistedE6TwoRootB (xiVD l + xiVLand l) = false ∧
    twistedE6TwoRootB (xiVD' l + xiVLand l) = false ∧
    twistedE6TwoRootB (xiVLand l + twistedE6ClassRootA) = false ∧
    xiVD l ≠ twistedE6ClassRootB ∧ xiVD' l ≠ twistedE6ClassRootB ∧
    xiVD l ≠ twistedE6ClassRootA' ∧ xiVD' l ≠ twistedE6ClassRootA ∧
    xiVD l ≠ xiVLand l ∧ xiVD' l ≠ xiVLand l ∧ xiVLand l ≠ twistedE6ClassRootA ∧
    xiVD l ≠ -twistedE6ClassRootB ∧ xiVD' l ≠ -twistedE6ClassRootB ∧
    xiVD l ≠ -twistedE6ClassRootA' ∧ xiVD' l ≠ -twistedE6ClassRootA ∧
    xiVD l ≠ -xiVLand l ∧ xiVD' l ≠ -xiVLand l ∧ xiVLand l ≠ -twistedE6ClassRootA ∧
    twistedE6ClassRootA ≠ xiVD l ∧ twistedE6ClassRootA ≠ -xiVD l ∧
    twistedE6ClassRootA' ≠ xiVD' l ∧ twistedE6ClassRootA' ≠ -xiVD' l := by
  decide +kernel

section Diagonal


variable {K : Type} [Field K]

theorem not_isRoot_of_twistedE6TwoRootB_eq_false {α : Fin TwistTag.E6.tag.rank → ℤ}
    (h : twistedE6TwoRootB α = false) : ¬ IsRoot TwistTag.E6.tag α := by
  rw [isRoot_iff_twistedE6TwoRootB, h]
  exact Bool.false_ne_true

theorem commute_xiVDiag_twistedE6ClassV [CharP K 2] (l : Fin 3) (c : K) :
    Commute (pinnedX TwistTag.E6.tag K (xiVD l) c * pinnedX TwistTag.E6.tag K (xiVD' l) c)
      (twistedE6ClassV K) := by
  obtain ⟨h1, h2, hγr, n1, n2, n3, n4, n5, n6, n7, d1, d2, d3, d4, d5, d6, d7, e1, e2, e3, e4,
    e5, e6, e7, f1, f2, f3, f4⟩ := xiVLand_check l
  obtain ⟨-, -, hD⟩ := xiV_central_check
  have hβ := isRoot_iff_twistedE6TwoRootB.2 (hD l).1
  have hβ' := isRoot_iff_twistedE6TwoRootB.2 (hD l).2.1
  have hγ := isRoot_iff_twistedE6TwoRootB.2 hγr
  obtain ⟨-, -, hA, hA', hB⟩ := isRoot_twistedE6ClassRoots
  set β := xiVD l with hβdef
  set β' := xiVD' l with hβ'def
  set γ := xiVLand l with hγdef
  set x := pinnedX TwistTag.E6.tag K β c with hx
  set y := pinnedX TwistTag.E6.tag K β' c with hy
  set z := pinnedX TwistTag.E6.tag K γ c with hz
  set a := pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 with ha
  set a' := pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 with ha'
  set b := pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 with hb
  have cxb : Commute x b := commute_pinnedX_of_not_isRoot_add_E6 hβ hB d1 e1
    (not_isRoot_of_twistedE6TwoRootB_eq_false n1) c 1
  have cyb : Commute y b := commute_pinnedX_of_not_isRoot_add_E6 hβ' hB d2 e2
    (not_isRoot_of_twistedE6TwoRootB_eq_false n2) c 1
  have cxa' : Commute x a' := commute_pinnedX_of_not_isRoot_add_E6 hβ hA' d3 e3
    (not_isRoot_of_twistedE6TwoRootB_eq_false n3) c 1
  have cya : Commute y a := commute_pinnedX_of_not_isRoot_add_E6 hβ' hA d4 e4
    (not_isRoot_of_twistedE6TwoRootB_eq_false n4) c 1
  have cxz : Commute x z := commute_pinnedX_of_not_isRoot_add_E6 hβ hγ d5 e5
    (not_isRoot_of_twistedE6TwoRootB_eq_false n5) c c
  have cyz : Commute y z := commute_pinnedX_of_not_isRoot_add_E6 hβ' hγ d6 e6
    (not_isRoot_of_twistedE6TwoRootB_eq_false n6) c c
  have cza : Commute z a := commute_pinnedX_of_not_isRoot_add_E6 hγ hA d7 e7
    (not_isRoot_of_twistedE6TwoRootB_eq_false n7) c 1
  have s1 : a' * y * a'⁻¹ = y * z :=
    E6Pilot.conj_pinnedX_eq_mul_of_charTwo hA' hβ' f3 f4 ((add_comm _ _).trans h2) hγ c cyz
  have s2 : a * x * a⁻¹ = x * z :=
    E6Pilot.conj_pinnedX_eq_mul_of_charTwo hA hβ f1 f2 ((add_comm _ _).trans h1) hγ c cxz
  have s1' : a' * y = y * z * a' := by rw [← s1, inv_mul_cancel_right]
  have s2' : a * x = x * z * a := by rw [← s2, inv_mul_cancel_right]
  have hzz : z * z = 1 := by
    rw [hz, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hA2 : Commute (x * y) (a * a') := by
    change x * y * (a * a') = a * a' * (x * y)
    symm
    calc a * a' * (x * y) = a * (a' * x) * y := by simp only [mul_assoc]
      _ = a * (x * a') * y := by rw [← cxa'.eq]
      _ = a * x * (a' * y) := by simp only [mul_assoc]
      _ = a * x * (y * z * a') := by rw [s1']
      _ = (a * x) * y * z * a' := by simp only [mul_assoc]
      _ = (x * z * a) * y * z * a' := by rw [s2']
      _ = x * z * (a * y) * z * a' := by simp only [mul_assoc]
      _ = x * z * (y * a) * z * a' := by rw [← cya.eq]
      _ = x * z * y * (a * z) * a' := by simp only [mul_assoc]
      _ = x * z * y * (z * a) * a' := by rw [← cza.eq]
      _ = x * (z * y) * z * (a * a') := by simp only [mul_assoc]
      _ = x * (y * z) * z * (a * a') := by rw [← cyz.eq]
      _ = x * y * (z * z) * (a * a') := by simp only [mul_assoc]
      _ = x * y * (a * a') := by rw [hzz, mul_one]
  have hv : twistedE6ClassV K = a * a' * b := rfl
  rw [hv]
  exact hA2.mul_right (cxb.mul_left cyb)

end Diagonal

section Count


theorem pow_dvd_card_centralizer_of_injective_le {τ : Tag} {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f) (C : Subgroup (ModGL τ K)) (w : C)
    {X : Type*} [Finite X] {a : ℕ} (hX : Nat.card X = p ^ a) (ψ : X → ModGL τ K)
    (hψ : Function.Injective ψ) (hψU : ∀ x, ψ x ∈ posUnipotent τ K) (hψC : ∀ x, ψ x ∈ C)
    (hψw : ∀ x, Commute (ψ x) (w : ModGL τ K)) :
    p ^ a ∣ Nat.card (centralizer ({w} : Set C)) := by
  classical
  set H : Subgroup (ModGL τ K) :=
    centralizer ({(w : ModGL τ K)} : Set (ModGL τ K)) ⊓ posUnipotent τ K ⊓ C with hHdef
  have hU : Nat.card (posUnipotent τ K) =
      p ^ (f * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) := by
    rw [card_posUnipotent, hK, ← pow_mul]
  have hHU : Nat.card H ∣ Nat.card (posUnipotent τ K) :=
    card_dvd_of_le (inf_le_left.trans inf_le_right)
  rw [hU] at hHU
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hHU
  have hUfin : Finite (posUnipotent τ K) :=
    Nat.finite_of_card_ne_zero (by rw [hU]; exact pow_ne_zero _ hp.ne_zero)
  have hHfin : Finite H :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left.trans inf_le_right : H ≤ posUnipotent τ K))
      (Subgroup.inclusion_injective _)
  have hmem : ∀ x, ψ x ∈ H := fun x =>
    mem_inf.2 ⟨mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hψw x).eq, hψU x⟩, hψC x⟩
  have hXH : Nat.card X ≤ Nat.card H :=
    Nat.card_le_card_of_injective (fun x => (⟨ψ x, hmem x⟩ : H))
      fun x y h => hψ (congrArg Subtype.val h)
  rw [hX, hk] at hXH
  have hak : a ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hXH
  have h1 : p ^ a ∣ Nat.card H := hk ▸ pow_dvd_pow p hak
  have h2 : Nat.card H ∣ Nat.card (centralizer ({w} : Set C)) := by
    rw [← card_map_of_injective C.subtype_injective]
    refine card_dvd_of_le fun y hy => ?_
    obtain ⟨⟨hyc, -⟩, hyC⟩ := mem_inf.1 hy |>.imp_left mem_inf.1
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hyc))
  exact h1.trans h2

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem two_pow_dvd_card_centralizer_twistedE6ClassV [CharP K 2] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ^ (27 * f) ∣ Nat.card (centralizer ({⟨twistedE6ClassV K,
      twistedE6ClassV_mem_graphFixedRootGroup (TwistedE6Pilot.apply_apply_eq hK hσ)⟩} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := TwistedE6Pilot.finite_of_card hK
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσσ := TwistedE6Pilot.apply_apply_eq hK hσ
  have hσk : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← map_pow]
    congr 1
    have : Fintype k := Fintype.ofFinite k
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hinjk := (algebraMap k K).injective
  let ι : (Fin 10 → k) × (Fin 7 → K) × (Fin 3 → k) → Fin 30 → K := fun x =>
    ![algebraMap k K (x.1 0), algebraMap k K (x.1 1), algebraMap k K (x.1 2), algebraMap k K (x.1 3), algebraMap k K (x.1 4), algebraMap k K (x.1 5), algebraMap k K (x.1 6), algebraMap k K (x.1 7), algebraMap k K (x.1 8), algebraMap k K (x.1 9), x.2.1 0, σ (x.2.1 0), x.2.1 1, σ (x.2.1 1), x.2.1 2, σ (x.2.1 2), x.2.1 3, σ (x.2.1 3), x.2.1 4, σ (x.2.1 4), x.2.1 5, σ (x.2.1 5), x.2.1 6, σ (x.2.1 6), algebraMap k K (x.2.2 0), algebraMap k K (x.2.2 0), algebraMap k K (x.2.2 1), algebraMap k K (x.2.2 1), algebraMap k K (x.2.2 2), algebraMap k K (x.2.2 2)]
  have hι : Function.Injective ι := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have e : ∀ n : Fin 30, ι (a, b, c) n = ι (a', b', c') n := fun n => congrFun h n
    simp only [ι] at e
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) (funext fun l => ?_))
    · fin_cases i
      · exact hinjk (by simpa using e 0)
      · exact hinjk (by simpa using e 1)
      · exact hinjk (by simpa using e 2)
      · exact hinjk (by simpa using e 3)
      · exact hinjk (by simpa using e 4)
      · exact hinjk (by simpa using e 5)
      · exact hinjk (by simpa using e 6)
      · exact hinjk (by simpa using e 7)
      · exact hinjk (by simpa using e 8)
      · exact hinjk (by simpa using e 9)
    · fin_cases j
      · simpa using e 10
      · simpa using e 12
      · simpa using e 14
      · simpa using e 16
      · simpa using e 18
      · simpa using e 20
      · simpa using e 22
    · fin_cases l
      · exact hinjk (by simpa using e 24)
      · exact hinjk (by simpa using e 26)
      · exact hinjk (by simpa using e 28)
  obtain ⟨hinjA, hroots⟩ := xiVAll_check
  obtain ⟨hU, hF⟩ := positive_root_product_injectivity TwistTag.E6.tag K xiVAll hinjA
    fun i => ⟨isRoot_iff_twistedE6TwoRootB.2 (hroots i).1, (hroots i).2⟩
  obtain ⟨hFc, hPc, hDc⟩ := xiV_central_check
  have hR : ∀ ε ∈ TwistedE6Pilot.vReprRoots, IsRoot TwistTag.E6.tag ε := by
    intro ε hε
    rw [isRoot_iff_twistedE6TwoRootB]
    revert ε
    decide +kernel
  have hv := TwistedE6Pilot.twistedE6ClassV_eq_list_prod (K := K)
  have hG : ∀ x, (List.ofFn fun i => pinnedX TwistTag.E6.tag K (xiVAll i) (ι x i)).prod =
      (List.ofFn fun i => pinnedX TwistTag.E6.tag K (xiVF i) (algebraMap k K (x.1 i))).prod *
        ((List.ofFn fun j => pinnedX TwistTag.E6.tag K (xiVP j) (x.2.1 j) *
          pinnedX TwistTag.E6.tag K (xiVP' j) (σ (x.2.1 j))).prod *
        (List.ofFn fun l => pinnedX TwistTag.E6.tag K (xiVD l) (algebraMap k K (x.2.2 l)) *
          pinnedX TwistTag.E6.tag K (xiVD' l) (algebraMap k K (x.2.2 l))).prod) := by
    intro x
    simp only [ι, xiVAll, xiVF, xiVP, xiVP', xiVD, xiVD', List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_nil, mul_one, mul_assoc, Matrix.cons_val_succ,
      Matrix.cons_val_zero]
    rfl
  refine pow_dvd_card_centralizer_of_injective_le Nat.prime_two (f := 2 * f)
    (by rw [hK, ← pow_mul, mul_comm]) (graphFixedRootGroup TwistTag.E6 K σ) _
    (X := (Fin 10 → k) × (Fin 7 → K) × (Fin 3 → k)) ?_ _ (hF.comp hι) (fun x => hU _)
    (fun x => ?_) (fun x => ?_)
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fun, Nat.card_fin,
      Nat.card_fin, Nat.card_fin, hk, hK, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add]
    ring_nf
  · change (List.ofFn fun i => pinnedX TwistTag.E6.tag K (xiVAll i) (ι x i)).prod ∈ _
    rw [hG]
    refine mul_mem (list_prod_mem fun g hg => ?_) (mul_mem (list_prod_mem fun g hg => ?_)
      (list_prod_mem fun g hg => ?_))
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact pinnedX_mem_graphFixedRootGroup_of_fixed σ
        (isRoot_iff_twistedE6TwoRootB.2 (hFc i).1) (hFc i).2.1 (hσk _)
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
      have h := twistedE6PairX_mem_graphFixedRootGroup hσσ
        (isRoot_iff_twistedE6TwoRootB.2 (hPc j).1) (x.2.1 j)
      rwa [twistedE6PairX, (hPc j).2.1] at h
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hg
      have h := twistedE6PairX_mem_graphFixedRootGroup hσσ
        (isRoot_iff_twistedE6TwoRootB.2 (hDc l).1) (algebraMap k K (x.2.2 l))
      rwa [twistedE6PairX, (hDc l).2.2, hσk] at h
  · change Commute (List.ofFn fun i => pinnedX TwistTag.E6.tag K (xiVAll i) (ι x i)).prod _
    rw [hG]
    refine Commute.mul_left (Commute.list_prod_left _ _ fun g hg => ?_)
      (Commute.mul_left (Commute.list_prod_left _ _ fun g hg => ?_)
        (Commute.list_prod_left _ _ fun g hg => ?_))
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      change Commute _ (twistedE6ClassV K)
      rw [hv]
      exact commute_pinnedX_list_prod_of_centralB hR
        (isRoot_iff_twistedE6TwoRootB.2 (hFc i).1) (hFc i).2.2 _
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
      change Commute _ (twistedE6ClassV K)
      rw [hv]
      exact (commute_pinnedX_list_prod_of_centralB hR
        (isRoot_iff_twistedE6TwoRootB.2 (hPc j).1) (hPc j).2.2.1 _).mul_left
        (commute_pinnedX_list_prod_of_centralB hR
          (isRoot_iff_twistedE6TwoRootB.2 (hPc j).2.2.2.1) (hPc j).2.2.2.2 _)
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hg
      exact commute_xiVDiag_twistedE6ClassV l _

end Count

end CFSG.SeitzReduction.F4Pilot
