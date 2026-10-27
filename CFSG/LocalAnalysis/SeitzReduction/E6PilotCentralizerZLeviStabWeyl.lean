module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviWeyl
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e6ZLeviStabWeylNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem zNodePair_check : ∀ p ∈ ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)),
    ∀ a ∈ ([Pi.single p.1 1, -Pi.single p.1 1] : List (Fin Tag.E6.rank → ℤ)),
    ∀ b ∈ ([Pi.single p.2 1, -Pi.single p.2 1] : List (Fin Tag.E6.rank → ℤ)),
      isRootB .E6 a = true ∧ isRootB .E6 b = true ∧ a ≠ -b ∧ isRootB .E6 (a + b) = false := by
  decide +kernel

theorem zReflect_check :
    (∀ β ∈ zFrame, reflect .E6 1 β = β) ∧
    (∀ β ∈ zFrame, reflect .E6 0 (reflect .E6 4 β) ∈ zFrame) ∧
    (∀ β ∈ zFrame, reflect .E6 4 (reflect .E6 0 β) ∈ zFrame) ∧
    (∀ β ∈ zFrame, reflect .E6 2 (reflect .E6 5 β) ∈ zFrame) ∧
    (∀ β ∈ zFrame, reflect .E6 5 (reflect .E6 2 β) ∈ zFrame) ∧
    reflect .E6 0 (Pi.single 4 1) = Pi.single 4 1 ∧ reflect .E6 4 (Pi.single 0 1) = Pi.single 0 1 ∧
    reflect .E6 2 (Pi.single 5 1) = Pi.single 5 1 ∧ reflect .E6 5 (Pi.single 2 1) = Pi.single 2 1 := by
  decide +kernel

theorem zPartner_check :
    (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 + (zγ - zδ) ∧
    (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1 + (zδ - zγ) ∧
    (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 + (zδ - zε) ∧
    (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 + (zε - zδ) := by
  decide +kernel

theorem zDescent_check :
    ∀ r ∈ rootFinset .E6, height r < 0 → r 3 = 0 → ∀ a ∈ zFrame, ∀ b ∈ zFrame, a ≠ b →
      r + (a - b) ∈ rootFinset .E6 → height (r + (a - b)) < 0 := by
  decide +kernel

theorem zFrame_nodup : zFrame.Nodup := by
  decide +kernel

theorem zNodePair_mem_zSPairs :
    (Pi.single 0 1, Pi.single 4 1) ∈ zSPairs ∧ (-Pi.single 0 1, -Pi.single 4 1) ∈ zSPairs ∧
    (Pi.single 2 1, Pi.single 5 1) ∈ zSPairs ∧ (-Pi.single 2 1, -Pi.single 5 1) ∈ zSPairs := by
  decide +kernel

variable {K : Type} [Field K]

theorem commute_pinnedX_of_isRootB_zS {a b : Fin Tag.E6.rank → ℤ} (ha : isRootB .E6 a = true)
    (hb : isRootB .E6 b = true) (hne : a ≠ -b) (hab : isRootB .E6 (a + b) = false) (s t : K) :
    Commute (pinnedX .E6 K a s) (pinnedX .E6 K b t) :=
  commute_pinnedX_of_oddDeriv (isRootB_iff.1 ha) (isRootB_iff.1 hb) hne
    (fun h => by rw [← isRootB_iff, hab] at h; exact Bool.false_ne_true h) s t

theorem pinnedX_mul_pinnedX_mem_zS {p : (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)}
    (hp : p ∈ zSPairs) (t : K) : pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t ∈ zS K :=
  subset_closure ⟨p, hp, t, rfl⟩

theorem commute_pinnedX_zNodePair {i j : Fin Tag.E6.rank}
    (hij : (i, j) ∈ ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)))
    {a b : Fin Tag.E6.rank → ℤ} (ha : a = Pi.single i 1 ∨ a = -Pi.single i 1)
    (hb : b = Pi.single j 1 ∨ b = -Pi.single j 1) (s t : K) :
    Commute (pinnedX .E6 K a s) (pinnedX .E6 K b t) := by
  have ha' : a ∈ ([Pi.single (i, j).1 1, -Pi.single (i, j).1 1] : List (Fin Tag.E6.rank → ℤ)) := by
    rcases ha with rfl | rfl <;> simp
  have hb' : b ∈ ([Pi.single (i, j).2 1, -Pi.single (i, j).2 1] : List (Fin Tag.E6.rank → ℤ)) := by
    rcases hb with rfl | rfl <;> simp
  obtain ⟨h1, h2, h3, h4⟩ := zNodePair_check (i, j) hij a ha' b hb'
  exact commute_pinnedX_of_isRootB_zS h1 h2 h3 h4 s t

theorem commute_weylElt_zNodePair {i j : Fin Tag.E6.rank}
    (hij : (i, j) ∈ ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank))) (s t : Kˣ) :
    Commute (weylElt .E6 K i s) (weylElt .E6 K j t) := by
  have c : ∀ {a b : Fin Tag.E6.rank → ℤ}, (a = Pi.single i 1 ∨ a = -Pi.single i 1) →
      (b = Pi.single j 1 ∨ b = -Pi.single j 1) → ∀ s t : K,
        Commute (pinnedX .E6 K a s) (pinnedX .E6 K b t) :=
    fun ha hb s t => commute_pinnedX_zNodePair hij ha hb s t
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, ← pinnedX_single, ← pinnedX_neg_single,
    ← pinnedX_single, ← pinnedX_neg_single]
  have hr : ∀ {a : Fin Tag.E6.rank → ℤ}, (a = Pi.single i 1 ∨ a = -Pi.single i 1) → ∀ s : K,
      Commute (pinnedX .E6 K a s) (pinnedX .E6 K (Pi.single j 1) t *
        pinnedX .E6 K (-Pi.single j 1) (-((t⁻¹ : Kˣ) : K)) * pinnedX .E6 K (Pi.single j 1) t) :=
    fun ha s => ((c ha (Or.inl rfl) s _).mul_right (c ha (Or.inr rfl) s _)).mul_right
      (c ha (Or.inl rfl) s _)
  exact ((hr (Or.inl rfl) _).mul_left (hr (Or.inr rfl) _)).mul_left (hr (Or.inl rfl) _)

theorem weylElt_mul_weylElt_mem_zS {i j : Fin Tag.E6.rank}
    (hij : (i, j) ∈ ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank))) (t : Kˣ) :
    weylElt .E6 K i t * weylElt .E6 K j t ∈ zS K := by
  have hp : (Pi.single i 1, Pi.single j 1) ∈ zSPairs ∧ (-Pi.single i 1, -Pi.single j 1) ∈ zSPairs := by
    have hij' : (i = 0 ∧ j = 4) ∨ (i = 2 ∧ j = 5) := by simpa using hij
    rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨zNodePair_mem_zSPairs.1, zNodePair_mem_zSPairs.2.1⟩
    · exact ⟨zNodePair_mem_zSPairs.2.2.1, zNodePair_mem_zSPairs.2.2.2⟩
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, ← pinnedX_single, ← pinnedX_neg_single,
    ← pinnedX_single, ← pinnedX_neg_single]
  set x := pinnedX .E6 K (Pi.single i 1) t
  set a := pinnedX .E6 K (-Pi.single i 1) (-((t⁻¹ : Kˣ) : K))
  set x' := pinnedX .E6 K (Pi.single j 1) t
  set a' := pinnedX .E6 K (-Pi.single j 1) (-((t⁻¹ : Kˣ) : K))
  have h1 : Commute x x' := commute_pinnedX_zNodePair hij (Or.inl rfl) (Or.inl rfl) _ _
  have h2 : Commute a x' := commute_pinnedX_zNodePair hij (Or.inr rfl) (Or.inl rfl) _ _
  have h3 : Commute x a' := commute_pinnedX_zNodePair hij (Or.inl rfl) (Or.inr rfl) _ _
  have e : x * a * x * (x' * a' * x') = (x * x') * (a * a') * (x * x') := by
    calc x * a * x * (x' * a' * x') = x * a * (x * x') * a' * x' := by group
      _ = x * a * (x' * x) * a' * x' := by rw [h1.eq]
      _ = x * (a * x') * (x * a') * x' := by group
      _ = x * (x' * a) * (a' * x) * x' := by rw [h2.eq, h3.eq]
      _ = (x * x') * (a * a') * (x * x') := by group
  rw [e]
  exact mul_mem (mul_mem (pinnedX_mul_pinnedX_mem_zS hp.1 (t : K))
    (pinnedX_mul_pinnedX_mem_zS hp.2 (-((t⁻¹ : Kˣ) : K)))) (pinnedX_mul_pinnedX_mem_zS hp.1 (t : K))

theorem torusElt_mul_torusElt_mem_zS {i j : Fin Tag.E6.rank}
    (hij : (i, j) ∈ ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank))) (t : Kˣ) :
    torusElt .E6 K i t * torusElt .E6 K j t ∈ zS K := by
  rw [torusElt, torusElt]
  have e : weylElt .E6 K i t * weylElt .E6 K i (-1) * (weylElt .E6 K j t * weylElt .E6 K j (-1)) =
      (weylElt .E6 K i t * weylElt .E6 K j t) * (weylElt .E6 K i (-1) * weylElt .E6 K j (-1)) := by
    rw [mul_assoc, ← mul_assoc (weylElt .E6 K i (-1)), (commute_weylElt_zNodePair hij _ _).eq]
    group
  rw [e]
  exact mul_mem (weylElt_mul_weylElt_mem_zS hij t) (weylElt_mul_weylElt_mem_zS hij (-1))

theorem weylElt_one_mul_weylElt_one_mem_zS {i j : Fin Tag.E6.rank}
    (hij : (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨ (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2)) :
    weylElt .E6 K j 1 * weylElt .E6 K i 1 ∈ zS K := by
  have h04 : ((0 : Fin Tag.E6.rank), (4 : Fin Tag.E6.rank)) ∈
      ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)) := by simp
  have h25 : ((2 : Fin Tag.E6.rank), (5 : Fin Tag.E6.rank)) ∈
      ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)) := by simp
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [← (commute_weylElt_zNodePair h04 1 1).eq]
    exact weylElt_mul_weylElt_mem_zS h04 1
  · exact weylElt_mul_weylElt_mem_zS h04 1
  · rw [← (commute_weylElt_zNodePair h25 1 1).eq]
    exact weylElt_mul_weylElt_mem_zS h25 1
  · exact weylElt_mul_weylElt_mem_zS h25 1

theorem height_smul_single_neg_of_partner {w : WeylGroup .E6}
    (hwJ : w ∈ parabolicWeylGroup .E6 zNodes) (hF : ∀ β ∈ zFrame, w • β ∈ zFrame)
    {i j : Fin Tag.E6.rank} {a b : Fin Tag.E6.rank → ℤ} (ha : a ∈ zFrame) (hb : b ∈ zFrame)
    (hab : a ≠ b) (hi3 : i ≠ 3)
    (hij : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 + (a - b))
    (hi : height (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) < 0) :
    height (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 := by
  have hr : w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 :=
    mem_rootFinset.2 (IsRoot.smul (isRoot_single _ i) w)
  have h3 : (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 3 = 0 := by
    rw [smul_apply_of_mem_parabolicWeylGroup hwJ _ (show (3 : Fin Tag.E6.rank) ∉ zNodes by
      simp [zNodes])]
    exact Pi.single_eq_of_ne (Ne.symm hi3) _
  have hne : w • a ≠ w • b := fun e => hab (smul_left_cancel w e)
  have e : w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) + (w • a - w • b) := by
    rw [hij, smul_add, smul_sub]
  rw [e]
  refine zDescent_check _ hr hi h3 _ (hF a ha) _ (hF b hb) hne ?_
  rw [← e]
  exact mem_rootFinset.2 (IsRoot.smul (isRoot_single _ j) w)

theorem canonicalRep_mem_zJ_sup_zS_of_length [CharP K 2] :
    ∀ (n : ℕ) (w : WeylGroup .E6), (coxeterSystem .E6).length w = n →
      w ∈ parabolicWeylGroup .E6 zNodes → (∀ β ∈ zFrame, w • β ∈ zFrame) →
      canonicalRep (coxeterSystem .E6) K w ∈ zJ K ⊔ zS K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hwJ hF
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one]
    exact one_mem _
  obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition .E6).2.2.2 w hw1
  have hiJ : i ∈ zNodes := by
    by_contra hi
    have h1 := smul_apply_of_mem_parabolicWeylGroup hwJ (Pi.single i 1) hi
    have h2 := (IsRoot.height_neg_iff hroot).1 hneg i
    rw [h1, Pi.single_eq_same] at h2
    omega
  have hlen1 : (coxeterSystem .E6).length (w * simple .E6 i) = n - 1 := by
    have := ((weyl_exchange_condition .E6).2.1 w i).1.2 ⟨hroot, hneg⟩
    omega
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, CoxeterSystem.length_eq_zero_iff] at hw
      exact absurd hw hw1
    · exact h0
  have hsi : simple .E6 i ∈ parabolicWeylGroup .E6 zNodes := subset_closure ⟨i, hiJ, rfl⟩
  have hi5 : i = 1 ∨ i = 0 ∨ i = 4 ∨ i = 2 ∨ i = 5 := by
    have key : ∀ i : Fin Tag.E6.rank, i ≠ 3 → i = 1 ∨ i = 0 ∨ i = 4 ∨ i = 2 ∨ i = 5 := by
      decide
    exact key i hiJ
  rcases hi5 with h | h
  · subst h
    have hF' : ∀ β ∈ zFrame, (w * simple .E6 1) • β ∈ zFrame := fun β hβ => by
      rw [mul_smul, simple_smul, zReflect_check.1 β hβ]
      exact hF β hβ
    have hmem := ih (n - 1) (by omega) _ hlen1 (mul_mem hwJ hsi) hF'
    have e : w = w * simple .E6 1 * simple .E6 1 := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e, canonicalRep_mul_charTwo', canonicalRep_simple]
    exact mul_mem hmem (mem_sup_left (EPilot.weylElt_mem_rootPair 1 1))
  · obtain ⟨j, a, b, ha, hb, hab, hij, hsij, hsF, hji, hjJ⟩ :
        ∃ (j : Fin Tag.E6.rank) (a b : Fin Tag.E6.rank → ℤ), a ∈ zFrame ∧ b ∈ zFrame ∧ a ≠ b ∧
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 + (a - b) ∧
          reflect .E6 i (Pi.single j 1) = Pi.single j 1 ∧
          (∀ β ∈ zFrame, reflect .E6 i (reflect .E6 j β) ∈ zFrame) ∧
          weylElt .E6 K j 1 * weylElt .E6 K i 1 ∈ zS K ∧ j ∈ zNodes := by
      have hγ : zγ ∈ zFrame := mem_zFrame.2 (Or.inl rfl)
      have hδ : zδ ∈ zFrame := mem_zFrame.2 (Or.inr (Or.inl rfl))
      have hε : zε ∈ zFrame := mem_zFrame.2 (Or.inr (Or.inr rfl))
      obtain ⟨-, k04, k40, k25, k52, r04, r40, r25, r52⟩ := zReflect_check
      obtain ⟨p04, p40, p25, p52⟩ := zPartner_check
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨4, zγ, zδ, hγ, hδ, zFrame_ne.1, p04, r04, k04,
          weylElt_one_mul_weylElt_one_mem_zS (Or.inl ⟨rfl, rfl⟩),
          show (4 : Fin Tag.E6.rank) ≠ 3 by decide⟩
      · exact ⟨0, zδ, zγ, hδ, hγ, Ne.symm zFrame_ne.1, p40, r40, k40,
          weylElt_one_mul_weylElt_one_mem_zS (Or.inr (Or.inl ⟨rfl, rfl⟩)),
          show (0 : Fin Tag.E6.rank) ≠ 3 by decide⟩
      · exact ⟨5, zδ, zε, hδ, hε, zFrame_ne.2.2, p25, r25, k25,
          weylElt_one_mul_weylElt_one_mem_zS (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
          show (5 : Fin Tag.E6.rank) ≠ 3 by decide⟩
      · exact ⟨2, zε, zδ, hε, hδ, Ne.symm zFrame_ne.2.2, p52, r52, k52,
          weylElt_one_mul_weylElt_one_mem_zS (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))),
          show (2 : Fin Tag.E6.rank) ≠ 3 by decide⟩
    have hnegj := height_smul_single_neg_of_partner hwJ hF ha hb hab hiJ hij hneg
    have hjroot : IsRoot .E6 ((w * simple .E6 i) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) _
    have hw1j : (w * simple .E6 i) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      rw [mul_smul, simple_smul, hsij]
    have hlen2 : (coxeterSystem .E6).length (w * simple .E6 i * simple .E6 j) = n - 2 := by
      have := ((weyl_exchange_condition .E6).2.1 (w * simple .E6 i) j).1.2
        ⟨hjroot, by rw [hw1j]; exact hnegj⟩
      omega
    have hsj : simple .E6 j ∈ parabolicWeylGroup .E6 zNodes := subset_closure ⟨j, hjJ, rfl⟩
    have hF' : ∀ β ∈ zFrame, (w * simple .E6 i * simple .E6 j) • β ∈ zFrame := fun β hβ => by
      rw [mul_smul, mul_smul, simple_smul, simple_smul]
      exact hF _ (hsF β hβ)
    have hmem := ih (n - 2) (by omega) _ hlen2 (mul_mem (mul_mem hwJ hsi) hsj) hF'
    have e : w = w * simple .E6 i * simple .E6 j * simple .E6 j * simple .E6 i := by
      rw [mul_assoc (w * simple .E6 i) (simple .E6 j) (simple .E6 j),
        CoxeterSystem.simple_mul_simple_self, mul_one, mul_assoc w (simple .E6 i) (simple .E6 i),
        CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e, canonicalRep_mul_charTwo', canonicalRep_mul_charTwo', canonicalRep_simple,
      canonicalRep_simple, mul_assoc]
    exact mul_mem hmem (mem_sup_right hji)

theorem canonicalRep_mem_zJ_sup_zS [CharP K 2] {w : WeylGroup .E6}
    (hwJ : w ∈ parabolicWeylGroup .E6 zNodes) (hF : ∀ β ∈ zFrame, w • β ∈ zFrame) :
    canonicalRep (coxeterSystem .E6) K w ∈ zJ K ⊔ zS K :=
  canonicalRep_mem_zJ_sup_zS_of_length _ w rfl hwJ hF

theorem rootChar_cartanChar_eq_prod (c : Fin Tag.E6.rank → Kˣ) (β : Fin Tag.E6.rank → ℤ) :
    rootChar (cartanChar c) β =
      c 0 ^ (∑ l, Tag.cartan .E6 0 l * β l) * c 1 ^ (∑ l, Tag.cartan .E6 1 l * β l) *
        c 2 ^ (∑ l, Tag.cartan .E6 2 l * β l) * c 3 ^ (∑ l, Tag.cartan .E6 3 l * β l) *
          c 4 ^ (∑ l, Tag.cartan .E6 4 l * β l) * c 5 ^ (∑ l, Tag.cartan .E6 5 l * β l) := by
  have h : rootChar (cartanChar c) β = ∏ j, c j ^ (∑ l, Tag.cartan .E6 j l * β l) := by
    simp only [rootChar, cartanChar, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow_eq_zpow_sum]
  rw [h]
  exact Fin.prod_univ_six (fun j : Fin 6 => c j ^ (∑ l, Tag.cartan .E6 j l * β l))

theorem zFrame_cartan_check :
    (∀ j, ∑ l, Tag.cartan .E6 j l * zγ l = (![-1, 0, 0, 0, 1, 0] : Fin Tag.E6.rank → ℤ) j) ∧
    (∀ j, ∑ l, Tag.cartan .E6 j l * zδ l = (![1, 0, -1, 1, -1, 1] : Fin Tag.E6.rank → ℤ) j) ∧
    (∀ j, ∑ l, Tag.cartan .E6 j l * zε l = (![0, 0, 1, 0, 0, -1] : Fin Tag.E6.rank → ℤ) j) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;> fin_cases j <;> decide +kernel

theorem rootDiagUnit_conj_rootProd (b : Fin Tag.E6.rank → Kˣ) {l : List (Fin Tag.E6.rank → ℤ)}
    (hl : ∀ β ∈ l, IsRoot .E6 β) (c : (Fin Tag.E6.rank → ℤ) → K) :
    rootDiagUnit .E6 b * rootProd .E6 K l c * (rootDiagUnit .E6 b)⁻¹ =
      rootProd .E6 K l (fun β => (rootChar b β : K) * c β) := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih =>
    rw [rootProd_cons, rootProd_cons, ← rootDiagUnit_conj_pinnedX b (hl a List.mem_cons_self),
      ← ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ)]
    group

theorem mem_zJ_sup_zS_of_mem_torusGroup {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K)
    (hz : h * zAS K = zAS K * h) : h ∈ zJ K ⊔ zS K := by
  obtain ⟨c, rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup hh
  have hconj : rootDiagUnit .E6 (cartanChar c) * zAS K * (rootDiagUnit .E6 (cartanChar c))⁻¹ =
      zAS K := by
    rw [hz, mul_inv_cancel_right]
  have hFr : ∀ β ∈ zFrame, IsRoot .E6 β ∧ 0 < height β := fun β hβ =>
    pos_of_mem_zPsi (mem_zPsi_of_mem_zFrame hβ)
  rw [zAS, rootDiagUnit_conj_rootProd _ (fun β hβ => (hFr β hβ).1)] at hconj
  have hinj := rootProd_injective zFrame_nodup hFr hconj
  have hχ : ∀ β ∈ zFrame, rootChar (cartanChar c) β = 1 := fun β hβ => by
    have := hinj β hβ
    rw [mul_one] at this
    exact Units.ext this
  obtain ⟨cγ, cδ, cε⟩ := zFrame_cartan_check
  have eγ : (c 0)⁻¹ * c 4 = 1 := by
    have := hχ zγ (mem_zFrame.2 (Or.inl rfl))
    rw [rootChar_cartanChar_eq_prod] at this
    simpa [cγ] using this
  have eδ : c 0 * (c 2)⁻¹ * c 3 * (c 4)⁻¹ * c 5 = 1 := by
    have := hχ zδ (mem_zFrame.2 (Or.inr (Or.inl rfl)))
    rw [rootChar_cartanChar_eq_prod] at this
    simpa [cδ] using this
  have eε : c 2 * (c 5)⁻¹ = 1 := by
    have := hχ zε (mem_zFrame.2 (Or.inr (Or.inr rfl)))
    rw [rootChar_cartanChar_eq_prod] at this
    simpa [cε] using this
  have h4 : c 4 = c 0 := (inv_mul_eq_one.1 eγ).symm
  have h5 : c 5 = c 2 := (mul_inv_eq_one.1 eε).symm
  have h3 : c 3 = 1 := by
    rw [h4, h5] at eδ
    have e : c 0 * (c 2)⁻¹ * c 3 * (c 0)⁻¹ * c 2 = c 3 := by
      simp only [mul_comm, mul_left_comm, mul_assoc]
      simp only [mul_inv_cancel_left]
    rw [← e]
    exact eδ
  have hdec : rootDiagUnit .E6 (cartanChar c) =
      torusElt .E6 K 1 (c 1) * (torusElt .E6 K 0 (c 0) * torusElt .E6 K 4 (c 0)) *
        (torusElt .E6 K 2 (c 2) * torusElt .E6 K 5 (c 2)) := by
    simp only [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext l
    simp only [cartanChar, Pi.mul_apply]
    rw [show (∏ j, c j ^ Tag.cartan .E6 j l) = c 0 ^ Tag.cartan .E6 0 l * c 1 ^ Tag.cartan .E6 1 l *
        c 2 ^ Tag.cartan .E6 2 l * c 3 ^ Tag.cartan .E6 3 l * c 4 ^ Tag.cartan .E6 4 l *
          c 5 ^ Tag.cartan .E6 5 l from
      Fin.prod_univ_six (fun j : Fin 6 => c j ^ Tag.cartan .E6 j l)]
    simp only [h3, h4, h5, one_zpow, mul_one]
    simp only [mul_left_comm, mul_assoc]
  have h04 : ((0 : Fin Tag.E6.rank), (4 : Fin Tag.E6.rank)) ∈
      ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)) := by simp
  have h25 : ((2 : Fin Tag.E6.rank), (5 : Fin Tag.E6.rank)) ∈
      ([(0, 4), (2, 5)] : List (Fin Tag.E6.rank × Fin Tag.E6.rank)) := by simp
  rw [hdec]
  exact mul_mem (mul_mem (mem_sup_left (F4Pilot.torusElt_mem_rootPair 1 (c 1)))
    (mem_sup_right (torusElt_mul_torusElt_mem_zS h04 (c 0))))
    (mem_sup_right (torusElt_mul_torusElt_mem_zS h25 (c 2)))

end CFSG.SeitzReduction.E6Pilot
