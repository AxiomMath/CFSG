module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem card_le_prod_cands {X : Type*} (n : ℕ) :
    ∀ (K : Type) [Group K] [Finite K] [MulAction K X] (b : ℕ → X) (cand : ℕ → Finset X),
      (∀ m < n, ∀ g : K, (∀ j < m, g • b j = b j) → g • b m ∈ cand m) →
      (∀ g : K, (∀ j < n, g • b j = b j) → g = 1) →
      Nat.card K ≤ ∏ m ∈ Finset.range n, (cand m).card := by
  induction n with
  | zero =>
    intro K _ _ _ b cand _ h1
    rw [Finset.prod_range_zero]
    have hsub : Subsingleton K := ⟨fun x y => by
      rw [h1 x fun j hj => absurd hj (Nat.not_lt_zero j),
        h1 y fun j hj => absurd hj (Nat.not_lt_zero j)]⟩
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ n ih =>
    intro K _ _ _ b cand h0 h1
    have hcard : Nat.card K = Nat.card (MulAction.orbit K (b 0)) *
        Nat.card (MulAction.stabilizer K (b 0)) := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (b 0))).symm
    have horb : Nat.card (MulAction.orbit K (b 0)) ≤ (cand 0).card := by
      have hsub : MulAction.orbit K (b 0) ⊆ ((cand 0 : Finset X) : Set X) := by
        rintro _ ⟨g, rfl⟩
        exact h0 0 (Nat.succ_pos n) g fun j hj => absurd hj (Nat.not_lt_zero j)
      calc Nat.card (MulAction.orbit K (b 0)) ≤ Nat.card ((cand 0 : Finset X) : Set X) :=
            Nat.card_mono (Finset.finite_toSet _) hsub
        _ = (cand 0).card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hA : ∀ m < n, ∀ g : ↥(MulAction.stabilizer K (b 0)),
        (∀ j < m, g • b (j + 1) = b (j + 1)) → g • b (m + 1) ∈ cand (m + 1) := by
      intro m hm g hg
      refine h0 (m + 1) (by omega) (g : K) fun j hj => ?_
      cases j with
      | zero => exact MulAction.mem_stabilizer_iff.1 g.2
      | succ i => exact hg i (by omega)
    have hB : ∀ g : ↥(MulAction.stabilizer K (b 0)),
        (∀ j < n, g • b (j + 1) = b (j + 1)) → g = 1 := by
      intro g hg
      apply Subtype.ext
      refine h1 (g : K) fun j hj => ?_
      cases j with
      | zero => exact MulAction.mem_stabilizer_iff.1 g.2
      | succ i => exact hg i (by omega)
    have hH := ih (MulAction.stabilizer K (b 0)) (fun i => b (i + 1))
      (fun i => cand (i + 1)) hA hB
    rw [hcard, Finset.prod_range_succ']
    calc Nat.card (MulAction.orbit K (b 0)) * Nat.card (MulAction.stabilizer K (b 0))
        ≤ (cand 0).card * ∏ m ∈ Finset.range n, (cand (m + 1)).card :=
          Nat.mul_le_mul horb hH
      _ = (∏ m ∈ Finset.range n, (cand (m + 1)).card) * (cand 0).card := mul_comm _ _

@[expose] def bF (j : ℕ) : Fin 128 := ⟨baseArr[j]! % 128, Nat.mod_lt _ (by norm_num)⟩

theorem bF_eq {j : ℕ} (hj : j < 6) : bF j = ⟨baseArr[j]!, (baseArr_facts j hj).1⟩ :=
  Fin.ext (Nat.mod_eq_of_lt (baseArr_facts j hj).1)

theorem bF_val {j : ℕ} (hj : j < 6) : ((bF j : Fin 128) : ℕ) = baseArr[j]! :=
  Nat.mod_eq_of_lt (baseArr_facts j hj).1

@[expose] def candF (k : ℕ) : Finset (Fin 128) :=
  Finset.univ.filter fun x : Fin 128 => (x : ℕ) ∈ candSet k

theorem card_candF (k : ℕ) : (candF k).card = (candSet k).length := by
  have hnd : (candSet k).Nodup := by
    unfold candSet
    exact (List.nodup_range).filter _
  have hmap : (candF k).map Fin.valEmbedding = (candSet k).toFinset := by
    ext y
    simp only [candF, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have hy128 : y < 128 := List.mem_range.1 (List.mem_of_mem_filter hy)
      exact ⟨⟨y, hy128⟩, hy, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, List.toFinset_card_of_nodup hnd]

theorem permVal_bF (π : Equiv.Perm (Fin 128)) {j : ℕ} (hj : j < 6) :
    permVal π baseArr[j]! = ((π (bF j) : Fin 128) : ℕ) := by
  rw [permVal_eq π (baseArr_facts j hj).1, bF_eq hj]

theorem candSet_prod :
    ∏ m ∈ Finset.range 6, (candSet m).length = 3317760 := by
  have h : (((List.range 6).map fun k => (candSet k).length).prod == 3317760) = true :=
    Certificates.certificate27820.2.2.2.2
  have e : ∏ m ∈ Finset.range 6, (candSet m).length =
      ((List.range 6).map fun k => (candSet k).length).prod := rfl
  rw [e]
  exact beq_iff_eq.1 h

theorem card_autC_le : Nat.card AutC ≤ 3317760 := by
  have hstep : ∀ m < 6, ∀ g : ↥AutC, (∀ j < m, g • bF j = bF j) → g • bF m ∈ candF m := by
    intro m hm g hg
    have hfix : ∀ j < m, permVal (g : Equiv.Perm (Fin 128)) baseArr[j]! = baseArr[j]! := by
      intro j hj
      have h1 : (g : Equiv.Perm (Fin 128)) (bF j) = bF j := hg j hj
      rw [permVal_bF _ (by omega : j < 6), h1, bF_val (by omega : j < 6)]
    have hmem := cand_mem g.2 hm hfix
    rw [permVal_bF _ hm] at hmem
    rw [candF, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem⟩
  have hfinal : ∀ g : ↥AutC, (∀ j < 6, g • bF j = bF j) → g = 1 := by
    intro g hg
    apply Subtype.ext
    show (g : Equiv.Perm (Fin 128)) = 1
    apply fixed_all g.2
    intro j hj x hx
    have hxb : x = bF j := Fin.ext (hx.trans (bF_val hj).symm)
    rw [hxb]
    exact hg j hj
  have hbound := card_le_prod_cands (X := Fin 128) 6 (↥AutC) bF candF hstep hfinal
  have hprod : ∏ m ∈ Finset.range 6, (candF m).card = 3317760 := by
    rw [Finset.prod_congr rfl fun m _ => card_candF m]
    exact candSet_prod
  rw [hprod] at hbound
  exact hbound

theorem pg_eq_autC : Pg = AutC :=
  Subgroup.eq_of_le_of_card_ge pg_le_autC (by rw [card_Pg]; exact card_autC_le)

end CFSG.EvenSporadicStandard.Fin76b.W16
