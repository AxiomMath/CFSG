module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LBound
public import Certificates.Certificate442313
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LRels

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup

variable {G : Type} [Group G]

theorem y2l_rels26_eq (n : ℕ) (e : Bool) :
    rels26 n e = {r : FreeGroup (Fin 5) | r ∈ (y2l_ws26 n e).map FreeGroup.mk} := by
  have hid : (FreeGroup.mk ∘ FreeGroup.toWord : FreeGroup (Fin 5) → FreeGroup (Fin 5)) = id :=
    funext fun _ => FreeGroup.mk_toWord
  ext x
  rw [Set.mem_setOf_eq, y2l_ws26, List.map_map, hid, List.map_id]
  rfl

theorem y2l_card_P26_le_of_check {n : ℕ} {e : Bool} {N : ℕ}
    (h : Finite (CFSG.CosetTable.PG 5 (y2l_ws26 n e)) ∧
      Nat.card (CFSG.CosetTable.PG 5 (y2l_ws26 n e)) ≤ N) :
    Finite (PresentedGroup (rels26 n e)) ∧ Nat.card (PresentedGroup (rels26 n e)) ≤ N := by
  rw [y2l_rels26_eq]
  exact h

theorem y2l_card_P26_le :
    (Finite (PresentedGroup (rels26 2 false)) ∧
        Nat.card (PresentedGroup (rels26 2 false)) ≤ 512) ∧
      (Finite (PresentedGroup (rels26 2 true)) ∧
        Nat.card (PresentedGroup (rels26 2 true)) ≤ 512) ∧
      (Finite (PresentedGroup (rels26 1 true)) ∧
        Nat.card (PresentedGroup (rels26 1 true)) ≤ 64) :=
  ⟨y2l_card_P26_le_of_check Certificates.certificate442313.1,
    y2l_card_P26_le_of_check Certificates.certificate442313.2.1,
    y2l_card_P26_le_of_check Certificates.certificate442313.2.2⟩

theorem y2l_card_P2_le (e : Bool) :
    Finite (PresentedGroup (rels26 2 e)) ∧ Nat.card (PresentedGroup (rels26 2 e)) ≤ 512 := by
  cases e
  · exact y2l_card_P26_le.1
  · exact y2l_card_P26_le.2.1

theorem y2l_isPres26_of_card {n : ℕ} {e : Bool} {P : Type} [Group P] {u v w r s : P}
    (h : ∀ x ∈ rels26 n e, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → P) x = 1)
    (hgen : closure ({u, v, w, r, s} : Set P) = ⊤) [Finite (PresentedGroup (rels26 n e))]
    (hcard : Nat.card (PresentedGroup (rels26 n e)) ≤ Nat.card P) :
    IsPres26 n e P u v w r s := by
  refine ⟨h, Function.Surjective.bijective_of_nat_card_le ?_ hcard⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
  rintro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact ⟨PresentedGroup.of 0, PresentedGroup.toGroup.of h⟩
  · exact ⟨PresentedGroup.of 1, PresentedGroup.toGroup.of h⟩
  · exact ⟨PresentedGroup.of 2, PresentedGroup.toGroup.of h⟩
  · exact ⟨PresentedGroup.of 3, PresentedGroup.toGroup.of h⟩
  · exact ⟨PresentedGroup.of 4, PresentedGroup.toGroup.of h⟩

theorem y2l_pres_equiv {n : ℕ} {e : Bool} {P Q : Type} [Group P] [Group Q] {u v w r s : P}
    {u' v' w' r' s' : Q} (hP : IsPres26 n e P u v w r s) (hQ : IsPres26 n e Q u' v' w' r' s') :
    Nonempty (P ≃* Q) := by
  obtain ⟨h, hb⟩ := hP
  obtain ⟨h', hb'⟩ := hQ
  exact ⟨(MulEquiv.ofBijective _ hb).symm.trans (MulEquiv.ofBijective _ hb')⟩

theorem y2l_lift_ws7_word (f : Fin 5 → G) (k1 k2 k3 : ℕ) :
    FreeGroup.lift f (FreeGroup.mk (List.replicate k1 (0, true) ++ List.replicate k2 (1, true) ++
      List.replicate k3 (2, true))) = f 0 ^ k1 * f 1 ^ k2 * f 2 ^ k3 := by
  simp only [FreeGroup.lift_mk, List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate, cond_true]

theorem y2l_mem_ws7 {k : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
      List (ℕ × ℕ × ℕ))) :
    List.replicate (k * t.1) (0, true) ++ List.replicate (k * t.2.1) (1, true) ++
      List.replicate (k * t.2.2) (2, true) ∈ y2l_ws7 k :=
  List.mem_map_of_mem ht

theorem y2l_ne_zero_coord {N : ℕ} {d : Fin 3 → ZMod N} (hd : d ≠ 0) :
    d 0 ≠ 0 ∨ d 1 ≠ 0 ∨ d 2 ≠ 0 := by
  by_contra hz
  simp only [not_or, not_not] at hz
  exact hd (funext fun i => by fin_cases i <;> simp [hz.1, hz.2.1, hz.2.2])

theorem y2l_mem_triples : ∀ a b c : Fin 2, (a.val, b.val, c.val) ≠ (0, 0, 0) →
    ∃ t ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
      List (ℕ × ℕ × ℕ)), t = (a.val, b.val, c.val) := by
  decide

theorem y2l_seven4 {u v w r s : G}
    (h7 : ∀ x ∈ y2l_ws7 2, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.mk x) ≠ 1) :
    ∀ d : Fin 3 → ZMod 4, d ≠ 0 → d + d = 0 → y2l_psi 4 u v w d ≠ 1 := by
  intro d hd h2
  have hz : ∀ z : ZMod 4, z + z = 0 → z.val = 2 * (z.val / 2) ∧ z.val / 2 < 2 := by decide
  have hz0 : ∀ z : ZMod 4, z.val / 2 = 0 → z + z = 0 → z = 0 := by decide
  obtain ⟨ha, ha'⟩ := hz (d 0) (congrFun h2 0)
  obtain ⟨hb, hb'⟩ := hz (d 1) (congrFun h2 1)
  obtain ⟨hc, hc'⟩ := hz (d 2) (congrFun h2 2)
  have hne : ((d 0).val / 2, (d 1).val / 2, (d 2).val / 2) ≠ (0, 0, 0) := by
    intro h0
    simp only [Prod.mk.injEq] at h0
    rcases y2l_ne_zero_coord hd with h | h | h
    · exact h (hz0 _ h0.1 (congrFun h2 0))
    · exact h (hz0 _ h0.2.1 (congrFun h2 1))
    · exact h (hz0 _ h0.2.2 (congrFun h2 2))
  obtain ⟨t, ht, rfl⟩ := y2l_mem_triples ⟨_, ha'⟩ ⟨_, hb'⟩ ⟨_, hc'⟩ hne
  have h := h7 _ (y2l_mem_ws7 ht)
  rw [y2l_lift_ws7_word] at h
  rw [y2l_psi, ha, hb, hc]
  exact h

theorem y2l_seven2 {u v w r s : G}
    (h7 : ∀ x ∈ y2l_ws7 1, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.mk x) ≠ 1) :
    ∀ d : Fin 3 → ZMod 2, d ≠ 0 → d + d = 0 → y2l_psi 2 u v w d ≠ 1 := by
  intro d hd _
  have key : ∀ a b c : ZMod 2, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ∃ t ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
        List (ℕ × ℕ × ℕ)), a.val = 1 * t.1 ∧ b.val = 1 * t.2.1 ∧ c.val = 1 * t.2.2 := by
    decide
  obtain ⟨t, ht, ha, hb, hc⟩ := key (d 0) (d 1) (d 2) (y2l_ne_zero_coord hd)
  have h := h7 _ (y2l_mem_ws7 ht)
  rw [y2l_lift_ws7_word] at h
  rw [y2l_psi, ha, hb, hc]
  exact h

theorem y2l_rels_closure {n : ℕ} {e : Bool} {u v w r s : G}
    (h : ∀ x ∈ rels26 n e, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) x = 1) :
    ∀ x ∈ rels26 n e, FreeGroup.lift (![⟨u, subset_closure (by simp)⟩,
      ⟨v, subset_closure (by simp)⟩, ⟨w, subset_closure (by simp)⟩,
      ⟨r, subset_closure (by simp)⟩, ⟨s, subset_closure (by simp)⟩] :
        Fin 5 → closure ({u, v, w, r, s} : Set G)) x = 1 := by
  intro x hx
  apply Subtype.val_injective
  have hcomp : (closure ({u, v, w, r, s} : Set G)).subtype.comp
      (FreeGroup.lift (![⟨u, subset_closure (by simp)⟩, ⟨v, subset_closure (by simp)⟩,
        ⟨w, subset_closure (by simp)⟩, ⟨r, subset_closure (by simp)⟩,
        ⟨s, subset_closure (by simp)⟩] : Fin 5 → closure ({u, v, w, r, s} : Set G))) =
      FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) := by
    ext i
    fin_cases i <;> rfl
  have := congrArg (fun φ : FreeGroup (Fin 5) →* G => φ x) hcomp
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at this
  rw [this, h x hx]
  rfl

theorem y2l_closure_closure (u v w r s : G) :
    closure ({⟨u, subset_closure (by simp)⟩, ⟨v, subset_closure (by simp)⟩,
      ⟨w, subset_closure (by simp)⟩, ⟨r, subset_closure (by simp)⟩,
      ⟨s, subset_closure (by simp)⟩} : Set (closure ({u, v, w, r, s} : Set G))) = ⊤ := by
  rw [← closure_closure_coe_preimage (k := ({u, v, w, r, s} : Set G))]
  congr 1
  ext ⟨y, hy⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.mk.injEq]

theorem y2l_isPres26_two {e : Bool} {u v w r s : G}
    (h : ∀ x ∈ rels26 2 e, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) x = 1)
    (h7 : ∀ x ∈ y2l_ws7 2, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.mk x) ≠ 1)
    [Finite (closure ({u, v, w, r, s} : Set G))] :
    IsPres26 2 e (closure ({u, v, w, r, s} : Set G)) ⟨u, subset_closure (by simp)⟩
      ⟨v, subset_closure (by simp)⟩ ⟨w, subset_closure (by simp)⟩
      ⟨r, subset_closure (by simp)⟩ ⟨s, subset_closure (by simp)⟩ ∧
      Nat.card (closure ({u, v, w, r, s} : Set G)) = 512 := by
  have hR := y2l_rels_iff.mp h
  have hge : 512 ≤ Nat.card (closure ({u, v, w, r, s} : Set G)) := by
    have := y2l_card_ge (N := 4) (by norm_num) (by decide) y2l_act8_dist4 (by simpa using hR.pu)
      (by simpa using hR.pv) (by simpa using hR.pw) hR.cuv hR.cuw hR.cvw hR.cru hR.crv hR.crw
      hR.csu hR.csv hR.csw (y2l_seven4 h7)
    simpa using this
  obtain ⟨hfin, hle⟩ := y2l_card_P2_le e
  have hP := y2l_isPres26_of_card (y2l_rels_closure h) (y2l_closure_closure u v w r s)
    (hle.trans hge)
  refine ⟨hP, le_antisymm ?_ hge⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hP.2)]
  exact hle

theorem y2l_isPres26_one {u v w r s : G}
    (h : ∀ x ∈ rels26 1 true, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) x = 1)
    (h7 : ∀ x ∈ y2l_ws7 1, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.mk x) ≠ 1)
    [Finite (closure ({u, v, w, r, s} : Set G))] :
    IsPres26 1 true (closure ({u, v, w, r, s} : Set G)) ⟨u, subset_closure (by simp)⟩
      ⟨v, subset_closure (by simp)⟩ ⟨w, subset_closure (by simp)⟩
      ⟨r, subset_closure (by simp)⟩ ⟨s, subset_closure (by simp)⟩ ∧
      Nat.card (closure ({u, v, w, r, s} : Set G)) = 64 := by
  have hR := y2l_rels_iff.mp h
  have hge : 64 ≤ Nat.card (closure ({u, v, w, r, s} : Set G)) := by
    have := y2l_card_ge (N := 2) (by norm_num) (by decide) y2l_act8_dist2 (by simpa using hR.pu)
      (by simpa using hR.pv) (by simpa using hR.pw) hR.cuv hR.cuw hR.cvw hR.cru hR.crv hR.crw
      hR.csu hR.csv hR.csw (y2l_seven2 h7)
    simpa using this
  obtain ⟨hfin, hle⟩ := y2l_card_P26_le.2.2
  have hP := y2l_isPres26_of_card (y2l_rels_closure h) (y2l_closure_closure u v w r s)
    (hle.trans hge)
  refine ⟨hP, le_antisymm ?_ hge⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hP.2)]
  exact hle

end CFSG.OddStandard.HigherRank.G2Three.Sec2
