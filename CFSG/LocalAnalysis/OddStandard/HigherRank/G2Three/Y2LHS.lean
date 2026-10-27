module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPres
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LInst
public import Certificates.Certificate442315

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.HS.Native (hsData)

theorem y2l_wordProd_append {G : Type*} [Group G] (x : ℕ → G) (w w' : List (ℕ × Bool)) :
    wordProd x (w ++ w') = wordProd x w * wordProd x w' := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem y2l_wordProd_invW {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (y2l_invW w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [y2l_invW, wordProd]
  | cons l w ih =>
    have e : y2l_invW (l :: w) = y2l_invW w ++ [(l.1, !l.2)] := by
      simp [y2l_invW]
    rw [e, y2l_wordProd_append, ih]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [wordProd, mul_inv_rev]

theorem y2l_wordProd_subst {G : Type*} [Group G] (x : ℕ → G) (W : List (List (ℕ × Bool)))
    (r : List (Fin 5 × Bool)) :
    wordProd x (y2l_subst W r) =
      FreeGroup.lift (fun i : Fin 5 => wordProd x (W.getD i [])) (FreeGroup.mk r) := by
  rw [FreeGroup.lift_mk]
  induction r with
  | nil => simp [y2l_subst, wordProd]
  | cons l r ih =>
    simp only [y2l_subst, List.flatMap_cons, List.map_cons, List.prod_cons,
      y2l_wordProd_append] at ih ⊢
    rw [ih]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [y2l_wordProd_invW]

@[expose] noncomputable def y2l_hsElt (i : Fin 5) : J hsData :=
  wordProd (img2 (a hsData) (b hsData)) ((y2l_hsW ()).getD i [])

theorem y2l_lift_hsElt (r : List (Fin 5 × Bool)) :
    FreeGroup.lift y2l_hsElt (FreeGroup.mk r) =
      wordProd (img2 (a hsData) (b hsData)) (y2l_subst (y2l_hsW ()) r) :=
  (y2l_wordProd_subst _ _ r).symm

theorem y2l_hs_check :
    relCheck hsData.n (O hsData).alpha (invT hsData.n (O hsData).alpha) (O hsData).beta
        (invT hsData.n (O hsData).beta) ((y2l_ws26 2 false).map (y2l_subst (y2l_hsW ()))) =
      true ∧
    ((y2l_ws7 2).map (y2l_subst (y2l_hsW ()))).all (fun v => (List.range hsData.n).any fun i =>
      ap (wordTab hsData.n (O hsData).alpha (invT hsData.n (O hsData).alpha) (O hsData).beta
        (invT hsData.n (O hsData).beta) v) i != i) = true :=
  Bool.and_eq_true_iff.mp Certificates.certificate442315

theorem y2l_hs_rels :
    ∀ x ∈ rels26 2 false, FreeGroup.lift y2l_hsElt x = 1 := by
  have := faithful CFSG.Sporadic.Bridge.HS.baseFacts
  have hA := rep_a CFSG.Sporadic.Bridge.HS.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.HS.baseFacts
  have h := wordProd_eq_one_of_relCheck (n_lt_two_pow CFSG.Sporadic.HS.hsFacts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.HS.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.HS.baseFacts.invB) y2l_hs_check.1
  intro x hx
  rw [y2l_rels26_eq, Set.mem_setOf_eq] at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  rw [y2l_lift_hsElt]
  exact h _ (List.mem_map_of_mem hr)

theorem y2l_hs_seven :
    ∀ x ∈ y2l_ws7 2, FreeGroup.lift y2l_hsElt (FreeGroup.mk x) ≠ 1 := by
  have hA := rep_a CFSG.Sporadic.Bridge.HS.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.HS.baseFacts
  intro x hx h1
  rw [y2l_lift_hsElt] at h1
  have hT := rep_wordTab (n_lt_two_pow CFSG.Sporadic.HS.hsFacts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.HS.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.HS.baseFacts.invB) (y2l_subst (y2l_hsW ()) x)
  rw [h1] at hT
  have h2 := List.all_eq_true.mp y2l_hs_check.2 _ (List.mem_map_of_mem hx)
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.mp h2
  have hfix : ap (wordTab hsData.n (O hsData).alpha (invT hsData.n (O hsData).alpha)
      (O hsData).beta (invT hsData.n (O hsData).beta) (y2l_subst (y2l_hsW ()) x)) i = i :=
    (hT i (List.mem_range.mp hi)).trans (idx_one i)
  simp [hfix] at hne

theorem y2l_card_J : Nat.card (J hsData) = 44352000 := by
  rw [← Nat.card_congr CFSG.Sporadic.Bridge.HS.nativeEquiv.toEquiv, CFSG.Sporadic.HS.card_HS]

theorem y2l_two_part : 2 ^ (44352000 : ℕ).factorization 2 = 512 := by
  rw [show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
  norm_num

theorem y2l_sylow_of_elts {K Q : Type} [Group K] [Group Q]
    [Finite K] (e : K ≃* Q) (hK : Nat.card K = 44352000) (x : Fin 5 → K)
    (hrel : ∀ y ∈ rels26 2 false, FreeGroup.lift x y = 1)
    (h7 : ∀ y ∈ y2l_ws7 2, FreeGroup.lift x (FreeGroup.mk y) ≠ 1)
    {P : Type} [Group P] {u v w r s : P} (hP : IsPres26 2 false P u v w r s) (S : Sylow 2 Q) :
    Nonempty (P ≃* S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : (![x 0, x 1, x 2, x 3, x 4] : Fin 5 → K) = x := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hH, hcard⟩ := y2l_isPres26_two (e := false) (u := x 0) (v := x 1) (w := x 2)
    (r := x 3) (s := x 4) (by rw [hx]; exact hrel) (by rw [hx]; exact h7)
  haveI : Finite Q := Finite.of_equiv _ e.toEquiv
  haveI : Finite (Sylow 2 Q) :=
    Finite.of_injective (fun T : Sylow 2 Q => (T : Set Q)) SetLike.coe_injective
  set H := Subgroup.closure ({x 0, x 1, x 2, x 3, x 4} : Set K)
  have hQ : Nat.card (H.map (e : K →* Q)) = 2 ^ (Nat.card Q).factorization 2 := by
    rw [← Nat.card_congr (e.subgroupMap H).toEquiv, hcard, ← Nat.card_congr e.toEquiv, hK,
      y2l_two_part]
  obtain ⟨f⟩ := y2l_pres_equiv hP hH
  exact ⟨f.trans ((e.subgroupMap H).trans (Sylow.equiv (Sylow.ofCard _ hQ) S))⟩

theorem lemma26HS_holds :
    Lemma26HS := by
  intro P _ u v w r s hP S
  have hne : Nat.card (J hsData) ≠ 0 := by
    rw [y2l_card_J]
    norm_num
  have hfin : Finite (J hsData) := Nat.finite_of_card_ne_zero hne
  obtain ⟨E⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have e : J hsData ≃* TauCeti.SporadicName.HS.Group :=
    CFSG.Sporadic.Bridge.HS.nativeEquiv.symm.trans E
  have hrel := y2l_hs_rels
  have h7 := y2l_hs_seven
  have h := @y2l_sylow_of_elts (J hsData) TauCeti.SporadicName.HS.Group _ _ hfin e y2l_card_J
    y2l_hsElt hrel h7
  exact h hP S

end CFSG.OddStandard.HigherRank.G2Three.Sec2
