module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizerExclusion
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizerConj
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag
open CFSG.LieType.Ree.LargeReeCover (torusPair torusPair_conj_pinnedX torusWeight)

section Six

variable {K : Type} [Field K] [CharP K F4.prime]

abbrev tSixRoots : List ℕ := [41, 45, 43, 46, 44, 47]

omit [CharP K F4.prime] in
theorem sylowRoot_pos
    {r : ℕ} (h1 : 24 ≤ r) (h2 : r ≤ 47) :
    IsRoot F4.tag (orbitCertRoot F4.tag r) ∧ 0 < height (orbitCertRoot F4.tag r) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 24, r = 24 + (i : ℕ) := ⟨⟨r - 24, by omega⟩, by simp; omega⟩
  exact orbitCertRoot_pos i

theorem sylowX_commute_of_commFactors
    {i j : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) (hj : 24 ≤ j ∧ j ≤ 47)
    (hij : i ≠ j) (h : commFactors i j = []) (s t : K) :
    Commute (sylowX K i s) (sylowX K j t) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨i', rfl⟩ : ∃ i' : Fin 24, i = 24 + (i' : ℕ) := ⟨⟨i - 24, by omega⟩, by simp; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin 24, j = 24 + (j' : ℕ) := ⟨⟨j - 24, by omega⟩, by simp; omega⟩
  rw [commFactors_eq] at h
  unfold Commute SemiconjBy
  rw [sylowX, sylowX, pinnedX_mul_pinnedX_eq hi hj hij, h, List.map_nil, List.prod_nil, one_mul]

omit [CharP K F4.prime] in
theorem commFactors_six : ∀ i ∈ tSixRoots, ∀ j ∈ tSixRoots, i ≠ j → commFactors i j = [] := by
  decide

theorem sylowX_six_commute
    {i j : ℕ} (hi : i ∈ tSixRoots) (hj : j ∈ tSixRoots) (hij : i ≠ j)
    (s t : K) : Commute (sylowX K i s) (sylowX K j t) :=
  sylowX_commute_of_commFactors (by simp at hi; omega) (by simp at hj; omega) hij
    (commFactors_six i hi j hj hij) s t

theorem pairwise_commute_six
    {l : List (ℕ × K)} (hl : ∀ q ∈ l, q.1 ∈ tSixRoots)
    (hnd : (l.map Prod.fst).Nodup) :
    (l.map fun q => (orbitCertRoot F4.tag q.1, q.2)).Pairwise fun p q =>
      Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2) := by
  rw [List.pairwise_map]
  have hnd' : l.Pairwise fun p q => p.1 ≠ q.1 := List.pairwise_map.1 hnd
  exact hnd'.imp_of_mem fun hp hq hne => sylowX_six_commute (hl _ hp) (hl _ hq) hne _ _

omit [CharP K F4.prime] in
theorem tSixRoots_nodup : (tSixRoots.map (orbitCertRoot F4.tag)).Nodup := by
  decide +kernel

abbrev tSixPos (lam mu p p' r r' : K) : List (ℕ × K) :=
  [(41, lam), (45, mu), (43, p), (46, p'), (44, r), (47, r')]

abbrev tSixList (lam mu p p' r r' : K) : List ((Fin F4.tag.rank → ℤ) × K) :=
  (tSixPos lam mu p p' r r').map fun q => (orbitCertRoot F4.tag q.1, q.2)

omit [CharP K F4.prime] in
theorem tSix_eq_rootProd
    (lam mu p p' r r' : K) :
    tSix K lam mu p p' r r' = rootProd (tSixList lam mu p p' r r') := by
  simp only [tSix, rootProd, tSixList, tSixPos, sylowX, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

omit [Field K] [CharP K F4.prime] in
theorem map_fst_tSixList (lam mu p p' r r' : K) :
    (tSixList lam mu p p' r r').map Prod.fst = tSixRoots.map (orbitCertRoot F4.tag) :=
  rfl

omit [Field K] [CharP K F4.prime] in
theorem mem_tSixList
    {lam mu p p' r r' : K} {x : (Fin F4.tag.rank → ℤ) × K}
    (hx : x ∈ tSixList lam mu p p' r r') :
    IsRoot F4.tag x.1 ∧ 0 < height x.1 := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  have hq1 : q.1 ∈ tSixRoots := by
    simp only [tSixPos, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact sylowRoot_pos (by simp at hq1; omega) (by simp at hq1; omega)

theorem tSixList_pairwise
    (lam mu p p' r r' : K) :
    (tSixList lam mu p p' r r').Pairwise fun p q =>
      Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2) :=
  pairwise_commute_six (fun q hq => by
    simp only [tSixPos, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by show ([41, 45, 43, 46, 44, 47] : List ℕ).Nodup; decide)

end Six

section Transport

variable {K : Type} [Field K]

theorem canonicalRep_conj_rootProd
    (h2 : (2 : K) = 0) (w : WeylGroup F4.tag)
    (l : List ((Fin F4.tag.rank → ℤ) × K)) (hl : ∀ q ∈ l, IsRoot F4.tag q.1) :
    canonicalRep (coxeterSystem F4.tag) K w * rootProd l *
        (canonicalRep (coxeterSystem F4.tag) K w)⁻¹ =
      rootProd (l.map fun q => (w • q.1, q.2)) := by
  induction l with
  | nil => simp [rootProd]
  | cons q l ih =>
    have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
      fun A X Y => by group
    simp only [rootProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (hl q List.mem_cons_self),
      ih fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')]

theorem pairwise_commute_map_smul
    (h2 : (2 : K) = 0) (w : WeylGroup F4.tag)
    {l : List ((Fin F4.tag.rank → ℤ) × K)} (hl : ∀ q ∈ l, IsRoot F4.tag q.1)
    (hc : l.Pairwise fun p q => Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2)) :
    (l.map fun q => (w • q.1, q.2)).Pairwise fun p q =>
      Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2) := by
  rw [List.pairwise_map]
  refine hc.imp_of_mem fun hp hq h => ?_
  rw [← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (hl _ hp),
    ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (hl _ hq)]
  exact h.map (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w))

end Transport

section Conjugates

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem sylowL_one_eq_tSix
    : sylowL a K 1 = tSix K 1 1 0 0 0 0 := by
  simp only [sylowL, tSix, largeReeSigma_one, sylowX, pinnedX_zero, mul_one]

omit [Finite K] [CharP K F4.prime] in
theorem torusPair_conj_tSix
    (t : Kˣ × Kˣ) (lam mu p p' r r' : K) :
    torusPair a t * tSix K lam mu p p' r r' * (torusPair a t)⁻¹ =
      tSix K ((torusWeight a (orbitCertRoot F4.tag 41) t : K) * lam)
        ((torusWeight a (orbitCertRoot F4.tag 45) t : K) * mu)
        ((torusWeight a (orbitCertRoot F4.tag 43) t : K) * p)
        ((torusWeight a (orbitCertRoot F4.tag 46) t : K) * p')
        ((torusWeight a (orbitCertRoot F4.tag 44) t : K) * r)
        ((torusWeight a (orbitCertRoot F4.tag 47) t : K) * r') := by
  have e : ∀ A X1 X2 X3 X4 X5 X6 : ModGL F4.tag K, A * (X1 * X2 * X3 * X4 * X5 * X6) * A⁻¹ =
      (A * X1 * A⁻¹) * (A * X2 * A⁻¹) * (A * X3 * A⁻¹) * (A * X4 * A⁻¹) * (A * X5 * A⁻¹) *
        (A * X6 * A⁻¹) := fun A X1 X2 X3 X4 X5 X6 => by group
  simp only [tSix, sylowX]
  rw [e, torusPair_conj_pinnedX a t (sylowRoot_pos (r := 41) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a t (sylowRoot_pos (r := 45) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a t (sylowRoot_pos (r := 43) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a t (sylowRoot_pos (r := 46) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a t (sylowRoot_pos (r := 44) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a t (sylowRoot_pos (r := 47) (by norm_num) (by norm_num)).1]

theorem exists_conj_tOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : ModGL F4.tag K}
    (hb : b ∈ F4.reeFixedBorel K a) :
    ∃ lam mu p p' r r' : K, lam ≠ 0 ∧ b * sylowL a K 1 * b⁻¹ = tSix K lam mu p p' r r' := by
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, x, hx, rfl⟩ := hb'
  obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hx
  have key : torusPair a (u, v) * sylowVec a K y * sylowL a K 1 *
      (torusPair a (u, v) * sylowVec a K y)⁻¹ = torusPair a (u, v) *
        (sylowVec a K y * (sylowX K 41 1 * sylowX K 45 1) * (sylowVec a K y)⁻¹) *
          (torusPair a (u, v))⁻¹ := by
    rw [sylowL, largeReeSigma_one]
    group
  rw [sylowVec, sylowV_conj_tPair, torusPair_conj_tSix] at key
  exact ⟨_, _, _, _, _, _, mul_ne_zero (Units.ne_zero _) one_ne_zero, key⟩

end Conjugates

section Bruhat

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem tOne_weyl_check : ∀ k : Fin F4.fixedWeylOrder,
    F4.fixedRelWord k = [] ∨ F4.fixedRelWord k = [⟨0, by decide⟩] ∨
      centralWeylImage k (orbitCertRoot F4.tag 41) ∉ tSixRoots.map (orbitCertRoot F4.tag) := by
  decide +kernel

theorem reeGamma_inf_centralizer_tOne_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {sylowL a K 1} ≤
      F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ‹CharP K F4.prime›
    exact CharTwo.two_eq_zero
  intro g hg
  obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hg' : g ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := hgΓ
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
  have hgw' := hgw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
  rcases tOne_weyl_check k with h1 | h1 | h1
  ·
    have hw1 : F4.fixedRelElt k = 1 := by rw [fixedRelElt, h1, List.map_nil, List.prod_nil]
    have hgB : b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b' ∈
        F4.reeFixedBorel K a := by
      rw [hw1, canonicalRep_one, mul_one]
      exact mul_mem hb hb'
    exact (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup (t := F4) ⟨0, by decide⟩) hgB
  ·
    have hw1 : F4.fixedRelElt k = F4.fixedOrbitElement ⟨0, by decide⟩ := by
      rw [fixedRelElt, h1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hmem : b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b' ∈
        ((F4.reeGamma K a ⊓ parabolicSubgroup F4.tag K (F4.fixedOrbitSet ⟨0, by decide⟩) :
          Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
      rw [coe_reeGamma_inf_parabolicSubgroup]
      right
      rw [← hw1]
      exact hgw'
    exact hmem
  ·
    exfalso
    obtain ⟨lam, mu, p, p', r, r', hlam, hc⟩ := exists_conj_tOne hK hb'
    obtain ⟨lam', mu', s, s', z, z', -, hc'⟩ := exists_conj_tOne hK (inv_mem hb)
    rw [inv_inv] at hc'
    have key : canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) *
        tSix K lam mu p p' r r' * (canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k))⁻¹ =
          tSix K lam' mu' s s' z z' := by
      rw [← hc, ← hc']
      have hcg : (b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b') *
          sylowL a K 1 * (b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b')⁻¹ =
            sylowL a K 1 := by rw [hgc, mul_inv_cancel_right]
      calc canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) *
            (b' * sylowL a K 1 * b'⁻¹) *
              (canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k))⁻¹ =
          b⁻¹ * ((b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b') *
            sylowL a K 1 *
              (b * canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * b')⁻¹) * b := by
            group
        _ = b⁻¹ * sylowL a K 1 * b := by rw [hcg]
    have hroot : ∀ q ∈ tSixList lam mu p p' r r', IsRoot F4.tag q.1 := fun q hq =>
      (mem_tSixList hq).1
    rw [tSix_eq_rootProd, tSix_eq_rootProd, canonicalRep_conj_rootProd h2 _ _ hroot] at key
    have hnd : (((tSixList lam mu p p' r r').map fun q => (F4.fixedRelElt k • q.1, q.2)).map
        Prod.fst).Nodup := by
      rw [List.map_map]
      have e : (Prod.fst ∘ fun q : (Fin F4.tag.rank → ℤ) × K => (F4.fixedRelElt k • q.1, q.2)) =
          (F4.fixedRelElt k • ·) ∘ Prod.fst := rfl
      rw [e, ← List.map_map, map_fst_tSixList]
      exact tSixRoots_nodup.map (MulAction.injective _)
    have hz := eq_zero_of_rootProd_eq hnd (by rw [map_fst_tSixList]; exact tSixRoots_nodup)
      (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact CFSG.LieType.Chevalley.IsRoot.smul (hroot q' hq') _)
      (fun q hq => mem_tSixList hq)
      (pairwise_commute_map_smul h2 _ hroot (tSixList_pairwise _ _ _ _ _ _))
      (tSixList_pairwise _ _ _ _ _ _) key
    refine hlam (hz (F4.fixedRelElt k • orbitCertRoot F4.tag 41, lam) (by simp) ?_)
    rw [map_fst_tSixList, fixedRelElt_smul_eq_centralWeylImage]
    exact h1

end Bruhat

end CFSG.LieType.Ree.LargeReeInvolution
