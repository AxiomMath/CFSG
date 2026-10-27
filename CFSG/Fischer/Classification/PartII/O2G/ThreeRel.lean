module

public import CFSG.Fischer.Classification.PartII.O2G.ThreeBound

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin
open Classical

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem not_isTwin_mul_mul (hP : Pair G D) {A : Set G} {y z : G} (hy : y ∈ D) (hz : z ∈ D)
    (hyz : y * z ≠ z * y) : ¬ IsTwin A (y * z * y) z := by
  intro h
  have hc : y * z * y * z = z * (y * z * y) := h.2.2.1
  rw [Pair.mul_mul_eq hP hy hz hyz] at hc
  have hzz := Pair.mul_self hP hz
  have hzy : z * y = y * z := by
    calc z * y = z * y * z * z := by rw [mul_assoc (z * y) z z, hzz, mul_one]
      _ = z * (z * y * z) := hc
      _ = y * z := by rw [← mul_assoc, ← mul_assoc, hzz, one_mul]
  exact hyz hzy.symm

theorem conj_sprod_mem_parity (hP : Pair G D) {w y z : G} (hz : z ∈ LocalClass D w)
    (hyz : y * z ≠ z * y) {Y : Finset G}
    (hY : (Y : Set G) ⊆ twinClass (LocalClass D w) y) :
    sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y * z *
        (sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y)⁻¹ ∈
      if Even Y.card then twinClass (LocalClass D w) z
      else twinClass (LocalClass D w) (y * z * y) := by
  induction Y using Finset.induction_on with
  | empty =>
    simp only [sprod_empty, one_mul, inv_one, mul_one, Finset.card_empty, Even.zero, ↓reduceIte]
    exact self_mem_twinClass hz
  | insert a Y haY ih =>
    have haT : a ∈ twinClass (LocalClass D w) y := hY (Finset.mem_insert_self a Y)
    have hYT : (Y : Set G) ⊆ twinClass (LocalClass D w) y :=
      fun t ht => hY (Finset.mem_insert_of_mem ht)
    have ha : a ∈ LocalClass D w := haT.2.1
    have haz : a * z ≠ z * a := fun e => hyz ((haT.2.2.2 z hz).2 e.symm).symm
    have hya : IsTwin (LocalClass D w) a y := isTwin_symm haT
    have hac' : IsTwin (LocalClass D w) (a * z * a) (y * z * y) :=
      isTwin_mul_mul_of_isTwin hP hya hz haz
    rw [sprod_insert _ haT haY, mul_inv_rev, Pair.inv_eq hP ha.1,
      show a * sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y * z *
          ((sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y)⁻¹ * a) =
        a * (sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y * z *
          (sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y)⁻¹) * a by group,
      Finset.card_insert_of_notMem haY]
    have ih := ih hYT
    by_cases hev : Even Y.card
    · simp only [hev, ↓reduceIte] at ih
      have hodd : ¬ Even (Y.card + 1) := by rw [Nat.even_add_one]; exact not_not.2 hev
      simp only [hodd, ↓reduceIte]
      exact isTwin_trans (isTwin_symm hac') (isTwin_conj_of_mem hP ha ih)
    · simp only [hev, ↓reduceIte] at ih
      have hev' : Even (Y.card + 1) := by rw [Nat.even_add_one]; exact hev
      simp only [hev', ↓reduceIte]
      have h1 := isTwin_conj_of_mem hP ha (isTwin_trans hac' ih)
      rwa [Pair.mul_mul_mul_mul hP ha.1] at h1

theorem even_card_of_commute (hP : Pair G D) {w y z : G} (hy : y ∈ LocalClass D w)
    (hz : z ∈ LocalClass D w) (hyz : y * z ≠ z * y) {Y : Finset G}
    (hY : (Y : Set G) ⊆ twinClass (LocalClass D w) y)
    (hc : sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y * z =
      z * sprod _ (pairwise_commute_twinClass (LocalClass D w) y) Y) : Even Y.card := by
  have h := conj_sprod_mem_parity hP hz hyz hY
  rw [hc, mul_inv_cancel_right] at h
  by_contra hodd
  simp only [hodd, ↓reduceIte] at h
  exact not_isTwin_mul_mul hP hy.1 hz.1 hyz h

theorem eq_empty_of_sprod_eq_one (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {x y y' : G} (hx : x ∈ D) (hy : y ∈ LocalClass D x)
    (hy' : IsTwin (LocalClass D x) y y') (hne : y' ≠ y) (X : Finset G)
    (hX : (X : Set G) ⊆ twinClass (LocalClass D x) y)
    (h1 : sprod _ (pairwise_commute_twinClass (LocalClass D x) y) X = 1) : X = ∅ := by
  by_contra hXne
  obtain ⟨c, hc, hcy⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hx hy
  have hev : Even X.card := even_card_of_commute hP hy hc (fun e => hcy e.symm) hX
    (by rw [h1, one_mul, mul_one])
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hXne
  have hwT : w ∈ twinClass (LocalClass D x) y := hX hw
  have hwD : w ∈ D := hwT.2.1.1
  obtain ⟨z₁, hz₁T, hz₁w⟩ : ∃ z₁ ∈ twinClass (LocalClass D x) y, z₁ ≠ w := by
    by_cases hwy : w = y
    · exact ⟨y', hy', fun e => hne (e.trans hwy)⟩
    · exact ⟨y, self_mem_twinClass hy, fun e => hwy e.symm⟩
  have hline := insert_twinClass_eq hP hZ hS hx hwT hz₁T (Ne.symm hz₁w)
  have hz₁loc : z₁ ∈ LocalClass D w :=
    ⟨hz₁T.2.1.1, hz₁w, (isTwin_of_mem hz₁T hwT).2.2.1⟩
  have hXT : ((X.erase w : Finset G) : Set G) ⊆ twinClass (LocalClass D x) y :=
    fun t ht => hX (Finset.mem_of_mem_erase ht)
  have hXT' : ((X.erase w : Finset G) : Set G) ⊆ twinClass (LocalClass D w) z₁ := by
    intro t ht
    have htw : t ≠ w := Finset.ne_of_mem_erase ht
    have hmem : t ∈ insert x (twinClass (LocalClass D x) y) := Or.inr (hXT ht)
    rw [hline] at hmem
    rcases hmem with h | h
    · exact absurd h htw
    · exact h
  have hsplit : sprod _ (pairwise_commute_twinClass (LocalClass D x) y) X =
      w * sprod _ (pairwise_commute_twinClass (LocalClass D x) y) (X.erase w) := by
    conv_lhs => rw [← Finset.insert_erase hw]
    exact sprod_insert _ hwT (Finset.notMem_erase w X)
  have hs : sprod _ (pairwise_commute_twinClass (LocalClass D x) y) (X.erase w) = w := by
    have h2 : w * sprod _ (pairwise_commute_twinClass (LocalClass D x) y) (X.erase w) = 1 :=
      hsplit ▸ h1
    calc sprod _ (pairwise_commute_twinClass (LocalClass D x) y) (X.erase w) = w⁻¹ :=
          (inv_eq_of_mul_eq_one_right h2).symm
      _ = w := Pair.inv_eq hP hwD
  have hprod : sprod _ (pairwise_commute_twinClass (LocalClass D w) z₁) (X.erase w) = w := by
    rw [← sprod_eq_sprod _ _ hXT hXT']
    exact hs
  obtain ⟨z', hz', hz'z⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hwD hz₁loc
  have hev' : Even (X.erase w).card := by
    refine even_card_of_commute hP hz₁loc hz' (fun e => hz'z e.symm) hXT' ?_
    rw [hprod]
    exact hz'.2.2.symm
  have hcard := Finset.card_erase_add_one hw
  rw [← hcard, Nat.even_add_one] at hev
  exact hev hev'

end O2G

end CFSG.Fischer.Classification
