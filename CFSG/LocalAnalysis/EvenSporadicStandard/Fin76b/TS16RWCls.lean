module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

section Cover

variable {G : Type*} [Group G] [Finite G]

theorem card_orbit_conj_eq (r : G) :
    Nat.card (MulAction.orbit (ConjAct G) r) =
      Nat.card G / Nat.card (Subgroup.centralizer ({r} : Set G)) := by
  rw [Nat.card_coe_set_eq]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) r)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have hpos : 0 < Nat.card (Subgroup.centralizer ({r} : Set G)) := Nat.card_pos
  exact (Nat.div_eq_of_eq_mul_right hpos h1.symm).symm

theorem cover_by_classes {α : Type*} (X : Set G)
    (hX : ∀ c g, g ∈ X → c * g * c⁻¹ ∈ X) {k : ℕ} (r : Fin k → G) (hr : ∀ j, r j ∈ X)
    (inv : G → α) (hinv : ∀ c g, inv (c * g * c⁻¹) = inv g)
    (hdist : ∀ j j', inv (r j) = inv (r j') → j = j')
    (hsum : ∑ j, Nat.card G / Nat.card (Subgroup.centralizer ({r j} : Set G)) = Nat.card X) :
    ∀ g ∈ X, ∃ j, ∃ c : G, g = c * r j * c⁻¹ := by
  have hmem : ∀ j, ∀ x ∈ MulAction.orbit (ConjAct G) (r j), x ∈ X := by
    intro j x hx
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.1 hx
    rw [ConjAct.smul_def]
    exact hX _ _ (hr j)
  have hcard : Nat.card (Σ j : Fin k, MulAction.orbit (ConjAct G) (r j)) = Nat.card X := by
    rw [Nat.card_sigma, ← hsum]
    exact Finset.sum_congr rfl fun j _ => card_orbit_conj_eq (r j)
  let φ : (Σ j : Fin k, MulAction.orbit (ConjAct G) (r j)) → X :=
    fun p => ⟨p.2.1, hmem p.1 p.2.1 p.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨j, x, hx⟩ ⟨j', y, hy⟩ hxy
    have hxy' : x = y := congrArg Subtype.val hxy
    subst hxy'
    have h1 : inv x = inv (r j) := by
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hx
      rw [← hc, ConjAct.smul_def, hinv]
    have h2 : inv x = inv (r j') := by
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hy
      rw [← hc, ConjAct.smul_def, hinv]
    obtain rfl := hdist j j' (h1.symm.trans h2)
    rfl
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  intro g hg
  obtain ⟨⟨j, x, hx⟩, hp⟩ := hbij.2 ⟨g, hg⟩
  have hxg : x = g := congrArg Subtype.val hp
  subst hxg
  obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hx
  exact ⟨j, ConjAct.ofConjAct c, by rw [← hc, ConjAct.smul_def]⟩

end Cover

@[expose] def fixCnt (π : Equiv.Perm (Fin 128)) : ℕ :=
  (Finset.univ.filter fun i : Fin 128 => π i = i).card

@[expose] def fixSq (π : Equiv.Perm (Fin 128)) : ℕ :=
  (Finset.univ.filter fun i : Fin 128 => π i = i ∧ mulF i i = tF).card

@[expose] def fp (π : Equiv.Perm (Fin 128)) : ℕ × ℕ := (fixCnt π, fixSq π)

@[expose] noncomputable def repPerm (j : ℕ) : Equiv.Perm (Fin 128) := permOfArr 128 repArrs[j]!

theorem fixCnt_conj (c π : Equiv.Perm (Fin 128)) : fixCnt (c * π * c⁻¹) = fixCnt π := by
  unfold fixCnt
  refine Finset.card_equiv c⁻¹ fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  exact Equiv.apply_eq_iff_eq_symm_apply c

theorem fixSq_conj {c : Equiv.Perm (Fin 128)} (hc : c ∈ AutC) (htc : c tF = tF)
    (π : Equiv.Perm (Fin 128)) : fixSq (c * π * c⁻¹) = fixSq π := by
  unfold fixSq
  refine Finset.card_equiv c⁻¹ fun i => ?_
  obtain ⟨j, rfl⟩ : ∃ j, i = c j := ⟨c⁻¹ i, by simp⟩
  have hsq : ∀ x : Fin 128, c x = tF ↔ x = tF := fun x =>
    ⟨fun h => c.injective (h.trans htc.symm), fun h => by rw [h]; exact htc⟩
  have hmul : mulF (c j) (c j) = c (mulF j j) := (hc j j).symm
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, hmul, hsq, c.injective.eq_iff]

theorem fp_conj (hPA : Pg ≤ AutC) (htF : ∀ c ∈ Pg, c tF = tF) {c : Equiv.Perm (Fin 128)}
    (hc : c ∈ Pg) (π : Equiv.Perm (Fin 128)) : fp (c * π * c⁻¹) = fp π :=
  Prod.ext (fixCnt_conj c π) (fixSq_conj (hPA hc) (htF c hc) π)

section Certified


theorem mulF_eq_tF_iff (a b : Fin 128) : mulF a b = tF ↔ mulC a b = tC := by
  have h := mulC_lt a.2 b.2
  simp only [mulF, tF, tC, Fin.ext_iff]
  rw [Nat.mod_eq_of_lt h]

theorem baseFaithful_Pg : BaseFaithful Pg baseArr.toList := by
  have hQb : QPg.base.toList.map Fin.val = baseArr.toList := rfl
  have h := baseFaithful_of_valid (validSchreier_of_chainOK chainArrays (by norm_num)
    chain_check).1
  rw [hQb] at h
  exact h

theorem base_lt : ∀ b ∈ baseArr.toList, b < 128 := by decide

theorem sqW_iff {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) :
    sqW w = true ↔ ∀ x : Fin 128, (x : ℕ) ∈ baseArr.toList → g (g x) = x := by
  unfold sqW
  rw [← Array.all_toList, List.all_eq_true]
  constructor
  · intro h x hx
    have h1 := h x hx
    rw [beq_iff_eq, hw x, hw (g x)] at h1
    exact Fin.ext h1
  · intro h x hx
    obtain ⟨y, rfl⟩ : ∃ y : Fin 128, (y : ℕ) = x := ⟨⟨x, base_lt x hx⟩, rfl⟩
    rw [beq_iff_eq, hw y, hw (g y), h y hx]

theorem neOneW_iff {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) :
    neOneW w = true ↔ ∃ x : Fin 128, (x : ℕ) ∈ baseArr.toList ∧ g x ≠ x := by
  unfold neOneW
  rw [← Array.any_toList, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, h⟩
    obtain ⟨y, rfl⟩ : ∃ y : Fin 128, (y : ℕ) = b := ⟨⟨b, base_lt b hb⟩, rfl⟩
    refine ⟨y, hb, fun he => ?_⟩
    rw [bne_iff_ne, hw y, he] at h
    exact h rfl
  · rintro ⟨x, hx, hne⟩
    refine ⟨x, hx, ?_⟩
    rw [bne_iff_ne, hw x]
    exact fun h => hne (Fin.ext h)

theorem involW_iff {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g)
    (hg : g ∈ Pg) : involW w = true ↔ g * g = 1 ∧ g ≠ 1 := by
  unfold involW
  rw [Bool.and_eq_true, sqW_iff hw, neOneW_iff hw]
  constructor
  · rintro ⟨h1, x, -, hne⟩
    refine ⟨baseFaithful_Pg (g * g) (Pg.mul_mem hg hg) fun y hy => ?_, fun h => hne ?_⟩
    · rw [Equiv.Perm.mul_apply]
      exact h1 y hy
    · rw [h, Equiv.Perm.one_apply]
  · rintro ⟨h2, h3⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have := congrArg (fun π : Equiv.Perm (Fin 128) => π x) h2
      simpa [Equiv.Perm.mul_apply] using this
    · by_contra hcon
      exact h3 (baseFaithful_Pg g hg fun x hx => by_contra fun hne => hcon ⟨x, hx, hne⟩)

theorem commW_pt {r : Array ℕ} {R : Equiv.Perm (Fin 128)} (hr : Rep 128 r R)
    {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) (x : Fin 128) :
    (evR w r[(x : ℕ)]! == r[evR w x]!) = true ↔ g (R x) = R (g x) := by
  rw [beq_iff_eq, hr x, hw (R x), hw x, hr (g x), ← Fin.ext_iff]

theorem commW_iff {r : Array ℕ} {R : Equiv.Perm (Fin 128)} (hr : Rep 128 r R) (hR : R ∈ Pg)
    {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) (hg : g ∈ Pg) :
    commW r w = true ↔ g * R = R * g := by
  unfold commW
  rw [← Array.all_toList, List.all_eq_true]
  constructor
  · intro h
    have hpt : ∀ x : Fin 128, (x : ℕ) ∈ baseArr.toList → g (R x) = R (g x) :=
      fun x hx => (commW_pt hr hw x).1 (h x hx)
    have hk : g⁻¹ * R⁻¹ * g * R = 1 := by
      refine baseFaithful_Pg _ (Pg.mul_mem (Pg.mul_mem (Pg.mul_mem (Pg.inv_mem hg)
        (Pg.inv_mem hR)) hg) hR) fun y hy => ?_
      have h1 := hpt y hy
      simp [Equiv.Perm.mul_apply, h1, Equiv.Perm.inv_def]
    have h3 : g⁻¹ * (R⁻¹ * g * R) = 1 := by simpa only [mul_assoc] using hk
    have h4 : g = R⁻¹ * g * R := inv_mul_eq_one.1 h3
    calc g * R = R * (R⁻¹ * g * R) := by group
      _ = R * g := by rw [← h4]
  · intro h x hx
    have hx' : x < 128 := base_lt x hx
    refine (commW_pt hr hw ⟨x, hx'⟩).2 ?_
    have := congrArg (fun π : Equiv.Perm (Fin 128) => π ⟨x, hx'⟩) h
    simpa [Equiv.Perm.mul_apply] using this

theorem lenFilter_range (p : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter p).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem fixCntW_eq {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) :
    fixCntW w = fixCnt g := by
  unfold fixCntW fixCnt
  rw [lenFilter_range, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hw i]
  simp [Fin.ext_iff]

theorem fixSqW_eq {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) :
    fixSqW w = fixSq g := by
  unfold fixSqW fixSq
  rw [lenFilter_range, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hw i, mulF_eq_tF_iff]
  simp [Fin.ext_iff]

end Certified

end CFSG.EvenSporadicStandard.Fin76b.W16
