module

public import CFSG.CGT.Hall82.TheoremASetting
import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.CGT.Hall82.TheoremA

open CFSG.RankThree.PartTwo (altHeart evenWeightOnes allOnes)
open CFSG.QuasithinUnique (evenWeight)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mk altAct_mul altAct_one altAct_inv_apply evenWeightPerm_apply
    evenWeightPerm_pairEW exists_forall_eq_of_mem_evenWeightOnes mem_evenWeightOnes_of_forall_eq
    mk_pairEW_ne_zero pairEW_comm)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  (pairEW pairEW_apply exists_ne_four perm_mem_of_pair_fixed perm_eq_one_of_altHeart_fixed)
open Equiv

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

private theorem zmod2_neg_add (a b c : ZMod 2) : -a + b = c ↔ a + b = c := by
  revert a b c; decide

private theorem altHeart_add_self (v : altHeart 6) : v + v = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 := Subtype.ext (funext fun i => zmod2_add_self _)
  rw [this, QuotientAddGroup.mk_zero]

private theorem neg_heart (v : altHeart 6) : -v = v :=
  neg_eq_of_add_eq_zero_right (altHeart_add_self v)

private theorem mk_eq_mk_iff {x y : evenWeight 6} :
    (x : altHeart 6) = (y : altHeart 6) ↔
      ∃ c : ZMod 2, ∀ p, (x : Fin 6 → ZMod 2) p + (y : Fin 6 → ZMod 2) p = c := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes h
    refine ⟨c, fun p => ?_⟩
    have hp := hc p
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at hp
    exact (zmod2_neg_add _ _ _).1 hp
  · rintro ⟨c, hc⟩
    refine mem_evenWeightOnes_of_forall_eq (c := c) fun p => ?_
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
    exact (zmod2_neg_add _ _ _).2 (hc p)

private theorem card_evenWeightOnes_six : Nat.card (evenWeightOnes 6) = 2 := by
  have hmem : allOnes 6 ∈ evenWeight 6 := by
    show ∑ _i : Fin 6, (1 : ZMod 2) = 0
    decide
  rw [Nat.card_eq_two_iff]
  refine ⟨0, ⟨⟨allOnes 6, hmem⟩, mem_evenWeightOnes_of_forall_eq (c := 1) fun _ => rfl⟩,
    ?_, ?_⟩
  · intro h
    have h01 : (0 : ZMod 2) = 1 := congrArg (fun z : evenWeightOnes 6 => (z : Fin 6 → ZMod 2) 0) h
    exact absurd h01 (by decide)
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes z.2
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · left
      exact Subtype.ext (Subtype.ext (funext fun p => hc p))
    · right
      exact Subtype.ext (Subtype.ext (funext fun p => hc p))

theorem card_altHeart_six : Nat.card (altHeart 6) = 16 := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes 6)
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight 6 (by norm_num),
    card_evenWeightOnes_six] at h
  have h' : Nat.card (altHeart 6) * 2 = 32 := by simpa [altHeart] using h.symm
  omega

private theorem pc_eq_mk (a b : Fin 6) : pc a b = ((pairEW a b : evenWeight 6) : altHeart 6) :=
  rfl

private theorem pc_self (a : Fin 6) : pc a a = 0 := by
  have h : pairEW a a = 0 := Subtype.ext <| funext fun p => by
    rw [pairEW_apply]
    exact zmod2_add_self _
  rw [pc_eq_mk, h, QuotientAddGroup.mk_zero]

private theorem pc_comm (a b : Fin 6) : pc a b = pc b a := by
  rw [pc_eq_mk, pc_eq_mk, pairEW_comm]

private theorem pc_add (a b c : Fin 6) : pc a b + pc b c = pc a c := by
  rw [pc_eq_mk, pc_eq_mk, pc_eq_mk, ← QuotientAddGroup.mk_add]
  refine mk_eq_mk_iff.2 ⟨0, fun p => ?_⟩
  simp only [AddSubgroup.coe_add, Pi.add_apply, pairEW_apply]
  have key : ∀ x y z : ZMod 2, x + y + (y + z) + (x + z) = 0 := by decide
  exact key _ _ _

private theorem exists_pc_aux : ∀ a b c d e g : ZMod 2, a + b + c + d + e + g = 0 →
    (∃ s : ZMod 2, ∀ p : Fin 6, ![a, b, c, d, e, g] p = s) ∨
    ∃ i j : Fin 6, i ≠ j ∧ ∃ s : ZMod 2, ∀ p : Fin 6,
      ![a, b, c, d, e, g] p + ((if p = i then 1 else 0) + (if p = j then 1 else 0)) = s := by
  decide

theorem exists_pc (v : altHeart 6) (hv : v ≠ 0) : ∃ i j : Fin 6, i ≠ j ∧ v = pc i j := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hx : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
  rw [Fin.sum_univ_six] at hx
  have hfun : (x : Fin 6 → ZMod 2) = ![(x : Fin 6 → ZMod 2) 0, (x : Fin 6 → ZMod 2) 1,
      (x : Fin 6 → ZMod 2) 2, (x : Fin 6 → ZMod 2) 3, (x : Fin 6 → ZMod 2) 4,
      (x : Fin 6 → ZMod 2) 5] := by
    funext p
    fin_cases p <;> rfl
  rcases exists_pc_aux _ _ _ _ _ _ hx with ⟨s, hs⟩ | ⟨i, j, hij, s, hs⟩
  · exfalso
    apply hv
    rw [← hfun] at hs
    exact (QuotientAddGroup.eq_zero_iff _).2 (mem_evenWeightOnes_of_forall_eq hs)
  · rw [← hfun] at hs
    refine ⟨i, j, hij, ?_⟩
    rw [pc_eq_mk]
    refine mk_eq_mk_iff.2 ⟨s, fun p => ?_⟩
    rw [pairEW_apply]
    exact hs p

theorem pc_ne_zero (i j : Fin 6) (hij : i ≠ j) : pc i j ≠ 0 := by
  obtain ⟨k, hki, hkj, -, -⟩ := exists_ne_four (by norm_num : 5 ≤ 6) i j i j
  exact mk_pairEW_ne_zero hij hki hkj

theorem altAct_pc (σ : Perm (Fin 6)) (i j : Fin 6) : altAct σ (pc i j) = pc (σ i) (σ j) :=
  (altAct_mk σ _).trans (congrArg _ (evenWeightPerm_pairEW σ i j))

theorem fixed_pc_iff (σ : Perm (Fin 6)) (i j : Fin 6) (hij : i ≠ j) :
    altAct σ (pc i j) = pc i j ↔ Pres σ i j := by
  constructor
  · intro h
    have hi : σ i = i ∨ σ i = j := by
      refine perm_mem_of_pair_fixed (by norm_num) σ hij ?_
      rw [pc_eq_mk, altAct_mk] at h
      exact h
    have hj : σ j = j ∨ σ j = i := by
      refine perm_mem_of_pair_fixed (by norm_num) σ hij.symm ?_
      rw [pc_comm, pc_eq_mk, altAct_mk] at h
      exact h
    rcases hi with hi | hi
    · left
      refine ⟨hi, ?_⟩
      rcases hj with hj | hj
      · exact hj
      · exact absurd (σ.injective (hj.trans hi.symm)) hij.symm
    · right
      refine ⟨hi, ?_⟩
      rcases hj with hj | hj
      · exact absurd (σ.injective (hi.trans hj.symm)) hij
      · exact hj
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [altAct_pc, h1, h2]
    · rw [altAct_pc, h1, h2, pc_comm]

private theorem exists_perm_pair {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Perm (Fin 6), σ a = c ∧ σ b = d := by
  have hb : swap a c b ≠ c := by
    intro h
    exact hab (((swap a c).injective (h.trans (swap_apply_left a c).symm)).symm)
  refine ⟨swap (swap a c b) d * swap a c, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hb) hcd]
  · rw [Perm.mul_apply]
    exact swap_apply_left _ _

theorem altAct_transitive (u v : altHeart 6) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ σ : Perm (Fin 6), altAct σ u = v := by
  obtain ⟨a, b, hab, rfl⟩ := exists_pc u hu
  obtain ⟨c, d, hcd, rfl⟩ := exists_pc v hv
  obtain ⟨σ, h1, h2⟩ := exists_perm_pair hab hcd
  exact ⟨σ, by rw [altAct_pc, h1, h2]⟩

theorem altAct_faithful (σ : Perm (Fin 6)) (h : ∀ v, altAct σ v = v) : σ = 1 :=
  perm_eq_one_of_altHeart_fixed (by norm_num) σ fun x => by
    rw [← altAct_mk]
    exact h _

private theorem cover_six {i j k l m n : Fin 6} (h : [i, j, k, l, m, n].Nodup) (p : Fin 6) :
    p = i ∨ p = j ∨ p = k ∨ p = l ∨ p = m ∨ p = n := by
  have hc : [i, j, k, l, m, n].toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup h]
    rfl
  have hu : [i, j, k, l, m, n].toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hc, Fintype.card_fin])
  have hp : p ∈ [i, j, k, l, m, n].toFinset := by
    rw [hu]
    exact Finset.mem_univ p
  simpa using hp

private theorem pc_six {i j k l m n : Fin 6} (h : [i, j, k, l, m, n].Nodup) :
    pc i j + pc k l + pc m n = 0 := by
  have hcov := cover_six h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or,
    List.nodup_nil, not_false_eq_true, and_true, true_and] at h
  obtain ⟨⟨hij, hik, hil, him, hin⟩, ⟨hjk, hjl, hjm, hjn⟩, ⟨hkl, hkm, hkn⟩, ⟨hlm, hln⟩, hmn⟩ := h
  rw [pc_eq_mk, pc_eq_mk, pc_eq_mk, ← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
  refine (QuotientAddGroup.eq_zero_iff _).2 (mem_evenWeightOnes_of_forall_eq (c := 1) fun p => ?_)
  simp only [AddSubgroup.coe_add, Pi.add_apply, pairEW_apply]
  rcases hcov p with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hij, hik, hil, him, hin, hjk, hjl, hjm, hjn, hkl, hkm, hkn, hlm, hln, hmn,
      Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm him, Ne.symm hin, Ne.symm hjk, Ne.symm hjl,
      Ne.symm hjm, Ne.symm hjn, Ne.symm hkl, Ne.symm hkm, Ne.symm hkn, Ne.symm hlm, Ne.symm hln,
      Ne.symm hmn]

private theorem add_eq_of_add_add_eq_zero {a b c : altHeart 6} (h : a + b + c = 0) : a + b = c := by
  rw [eq_neg_of_add_eq_zero_left h, neg_heart]

private theorem ne_of_add_ne_zero {a b : altHeart 6} (h : a + b ≠ 0) : a ≠ b := fun e =>
  h (by rw [e]; exact altHeart_add_self _)

theorem exists_indep : ∃ u v w : altHeart 6, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧ u + v ≠ 0 ∧ u + w ≠ 0 ∧
    v + w ≠ 0 ∧ u + v + w ≠ 0 := by
  have h01 : pc 0 1 + pc 0 2 = pc 1 2 := by rw [pc_comm 0 1, pc_add]
  have h02 : pc 0 1 + pc 0 3 = pc 1 3 := by rw [pc_comm 0 1, pc_add]
  have h12 : pc 0 2 + pc 0 3 = pc 2 3 := by rw [pc_comm 0 2, pc_add]
  have h3 : pc 0 1 + pc 0 2 + pc 0 3 = pc 4 5 := by
    rw [h01]
    exact add_eq_of_add_add_eq_zero (pc_six (by decide) : pc 1 2 + pc 0 3 + pc 4 5 = 0)
  refine ⟨pc 0 1, pc 0 2, pc 0 3, pc_ne_zero _ _ (by decide), pc_ne_zero _ _ (by decide),
    pc_ne_zero _ _ (by decide), ?_, ?_, ?_, ?_⟩
  · rw [h01]
    exact pc_ne_zero _ _ (by decide)
  · rw [h02]
    exact pc_ne_zero _ _ (by decide)
  · rw [h12]
    exact pc_ne_zero _ _ (by decide)
  · rw [h3]
    exact pc_ne_zero _ _ (by decide)

private theorem Pres.of_fix {σ : Perm (Fin 6)} {i j : Fin 6} (hi : σ i = i) (hj : σ j = j) :
    Pres σ i j :=
  Or.inl ⟨hi, hj⟩

private theorem Pres.mul {σ τ : Perm (Fin 6)} {i j : Fin 6} (hσ : Pres σ i j) (hτ : Pres τ i j) :
    Pres (σ * τ) i j := by
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hτ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp [Pres, Perm.mul_apply, h1, h2, h3, h4]

private theorem Pres.swap_of_ne {i j k l : Fin 6} (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j) : Pres (swap k l) i j :=
  Pres.of_fix (swap_apply_of_ne_of_ne hki.symm hli.symm) (swap_apply_of_ne_of_ne hkj.symm hlj.symm)

theorem decomp (i j : Fin 6) (_hij : i ≠ j) (σ : Perm (Fin 6)) (hσ : Pres σ i j) :
    ∃ σ₁ σ₂ : Perm (Fin 6), σ = σ₁ * σ₂ ∧ Pres σ₁ i j ∧ Pres σ₂ i j ∧
      (∃ k, k ≠ i ∧ k ≠ j ∧ σ₁ k = k) ∧ (∃ k, k ≠ i ∧ k ≠ j ∧ σ₂ k = k) := by
  obtain ⟨k, hki, hkj, -, -⟩ := exists_ne_four (by norm_num : 5 ≤ 6) i j i j
  by_cases hk : σ k = k
  · exact ⟨σ, 1, (mul_one σ).symm, hσ, Pres.of_fix rfl rfl, ⟨k, hki, hkj, hk⟩,
      ⟨k, hki, hkj, rfl⟩⟩
  · have hli : σ k ≠ i := by
      intro h
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hki (σ.injective (h.trans h1.symm))
      · exact hkj (σ.injective (h.trans h2.symm))
    have hlj : σ k ≠ j := by
      intro h
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hkj (σ.injective (h.trans h2.symm))
      · exact hki (σ.injective (h.trans h1.symm))
    obtain ⟨m, hmi, hmj, hmk, hml⟩ := exists_ne_four (by norm_num : 5 ≤ 6) i j k (σ k)
    have hP : Pres (swap k (σ k)) i j := Pres.swap_of_ne hki hkj hli hlj
    exact ⟨swap k (σ k), swap k (σ k) * σ, (swap_mul_self_mul _ _ _).symm, hP, hP.mul hσ,
      ⟨m, hmi, hmj, swap_apply_of_ne_of_ne hmk hml⟩,
      ⟨k, hki, hkj, by rw [Perm.mul_apply, swap_apply_right]⟩⟩

private theorem cyc_apply_left {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) : cyc i j k i = j := by
  rw [cyc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hij.symm hjk]

private theorem cyc_apply_mid {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) : cyc i j k j = k := by
  rw [cyc, Perm.mul_apply, swap_apply_right, swap_apply_left]

private theorem cyc_apply_right {i j k : Fin 6} (hik : i ≠ k) (hjk : j ≠ k) : cyc i j k k = i := by
  rw [cyc, Perm.mul_apply, swap_apply_of_ne_of_ne hik.symm hjk.symm, swap_apply_right]

theorem cyc_sum (i j k : Fin 6) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    pc i j + altAct (cyc i j k) (pc i j) + altAct (cyc i j k)⁻¹ (pc i j) = 0 := by
  have h1 : (cyc i j k)⁻¹ i = k := Perm.inv_eq_iff_eq.2 (cyc_apply_right hik hjk).symm
  have h2 : (cyc i j k)⁻¹ j = i := Perm.inv_eq_iff_eq.2 (cyc_apply_left hij hjk).symm
  rw [altAct_pc, altAct_pc, cyc_apply_left hij hjk, cyc_apply_mid hij hjk, h1, h2,
    pc_add, pc_add, pc_self]

private theorem swap_three : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
    swap j k * swap j i = swap i j * swap i k := by
  decide

theorem cyc_conj (i j k : Fin 6) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (σ : Perm (Fin 6)) (hσ : Pres σ i j) (hk : σ k = k) :
    σ * cyc i j k * σ⁻¹ = cyc i j k ∨ σ * cyc i j k * σ⁻¹ = (cyc i j k)⁻¹ := by
  have hconj : σ * (swap i k * swap i j) * σ⁻¹ = swap (σ i) (σ k) * swap (σ i) (σ j) := by
    rw [swap_apply_apply σ i k, swap_apply_apply σ i j]
    group
  unfold cyc
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [hconj, h1, h2, hk]
  · right
    rw [hconj, h1, h2, hk, mul_inv_rev, swap_inv, swap_inv]
    exact swap_three i j k hij hjk hik

theorem index_stabSub (u : altHeart 6) (hu : u ≠ 0) : (stabSub u).index = 15 := by
  letI : MulAction (Perm (Fin 6)) (altHeart 6) :=
    { smul := fun σ v => altAct σ v, one_smul := altAct_one, mul_smul := altAct_mul }
  have hstab : MulAction.stabilizer (Perm (Fin 6)) u = stabSub u :=
    Subgroup.ext fun σ => Iff.rfl
  rw [← hstab, MulAction.index_stabilizer]
  have horb : MulAction.orbit (Perm (Fin 6)) u = Set.univ \ {0} := by
    ext v
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨σ, rfl⟩ h
      apply hu
      have h' : altAct σ u = 0 := h
      have := altAct_inv_apply σ u
      rw [h', map_zero] at this
      exact this.symm
    · intro hv
      obtain ⟨σ, hσ⟩ := altAct_transitive u v hu hv
      exact ⟨σ, hσ⟩
  rw [horb, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, card_altHeart_six]

private noncomputable def diffHom (σ : Perm (Fin 6)) : altHeart 6 →+ altHeart 6 :=
  altAct σ + AddMonoidHom.id (altHeart 6)

private theorem diffHom_apply (σ : Perm (Fin 6)) (v : altHeart 6) :
    diffHom σ v = altAct σ v + v := rfl

private theorem ker_diffHom (σ : Perm (Fin 6)) : (diffHom σ).ker = fixSub σ := by
  ext v
  rw [AddMonoidHom.mem_ker, diffHom_apply, mem_fixSub]
  constructor
  · intro h
    have := eq_neg_of_add_eq_zero_left h
    rwa [neg_heart] at this
  · intro h
    rw [h]
    exact altHeart_add_self v

private theorem swap_diff_apply (i j : Fin 6) (hij : i ≠ j) (x : evenWeight 6) (p : Fin 6) :
    (x : Fin 6 → ZMod 2) ((swap i j)⁻¹ p) + (x : Fin 6 → ZMod 2) p =
      ((x : Fin 6 → ZMod 2) i + (x : Fin 6 → ZMod 2) j) *
        ((if p = i then 1 else 0) + (if p = j then 1 else 0)) := by
  rw [swap_inv]
  by_cases hpi : p = i
  · subst hpi
    simp [hij, swap_apply_left, add_comm]
  · by_cases hpj : p = j
    · subst hpj
      simp [hpi, swap_apply_right]
    · rw [swap_apply_of_ne_of_ne hpi hpj]
      simp [hpi, hpj, zmod2_add_self]

private theorem diffHom_swap_mk (i j : Fin 6) (hij : i ≠ j) (x : evenWeight 6) :
    diffHom (swap i j) (x : altHeart 6) = 0 ∨ diffHom (swap i j) (x : altHeart 6) = pc i j := by
  rw [diffHom_apply, altAct_mk, ← QuotientAddGroup.mk_add]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1)
      ((x : Fin 6 → ZMod 2) i + (x : Fin 6 → ZMod 2) j) with hc | hc
  · left
    refine (QuotientAddGroup.eq_zero_iff _).2
      (mem_evenWeightOnes_of_forall_eq (c := 0) fun p => ?_)
    simp only [AddSubgroup.coe_add, Pi.add_apply, evenWeightPerm_apply]
    rw [swap_diff_apply i j hij x p, hc, zero_mul]
  · right
    rw [pc_eq_mk]
    refine mk_eq_mk_iff.2 ⟨0, fun p => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, evenWeightPerm_apply, pairEW_apply]
    rw [swap_diff_apply i j hij x p, hc, one_mul]
    exact zmod2_add_self _

private theorem range_diffHom_swap (i j : Fin 6) (hij : i ≠ j) :
    (diffHom (swap i j)).range = AddSubgroup.zmultiples (pc i j) := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
    rcases diffHom_swap_mk i j hij x with h | h
    · rw [h]
      exact zero_mem _
    · rw [h]
      exact AddSubgroup.mem_zmultiples _
  · rw [AddSubgroup.zmultiples_le]
    obtain ⟨k, hki, hkj, -, -⟩ := exists_ne_four (by norm_num : 5 ≤ 6) i j i j
    refine ⟨pc i k, ?_⟩
    rw [diffHom_apply, altAct_pc, swap_apply_left, swap_apply_of_ne_of_ne hki hkj,
      pc_comm i k, pc_add, pc_comm j i]

private theorem card_range_diffHom_swap (i j : Fin 6) (hij : i ≠ j) :
    Nat.card (diffHom (swap i j)).range = 2 := by
  rw [range_diffHom_swap i j hij, Nat.card_zmultiples]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact addOrderOf_eq_prime (by rw [two_nsmul]; exact altHeart_add_self _) (pc_ne_zero i j hij)

theorem card_fixSub_swap (i j : Fin 6) (hij : i ≠ j) : Nat.card (fixSub (swap i j)) = 8 := by
  have h1 := AddSubgroup.card_ker_mul_card_range (diffHom (swap i j))
  rw [ker_diffHom, card_altHeart_six, card_range_diffHom_swap i j hij] at h1
  omega

private theorem pres_two_aux : ∀ a b : Fin 6, a ≠ b → Pres (swap 4 5) a b → Pres (swap 0 2) a b →
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) ∨
      (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by
  unfold Pres
  decide

theorem card_fixSub_two : Nat.card ↥(fixSub (swap 4 5) ⊓ fixSub (swap 0 2)) = 4 := by
  have hset : ((fixSub (swap 4 5) ⊓ fixSub (swap 0 2) : AddSubgroup (altHeart 6)) :
      Set (altHeart 6)) = {0, pc 0 2, pc 4 5, pc 1 3} := by
    ext v
    simp only [AddSubgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixSub,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hv : v = 0
      · exact Or.inl hv
      · right
        obtain ⟨a, b, hab, rfl⟩ := exists_pc v hv
        have p1 := (fixed_pc_iff _ a b hab).1 h1
        have p2 := (fixed_pc_iff _ a b hab).1 h2
        rcases pres_two_aux a b hab p1 p2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inl (pc_comm _ _)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inl (pc_comm _ _))
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inr (pc_comm _ _))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨map_zero _, map_zero _⟩
      · exact ⟨(fixed_pc_iff _ 0 2 (by decide)).2 (by unfold Pres; decide),
          (fixed_pc_iff _ 0 2 (by decide)).2 (by unfold Pres; decide)⟩
      · exact ⟨(fixed_pc_iff _ 4 5 (by decide)).2 (by unfold Pres; decide),
          (fixed_pc_iff _ 4 5 (by decide)).2 (by unfold Pres; decide)⟩
      · exact ⟨(fixed_pc_iff _ 1 3 (by decide)).2 (by unfold Pres; decide),
          (fixed_pc_iff _ 1 3 (by decide)).2 (by unfold Pres; decide)⟩
  have s1 : pc 0 2 + pc 4 5 = pc 1 3 := add_eq_of_add_add_eq_zero (pc_six (by decide))
  have s2 : pc 0 2 + pc 1 3 = pc 4 5 := add_eq_of_add_add_eq_zero (pc_six (by decide))
  have s3 : pc 4 5 + pc 1 3 = pc 0 2 := add_eq_of_add_add_eq_zero (pc_six (by decide))
  have n1 : pc 0 2 ≠ pc 4 5 := ne_of_add_ne_zero (by rw [s1]; exact pc_ne_zero _ _ (by decide))
  have n2 : pc 0 2 ≠ pc 1 3 := ne_of_add_ne_zero (by rw [s2]; exact pc_ne_zero _ _ (by decide))
  have n3 : pc 4 5 ≠ pc 1 3 := ne_of_add_ne_zero (by rw [s3]; exact pc_ne_zero _ _ (by decide))
  have z1 : (0 : altHeart 6) ≠ pc 0 2 := (pc_ne_zero _ _ (by decide)).symm
  have z2 : (0 : altHeart 6) ≠ pc 4 5 := (pc_ne_zero _ _ (by decide)).symm
  have z3 : (0 : altHeart 6) ≠ pc 1 3 := (pc_ne_zero _ _ (by decide)).symm
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    Set.ncard_insert_of_notMem (by simp [z1, z2, z3]),
    Set.ncard_insert_of_notMem (by simp [n1, n2]), Set.ncard_pair n3]

private theorem invol_ne {σ : Perm (Fin 6)} {i j p : Fin 6} (hinv : ∀ q, σ (σ q) = q)
    (hσ : Pres σ i j) (hpi : p ≠ i) (hpj : p ≠ j) : σ p ≠ i ∧ σ p ≠ j := by
  constructor
  · intro h
    have h' : σ i = p := by rw [← h]; exact hinv p
    rcases hσ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hpi (h'.symm.trans h1)
    · exact hpj (h'.symm.trans h1)
  · intro h
    have h' : σ j = p := by rw [← h]; exact hinv p
    rcases hσ with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact hpj (h'.symm.trans h2)
    · exact hpi (h'.symm.trans h2)

private theorem conj_swap_apply (a b : Fin 6) (σ : Perm (Fin 6)) (p : Fin 6) :
    (swap a b * σ * (swap a b)⁻¹) p = swap a b (σ (swap a b p)) := by
  rw [Perm.mul_apply, Perm.mul_apply, swap_inv]

private theorem quad_alg {i j k l m n s : Fin 6} (hij : i ≠ j) (hnd : [i, j, k, n, l, m].Nodup)
    (h : pc i n + pc s m + (pc s l + pc i k) = 0) : False := by
  have hnk : pc n k + pc m l = 0 := by
    calc pc n k + pc m l = (pc n i + pc i k) + (pc m s + pc s l) := by rw [pc_add, pc_add]
      _ = (pc i n + pc s m) + (pc s l + pc i k) := by rw [pc_comm n i, pc_comm m s]; abel
      _ = 0 := h
  have h6 := pc_six hnd
  rw [pc_comm k n, pc_comm l m, add_assoc, hnk, add_zero] at h6
  exact pc_ne_zero i j hij h6

theorem quad (i j : Fin 6) (hij : i ≠ j) (E : Subgroup (Perm (Fin 6)))
    (hP : ∀ e ∈ E, Pres e i j) (hN : ∀ h : Perm (Fin 6), Pres h i j → ∀ e ∈ E, h * e * h⁻¹ ∈ E)
    (hSq : ∀ e ∈ E, e * e = 1)
    (hQ : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : altHeart 6,
      altAct e' (altAct e v + v) + (altAct e v + v) = 0) :
    ∀ e ∈ E, e = 1 ∨ e = swap i j := by
  intro σ hσ
  have hσP := hP σ hσ
  have hinv : ∀ p, σ (σ p) = p := fun p => by
    have := congrArg (fun f : Perm (Fin 6) => f p) (hSq σ hσ)
    simpa [Perm.mul_apply] using this
  by_cases hfix : ∀ k, k ≠ i → k ≠ j → σ k = k
  · rcases hσP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine Equiv.ext fun p => ?_
      by_cases hpi : p = i
      · simp [hpi, h1]
      · by_cases hpj : p = j
        · simp [hpj, h2]
        · exact hfix p hpi hpj
    · right
      refine Equiv.ext fun p => ?_
      by_cases hpi : p = i
      · simp [hpi, h1]
      · by_cases hpj : p = j
        · simp [hpj, h2]
        · rw [swap_apply_of_ne_of_ne hpi hpj]
          exact hfix p hpi hpj
  · exfalso
    push Not at hfix
    obtain ⟨k, hki, hkj, hk⟩ := hfix
    have hl_i : σ k ≠ i := (invol_ne hinv hσP hki hkj).1
    have hl_j : σ k ≠ j := (invol_ne hinv hσP hki hkj).2
    obtain ⟨m, hmi, hmj, hmk, hml⟩ := exists_ne_four (by norm_num : 5 ≤ 6) i j k (σ k)
    have hhi : swap (σ k) m i = i := swap_apply_of_ne_of_ne hl_i.symm hmi.symm
    have hhj : swap (σ k) m j = j := swap_apply_of_ne_of_ne hl_j.symm hmj.symm
    have hσ' : swap (σ k) m * σ * (swap (σ k) m)⁻¹ ∈ E :=
      hN _ (Pres.of_fix hhi hhj) σ hσ
    by_cases hm : σ m = m
    · have hs1 : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) k = m := by
        rw [conj_swap_apply, swap_apply_of_ne_of_ne hk.symm hmk.symm, swap_apply_left]
      have hs2 : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) m = k := by
        rw [conj_swap_apply, swap_apply_right, hinv k, swap_apply_of_ne_of_ne hk.symm hmk.symm]
      have key : ∀ σ' : Perm (Fin 6), σ' ∈ E → σ' k = m → σ' m = k → False := by
        intro σ' hσ'E h1 h2
        have hsq := hSq _ (E.mul_mem hσ hσ'E)
        have h3 := congrArg (fun f : Perm (Fin 6) => f k) hsq
        simp only [Perm.mul_apply, Perm.one_apply] at h3
        rw [h1, hm, h2] at h3
        exact hk h3
      exact key _ hσ' hs1 hs2
    · have hn_i : σ m ≠ i := (invol_ne hinv hσP hmi hmj).1
      have hn_j : σ m ≠ j := (invol_ne hinv hσP hmi hmj).2
      have hn_k : σ m ≠ k := fun h => hml ((hinv m).symm.trans (congrArg σ h))
      have hn_l : σ m ≠ σ k := fun h => hmk (σ.injective h)
      have hnd : [i, j, k, σ m, σ k, m].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or,
          List.nodup_nil, not_false_eq_true, and_true, true_and]
        exact ⟨⟨hij, hki.symm, hn_i.symm, hl_i.symm, hmi.symm⟩,
          ⟨hkj.symm, hn_j.symm, hl_j.symm, hmj.symm⟩, ⟨hn_k.symm, hk.symm, hmk.symm⟩,
          ⟨hn_l, hm⟩, hml.symm⟩
      have hhσi : swap (σ k) m (σ i) = σ i := by
        rcases hσP with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]
          exact hhi
        · rw [h1]
          exact hhj
      have hs_σi : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) (σ i) = i := by
        rw [conj_swap_apply, hhσi, hinv i, hhi]
      have hs_σk : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) (σ k) = σ m := by
        rw [conj_swap_apply, swap_apply_left, swap_apply_of_ne_of_ne hn_l hm]
      have hs_i : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) i = σ i := by
        rw [conj_swap_apply, hhi, hhσi]
      have hs_k : (swap (σ k) m * σ * (swap (σ k) m)⁻¹) k = m := by
        rw [conj_swap_apply, swap_apply_of_ne_of_ne hk.symm hmk.symm, swap_apply_left]
      have hQv := hQ σ hσ _ hσ' (pc i k)
      rw [altAct_pc, map_add, altAct_pc, altAct_pc, hs_σi, hs_σk, hs_i, hs_k] at hQv
      exact quad_alg hij hnd hQv

theorem facts_holds : Facts where
  card := card_altHeart_six
  trans := altAct_transitive
  faithful := altAct_faithful
  exists_pc := exists_pc
  pc_ne_zero := pc_ne_zero
  altAct_pc := altAct_pc
  fixed_pc_iff := fixed_pc_iff
  indep := exists_indep
  cyc_sum := cyc_sum
  cyc_conj := cyc_conj
  decomp := decomp
  index_stabSub := index_stabSub
  card_fix_swap := card_fixSub_swap
  card_fix_two := card_fixSub_two
  quad := quad

end CFSG.CGT.Hall82.TheoremA
