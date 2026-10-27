module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Transvection
public import Mathlib.Order.CompletePartialOrder
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Finset

@[expose] def bs : Fin 6 → V6 :=
  ![![0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 0, 0, 1, 0, 1], ![1, 1, 0, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0], ![0, 1, 1, 0, 0, 1]]

set_option maxRecDepth 100000 in
theorem bs_span (x : V6) : ∃ c : Fin 6 → ZMod 2, x = ∑ i, c i • bs i := by
  revert x
  decide +kernel

theorem eq_one_of_fix_bs (g : Equiv.Perm V6) (hg : IsAddPerm g) (h : ∀ i, g (bs i) = bs i) :
    g = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨c, hc⟩ := bs_span x
  let F : AddMonoidHom V6 V6 := AddMonoidHom.mk' g hg
  have hg0 : g 0 = 0 := map_zero F
  have hsmul : ∀ (c : ZMod 2) (v : V6), g (c • v) = c • g v := by
    intro c v
    have hlt : c.val < 2 := ZMod.val_lt c
    have hc01 : c = 0 ∨ c = 1 := by
      rcases (by omega : c.val = 0 ∨ c.val = 1) with hc0 | hc1
      · left
        rw [← ZMod.natCast_zmod_val c, hc0]
        norm_num
      · right
        rw [← ZMod.natCast_zmod_val c, hc1]
        norm_num
    rcases hc01 with rfl | rfl <;> simp [hg0]
  have hsum : ∀ s : Finset (Fin 6), g (∑ i ∈ s, c i • bs i) = ∑ i ∈ s, c i • bs i := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using hg0
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, hg, ih, hsmul, h i]
  rw [hc, Equiv.Perm.one_apply]
  exact hsum Finset.univ

@[expose] def TG (q : V6 → ZMod 2) : Subgroup (Equiv.Perm V6) :=
  Subgroup.closure {g | ∃ u : V6, q u = 1 ∧ g = transv u}

@[expose] def StabK (q : V6 → ZMod 2) (k : ℕ) : Subgroup (Equiv.Perm V6) where
  carrier := {g | g ∈ OrthOf q ∧ ∀ i : Fin 6, i.val < k → g (bs i) = bs i}
  mul_mem' := by
    rintro g h ⟨hg, hgfix⟩ ⟨hh, hhfix⟩
    refine ⟨mul_mem hg hh, fun i hi => ?_⟩
    rw [Equiv.Perm.mul_apply, hhfix i hi, hgfix i hi]
  one_mem' := by
    exact ⟨Subgroup.one_mem _, fun i _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hg, hgfix⟩
    refine ⟨inv_mem hg, fun i hi => ?_⟩
    show g.symm (bs i) = bs i
    rw [Equiv.symm_apply_eq]
    exact (hgfix i hi).symm

private lemma mem_stabK_iff {q : V6 → ZMod 2} {k : ℕ} {g : Equiv.Perm V6} :
    g ∈ StabK q k ↔ g ∈ OrthOf q ∧ ∀ i : Fin 6, i.val < k → g (bs i) = bs i :=
  Iff.rfl

private lemma mem_stabK_succ_iff {q : V6 → ZMod 2} {k : Fin 6} {g : Equiv.Perm V6} :
    g ∈ StabK q (k.val + 1) ↔ g ∈ StabK q k.val ∧ g (bs k) = bs k := by
  rw [mem_stabK_iff, mem_stabK_iff]
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨⟨hg, fun i hi => hfix i (by omega)⟩, hfix k (by omega)⟩
  · rintro ⟨⟨hg, hfix⟩, hk⟩
    refine ⟨hg, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact hfix i h
    · have hik : i = k := Fin.ext h
      rw [hik, hk]

private lemma mem_stabK_succ_iff' {q : V6 → ZMod 2} {k : ℕ} (hk : k < 6) {g : Equiv.Perm V6} :
    g ∈ StabK q (k + 1) ↔ g ∈ StabK q k ∧ g (bs ⟨k, hk⟩) = bs ⟨k, hk⟩ := by
  rw [mem_stabK_iff, mem_stabK_iff]
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨⟨hg, fun i hi => hfix i (by omega)⟩, hfix ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨⟨hg, hfix⟩, hk'⟩
    refine ⟨hg, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact hfix i h
    · have hik : i = ⟨k, hk⟩ := Fin.ext h
      rw [hik, hk']

private lemma stabK_zero (q : V6 → ZMod 2) : StabK q 0 = OrthOf q := by
  ext g
  rw [mem_stabK_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun i hi => by omega⟩

private lemma stabK_six (q : V6 → ZMod 2) : StabK q 6 = ⊥ := by
  ext g
  rw [Subgroup.mem_bot]
  constructor
  · intro hg
    rw [mem_stabK_iff] at hg
    exact eq_one_of_fix_bs g hg.1.1 (fun i => hg.2 i i.isLt)
  · intro hg
    rw [hg]
    exact Subgroup.one_mem _

@[expose] def Cset (q : V6 → ZMod 2) (k : Fin 6) : Finset V6 :=
  Finset.univ.filter fun c =>
    q c = q (bs k) ∧ ∀ i : Fin 6, i < k → bil c (bs i) = bil (bs k) (bs i)

@[expose] def allowed (q : V6 → ZMod 2) (k : Fin 6) : Finset V6 :=
  Finset.univ.filter fun u => q u = 1 ∧ ∀ i : Fin 6, i < k → bil u (bs i) = 0

@[expose] def reachStep (q : V6 → ZMod 2) (k : Fin 6) (R : Finset V6) : Finset V6 :=
  R ∪ R.biUnion fun x => (allowed q k).image fun u => x + bil x u • u

@[expose] def reachSet (q : V6 → ZMod 2) (k : Fin 6) (d : ℕ) : Finset V6 :=
  (reachStep q k)^[d] {bs k}

theorem exists_mem_stab_of_mem_reachSet {q : V6 → ZMod 2} (hq : IsQF q) (k : Fin 6) (d : ℕ)
    {c : V6} (hc : c ∈ reachSet q k d) :
    ∃ g ∈ StabK q k.val ⊓ TG q, g (bs k) = c := by
  suffices h : ∀ d : ℕ, ∀ c : V6, c ∈ reachSet q k d →
      ∃ g ∈ StabK q k.val ⊓ TG q, g (bs k) = c from h d c hc
  intro d
  induction d with
  | zero =>
      intro c hc
      rw [reachSet, Function.iterate_zero_apply, Finset.mem_singleton] at hc
      rw [hc]
      exact ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, by simp⟩
  | succ d ih =>
      intro c hc
      rw [reachSet, Function.iterate_succ_apply', reachStep, Finset.mem_union] at hc
      rcases hc with hc | hc
      · exact ih c hc
      · rw [Finset.mem_biUnion] at hc
        obtain ⟨x, hx, hc⟩ := hc
        rw [Finset.mem_image] at hc
        obtain ⟨u, hu, huc⟩ := hc
        simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨g₀, hg₀, hg₀x⟩ := ih x hx
        obtain ⟨hg₀K, hg₀TG⟩ := Subgroup.mem_inf.mp hg₀
        rw [mem_stabK_iff] at hg₀K
        refine ⟨transv u * g₀, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [mem_stabK_iff]
          refine ⟨mul_mem (transv_mem_orthOf hq hu.1) hg₀K.1, fun i hi => ?_⟩
          have hik : i < k := Fin.lt_iff_val_lt_val.mpr hi
          have hui : bil u (bs i) = 0 := hu.2 i hik
          have hfixi : transv u (bs i) = bs i :=
            transv_apply_of_bil_eq_zero (u := u) (x := bs i) (by rw [bil_comm]; exact hui)
          rw [Equiv.Perm.mul_apply, hg₀K.2 i hi, hfixi]
        · exact mul_mem (Subgroup.subset_closure ⟨u, hu.1, rfl⟩) hg₀TG
        · show (transv u * g₀) (bs k) = c
          rw [Equiv.Perm.mul_apply, hg₀x, transv_apply]
          exact huc

private lemma mem_Cset_of_mem_stabK {q : V6 → ZMod 2} (hq : IsQF q) {k : Fin 6}
    {g : Equiv.Perm V6} (hg : g ∈ StabK q k.val) : g (bs k) ∈ Cset q k := by
  rw [mem_stabK_iff] at hg
  rw [Cset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hg.1.2 (bs k), fun i hi => ?_⟩
  have hgi : g (bs i) = bs i := hg.2 i (Fin.lt_iff_val_lt_val.mp hi)
  calc bil (g (bs k)) (bs i) = bil (g (bs k)) (g (bs i)) := by rw [hgi]
    _ = bil (bs k) (bs i) := bil_apply_of_mem_orthOf hq hg.1 (bs k) (bs i)

private lemma orbit_stabK_eq_card_Cset {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2) (k : Fin 6) :
    Nat.card (MulAction.orbit (StabK q k.val) (bs k)) = (Cset q k).card := by
  have hset : MulAction.orbit (StabK q k.val) (bs k) = (Cset q k : Set V6) := by
    ext c
    constructor
    · intro hc
      rw [MulAction.mem_orbit_iff] at hc
      obtain ⟨g, hg⟩ := hc
      rw [← hg]
      simpa [Subgroup.smul_def] using mem_Cset_of_mem_stabK hq g.2
    · intro hc
      obtain ⟨g, hg, hgc⟩ := exists_mem_stab_of_mem_reachSet hq k 2 (hreach k c hc)
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨g, hg.1⟩, by simpa [Subgroup.smul_def] using hgc⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private lemma card_stabilizer_eq {q : V6 → ZMod 2} (k : Fin 6) :
    Nat.card (MulAction.stabilizer (StabK q k.val) (bs k)) =
      Nat.card (StabK q (k.val + 1)) := by
  have hmap : (MulAction.stabilizer (StabK q k.val) (bs k)).map
        (Subgroup.subtype (StabK q k.val)) = StabK q (k.val + 1) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxg⟩
      rw [← hxg]
      show (x : Equiv.Perm V6) ∈ StabK q (k.val + 1)
      have hxfix : (x : Equiv.Perm V6) (bs k) = bs k := by
        have h := hx
        rw [MulAction.mem_stabilizer_iff] at h
        simpa [Subgroup.smul_def] using h
      exact mem_stabK_succ_iff.mpr ⟨x.2, hxfix⟩
    · intro hg
      obtain ⟨hgK, hgk⟩ := (mem_stabK_succ_iff (q := q) (k := k) (g := g)).mp hg
      refine ⟨⟨g, hgK⟩, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hgk
  calc Nat.card (MulAction.stabilizer (StabK q k.val) (bs k))
      = Nat.card ((MulAction.stabilizer (StabK q k.val) (bs k)).map
          (Subgroup.subtype (StabK q k.val))) :=
        (Subgroup.card_map_of_injective (K := MulAction.stabilizer (StabK q k.val) (bs k))
          (f := Subgroup.subtype (StabK q k.val)) (Subgroup.subtype_injective _)).symm
    _ = Nat.card (StabK q (k.val + 1)) := by rw [hmap]

private lemma card_stabK_mul_card_Cset {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2) (k : Fin 6) :
    (Cset q k).card * Nat.card (StabK q (k.val + 1)) = Nat.card (StabK q k.val) := by
  calc (Cset q k).card * Nat.card (StabK q (k.val + 1))
      = Nat.card (MulAction.orbit (StabK q k.val) (bs k)) *
          Nat.card (MulAction.stabilizer (StabK q k.val) (bs k)) := by
        rw [← orbit_stabK_eq_card_Cset hq hreach k, ← card_stabilizer_eq k]
    _ = Nat.card ((StabK q k.val) ⧸ MulAction.stabilizer (StabK q k.val) (bs k)) *
          Nat.card (MulAction.stabilizer (StabK q k.val) (bs k)) := by
        rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (StabK q k.val) (bs k))]
    _ = Nat.card (StabK q k.val) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (MulAction.stabilizer (StabK q k.val) (bs k))).symm

private lemma stabK_le_TG_succ {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2)
    {k : ℕ} (hk : k < 6) (hnext : StabK q (k + 1) ≤ TG q) :
    StabK q k ≤ TG q := by
  intro g hg
  rw [mem_stabK_iff] at hg
  let kf : Fin 6 := ⟨k, hk⟩
  have hgK : g ∈ StabK q kf.val := mem_stabK_iff.mpr ⟨hg.1, fun i hi => hg.2 i hi⟩
  have hcC : g (bs kf) ∈ Cset q kf := mem_Cset_of_mem_stabK hq hgK
  have hcreach : g (bs kf) ∈ reachSet q kf 2 := hreach kf _ hcC
  obtain ⟨τ, hτ, hτc⟩ := exists_mem_stab_of_mem_reachSet hq kf 2 hcreach
  obtain ⟨hτK, hτTG⟩ := Subgroup.mem_inf.mp hτ
  rw [mem_stabK_iff] at hτK
  have hmem : τ⁻¹ * g ∈ StabK q (k + 1) := by
    rw [mem_stabK_succ_iff' hk]
    refine ⟨?_, ?_⟩
    · refine mem_stabK_iff.mpr ⟨mul_mem (inv_mem hτK.1) hg.1, fun i hi => ?_⟩
      have hgi : g (bs i) = bs i := hg.2 i hi
      have hτi : τ (bs i) = bs i := hτK.2 i hi
      have hτinvi : τ⁻¹ (bs i) = bs i := by
        show τ.symm (bs i) = bs i
        rw [Equiv.symm_apply_eq]
        exact hτi.symm
      rw [Equiv.Perm.mul_apply, hgi]
      exact hτinvi
    · show (τ⁻¹ * g) (bs kf) = bs kf
      rw [Equiv.Perm.mul_apply, ← hτc]
      show τ.symm (τ (bs kf)) = bs kf
      rw [Equiv.symm_apply_apply]
  have hτinv : τ⁻¹ * g ∈ TG q := hnext hmem
  have hg_eq : τ * (τ⁻¹ * g) = g := by group
  rw [← hg_eq]
  exact mul_mem hτTG hτinv

private lemma stabK_le_TG_of_le_six {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2) :
    ∀ k, k ≤ 6 → StabK q k ≤ TG q := by
  intro k hk
  refine Nat.decreasingInduction
    (motive := fun k _ => StabK q k ≤ TG q)
    (fun k hk hnext => stabK_le_TG_succ hq hreach hk hnext) ?_ hk
  rw [stabK_six]
  exact bot_le

private lemma telescoping {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2) :
    Nat.card (StabK q 0) = ∏ k : Fin 6, (Cset q k).card := by
  have h0 : Nat.card (StabK q 0) = (Cset q 0).card * Nat.card (StabK q 1) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (0 : Fin 6)).symm
  have h1 : Nat.card (StabK q 1) = (Cset q 1).card * Nat.card (StabK q 2) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (1 : Fin 6)).symm
  have h2 : Nat.card (StabK q 2) = (Cset q 2).card * Nat.card (StabK q 3) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (2 : Fin 6)).symm
  have h3 : Nat.card (StabK q 3) = (Cset q 3).card * Nat.card (StabK q 4) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (3 : Fin 6)).symm
  have h4 : Nat.card (StabK q 4) = (Cset q 4).card * Nat.card (StabK q 5) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (4 : Fin 6)).symm
  have h5 : Nat.card (StabK q 5) = (Cset q 5).card * Nat.card (StabK q 6) := by
    simpa using (card_stabK_mul_card_Cset hq hreach (5 : Fin 6)).symm
  have h6 : Nat.card (StabK q 6) = 1 := by
    rw [stabK_six]
    exact Subgroup.card_bot
  rw [Fin.prod_univ_six]
  rw [h0, h1, h2, h3, h4, h5, h6]
  ring

theorem orthOf_chain {q : V6 → ZMod 2} (hq : IsQF q)
    (hreach : ∀ k : Fin 6, ∀ c ∈ Cset q k, c ∈ reachSet q k 2) :
    Nat.card (OrthOf q) = ∏ k : Fin 6, (Cset q k).card ∧ OrthOf q = TG q := by
  constructor
  · rw [← stabK_zero q]
    exact telescoping hq hreach
  · apply le_antisymm
    · have h := stabK_le_TG_of_le_six hq hreach 0 (Nat.zero_le 6)
      rw [stabK_zero q] at h
      exact h
    · rw [TG, Subgroup.closure_le]
      rintro g ⟨u, hu, rfl⟩
      exact transv_mem_orthOf hq hu

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
