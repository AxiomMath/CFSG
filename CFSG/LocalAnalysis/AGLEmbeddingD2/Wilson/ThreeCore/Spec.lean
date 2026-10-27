module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Check
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
open CFSG.RankThree.LocalRank

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

structure GroupDataSound (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (pg : Array Table)
    (gg : ℕ → Equiv.Perm (Fin n)) (sift : Table → Bool) : Prop where
  lt : n < 2 ^ 32
  rep : ∀ l < pg.size, Rep n pg[l]! (gg l)
  gen : P = closure (gg '' {l | l < pg.size})
  sift : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → sift T = true → g ∈ P

theorem groupDataSound_of_groupData (hD : GroupData n P pg gg sift) :
    GroupDataSound n P pg gg sift :=
  ⟨hD.lt, hD.rep, hD.gen, fun T g hT h => (hD.sift T g hT).1 h⟩

theorem GroupDataSound.mem (hD : GroupDataSound n P pg gg sift) {l : ℕ} (hl : l < pg.size) :
    gg l ∈ P := by
  rw [hD.gen]
  exact subset_closure ⟨l, hl, rfl⟩

theorem threeSylowOK_spec (hD : GroupDataSound n P pg gg sift) {cap : ℕ} {sylowGens : List Table}
    {sylowOrder : ℕ} (h : threeSylowOK n cap pg pgInv sift sylowGens sylowOrder = true) :
    (∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹) ∧
      closure (tp n '' {x | x ∈ sylowGens.toArray}) ≤ P ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ sylowGens.toArray})) = sylowOrder ∧
      (∀ x ∈ closure (tp n '' {x | x ∈ sylowGens.toArray}),
        ∃ k < (mulClosureH n sylowGens.toArray cap).1.size,
          Rep n (mulClosureH n sylowGens.toArray cap).1[k]! x) := by
  have hn := hD.lt
  simp only [threeSylowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hinv⟩, hsg⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  have hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹ := by
    intro l hl
    have := allIn_eq_true.1 hinv l (Nat.zero_le _) hl
    exact Rep.inv_of_invOK (hD.rep l hl) this
  rw [Array.all_eq_true'] at hsg
  simp only [Bool.and_eq_true] at hsg
  have hg : ∀ x ∈ sylowGens.toArray, permOK n x = true := fun x hx => (hsg x hx).1.1
  have hginv : ∀ x ∈ sylowGens.toArray, invOK n x (invT n x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨-, hcov, hcard⟩ := enum_spec hn hg hginv htree hclosed hdist
  refine ⟨hpgi, ?_, hcard.trans hsize, hcov⟩
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hD.sift _ _ (rep_tp (hg x hx)) (hsg x hx).2

theorem threeClassOK_spec (hD : GroupDataSound n P pg gg sift) {NP cap : ℕ} (hP : Nat.card P = NP)
    (hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹) {r : ClassRow}
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 3 → q ∈ r.oddPrimes)
    (h : threeClassOK n NP cap pg pgInv sift r (conjClosureH n pg pgInv r.rep cap) = true) :
    Rep n r.rep (tp n r.rep) ∧ orderOf (tp n r.rep) = 3 ∧ tp n r.rep ∈ P ∧
      (∀ k < (conjClosureH n pg pgInv r.rep cap).1.size, ∃ c ∈ P,
        Rep n (conjClosureH n pg pgInv r.rep cap).1[k]! (c * tp n r.rep * c⁻¹)) ∧
      closure (tp n '' {x | x ∈ r.centGens.toArray}) = P ⊓ centralizer ({tp n r.rep} : Set _) ∧
      Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder ∧
      (conjClass P (tp n r.rep)).ncard = r.classSize ∧
      aschbacherSolvableCore 3
        ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = ⊥ := by
  have hn := hD.lt
  set t := tp n r.rep
  set o := conjClosureH n pg pgInv r.rep cap
  set cg := r.centGens.toArray
  set cgInv := cg.map (invT n)
  set C := mulClosureH n cg cap
  set queues := r.odd.map fun s => (s, conjClosureH n cg cgInv s.rep cap)
  simp only [threeClassOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht1, ht3⟩, htP⟩, horb⟩, hodist⟩, hosize⟩, hcg⟩, hCtree⟩, hCdist⟩,
    hCsize⟩, hprod⟩, hodd⟩, hqtree⟩, hcov⟩ := h
  have hT := rep_tp ht1
  have hord : orderOf t = 3 := (ordTest_iff_perm hT (by norm_num)).1 ht3
  have htP' : t ∈ P := hD.sift _ _ hT htP
  have hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P :=
    fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩
  have horb' := conjTreeOK_spec P hgP hT horb
  rw [Array.all_eq_true'] at hcg
  simp only [Bool.and_eq_true] at hcg
  have hcgP : ∀ c ∈ cg, Rep n c (tp n c) ∧ tp n c ∈ P ⊓ centralizer ({t} : Set _) := by
    intro c hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hcg c hc
    have hc' := rep_tp h1
    refine ⟨hc', mem_inf.mpr ⟨hD.sift _ _ hc' h2, ?_⟩⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff hc' hT).1 h3
  set K := closure (tp n '' {x | x ∈ cg})
  have hKle : K ≤ P ⊓ centralizer ({t} : Set _) := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact (hcgP c hc).2
  have hga : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ tp n cg[l]! ∈ K := fun l hl =>
    ⟨(hcgP _ (getElem!_mem_array hl)).1, subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hCK := mulTreeOK_spec hn K (gg := fun l => tp n cg[l]!) hga hCtree
  have hCrep : ∀ k < C.1.size, Rep n C.1[k]! (tablePerm n C.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hCmem : ∀ k < C.1.size, tablePerm n C.1[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  have hCnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hCdist
  have hKcard : r.centOrder ≤ Nat.card K := by
    have := length_le_card_of_nodup hCnodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
      exact hCmem k hk
    rwa [List.length_map, Array.length_toList, hCsize] at this
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hodist
  have hclass : r.classSize ≤ (conjClass P t).ncard := by
    have := length_le_ncard_of_nodup honodup (S := conjClass P t) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := horb' k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList, hosize] at this
  have hos := ncard_conjClass_mul_card P t
  rw [hP, ← hprod] at hos
  have hCle : Nat.card K ≤ Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := card_le_of_le hKle
  have hpos1 : 0 < r.classSize := by
    rcases Nat.eq_zero_or_pos r.classSize with h0 | h0
    · rw [h0, zero_mul] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hpos2 : 0 < r.centOrder := by
    rcases Nat.eq_zero_or_pos r.centOrder with h0 | h0
    · rw [h0, mul_zero] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hcent : Nat.card ↥(P ⊓ centralizer ({t} : Set _)) = r.centOrder := by
    by_contra hne
    have hlt : r.centOrder < Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := by omega
    have : r.classSize * r.centOrder < (conjClass P t).ncard *
        Nat.card ↥(P ⊓ centralizer ({t} : Set _)) :=
      Nat.mul_lt_mul_of_le_of_lt hclass hlt (hpos1.trans_le hclass)
    omega
  have hcls : (conjClass P t).ncard = r.classSize := by
    rw [hcent] at hos
    exact Nat.eq_of_mul_eq_mul_right hpos2 hos
  have hKeq : K = P ⊓ centralizer ({t} : Set _) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hcent]; exact hKcard)
  refine ⟨hT, hord, htP', horb', hKeq, hcent, hcls, ?_⟩
  have hCcov : ∀ y ∈ P ⊓ centralizer ({t} : Set _), ∃ k < C.1.size, Rep n C.1[k]! y := by
    intro y hy
    have hmem := mem_of_nodup_of_card_le hCnodup (K := P ⊓ centralizer ({t} : Set _))
      (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
        exact hKle (hCmem k hk))
      (by rw [List.length_map, Array.length_toList, hCsize, hcent]) y hy
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hmem
    exact ⟨k, hk, hCrep k hk⟩
  have hcgK : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ Rep n cgInv[l]! (tp n cg[l]!)⁻¹ ∧
      tp n cg[l]! ∈ P ⊓ centralizer ({t} : Set _) := by
    intro l hl
    have hc := hcgP _ (getElem!_mem_array hl)
    refine ⟨hc.1, ?_, hc.2⟩
    have hinv := (hcg _ (getElem!_mem_array hl)).2
    rw [getElem!_pos cgInv l (by simpa [cgInv] using hl), Array.getElem_map,
      ← getElem!_pos cg l hl]
    exact rep_invT hc.1 hinv
  rw [List.all_eq_true] at hodd hqtree
  apply aschbacherSolvableCore_eq_bot_of_witnesses (P ⊓ centralizer ({t} : Set _))
    (r.odd.map fun s => tp n s.rep)
  · intro y hy hyp hy3
    obtain ⟨k, hk, hrep⟩ := hCcov y hy
    have hsel : selOK n r.oddPrimes C.1[k]! = true := by
      rw [selOK_iff hn hrep]
      refine ⟨fun h1 => ?_, orderOf y, hprimes _ hyp ?_ hy3, pow_orderOf_eq_one y⟩
      · rw [h1, orderOf_one] at hyp
        exact Nat.not_prime_one hyp
      · rw [← hcent, ← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _
    rw [Array.all_eq_true] at hcov
    have h2 := hcov k hk
    rw [← getElem!_pos C.1 k hk, hsel, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
    obtain ⟨q, hq, hmemq⟩ := h2
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    have hsrep := rep_tp (by
      have := hodd s hs
      simp only [threeRowOK, Bool.and_eq_true] at this
      exact this.1.1.1.1)
    have hqspec := conjTreeOK_spec (P ⊓ centralizer ({t} : Set _)) hcgK hsrep
      (hqtree _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
    have hqrep : ∀ j < (conjClosureH n cg cgInv s.rep cap).1.size,
        Rep n (conjClosureH n cg cgInv s.rep cap).1[j]!
          (tablePerm n (conjClosureH n cg cgInv s.rep cap).1[j]!) := by
      intro j hj
      obtain ⟨c, -, hc⟩ := hqspec j hj
      rw [tablePerm_eq hc]
      exact hc
    obtain ⟨j, hj, hyj⟩ := memT_spec hqrep hrep hmemq
    obtain ⟨c, hcK, hc⟩ := hqspec j hj
    rw [tablePerm_eq hc] at hyj
    exact ⟨tp n s.rep, List.mem_map.mpr ⟨s, hs, rfl⟩, c, hcK, hyj⟩
  · intro x hx N hNK hNn hxN
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have hrow := hodd s hs
    obtain ⟨srep, sprime, ssize, swit⟩ := s
    simp only [threeRowOK, Bool.and_eq_true] at hrow
    obtain ⟨⟨⟨⟨hs1, -⟩, -⟩, -⟩, hwit⟩ := hrow
    have hsrep := rep_tp hs1
    cases swit with
    | conj h ord =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwit
      obtain ⟨⟨⟨⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩, hord3⟩, hordpos⟩, hordt⟩ := hwit
      have hH := rep_tp hh1
      have hHK : tp n h ∈ P ⊓ centralizer ({t} : Set _) := by
        refine mem_inf.mpr ⟨hD.sift _ _ hH hh2, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact (commTT_iff hH hT).1 hh3
      refine ⟨tp n srep * (tp n h * tp n srep * (tp n h)⁻¹),
        N.mul_mem hxN (hNn _ hHK _ hxN), ?_⟩
      have hz := Rep.compT hsrep (rep_conjT hH (rep_invT hH hh4) hsrep)
      rw [(ordTest_iff_perm hz hordpos).1 hordt]
      exact Nat.dvd_of_mod_eq_zero hord3
    | normal gs _ =>
      simp only [Bool.and_eq_true, List.all_eq_true] at hwit
      obtain ⟨⟨⟨hqt, hgs⟩, het⟩, hthree⟩ := hwit
      have hqspec := conjTreeOK_spec (P ⊓ centralizer ({t} : Set _)) hcgK hsrep hqt
      have hqrep : ∀ j < (conjClosureH n cg cgInv srep cap).1.size,
          Rep n (conjClosureH n cg cgInv srep cap).1[j]!
            (tablePerm n (conjClosureH n cg cgInv srep cap).1[j]!) := by
        intro j hj
        obtain ⟨c, -, hc⟩ := hqspec j hj
        rw [tablePerm_eq hc]
        exact hc
      have hgsN : ∀ g ∈ gs, Rep n g (tp n g) ∧ tp n g ∈ N := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := hgs g hg
        have hgr := rep_tp hg1
        obtain ⟨j, hj, hgj⟩ := memT_spec hqrep hgr hg2
        obtain ⟨c, hcK, hc⟩ := hqspec j hj
        rw [tablePerm_eq hc] at hgj
        refine ⟨hgr, ?_⟩
        rw [hgj]
        exact hNn _ hcK _ hxN
      have hga : ∀ l < gs.toArray.size, Rep n gs.toArray[l]! (tp n gs.toArray[l]!) ∧
          tp n gs.toArray[l]! ∈ N := by
        intro l hl
        have hmem : gs.toArray[l]! ∈ gs := by
          have := getElem!_mem_array hl
          simpa using this
        exact hgsN _ hmem
      have heN := mulTreeOK_spec hn N (gg := fun l => tp n gs.toArray[l]!) hga het
      rw [Array.any_eq_true] at hthree
      obtain ⟨k, hk, hk3⟩ := hthree
      obtain ⟨z, hzN, hzrep⟩ := heN k hk
      rw [getElem!_pos _ k hk] at hzrep
      refine ⟨z, hzN, ?_⟩
      rw [(ordTest_iff_perm hzrep (by norm_num)).1 hk3]

theorem threeData_spec (hD : GroupDataSound n P pg gg sift) {NP cap : ℕ} {sylowGens : List Table}
    {sylowOrder : ℕ} {rows : List ClassRow} (hP : Nat.card P = NP)
    (hprimes : ∀ r ∈ rows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 3 → q ∈ r.oddPrimes)
    (hsyl : sylowOrder = 3 ^ NP.factorization 3)
    (h : threeDataOK n NP cap pg pgInv sift sylowGens sylowOrder rows = true) :
    closure (tp n '' {x | x ∈ sylowGens.toArray}) ≤ P ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ sylowGens.toArray})) = sylowOrder ∧
      (∀ r ∈ rows, tp n r.rep ∈ P ∧ orderOf (tp n r.rep) = 3 ∧
        closure (tp n '' {x | x ∈ r.centGens.toArray}) =
          P ⊓ centralizer ({tp n r.rep} : Set _) ∧
        Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder ∧
        (conjClass P (tp n r.rep)).ncard = r.classSize ∧
        aschbacherSolvableCore 3
          ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = ⊥) ∧
      (∀ t ∈ P, orderOf t = 3 → ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹) ∧
      (∀ t ∈ P, orderOf t = 3 →
        aschbacherSolvableCore 3 ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = ⊥) := by
  have hn := hD.lt
  simp only [threeDataOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsy, hcl⟩, hco⟩ := h
  obtain ⟨hpgi, hSP, hScard, hScov⟩ := threeSylowOK_spec hD hsy
  have hcl' : ∀ r ∈ rows,
      threeClassOK n NP cap pg pgInv sift r (conjClosureH n pg pgInv r.rep cap) = true :=
    fun r hr => hcl (r, conjClosureH n pg pgInv r.rep cap) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hrow := fun r (hr : r ∈ rows) => threeClassOK_spec hD hP hpgi (hprimes r hr) (hcl' r hr)
  simp only [threeCoverOK, Array.all_eq_true] at hco
  have hconjOf : ∀ r ∈ rows, ∀ k < (conjClosureH n pg pgInv r.rep cap).1.size,
      ∃ c ∈ P, Rep n (conjClosureH n pg pgInv r.rep cap).1[k]! (c * tp n r.rep * c⁻¹) :=
    fun r hr => (hrow r hr).2.2.2.1
  have hmemOrb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g →
      (∃ p, (∃ r ∈ rows, (r, conjClosureH n pg pgInv r.rep cap) = p) ∧ memT n p.2.1 x = true) →
      ∃ r ∈ rows, ∃ c ∈ P, g = c * tp n r.rep * c⁻¹ := by
    rintro x g hx ⟨_, ⟨r, hr, rfl⟩, hm⟩
    have hqrep : ∀ j < (conjClosureH n pg pgInv r.rep cap).1.size,
        Rep n (conjClosureH n pg pgInv r.rep cap).1[j]!
          (tablePerm n (conjClosureH n pg pgInv r.rep cap).1[j]!) := by
      intro j hj
      obtain ⟨c, -, hc⟩ := hconjOf r hr j hj
      rw [tablePerm_eq hc]
      exact hc
    obtain ⟨j, hj, hgj⟩ := memT_spec hqrep hx hm
    obtain ⟨c, hcP, hc⟩ := hconjOf r hr j hj
    rw [tablePerm_eq hc] at hgj
    exact ⟨r, hr, c, hcP, hgj⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcover : ∀ t ∈ P, orderOf t = 3 → ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹ := by
    intro t ht ht3
    obtain ⟨x, hxP, hxS⟩ := exists_conj_mem_of_card_prime hSP (by rw [hScard, hP, hsyl]) ht ht3
    have hs3 : orderOf (x⁻¹ * t * x) = 3 := by
      rw [show x⁻¹ * t * x = (MulAut.conj x⁻¹) t by simp, MulEquiv.orderOf_eq, ht3]
    obtain ⟨k, hk, hkrep⟩ := hScov _ hxS
    have hk3 : ordTest n 3 (mulClosureH n sylowGens.toArray cap).1[k]! = true :=
      (ordTest_iff_perm hkrep (by norm_num)).2 hs3
    have h1 := hco k hk
    rw [← getElem!_pos _ k hk, hk3, Bool.not_true, Bool.false_or] at h1
    simp only [List.any_eq_true, List.mem_map] at h1
    obtain ⟨r, hr, c, hcP, hc⟩ := hmemOrb _ _ hkrep h1
    refine ⟨r, hr, x * c, P.mul_mem hxP hcP, ?_⟩
    calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
      _ = _ := by rw [hc]; group
  refine ⟨hSP, hScard, fun r hr => ?_, hcover, ?_⟩
  · obtain ⟨-, hord, hR, -, hK, hcent, hcls, hθ⟩ := hrow r hr
    exact ⟨hR, hord, hK, hcent, hcls, hθ⟩
  · intro t ht ht3
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht3
    exact aschbacherSolvableCore_inf_centralizer_conj P hg (hrow r hr).2.2.2.2.2.2.2

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore
