module

public import Certificates.Data.Kernel.SporSch.ClsZK
public import CFSG.Certificates.Kernel.SporSch.CntZOrbProof

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.SmallOddCore CFSG.KS.SporSch.ClsSpec CFSG.KS.M11 CFSG.KS.MEnum

variable {n w : Nat}

theorem clsSrtK_facts {d : ClsD} {k : Nat} (hk : k < d.c) (h : clsSrtK (n * w) d k = true) :
    (k + 1 < d.c → d.ST k < d.ST (k + 1)) ∧ d.ST k >>> (n * w) = 0 := by
  unfold clsSrtK at h
  simp only [bAnd_eq, Orb.strictB_eq] at h
  simp only [Orb.bIf_eq, Nat.blt_eq, hk, ↓reduceIte, Bool.and_eq_true, beq_dec,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hk1 => by simpa [hk1] using h1, by simpa using h2⟩

theorem prep_of_zrel {Z P K : Nat} {z y : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (pZ : PRep n w Z z) (pP : PRep n w P y)
    (h : pcomp n w (mask w) Z P = pcomp n w (mask w) K Z) : PRep n w K (z * y * z⁻¹) := by
  intro x
  have e := congrArg (fun X => pg w (mask w) X (z⁻¹ x)) h
  beta_reduce at e
  rw [PF.pg_pcomp hn (z⁻¹ x).2, PF.pg_pcomp hn (z⁻¹ x).2, pP, pZ, pZ] at e
  have hx : z (z⁻¹ x) = x := by simp
  rw [hx] at e
  rw [← e]
  simp [Equiv.Perm.mul_apply]

section Tree

variable {gA gB z : Equiv.Perm (Fin n)} {A Ai B Bi Z Zi : Nat} (hn : n < 2 ^ 32)
  (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB) (pBi : PRep n w Bi gB⁻¹)
  (hzK : z ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) (pZ : PRep n w Z z)
  (pZi : PRep n w Zi z⁻¹)
  {mx cap nr q : Nat} {RP OT : Nat → Nat} {d : ClsD} (hd : clsHdK n w (mask w) mx cap d = true)
  (hO : ∀ k < d.c, zOrbK n w (mask w) nr q Z RP OT d k = true)
  {r : Equiv.Perm (Fin n)} (pR : PRep n w d.R r)

include hn hzK pZ hO in
theorem orb_mem_class (k : Nat) (hk : k < d.c)
    (hrep : ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST (RP (oF OT 1 k))) x) :
    ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST k) x := by
  suffices H : ∀ e, ∀ k < d.c, oF OT 2 k = e → oF OT 1 k = oF OT 1 k →
      (∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST (RP (oF OT 1 k))) x) →
      ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST k) x from H _ k hk rfl rfl hrep
  intro e
  induction e with
  | zero =>
    intro k hk he _ hr
    rw [(zOrbK_spec hk (hO k hk)).2.2.1 he] at hr
    exact hr
  | succ e ih =>
    intro k hk he _ hr
    obtain ⟨hp, hpj, hpe, hpc⟩ := (zOrbK_spec hk (hO k hk)).2.2.2 (by omega)
    obtain ⟨y, hy, py⟩ := ih _ hp (by omega) rfl (by rw [hpj]; exact hr)
    exact ⟨z * y * z⁻¹, conj_mem_conjClass hzK hy, prep_of_zrel hn pZ py hpc⟩

include hn hzK pZ hd hO pR in
theorem walk_mem_class : ∀ t, ∀ k < d.c,
    fpow (fun k => pg 16 65535 (OT k) 0) t k = d.r → t ≤ oF OT 2 k →
      ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST k) x := by
  obtain ⟨-, -, -, hST, -⟩ := clsHdK_facts hd
  intro t
  induction t with
  | zero =>
    intro k hk hw _
    rw [fpow_iterZ] at hw
    simp only [Function.iterate_zero, id_eq] at hw
    subst hw
    exact ⟨r, ⟨1, Subgroup.one_mem _, by simp⟩, by rw [hST]; exact pR⟩
  | succ t ih =>
    intro k hk hw ht
    obtain ⟨hp, -, hpe, hpc⟩ := (zOrbK_spec hk (hO k hk)).2.2.2 (by omega)
    have hw' : fpow (fun k => pg 16 65535 (OT k) 0) t (oF OT 0 k) = d.r := by
      rw [fpow_iterZ, Function.iterate_succ_apply] at hw
      rw [fpow_iterZ]
      exact hw
    obtain ⟨y, hy, py⟩ := ih _ hp hw' (by omega)
    exact ⟨z * y * z⁻¹, conj_mem_conjClass hzK hy, prep_of_zrel hn pZ py hpc⟩

include hn hzK pZ pZi in
theorem iterZ_mem_class (b : Bool) : ∀ t (X : Nat) {x : Equiv.Perm (Fin n)}, PRep n w X x →
    x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r →
    ∃ y ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r,
      PRep n w (fpow (fun Y => nIf(b, conjK n w (mask w) Z Zi Y, conjK n w (mask w) Zi Z Y)) t X)
        y := by
  have hziK : z⁻¹ ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.inv_mem _ hzK
  have pZ' : PRep n w Z z⁻¹⁻¹ := by
    rw [inv_inv]
    exact pZ
  intro t
  induction t with
  | zero =>
    intro X x px hx
    rw [fpow_iterZ]
    exact ⟨x, hx, px⟩
  | succ t ih =>
    intro X x px hx
    rw [fpow_iterZ, Function.iterate_succ_apply, ← fpow_iterZ]
    cases b
    · exact ih _ (prep_conjK hn pZi pZ' px) (conj_mem_conjClass hziK hx)
    · exact ih _ (prep_conjK hn pZ pZi px) (conj_mem_conjClass hzK hx)

include hn pA pAi pB pBi hzK pZ pZi hd hO pR in
theorem rep_mem_class (hT : ∀ j < nr, zRepTreeK n w (mask w) A Ai B Bi Z Zi RP OT d j = true) :
    ∀ j < nr, ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST (RP j)) x := by
  have hAK : gA ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.subset_closure (by simp)
  have hBK : gB ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨-, -, -, hST, -⟩ := clsHdK_facts hd
  suffices H : ∀ m, ∀ j < nr, d.DP j = m → ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST (RP j)) x from
    fun j hj => H _ j hj rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hj hm
    have h := hT j hj
    unfold zRepTreeK at h
    simp only [bAnd_eq, Orb.strictB_eq, Bool.and_eq_true] at h
    obtain ⟨hp0, hdp, hc⟩ := h
    have hp : d.PA j < d.c := Nat.le_of_ble_eq_true hp0
    obtain ⟨y, hy, py⟩ : ∃ y ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r,
        PRep n w (d.ST (d.PA j)) y := by
      cases h2 : Nat.beq (d.LB j) 2
      · rw [h2] at hdp
        have hlt : d.DP (oF OT 1 (d.PA j)) < m := by
          rw [← hm]
          exact Nat.le_of_ble_eq_true hdp
        exact orb_mem_class hn hzK pZ hO _ hp (ih _ hlt _ (zOrbK_spec hp (hO _ hp)).1 rfl)
      · rw [h2] at hdp
        rw [Nat.eq_of_beq_eq_true hdp, hST]
        exact ⟨r, ⟨1, Subgroup.one_mem _, by simp⟩, pR⟩
    have hs : ∃ x0 ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r,
        PRep n w (nIf(Nat.beq (d.LB j) (nat_lit 0), conjK n w (mask w) A Ai (d.ST (d.PA j)),
          nIf(Nat.beq (d.LB j) (nat_lit 1), conjK n w (mask w) B Bi (d.ST (d.PA j)),
            d.ST (d.PA j)))) x0 := by
      cases h0 : Nat.beq (d.LB j) 0
      · cases h1 : Nat.beq (d.LB j) 1
        · exact ⟨y, hy, py⟩
        · exact ⟨gB * y * gB⁻¹, conj_mem_conjClass hBK hy, prep_conjK hn pB pBi py⟩
      · exact ⟨gA * y * gA⁻¹, conj_mem_conjClass hAK hy, prep_conjK hn pA pAi py⟩
    obtain ⟨x0, hx0, px0⟩ := hs
    obtain ⟨y', hy', py'⟩ := iterZ_mem_class hn hzK pZ pZi (Nat.beq (d.IB j) 0) (d.IA j) _ px0 hx0
    rw [Nat.eq_of_beq_eq_true hc] at py'
    exact ⟨y', hy', py'⟩

include hn pA pAi pB pBi hzK pZ pZi hd hO pR in
theorem entryZ_mem_class (hT : ∀ j < nr, zRepTreeK n w (mask w) A Ai B Bi Z Zi RP OT d j = true) :
    ∀ k < d.c, ∃ x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST k) x := fun k hk =>
  orb_mem_class hn hzK pZ hO k hk
    (rep_mem_class hn pA pAi pB pBi hzK pZ pZi hd hO pR hT _ (zOrbK_spec hk (hO k hk)).1)

include hn pA pAi pB pBi hzK pZ pZi hd hO pR in
theorem memZ_class_iff (hw : 0 < w) (hs : ∀ k < d.c, clsSrtK (n * w) d k = true)
    (hT : ∀ j < nr, zRepTreeK n w (mask w) A Ai B Bi Z Zi RP OT d j = true)
    (hcard : (conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard ≤ d.c) (x : Equiv.Perm (Fin n)) :
    x ∈ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔ ∃ k < d.c, PRep n w (d.ST k) x := by
  have hE := entryZ_mem_class hn pA pAi pB pBi hzK pZ pZi hd hO pR hT
  set S : Set (Equiv.Perm (Fin n)) := {x | ∃ k < d.c, PRep n w (d.ST k) x} with hSdef
  have hsub : S ⊆ conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r := by
    rintro x ⟨k, hk, pk⟩
    obtain ⟨y, hy, py⟩ := hE k hk
    rw [MOC.prep_unique pk py]
    exact hy
  have hinc := MOC.lt_of_consec (c := d.c) (ST := d.ST) fun k hk =>
    (clsSrtK_facts (by omega) (hs k (by omega))).1 hk
  have hS : S.ncard = d.c := by
    refine Set.ncard_eq_of_bijective (fun k hk => Classical.choose (hE k hk))
      (fun x hx => ?_) (fun k hk => ⟨k, hk, (Classical.choose_spec (hE k hk)).2⟩)
      (fun i j hi hj e => ?_)
    · obtain ⟨k, hk, pk⟩ := hx
      exact ⟨k, hk, MOC.prep_unique (Classical.choose_spec (hE k hk)).2 pk⟩
    · have p1 := (Classical.choose_spec (hE i hi)).2
      have p2 := (Classical.choose_spec (hE j hj)).2
      rw [e] at p1
      have eq : d.ST i = d.ST j := PF.eq_of_fields hw (clsSrtK_facts hi (hs i hi)).2
        (clsSrtK_facts hj (hs j hj)).2 fun t ht => by rw [p1 ⟨t, ht⟩, p2 ⟨t, ht⟩]
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact absurd eq (Nat.ne_of_lt (hinc i j h hj))
      · exact h
      · exact absurd eq (Nat.ne_of_gt (hinc j i h hi))
  have heq : S = conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r :=
    Set.eq_of_subset_of_ncard_le hsub (hS ▸ hcard) (Set.toFinite _)
  rw [← heq]
  exact Iff.rfl

end Tree

end CFSG.KS.SporSch.MBT

end
