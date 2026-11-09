module

public import Certificates.Data.Kernel.SporSch.HeSrch
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
import CFSG.Certificates.Kernel.SporSch.HeSrchLemmas

public section

namespace CFSG.KS.SporSch.Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier
  CFSG.KS.SporSch

variable {n : Nat} {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat} {Q : RawSchreierDatum n} {O : Array (Array Nat)}
  {W : Array (List Int)} {chunks : Nat}

theorem srchPC_card {b0 b1 b2 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {Y : Nat → Nat} {y : Equiv.Perm (Fin n)} (hY : RepF n Y y) (hb0 : b0 < n) (hb1 : b1 < n)
    (hb2 : b2 < n) {a : Nat} (ha : a < rcnt (LR 0)) :
    srchPC w kS NR NL LT PT QT LR Y a * (rcnt (LR 3) * rcnt (LR 4)) =
      Nat.card {g : Q.originalSubgroup // (((g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ : Fin n) : Nat) =
        trPtT w NR NL LT PT (nat_lit 0) a b0 ∧
          (g : Equiv.Perm (Fin n)) ⟨b2, hb2⟩ = y ((g : Equiv.Perm (Fin n)) ⟨b1, hb1⟩)} := by
  obtain ⟨hb, hp, ho, hN, htab, hbs⟩ := id hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h5 : Q.baseCount = 5 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm : ∀ i < 5, (lev n S base i).pts.size = rcnt (LR i) := fun i hi =>
    (cnt_eq hb hp ho hN hi).symm
  have ha0 : a < (lev n S base 0).pts.size := (hm 0 (by norm_num)) ▸ ha
  have hβ0 : Q.base.get ⟨0, by omega⟩ = ⟨b0, hb0⟩ := Fin.ext ((hA.base_val ⟨0, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hβ1 : Q.base.get ⟨1, by omega⟩ = ⟨b1, hb1⟩ := Fin.ext ((hA.base_val ⟨1, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hβ2 : Q.base.get ⟨2, by omega⟩ = ⟨b2, hb2⟩ := Fin.ext ((hA.base_val ⟨2, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hP : trPtT w NR NL LT PT (nat_lit 0) a b0 = (levPts Q S base 0 a : Nat) := by
    rw [trPtT_eq hb hp ho hN htab (by norm_num) ha ⟨b0, hb0⟩,
      ← trT_eq_levT hb hp ho hN (by norm_num) ha, ← hβ0, (levT_spec hA hF (by omega) ha0).2]
  have hk' : ∀ {k : Nat × Nat × Nat × Nat × Nat}, k ∈ box5 n S base →
      k.1 < (lev n S base 0).pts.size ∧ k.2.1 < (lev n S base 1).pts.size ∧
        k.2.2.1 < (lev n S base 2).pts.size ∧ k.2.2.2.1 < (lev n S base 3).pts.size ∧
          k.2.2.2.2 < (lev n S base 4).pts.size := fun hk => by
    simpa only [box5, Finset.mem_product, Finset.mem_range] using hk
  have f0 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
    intro k hk
    have hk := hk' hk
    rw [← hβ0]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      levT_fix hA hF (i := 1) (by omega) (by omega) hk.2.1,
      (levT_spec hA hF (by omega) hk.1).2]
  have f1 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b1, hb1⟩ =
      levT n S base 0 k.1 (levPts Q S base 1 k.2.1) := by
    intro k hk
    have hk := hk' hk
    rw [← hβ1]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      (levT_spec hA hF (by omega) hk.2.1).2]
  have f2 : ∀ k ∈ box5 n S base, E5 n S base k ⟨b2, hb2⟩ =
      levT n S base 0 k.1 (levT n S base 1 k.2.1 (levPts Q S base 2 k.2.2.1)) := by
    intro k hk
    have hk := hk' hk
    rw [← hβ2]
    unfold E5
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 4) (by omega) (by omega) hk.2.2.2.2,
      levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2.1,
      (levT_spec hA hF (by omega) hk.2.2.1).2]
  have hT0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trPtT w NR NL LT PT (nat_lit 0) a z = (levT n S base 0 a ⟨z, hz⟩ : Nat) := fun ha z hz => by
    rw [trPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
      ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hI0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trInvPtT w kS NR NL LT PT (nat_lit 0) a z = ((levT n S base 0 a)⁻¹ ⟨z, hz⟩ : Nat) :=
    fun ha z hz => by
      rw [trInvPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
        ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hI1 : ∀ {b : Nat}, b < rcnt (LR (nat_lit 1)) → ∀ z (hz : z < n),
      trInvPtT w kS NR NL LT PT (nat_lit 1) b z = ((levT n S base 1 b)⁻¹ ⟨z, hz⟩ : Nat) :=
    fun hb' z hz => by
      rw [trInvPtT_eq hb hp ho hN htab (by norm_num) hb' ⟨z, hz⟩,
        ← trT_eq_levT hb hp ho hN (by norm_num) hb']
  have hpt : ∀ {i k : Nat}, i < 5 → k < (lev n S base i).pts.size →
      rpt w (mask w) (LR i) k = (levPts Q S base i k : Nat) := by
    intro i k hi hk
    rw [(agree hb hp ho hN hi).2.pt k hk, hA.levPts_val hF (by omega) hk]
  have R2 := recFacts ho hN (i := 2) (by norm_num)
  have ha' : a < rcnt (LR (nat_lit 0)) := ha
  have e1 : rcnt (LR (nat_lit 1)) = (lev n S base 1).pts.size := (hm 1 (by norm_num)).symm
  have e2 : rcnt (LR (nat_lit 2)) = (lev n S base 2).pts.size := (hm 2 (by norm_num)).symm
  have e3 : rcnt (LR 3) = (lev n S base 3).pts.size := (hm 3 (by norm_num)).symm
  have e4 : rcnt (LR 4) = (lev n S base 4).pts.size := (hm 4 (by norm_num)).symm
  rw [card5 hA hF hQ h5 (fun g => ((g ⟨b0, hb0⟩ : Fin n) : Nat) = trPtT w NR NL LT PT (nat_lit 0) a b0 ∧
    g ⟨b2, hb2⟩ = y (g ⟨b1, hb1⟩))]
  unfold box5
  simp only [Finset.sum_product]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_range.2 ha0) (fun a' ha'' hne =>
    Finset.sum_eq_zero fun b hb' => Finset.sum_eq_zero fun c hc' => Finset.sum_eq_zero fun d hd =>
      Finset.sum_eq_zero fun e he => ite_eq_right_iff.2 fun h => absurd ?_ hne)]
  ·
    let V : Nat → Fin n := fun b => (levT n S base 1 b)⁻¹ ((levT n S base 0 a)⁻¹
      (y (levT n S base 0 a (levPts Q S base 1 b))))
    have hstep : ∀ b < (lev n S base 1).pts.size, ∀ s,
        strictN (trPtT w NR NL LT PT (nat_lit 0) a (rpt w (mask w) (LR (nat_lit 1)) b)) (fun q =>
        strictN (trInvPtT w kS NR NL LT PT (nat_lit 1) b
          (trInvPtT w kS NR NL LT PT (nat_lit 0) a (Y q))) (fun v =>
        strictN (lvT NL w QT (nat_lit 2) v) (fun k2 =>
        nIf(Nat.blt k2 (rcnt (LR (nat_lit 2))), Nat.succ s, s)))) =
          s + if rpos w (mask w) (n * w) (LR 2) (V b : Nat) < (lev n S base 2).pts.size
            then 1 else 0 := by
      intro b hb' s
      have hb'' : b < rcnt (LR (nat_lit 1)) := e1 ▸ hb'
      rw [strictN_eq, hpt (by norm_num) hb', hT0 ha' _ (levPts Q S base 1 b).2, strictN_eq,
        hY _ (levT n S base 0 a _).2, hI0 ha' _ (y _).2, hI1 hb'' _ ((levT n S base 0 a)⁻¹ _).2,
        strictN_eq, lvT_QT htab (by norm_num) ((levT n S base 1 b)⁻¹ _).2, e2, nIf_succ]
      simp only [Fin.eta]
      exact congrArg (s + ·) (if_congr Nat.blt_eq.to_iff rfl rfl)
    unfold srchPC
    rw [e1, foldUp_add _ hstep 0, Nat.zero_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb' => ?_
    rw [Finset.mem_range] at hb'
    have hiff : ∀ c < (lev n S base 2).pts.size, ∀ d < (lev n S base 3).pts.size,
        ∀ e < (lev n S base 4).pts.size,
        ((((E5 n S base (a, b, c, d, e)) ⟨b0, hb0⟩ : Fin n) : Nat) =
          trPtT w NR NL LT PT (nat_lit 0) a b0 ∧
          E5 n S base (a, b, c, d, e) ⟨b2, hb2⟩ = y (E5 n S base (a, b, c, d, e) ⟨b1, hb1⟩)) ↔
          c = rpos w (mask w) (n * w) (LR 2) (V b : Nat) := by
      intro c hc d hd e he
      have hk : (a, b, c, d, e) ∈ box5 n S base := by
        simp only [box5, Finset.mem_product, Finset.mem_range]
        exact ⟨ha0, hb', hc, hd, he⟩
      rw [f0 _ hk, hP, f2 _ hk, f1 _ hk]
      simp only [true_and]
      have hc2 : c < rcnt (LR 2) := (hm 2 (by norm_num)) ▸ hc
      constructor
      · intro h
        have hv : levPts Q S base 2 c = V b := by
          simp only [V]
          rw [Equiv.Perm.eq_inv_iff_eq, Equiv.Perm.eq_inv_iff_eq]
          exact h
        rw [← hv, ← hpt (by norm_num) hc]
        exact (R2.pt c hc2).2.symm
      · intro h
        have hlt : rpos w (mask w) (n * w) (LR 2) (V b : Nat) < rcnt (LR 2) := by
          rw [← h]
          exact hc2
        have hv : levPts Q S base 2 c = V b := by
          refine Fin.ext ?_
          rw [← hpt (by norm_num) hc, h]
          exact R2.pos _ (V b).2 hlt
        simp only [V] at hv
        rw [Equiv.Perm.eq_inv_iff_eq, Equiv.Perm.eq_inv_iff_eq] at hv
        exact hv
    rw [e3, e4]
    have hsum : ∑ c ∈ Finset.range (lev n S base 2).pts.size,
        ∑ d ∈ Finset.range (lev n S base 3).pts.size, ∑ e ∈ Finset.range (lev n S base 4).pts.size,
          (if (((E5 n S base (a, b, c, d, e)) ⟨b0, hb0⟩ : Fin n) : Nat) =
            trPtT w NR NL LT PT (nat_lit 0) a b0 ∧
            E5 n S base (a, b, c, d, e) ⟨b2, hb2⟩ = y (E5 n S base (a, b, c, d, e) ⟨b1, hb1⟩)
            then 1 else 0) =
        ∑ c ∈ Finset.range (lev n S base 2).pts.size,
          ∑ d ∈ Finset.range (lev n S base 3).pts.size, ∑ e ∈ Finset.range (lev n S base 4).pts.size,
            (if c = rpos w (mask w) (n * w) (LR 2) (V b : Nat) then 1 else 0) :=
      Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd =>
        Finset.sum_congr rfl fun e he => by
          rw [Finset.mem_range] at hc hd he
          exact if_congr (hiff c hc d hd e he) rfl rfl
    rw [hsum]
    by_cases hK : rpos w (mask w) (n * w) (LR 2) (V b : Nat) < (lev n S base 2).pts.size
    · simp only [hK, ↓reduceIte]
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.2 hK) (fun c _ hne => by simp [hne])]
      simp
    · simp only [hK, ↓reduceIte, Nat.zero_mul]
      symm
      refine Finset.sum_eq_zero fun c hc => ?_
      have hne : c ≠ rpos w (mask w) (n * w) (LR 2) (V b : Nat) := fun h =>
        hK (h ▸ Finset.mem_range.1 hc)
      simp [hne]
  · have hk : (a', b, c, d, e) ∈ box5 n S base := by
      simp only [box5, Finset.mem_product]
      exact ⟨ha'', hb', hc', hd, he⟩
    have h1' := h.1
    rw [f0 _ hk, hP] at h1'
    exact levPts_inj hA hF (by omega) (Finset.mem_range.1 ha'') ha0 (Fin.ext h1')

theorem srchAAt_zero_of_pc {b0 b1 b2 : Nat} {bs : List Nat} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) (hb0 : b0 < n) (hb1 : b1 < n) (hb2 : b2 < n) {a : Nat}
    (ha : a < rcnt (LR 0)) (hz : 0 < rcnt (LR 0))
    (hr : trPtT w NR NL LT PT (nat_lit 0) 0 b0 = b0)
    (hne : srchPC w kS NR NL LT PT QT LR Y a ≠ srchPC w kS NR NL LT PT QT LR X 0) :
    srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y a = 0 := by
  obtain ⟨-, -, ho, hN, -, -⟩ := id hT
  rw [srchAAt_card hA hc hch hT hX hY hxy h0 h1 hb0 ha]
  by_contra hne0
  obtain ⟨⟨g0, hg0p, hg0c⟩⟩ := (Nat.card_ne_zero.1 hne0).1
  apply hne
  have hM : 0 < rcnt (LR 3) * rcnt (LR 4) :=
    Nat.mul_pos (recFacts ho hN (i := 3) (by norm_num)).c_pos
      (recFacts ho hN (i := 4) (by norm_num)).c_pos
  refine Nat.eq_of_mul_eq_mul_right hM ?_
  rw [srchPC_card hA hc hch hT hY hb0 hb1 hb2 ha, srchPC_card hA hc hch hT hX hb0 hb1 hb2 hz]
  have hc' : ∀ z, (g0 : Equiv.Perm (Fin n)) (x z) = y ((g0 : Equiv.Perm (Fin n)) z) := fun z => by
    have := congrArg (fun g : Equiv.Perm (Fin n) => g z) hg0c
    simpa only [Equiv.Perm.mul_apply] using this
  refine Nat.card_congr
    { toFun := fun g => ⟨g0⁻¹ * g.1, ?_⟩
      invFun := fun g => ⟨g0 * g.1, ?_⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · obtain ⟨g, hgp, hgc⟩ := g
    have hg0 : (g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ = (g0 : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ :=
      Fin.ext (hgp.trans hg0p.symm)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    refine ⟨?_, ?_⟩
    · rw [hg0, hr]
      simp
    · rw [hgc, Equiv.Perm.inv_eq_iff_eq, hc']
      simp
  · obtain ⟨g, hgp, hgc⟩ := g
    rw [hr] at hgp
    have hg0 : (g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ = ⟨b0, hb0⟩ := Fin.ext hgp
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
    refine ⟨?_, ?_⟩
    · rw [hg0]
      exact hg0p
    · rw [hgc, hc']

end CFSG.KS.SporSch.Tab

end
