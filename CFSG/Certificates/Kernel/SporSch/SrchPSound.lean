module

public import CFSG.Certificates.Kernel.SporSch.HeSrchLemmas
public import Certificates.Data.Kernel.SporSch.SrchP
import CFSG.Certificates.Kernel.SporSch.Srch4Proof

public section

namespace CFSG.KS.SporSch.Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier
  CFSG.KS.SporSch

variable {n : Nat}

theorem srchP_sound {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {b0 b1 : Nat} {bs : List Nat}
    {Q : RawSchreierDatum n} {O : Array (Array Nat)} {W : Array (List Int)} {chunks : Nat}
    (hA : ChainArrays Q O S base W) (hc : rawChainOK n O S base W chunks = true) (hch : 0 < chunks)
    (hT : TabChain n w kS 4 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hx : x ∈ Q.originalSubgroup) (hy : y ∈ Q.originalSubgroup) (h01 : X b0 = b1)
    {Fl : (Nat → Nat) → Bool} {Pr : Equiv.Perm (Fin n) → Prop}
    (hFl : ∀ g ∈ Q.originalSubgroup, ∀ f : Nat → Nat, RepF n f g → (Fl f = true ↔ Pr g)) :
    sumN (rcnt (LR 0)) (srchPAt w kS NR NL LT PT QT LR (b0 :: b1 :: bs) b0 X Y Fl) =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) * x = y * g ∧ Pr g} := by
  classical
  obtain ⟨hb, hp, ho, hN, htab, hbs⟩ := hT
  have hF := chainCheckFacts hc
  have hQ := (validSchreier_of_chainOK hA hch hc).1
  have h4 : Q.baseCount = 4 := by rw [← hA.base_size]; exact hb.2.2.2.2.2.1
  have hm : ∀ i < 4, (lev n S base i).pts.size = rcnt (LR i) := fun i hi =>
    (cnt_eq hb hp ho hN hi).symm
  have hbl := base_lt hb ho hN
  have hb0 : b0 < n := by
    have := hbl 0 (by norm_num)
    rwa [getD_base hbs (i := 0) (by simp)] at this
  have hb1 : b1 < n := by
    have := hbl 1 (by norm_num)
    rwa [getD_base hbs (i := 1) (by simp)] at this
  have hβ0 : Q.base.get ⟨0, by omega⟩ = ⟨b0, hb0⟩ := Fin.ext ((hA.base_val ⟨0, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hβ1 : Q.base.get ⟨1, by omega⟩ = ⟨b1, hb1⟩ := Fin.ext ((hA.base_val ⟨1, by omega⟩).trans
    (getD_base hbs (by simp)))
  have hfaith : BaseFaithful Q.originalSubgroup (b0 :: b1 :: bs) := by
    have := baseFaithful_of_valid hQ
    rwa [base_map_val hA hF, hbs] at this
  have hlt : ∀ b ∈ b0 :: b1 :: bs, b < n := fun b hb' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb'
    rw [← getD_base hbs hi]
    have : i < 4 := by rw [← hb.2.2.2.2.2.1, ← Array.length_toList, hbs]; exact hi
    exact hbl i this
  have hx0 : x ⟨b0, hb0⟩ = ⟨b1, hb1⟩ := Fin.ext ((hX b0 hb0).symm.trans h01)
  have hk' : ∀ {k : Nat × Nat × Nat × Nat}, k ∈ box4 n S base →
      k.1 < (lev n S base 0).pts.size ∧ k.2.1 < (lev n S base 1).pts.size ∧
        k.2.2.1 < (lev n S base 2).pts.size ∧ k.2.2.2 < (lev n S base 3).pts.size := fun hk => by
    simpa only [box4, Finset.mem_product, Finset.mem_range] using hk
  have f0 : ∀ k ∈ box4 n S base, E4 n S base k ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
    intro k hk
    have hk := hk' hk
    rw [← hβ0]
    unfold E4
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      levT_fix hA hF (i := 1) (by omega) (by omega) hk.2.1,
      (levT_spec hA hF (by omega) hk.1).2]
  have f1 : ∀ k ∈ box4 n S base, E4 n S base k ⟨b1, hb1⟩ =
      levT n S base 0 k.1 (levPts Q S base 1 k.2.1) := by
    intro k hk
    have hk := hk' hk
    rw [← hβ1]
    unfold E4
    simp only [Equiv.Perm.mul_apply]
    rw [levT_fix hA hF (i := 3) (by omega) (by omega) hk.2.2.2,
      levT_fix hA hF (i := 2) (by omega) (by omega) hk.2.2.1,
      (levT_spec hA hF (by omega) hk.2.1).2]
  have h65 : ∀ i < 4, (lev n S base i).pts.size < 65536 := fun i hi => (hm i hi) ▸ rcnt_lt _
  have eqv : ∀ k ∈ box4 n S base,
      (bAnd(eqOnL (b0 :: b1 :: bs)
        (fun b => nfPtT w NR NL LT PT 4 (nf4 k.1 k.2.1 k.2.2.1 k.2.2.2) (X b))
        (fun b => Y (nfPtT w NR NL LT PT 4 (nf4 k.1 k.2.1 k.2.2.1 k.2.2.2) b)),
        Fl (fun b => nfPtT w NR NL LT PT 4 (nf4 k.1 k.2.1 k.2.2.1 k.2.2.2) b)) = true ↔
        E4 n S base k * x = y * E4 n S base k ∧ Pr (E4 n S base k)) := by
    intro k hk
    have hk := hk' hk
    have hv := nfValid_nf4 (LR := LR) (hm 0 (by norm_num) ▸ hk.1) (hm 1 (by norm_num) ▸ hk.2.1)
      (hm 2 (by norm_num) ▸ hk.2.2.1) (hm 3 (by norm_num) ▸ hk.2.2.2)
    have hR := (nfPtT_spec hb hp ho hN htab hv).2
    have e : nfA 4 (nf4 k.1 k.2.1 k.2.2.1 k.2.2.2) = #[k.1, k.2.1, k.2.2.1, k.2.2.2] :=
      nfArr_nf4 (lt_trans hk.1 (h65 0 (by norm_num))) (lt_trans hk.2.1 (h65 1 (by norm_num)))
        (lt_trans hk.2.2.1 (h65 2 (by norm_num))) (lt_trans hk.2.2.2 (h65 3 (by norm_num)))
    rw [e, nfElt4] at hR
    have hmem := E4_mem hA hF hQ h4 (k := k) (by simpa only [box4, Finset.mem_product,
      Finset.mem_range] using hk)
    rw [Orb.bAnd_eq, Bool.and_eq_true, hFl _ hmem _ hR]
    refine and_congr_left' ?_
    rw [eqOnL_iff]
    have hxy : (E4 n S base k * x)⁻¹ * (y * E4 n S base k) ∈ Q.originalSubgroup :=
      Q.originalSubgroup.mul_mem (Q.originalSubgroup.inv_mem (Q.originalSubgroup.mul_mem hmem hx))
        (Q.originalSubgroup.mul_mem hy hmem)
    constructor
    · intro hall
      have h1 := hfaith _ hxy fun z hz => by
        have := hall z hz
        rw [hX z z.2, hR _ (hX z z.2 ▸ (x z).2), hR z z.2, hY _ (E4 n S base k z).2] at this
        rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply]
        exact (Fin.ext this).symm
      exact (inv_mul_eq_one.1 h1)
    · intro he b hb'
      have hbn := hlt b hb'
      rw [hX b hbn, hR _ (x ⟨b, hbn⟩).2, hR b hbn, hY _ (E4 n S base k ⟨b, hbn⟩).2]
      have := congrArg (fun g => ((g ⟨b, hbn⟩ : Fin n) : Nat)) he
      simpa only [Equiv.Perm.mul_apply] using this
  have hT0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trPtT w NR NL LT PT (nat_lit 0) a z = (levT n S base 0 a ⟨z, hz⟩ : Nat) := fun ha z hz => by
    rw [trPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
      ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hI0 : ∀ {a : Nat}, a < rcnt (LR (nat_lit 0)) → ∀ z (hz : z < n),
      trInvPtT w kS NR NL LT PT (nat_lit 0) a z = ((levT n S base 0 a)⁻¹ ⟨z, hz⟩ : Nat) :=
    fun ha z hz => by
      rw [trInvPtT_eq hb hp ho hN htab (by norm_num) ha ⟨z, hz⟩,
        ← trT_eq_levT hb hp ho hN (by norm_num) ha]
  have hpt : ∀ {i k : Nat}, i < 4 → k < (lev n S base i).pts.size →
      rpt w (mask w) (LR i) k = (levPts Q S base i k : Nat) := by
    intro i k hi hk
    rw [(agree hb hp ho hN hi).2.pt k hk, hA.levPts_val hF (by omega) hk]
  have forced : ∀ k ∈ box4 n S base, E4 n S base k * x = y * E4 n S base k →
      rpos w (mask w) (n * w) (LR 1) ((levT n S base 0 k.1)⁻¹
        (y (levT n S base 0 k.1 ⟨b0, hb0⟩)) : Nat) = k.2.1 := by
    intro k hk he
    have hk2 := hk' hk
    have hP0 : levT n S base 0 k.1 ⟨b0, hb0⟩ = levPts Q S base 0 k.1 := by
      rw [← hβ0]
      exact (levT_spec hA hF (by omega) hk2.1).2
    have e0 := congrArg (fun g => g ⟨b0, hb0⟩) he
    simp only [Equiv.Perm.mul_apply] at e0
    rw [hx0, f1 _ hk, f0 _ hk] at e0
    rw [hP0, ← e0, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply,
      ← hpt (by norm_num) hk2.2.1]
    exact ((recFacts ho hN (i := 1) (by norm_num)).pt _ (hm 1 (by norm_num) ▸ hk2.2.1)).2
  rw [card4 hA hF hQ h4 (fun g => g * x = y * g ∧ Pr g), sumN_eq, lsum, ← hm 0 (by norm_num)]
  unfold box4
  simp only [Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  have ha' : a < rcnt (LR (nat_lit 0)) := hm 0 (by norm_num) ▸ ha
  have mem : ∀ {b c d : Nat}, b < (lev n S base 1).pts.size → c < (lev n S base 2).pts.size →
      d < (lev n S base 3).pts.size → (a, b, c, d) ∈ box4 n S base := fun hb' hc' hd' => by
    simp only [box4, Finset.mem_product, Finset.mem_range]
    exact ⟨ha, hb', hc', hd'⟩
  have e1 : rcnt (LR (nat_lit 1)) = (lev n S base 1).pts.size := (hm 1 (by norm_num)).symm
  have e2 : rcnt (LR (nat_lit 2)) = (lev n S base 2).pts.size := (hm 2 (by norm_num)).symm
  have e3 : rcnt (LR (nat_lit 3)) = (lev n S base 3).pts.size := (hm 3 (by norm_num)).symm
  unfold srchPAt
  rw [strictN_eq, hT0 ha' b0 hb0, hY _ (levT n S base 0 a ⟨b0, hb0⟩).2, hI0 ha' _ (y _).2,
    strictN_eq, lvT_QT htab (by norm_num) ((levT n S base 0 a)⁻¹ _).2]
  simp only [Fin.eta]
  set K1 := rpos w (mask w) (n * w) (LR 1) ((levT n S base 0 a)⁻¹
    (y (levT n S base 0 a ⟨b0, hb0⟩)) : Nat) with hK1
  by_cases hK : K1 < (lev n S base 1).pts.size
  · rw [blt_true (e1 ▸ hK)]
    dsimp only
    rw [e2, e3, foldUp_add _ (fun c _ s => foldUp_add _
      (fun d _ s => by rw [strictN_eq, nIf_succ]) s) 0, Nat.zero_add]
    rw [Finset.sum_eq_single_of_mem K1 (Finset.mem_range.2 hK) (fun b hb hne =>
      Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun d hd => ?_)]
    · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_range] at hc hd
      have hiff := eqv _ (mem hK hc hd)
      simp only at hiff
      simp only [hiff]
    · rw [Finset.mem_range] at hb hc hd
      refine ite_eq_right_iff.2 fun h => absurd ?_ hne
      have := forced _ (mem hb hc hd) h.1
      simp only at this
      rw [← this]
  · rw [blt_false (fun h => hK (e1 ▸ h))]
    dsimp only
    symm
    refine Finset.sum_eq_zero fun b hb' => Finset.sum_eq_zero fun c hc =>
      Finset.sum_eq_zero fun d hd => ite_eq_right_iff.2 fun h => absurd ?_ hK
    rw [Finset.mem_range] at hb' hc hd
    have := forced _ (mem hb' hc hd) h.1
    simp only at this
    rw [hK1, this]
    exact hb'

end CFSG.KS.SporSch.Tab

end
