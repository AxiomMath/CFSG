module

public import CFSG.GF2Type.Widths1112.Co2Module.Checks
public import CFSG.GF2Type.Widths1112.Co2Module.Gluing22
public import CFSG.GF2Type.Widths1112.Co2Module.BlockData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.GF2W1112

theorem horbit_co2 :
    ∀ w ∈ lineReps, ∀ w' ∈ lineReps, uCls w = uCls w' → Relation.EqvGen
      (fun a b : F3Vec => ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧
        Matrix.vecMul b (uA (4 + s.val)) = c • a) w w' := by
  have htree := Certificates.certificate38956.2.2.2.1
  have key : ∀ w ∈ lineReps, Relation.EqvGen
      (fun a b : F3Vec => ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧
        Matrix.vecMul b (uA (4 + s.val)) = c • a) w (uRoot (uCls w)) := by
    intro w
    induction' h : uDepth w using Nat.strong_induction_on with d ih generalizing w
    intro hw
    by_cases hr : w = uRoot (uCls w)
    · rw [← hr]
      exact Relation.EqvGen.refl _
    · obtain ⟨hpar, hcls, hlt, hc, hv⟩ := htree w hw hr
      have h1 : ∃ s : Fin 2, ∃ c : ZMod 3, c ≠ 0 ∧
          Matrix.vecMul w (uA (4 + s.val)) = c • uPar w := ⟨uGen w, uC w, hc, hv⟩
      have h2 := ih (uDepth (uPar w)) (h ▸ hlt) (uPar w) rfl hpar
      rw [hcls] at h2
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h1)) h2
  intro w hw w' hw' hcls
  have h1 := key w hw
  have h2 := key w' hw'
  rw [hcls] at h1
  exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)

private theorem normIdx_n (s : Fin 2) : 4 + s.val ∈ w12UNormIdx := by
  revert s
  decide

private theorem normIdx_r (i : Fin 10) : 6 + i.val ∈ w12UNormIdx := by
  revert i
  decide

private theorem normIdx_p (j : Fin 5) : 17 + j.val ∈ w12UNormIdx := by
  revert j
  decide

private theorem normIdx_m (k : Fin 8) : w12UIdxM k.val ∈ w12UNormIdx := by
  revert k
  decide

private theorem idxM_n (s : Fin 2) : w12UIdxM (iN s).val = 4 + s.val := by
  show w12UIdxM s.val = 4 + s.val
  rw [w12UIdxM, if_pos s.isLt]

private theorem idxM_y (k : Fin 3) : w12UIdxM (iY k).val = 22 + k.val := by
  show w12UIdxM (2 + k.val) = 22 + k.val
  rw [w12UIdxM, if_neg (by omega)]
  omega

private theorem idxM_z (k : Fin 3) : w12UIdxM (iZ k).val = 25 + k.val := by
  show w12UIdxM (5 + k.val) = 25 + k.val
  rw [w12UIdxM, if_neg (by omega)]
  omega

noncomputable def co2BlockData :
    BlockData iotaE where
  n s := gen (4 + s.val)
  An s := uA (4 + s.val)
  hn s := conjAct_gen (normIdx_n s)
  cls := uCls
  h0 := Certificates.certificate38956.2.1
  h1 := Certificates.certificate38956.2.2.1
  horbit := horbit_co2
  w₁ := uW1
  v₀ := uV0
  hw₁R := Certificates.certificate38956.2.2.2.2.1.1
  hw₁cls := Certificates.certificate38956.2.2.2.2.1.2.1
  hv₀ := Certificates.certificate38956.2.2.2.2.1.2.2
  w := uW
  hwinj := Certificates.certificate38956.2.2.2.2.2.1.1
  hwR := Certificates.certificate38956.2.2.2.2.2.1.2.1
  hwcls := Certificates.certificate38956.2.2.2.2.2.1.2.2
  r i := gen (6 + i.val)
  Ar i := uA (6 + i.val)
  cr := uCr
  hr i := conjAct_gen (normIdx_r i)
  hcr i := (Certificates.certificate38956.2.2.2.2.2.2.1 i).1
  hwA i := (Certificates.certificate38956.2.2.2.2.2.2.1 i).2
  t := gen 16
  At := uA 16
  ct := uCt
  ht := conjAct_gen (by decide)
  ht2 := by
    have h := ord_gen 16
    have h2 : w12UOrd 16 = 2 := by decide
    rw [h2, pow_two] at h
    exact h
  hct := Certificates.certificate38956.2.2.2.2.2.2.2.1.1
  hwt := Certificates.certificate38956.2.2.2.2.2.2.2.1.2
  p j := gen (17 + j.val)
  hpstab j := ⟨uA (17 + j.val), conjAct_gen (normIdx_p j),
    Certificates.certificate38956.2.2.2.2.2.2.2.2.1 j⟩
  hp2 j := by
    obtain ⟨k, hk⟩ := Certificates.certificate38956.2.2.2.2.2.2.2.2.2.1 j
    exact ⟨k, by rw [← hk]; exact ord_gen _⟩
  m k := gen (w12UIdxM k.val)
  hmn s := by
    show gen (w12UIdxM (iN s).val) = gen (4 + s.val)
    rw [idxM_n]
  Am k := uA (w12UIdxM k.val)
  hm k := conjAct_gen (normIdx_m k)
  σ := uSigma
  u := uU
  ε := uEps
  pp := ppE
  hpp := ppE_mem
  hdec := dec_spec
  Ninf := NinfE
  hNnorm := NinfE_norm
  hNperf := NinfE_perf
  hy k := by
    show gen (w12UIdxM (iY k).val) ∈ NinfE
    rw [idxM_y]
    exact y_mem k
  hz k := by
    show gen (w12UIdxM (iZ k).val) ∈ NinfE
    rw [idxM_z]
    exact z_mem k
  g := gen 28
  hg3 := by
    have h := ord_gen 28
    have h2 : w12UOrd 28 = 3 := by decide
    rw [h2] at h
    exact h
  hzdef k := by
    rw [idxM_y, idxM_z, eq_mul_inv_iff_mul_eq]
    exact (glue_eq k).symm
  hgen := closure_n1_n2_g
  tw := uTw
  kk := uKk
  hrel := rel_tau
  X0 := uX0
  M0 := uM0
  hEnum θ M h1 h2 h3 := hEnum_co2 θ M h1 h2 h3

end CFSG.GF2Type.Widths1112.Co2Module
