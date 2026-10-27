module

public import CFSG.GF2Type.Smith1979W3.Cert690.SqReps
public import Certificates.Certificate690002

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

private structure Cert (D : PGLSquareData) : Prop where
  enumK : EnumCert kPGLGens D.pgl.elems.toList
  enumK0 : EnumCert kPGL0Gens D.pgl.elems0.toList
  s1 : pglS1Of D = true
  s2 : pglS2Of D = true
  s3 : pglS3Of D = true
  s4 : pglS4Of D = true
  pgl_eq : D.pgl = pglData ()
  theta_eq : D.theta = repThetas D.reps
  root_eq : D.root = repRoot D.innTabs D.theta
  witMap_eq : D.witMap = witMapOf D.wits
  innTabs_eq : D.innTabs = innTabs ()
  qmulFlat_eq : D.qmulFlat = qmulFlat ()

variable {D : PGLSquareData} {σ : (Q0 ≃* Q0) → Q0}

private theorem memK_iff (C : Cert D) {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    x ∈ KPGL ↔ c ∈ D.pgl.elems := by
  rw [← Array.mem_toList_iff]
  exact C.enumK.mem_iff hx hc

private theorem memK0_iff (C : Cert D) {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    x ∈ KPGL0 ↔ c ∈ D.pgl.elems0 := by
  rw [← Array.mem_toList_iff]
  exact C.enumK0.mem_iff hx hc

private theorem exists_mem_KPGL (C : Cert D) {c : ℕ} (hc : c ∈ D.pgl.elems) :
    ∃ k : V₀ ≃ₗ[ZMod 2] V₀, k ∈ KPGL ∧
      Code.HasCode (k : V₀ →ₗ[ZMod 2] V₀) c :=
  C.enumK.exists_mem (Array.mem_toList_iff.mpr hc)

private theorem outer_code (C : Cert D) {u : V₀ ≃ₗ[ZMod 2] V₀} (hu : u ∈ KPGL)
    (hu0 : u ∉ KPGL0) (hu2 : u * u = 1) :
    ∃ cu : ℕ, cu < 2 ^ 36 ∧ Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu ∧
      cu ∈ D.pgl.outers ∧ cu ∈ D.pgl.involutions := by
  obtain ⟨cu, hcu_lt, hcu⟩ := exists_code u
  have hone0 : (1 : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL0 := KPGL0.one_mem
  have hu_ne_one : u ≠ 1 := fun h => hu0 (h ▸ hone0)
  have hcuE : cu ∈ D.pgl.elems := (memK_iff C hcu hcu_lt).mp hu
  have hcuE0 : cu ∉ D.pgl.elems0 := fun h => hu0 ((memK0_iff C hcu hcu_lt).mpr h)
  have hcu_ne : cu ≠ Code.one := by
    intro h
    exact hu_ne_one (Code.HasCode.eq_of_equiv (h ▸ hcu) Code.hasCode_one)
  have hcu_sq : Code.mul cu cu = Code.one := by
    have h : Code.HasCode ((u * u : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul cu cu) := hcu.mul hcu
    rw [hu2] at h
    exact Code.HasCode.code_eq h Code.hasCode_one (Code.mul_lt _ _) Code.one_lt
  have hcu_inv : isInvCode cu = true := isInvCode_iff.2 ⟨hcu_ne, hcu_sq⟩
  exact ⟨cu, hcu_lt, hcu,
    (mem_outers_iff_of_pglOutersOK (pglS4Of_spec C.s4).1).mpr ⟨hcuE, hcu_inv, hcuE0⟩,
    (mem_involutions_iff_of_pglInvolutionsOK (pglS1Of_spec C.s1).1).mpr
      ⟨hcuE, hcu_inv⟩⟩

private theorem reps_size (C : Cert D) : D.reps.size = 2 :=
  (pglS1Of_spec C.s1).2.1

private theorem reps_mem (C : Cert D) {i : ℕ} (hi : i < 2) :
    D.reps[i]! ∈ D.pgl.elems ∧ isInvCode D.reps[i]! = true := by
  have hi' : i < D.reps.size := by rw [reps_size C]; exact hi
  exact (pglS1Of_spec C.s1).2.2.1 (D.reps[i]!) (by
    rw [getElem!_pos _ i hi']
    exact Array.getElem_mem hi')

private theorem reps_hrep (C : Cert D) :
    ∀ i < 2, ∃ r ∈ KPGL, r * r = 1 ∧
      Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) D.reps[i]! := by
  intro i hi
  obtain ⟨hElems, hInv⟩ := reps_mem C hi
  obtain ⟨-, hmul⟩ := isInvCode_iff.1 hInv
  obtain ⟨r, hrcode⟩ := exists_equiv_of_mul_eq_one hmul
  have hr2 : r * r = 1 := by
    have h : Code.HasCode ((r * r : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul D.reps[i]! D.reps[i]!) := hrcode.mul hrcode
    rw [hmul] at h
    exact Code.HasCode.eq_of_equiv h Code.hasCode_one
  exact ⟨r, (memK_iff C hrcode (C.enumK.lt _ (Array.mem_toList_iff.mpr hElems))).mpr
    hElems, hr2, hrcode⟩

private theorem reps_hhom (C : Cert D) :
    ∀ i < 2, isHomTab (liftTab D.reps[i]! 0) = true := by
  intro i hi
  have hinv : D.reps[i]! ∈ D.pgl.involutions :=
    (mem_involutions_iff_of_pglInvolutionsOK (pglS1Of_spec C.s1).1).mpr (reps_mem C hi)
  have hh := (pglS3Of_spec C.s3).1 _ hinv 0 (by norm_num)
  rw [isHomTab, ← C.qmulFlat_eq]
  exact hh

private theorem rootsOK_reps (C : Cert D) :
    rootsOK (innTabs ()) (repThetas D.reps) = true := by
  rw [← C.innTabs_eq, ← C.theta_eq]
  exact (pglS2Of_spec C.s2).2

private theorem root_eq_reps (C : Cert D) :
    D.root = repRoot (innTabs ()) (repThetas D.reps) := by
  rw [C.root_eq, C.innTabs_eq, C.theta_eq]

private theorem hom_of_outer (C : Cert D) {cu : ℕ} (hcu : cu ∈ D.pgl.involutions)
    {f : ℕ} (hf : f < 64) : isHomTab (liftTab cu f) = true := by
  have hh := (pglS3Of_spec C.s3).1 cu hcu f hf
  rw [isHomTab, ← C.qmulFlat_eq]
  exact hh

private noncomputable def outerF (C : Cert D) {cu : ℕ} (hcu : cu ∈ D.pgl.involutions) :
    ℕ → Q0 ≃* Q0 :=
  fun f => if h : isHomTab (liftTab cu f) = true then ofTab (liftTab cu f) h else 1

private theorem outerF_eq (C : Cert D) {cu : ℕ} (hcu : cu ∈ D.pgl.involutions)
    {f : ℕ} (hf : f < 64) :
    outerF C hcu f = ofTab (liftTab cu f) (hom_of_outer C hcu hf) := by
  unfold outerF
  rw [dif_pos (hom_of_outer C hcu hf)]

private theorem outerF_tab (C : Cert D) {cu : ℕ} (hcu : cu ∈ D.pgl.involutions)
    {f : ℕ} (hf : f < 64) :
    tabOf (outerF C hcu f) = liftTab cu f := by
  rw [outerF_eq C hcu hf]
  exact tabOf_ofTab _ _

private theorem outerF_inj (C : Cert D) {cu : ℕ} (hcu : cu ∈ D.pgl.involutions)
    (hdistinct : ∀ f < 64, ∀ f' < 64, liftTab cu f = liftTab cu f' → f = f') :
    ∀ f ∈ List.range 64, ∀ f' ∈ List.range 64, outerF C hcu f = outerF C hcu f' → f = f' := by
  intro f hf f' hf' heq
  have hf64 : f < 64 := List.mem_range.mp hf
  have hf64' : f' < 64 := List.mem_range.mp hf'
  rw [outerF_eq C hcu hf64, outerF_eq C hcu hf64'] at heq
  have htab : liftTab cu f = liftTab cu f' := by
    have := congrArg tabOf heq
    rwa [tabOf_ofTab, tabOf_ofTab] at this
  exact hdistinct f hf64 f' hf64' htab

private theorem outerF_image (C : Cert D) {u : V₀ ≃ₗ[ZMod 2] V₀} {cu : ℕ}
    (hcu : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu)
    (hcu_invol : cu ∈ D.pgl.involutions) :
    outerF C hcu_invol '' {f | f ∈ List.range 64} =
      {θ : Q0 ≃* Q0 | ∀ x, (θ x).v = u x.v} := by
  ext θ
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro x
    rw [outerF_eq C hcu_invol (List.mem_range.mp hf)]
    exact v_ofTab_liftTab hcu (hom_of_outer C hcu_invol (List.mem_range.mp hf)) x
  · intro hθlin
    obtain ⟨f, hf64, htab⟩ := exists_liftTab_eq hcu hθlin
    refine ⟨f, List.mem_range.mpr hf64, ?_⟩
    rw [outerF_eq C hcu_invol hf64]
    apply tabOf_injective
    rw [tabOf_ofTab, htab]

private theorem cand_pgl (C : Cert D) (hσ : IsSquareData KPGL σ) {b : Bool × Bool}
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab D.reps[i]! 0) (reps_hhom C i hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i))
    {u : V₀ ≃ₗ[ZMod 2] V₀} {cu : ℕ} (hcu : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu)
    (hcu_invol : cu ∈ D.pgl.involutions)
    {w : SqWit} (hw : D.witMap.get? cu = some w) (hsomew : some w ∈ D.wits)
    (hcandAll : ∀ f < 64, (pglCand D b w cu f).isSome = true) {f : ℕ} (hf : f < 64) :
    pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))) := by
  obtain ⟨-, hEk, hrepIdx, -, -, hpsi, htp, hitp, -⟩ :=
    witOK_spec (pglS4Of_spec C.s4).2.2.1 hsomew
  have hrep2 : w.repIdx < 2 := by rw [reps_size C] at hrepIdx; exact hrepIdx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hcandAll f hf)
  have hk : ∃ k ∈ KPGL, Code.HasCode (k : V₀ →ₗ[ZMod 2] V₀) w.k :=
    exists_mem_KPGL C hEk
  have hkt : isHomTab (liftTab w.k 0) = true := by
    have hk' := (pglS3Of_spec C.s3).2 w hsomew
    rwa [hpsi, C.qmulFlat_eq] at hk'
  have htp' : w.tp = compTab (compTab w.psi (repThetas D.reps)[w.repIdx]!)
      (invTab w.psi) := by
    rw [htp, C.theta_eq]
  let θ : Q0 ≃* Q0 := outerF C hcu_invol f
  have htabθ : tabOf θ = liftTab cu f := outerF_tab C hcu_invol hf
  have hvC : candVal (innTabs ()) (tabOf θ) w.psi w.tp w.itp
      (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 w.repIdx) = some v := by
    unfold pglCand at hv
    rw [C.innTabs_eq] at hv
    rw [root_eq_reps C] at hv
    rw [← htabθ] at hv
    exact hv
  have hveq : v = enc (σ θ) :=
    hσ.candVal_wit_eq (reps_size C) (reps_hrep C) (reps_hhom C) hb hrep2 hk hkt hpsi htp'
      hitp hvC
  rw [hv, hveq]

private theorem outerF_set_eq (C : Cert D) (hσ : IsSquareData KPGL σ) {b : Bool × Bool}
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab D.reps[i]! 0) (reps_hhom C i hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i))
    {u : V₀ ≃ₗ[ZMod 2] V₀} {cu : ℕ} (hcu : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu)
    (hcu_out : cu ∈ D.pgl.outers) (hcu_invol : cu ∈ D.pgl.involutions)
    {w : SqWit} (hw : D.witMap.get? cu = some w) (hsomew : some w ∈ D.wits)
    (hval : ∀ f < 64, pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))))
    {q : Q0} {n : ℕ} (hn : enc q = n) :
    {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = q} =
      outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some n) = true} := by
  ext θ
  constructor
  · rintro ⟨hlin, hσq⟩
    have hmem : θ ∈ outerF C hcu_invol '' {f | f ∈ List.range 64} := by
      rw [outerF_image C hcu hcu_invol]
      exact hlin
    obtain ⟨f, hf, hFθ⟩ := hmem
    refine ⟨f, ⟨hf, ?_⟩, hFθ⟩
    rw [hval f (List.mem_range.mp hf), hFθ, hσq, hn]
    exact beq_iff_eq.mpr rfl
  · rintro ⟨f, ⟨hf, hpc⟩, hFθ⟩
    have hf64 : f < 64 := List.mem_range.mp hf
    have hpc' : pglCand D b w cu f = some n := beq_iff_eq.mp hpc
    refine ⟨?_, ?_⟩
    · intro x
      rw [← hFθ, outerF_eq C hcu_invol hf64]
      exact v_ofTab_liftTab hcu (hom_of_outer C hcu_invol hf64) x
    · have hsome : enc (σ (outerF C hcu_invol f)) = n := by
        rw [hval f hf64] at hpc'
        exact Option.some.inj hpc'
      have hq : σ (outerF C hcu_invol f) = q := by
        apply enc_injective
        rw [hsome, ← hn]
      rw [← hFθ]
      exact hq

private theorem outerF_ncard (C : Cert D) {b : Bool × Bool} {w : SqWit} {cu : ℕ}
    (hcu_invol : cu ∈ D.pgl.involutions)
    (hdistinct : ∀ f < 64, ∀ f' < 64, liftTab cu f = liftTab cu f' → f = f') {n : ℕ} :
    (outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
      (pglCand D b w cu f == some n) = true}).ncard =
      ((List.range 64).filter fun f => (pglCand D b w cu f == some n)).length :=
  ncard_image_filter (L := List.range 64) (F := outerF C hcu_invol)
    (P := fun f => (pglCand D b w cu f == some n)) List.nodup_range
    (outerF_inj C hcu_invol hdistinct)

private theorem count_clause (C : Cert D) {b : Bool × Bool} {w : SqWit} {cu : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hcu_invol : cu ∈ D.pgl.involutions)
    (hcounts : ((((List.range 64).filter fun f => pglCand D b w cu f == some 0).length = 8 ∧
        ((List.range 64).filter fun f => pglCand D b w cu f == some z0N).length = 0) ∨
      (((List.range 64).filter fun f => pglCand D b w cu f == some 0).length = 0 ∧
        ((List.range 64).filter fun f => pglCand D b w cu f == some z0N).length = 8)))
    (hset1 : {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = 1} =
      outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some 0) = true})
    (hset2 : {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = z0} =
      outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some z0N) = true})
    (hcount0 : (outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some 0) = true}).ncard =
      ((List.range 64).filter fun f => (pglCand D b w cu f == some 0)).length)
    (hcountz : (outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some z0N) = true}).ncard =
      ((List.range 64).filter fun f => (pglCand D b w cu f == some z0N)).length) :
    ((Set.ncard {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = 1} = 8 ∧
        {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = z0} = ∅) ∨
      ({θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = 1} = ∅ ∧
        Set.ncard {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = z0} = 8)) := by
  rcases hcounts with ⟨h0, hz⟩ | ⟨h0, hz⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [hset1, hcount0]
      exact h0
    · rw [hset2]
      exact (Set.ncard_eq_zero (s := outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some z0N) = true})).mp (by rw [hcountz]; exact hz)
  · right
    refine ⟨?_, ?_⟩
    · rw [hset1]
      exact (Set.ncard_eq_zero (s := outerF C hcu_invol '' {f | f ∈ List.range 64 ∧
        (pglCand D b w cu f == some 0) = true})).mp (by rw [hcount0]; exact h0)
    · rw [hset2, hcountz]
      exact hz

private theorem fixed_ncard (C : Cert D) {b : Bool × Bool} {cu : ℕ} {w : SqWit}
    (hcu_invol : cu ∈ D.pgl.involutions)
    (hval : ∀ f < 64, pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))))
    (hsigma2 : ∀ f < 64, ∀ v, pglCand D b w cu f = some v → (v = 0 ∨ v = z0N) →
      ((List.range 128).filter fun x => (liftTab cu f)[x]! == x).length = 8 ∧
      (∀ x < 128, (liftTab cu f)[x]! = x → qmulN x x = 0) ∧
      ∀ w0 ∈ D.pgl.elems0, w0 ≠ Code.one → Code.mul w0 w0 = Code.one →
        Code.mul w0 cu = Code.mul cu w0 →
        ∃ x < 128, (liftTab cu f)[x]! = x ∧ Code.act w0 (x / 2) ≠ x / 2)
    {θ : Q0 ≃* Q0} {f : ℕ} (hf : f < 64) (hFθ : outerF C hcu_invol f = θ)
    (hσθ : σ θ = 1 ∨ σ θ = z0) :
    Set.ncard {x : Q0 | θ x = x} = 8 := by
  have hvalθ : pglCand D b w cu f = some (enc (σ θ)) := by
    rw [hval f hf, hFθ]
  have hvaln : enc (σ θ) = 0 ∨ enc (σ θ) = z0N := by
    rcases hσθ with h | h
    · left; rw [h, enc_one]
    · right; rw [h, enc_z0]
  have hsig := hsigma2 f hf (enc (σ θ)) hvalθ hvaln
  have htab : tabOf θ = liftTab cu f := by
    rw [← hFθ, outerF_tab C hcu_invol hf]
  rw [ncard_fixed θ, htab]
  exact hsig.1

private theorem fixed_sq (C : Cert D) {b : Bool × Bool} {cu : ℕ} {w : SqWit}
    (hcu_invol : cu ∈ D.pgl.involutions)
    (hval : ∀ f < 64, pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))))
    (hsigma2 : ∀ f < 64, ∀ v, pglCand D b w cu f = some v → (v = 0 ∨ v = z0N) →
      ((List.range 128).filter fun x => (liftTab cu f)[x]! == x).length = 8 ∧
      (∀ x < 128, (liftTab cu f)[x]! = x → qmulN x x = 0) ∧
      ∀ w0 ∈ D.pgl.elems0, w0 ≠ Code.one → Code.mul w0 w0 = Code.one →
        Code.mul w0 cu = Code.mul cu w0 →
        ∃ x < 128, (liftTab cu f)[x]! = x ∧ Code.act w0 (x / 2) ≠ x / 2)
    {θ : Q0 ≃* Q0} {f : ℕ} (hf : f < 64) (hFθ : outerF C hcu_invol f = θ)
    (hσθ : σ θ = 1 ∨ σ θ = z0) :
    ∀ x : Q0, θ x = x → x * x = 1 := by
  have hvalθ : pglCand D b w cu f = some (enc (σ θ)) := by
    rw [hval f hf, hFθ]
  have hvaln : enc (σ θ) = 0 ∨ enc (σ θ) = z0N := by
    rcases hσθ with h | h
    · left; rw [h, enc_one]
    · right; rw [h, enc_z0]
  have hsig := hsigma2 f hf (enc (σ θ)) hvalθ hvaln
  have htab : tabOf θ = liftTab cu f := by
    rw [← hFθ, outerF_tab C hcu_invol hf]
  intro x hx
  have hfix : (liftTab cu f)[enc x]! = enc x := by
    have h := (mem_fixed_iff θ x).mp hx
    rwa [htab] at h
  have hq := hsig.2.1 (enc x) (enc_lt x) hfix
  rw [qmulN_enc, ← enc_one] at hq
  exact enc_injective hq

private theorem comm_code (C : Cert D) {u : V₀ ≃ₗ[ZMod 2] V₀} {cu : ℕ}
    (hcu : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu)
    {w0 : V₀ ≃ₗ[ZMod 2] V₀} (hw0K : w0 ∈ KPGL0) (hw0ne : w0 ≠ 1)
    (hw0two : w0 * w0 = 1) (hw0comm : w0 * u = u * w0) :
    ∃ c0 : ℕ, c0 < 2 ^ 36 ∧ Code.HasCode (w0 : V₀ →ₗ[ZMod 2] V₀) c0 ∧
      c0 ∈ D.pgl.elems0 ∧ c0 ≠ Code.one ∧ Code.mul c0 c0 = Code.one ∧
      Code.mul c0 cu = Code.mul cu c0 := by
  obtain ⟨c0, hc0_lt, hc0⟩ := exists_code w0
  have hc0E0 : c0 ∈ D.pgl.elems0 := (memK0_iff C hc0 hc0_lt).mp hw0K
  have hc0ne : c0 ≠ Code.one := by
    intro h
    apply hw0ne
    have hcode1 : Code.HasCode (w0 : V₀ →ₗ[ZMod 2] V₀) Code.one := by
      rwa [h] at hc0
    exact Code.HasCode.eq_of_equiv hcode1 Code.hasCode_one
  have hc0sq : Code.mul c0 c0 = Code.one := by
    have h : Code.HasCode ((w0 * w0 : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul c0 c0) := hc0.mul hc0
    rw [hw0two] at h
    exact Code.HasCode.code_eq h Code.hasCode_one (Code.mul_lt _ _) Code.one_lt
  have hc0comm : Code.mul c0 cu = Code.mul cu c0 := by
    have h : Code.HasCode ((w0 * u : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul c0 cu) := hc0.mul hcu
    rw [hw0comm] at h
    exact Code.HasCode.code_eq h (hcu.mul hc0) (Code.mul_lt _ _) (Code.mul_lt _ _)
  exact ⟨c0, hc0_lt, hc0, hc0E0, hc0ne, hc0sq, hc0comm⟩

private theorem fixed_moved (C : Cert D) {b : Bool × Bool} {cu : ℕ} {w : SqWit}
    (hcu_invol : cu ∈ D.pgl.involutions)
    (hval : ∀ f < 64, pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))))
    (hsigma2 : ∀ f < 64, ∀ v, pglCand D b w cu f = some v → (v = 0 ∨ v = z0N) →
      ((List.range 128).filter fun x => (liftTab cu f)[x]! == x).length = 8 ∧
      (∀ x < 128, (liftTab cu f)[x]! = x → qmulN x x = 0) ∧
      ∀ w0 ∈ D.pgl.elems0, w0 ≠ Code.one → Code.mul w0 w0 = Code.one →
        Code.mul w0 cu = Code.mul cu w0 →
        ∃ x < 128, (liftTab cu f)[x]! = x ∧ Code.act w0 (x / 2) ≠ x / 2)
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hcu : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) cu)
    {θ : Q0 ≃* Q0} {f : ℕ} (hf : f < 64)
    (hFθ : outerF C hcu_invol f = θ) (hσθ : σ θ = 1 ∨ σ θ = z0)
    {w0 : V₀ ≃ₗ[ZMod 2] V₀} (hw0K : w0 ∈ KPGL0) (hw0ne : w0 ≠ 1)
    (hw0two : w0 * w0 = 1) (hw0comm : w0 * u = u * w0) :
    ∃ x : Q0, θ x = x ∧ w0 x.v ≠ x.v := by
  have hvalθ : pglCand D b w cu f = some (enc (σ θ)) := by
    rw [hval f hf, hFθ]
  have hvaln : enc (σ θ) = 0 ∨ enc (σ θ) = z0N := by
    rcases hσθ with h | h
    · left; rw [h, enc_one]
    · right; rw [h, enc_z0]
  have hsig := hsigma2 f hf (enc (σ θ)) hvalθ hvaln
  have htab : tabOf θ = liftTab cu f := by
    rw [← hFθ, outerF_tab C hcu_invol hf]
  obtain ⟨c0, hc0_lt, hc0, hc0E0, hc0ne, hc0sq, hc0comm⟩ :=
    comm_code C hcu hw0K hw0ne hw0two hw0comm
  obtain ⟨xN, hxNlt, hxNfix, hxNne⟩ := hsig.2.2 c0 hc0E0 hc0ne hc0sq hc0comm
  refine ⟨dec xN, ?_, ?_⟩
  · apply (mem_fixed_iff θ (dec xN)).mpr
    rw [htab, enc_dec hxNlt]
    exact hxNfix
  · intro hweq
    have hvec : Code.vec (Code.act c0 (xN / 2)) = Code.vec (xN / 2) := by
      have h2 : w0 (Code.vec (xN / 2)) = Code.vec (Code.act c0 (xN / 2)) :=
        apply_vec_of_hasCode hc0 (xN / 2)
      rw [← h2]
      exact hweq
    have hlt : xN / 2 < 64 := by omega
    exact hxNne (vec_injective_of_lt (Code.act_lt c0 (xN / 2)) hlt hvec)

theorem pglSquare_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (hS : pglSquareCheck () = true) :
    PGLSquareProp := by
  intro σ hσ u hu hu0 hu2
  let D : PGLSquareData := pglSquareData ()
  have hS' : (pglS1Of D && pglS2Of D && pglS3Of D && pglS4Of D) = true := by
    simpa only [pglSquareCheck] using hS
  obtain ⟨⟨⟨hS1, hS2⟩, hS3⟩, hS4⟩ := by
    simpa only [Bool.and_eq_true] using hS'
  let C : Cert D :=
    ⟨by rw [pglSquareData_pgl]; exact hK, by rw [pglSquareData_pgl]; exact hK0,
      hS1, hS2, hS3, hS4, pglSquareData_pgl, pglSquareData_theta, pglSquareData_root,
      pglSquareData_witMap, pglSquareData_innTabs, pglSquareData_qmulFlat⟩
  obtain ⟨cu, hcu_lt, hcu, hcu_out, hcu_invol⟩ := outer_code C hu hu0 hu2
  obtain ⟨b, hb⟩ := IsSquareData.exists_bits hσ (reps_size C) (reps_hrep C)
    (reps_hhom C) (rootsOK_reps C)
  obtain ⟨w, hw, -, hcandAll, hcounts, hsigma2, hdistinct⟩ :=
    (pglS4Of_spec C.s4).2.2.2 b cu hcu_out
  have hsomew : some w ∈ D.wits := by
    have hw' : (witMapOf D.wits).get? cu = some w := by rwa [← C.witMap_eq]
    exact (witMapOf_get?_eq_some hw').2
  have hval : ∀ f < 64, pglCand D b w cu f = some (enc (σ (outerF C hcu_invol f))) :=
    fun f hf => cand_pgl C hσ hb hcu hcu_invol hw hsomew hcandAll hf
  have hset1 := outerF_set_eq C hσ hb hcu hcu_out hcu_invol hw hsomew hval (q := 1) (n := 0)
    enc_one
  have hset2 := outerF_set_eq C hσ hb hcu hcu_out hcu_invol hw hsomew hval (q := z0) (n := z0N)
    enc_z0
  refine ⟨count_clause C hcu_invol hcounts hset1 hset2
    (outerF_ncard C hcu_invol hdistinct) (outerF_ncard C hcu_invol hdistinct), ?_⟩
  intro θ hθlin hσθ
  have hmem : θ ∈ outerF C hcu_invol '' {f | f ∈ List.range 64} := by
    rw [outerF_image C hcu hcu_invol]
    exact hθlin
  obtain ⟨f, hf, hFθ⟩ := hmem
  have hf64 : f < 64 := List.mem_range.mp hf
  refine ⟨fixed_ncard C hcu_invol hval hsigma2 hf64 hFθ hσθ,
    fixed_sq C hcu_invol hval hsigma2 hf64 hFθ hσθ, ?_⟩
  intro w0 hw0K hw0ne hw0two hw0comm
  exact fixed_moved C hcu_invol hval hsigma2 hcu hf64 hFθ hσθ hw0K hw0ne hw0two hw0comm

theorem pglSquare_sound_of_cert
    (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) : PGLSquareProp :=
  pglSquare_sound_of hK hK0 Certificates.certificate690002

end CFSG.GF2Type.Smith1979W3.Cert690

end
