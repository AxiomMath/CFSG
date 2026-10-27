module

public import CFSG.GF2Type.Smith1979W3.Cert690.SqReps
public import Certificates.Certificate690003

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

private def a8GensArr (D : A8Data) : Array ℕ := #[Code.one] ++ D.involutions

private structure Cert (D : A8Data) : Prop where
  enum : EnumCert a8Gens D.elems.toList
  s1 : a8S1Of D = true
  s2 : a8S2Of D = true
  s3 : a8S3Of D = true
  s4 : a8S4Of D = true
  s5 : a8S5Of D = true
  theta_eq : D.theta = repThetas D.reps
  root_eq : D.root = repRoot D.innTabs D.theta
  innTabs_eq : D.innTabs = innTabs ()
  qmulFlat_eq : D.qmulFlat = qmulFlat ()
  involutions_eq : D.involutions = invsOf D.elems
  witMap_eq : D.witMap = witMapOf D.wits

variable {D : A8Data}

private theorem cert_elems_size (C : Cert D) : D.elems.size = 20160 :=
  (a8S1Of_spec C.s1).2

private theorem mem_omega_iff_mem_elems (C : Cert D) {u : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hcode : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    u ∈ Ω₀ false ↔ c ∈ D.elems := by
  have hlen : D.elems.toList.length = 20160 := by
    rw [Array.length_toList, cert_elems_size C]
  rw [omega0_false_eq_codeSubgroup_a8Gens C.enum hlen, ← Array.mem_toList_iff]
  exact C.enum.mem_iff hcode hc

private theorem mem_involutions_of_involution (C : Cert D) {u : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hu : u ∈ Ω₀ false) (hu2 : u * u = 1)
    (hcode : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    c ∈ a8GensArr D := by
  by_cases h1 : u = 1
  · subst h1
    have hc1 : c = Code.one :=
      Code.HasCode.code_eq (by simpa using hcode) Code.hasCode_one hc Code.one_lt
    rw [hc1]
    exact Array.mem_append_left _ (by simp)
  · have hcE : c ∈ D.elems := (mem_omega_iff_mem_elems C hcode hc).mp hu
    have hcne : c ≠ Code.one := by
      intro hc1
      exact h1 (Code.HasCode.eq_of_equiv hcode (hc1 ▸ Code.hasCode_one))
    have hmul : Code.mul c c = Code.one := by
      have hm := hcode.mul hcode
      rw [hu2] at hm
      exact Code.HasCode.code_eq hm Code.hasCode_one (Code.mul_lt c c) Code.one_lt
    have hinv : isInvCode c = true := isInvCode_iff.2 ⟨hcne, hmul⟩
    exact Array.mem_append_right _
      ((mem_involutions_iff_of_a8InvolutionsOK (a8S2Of_spec C.s2).1).mpr ⟨hcE, hinv⟩)

private theorem exists_mem_omega_of_mem_elems (C : Cert D) {c : ℕ} (hc : c ∈ D.elems) :
    ∃ u : V₀ ≃ₗ[ZMod 2] V₀, u ∈ Ω₀ false ∧
      Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) c := by
  obtain ⟨u, huK, hcode⟩ := C.enum.exists_mem (Array.mem_toList_iff.mpr hc)
  refine ⟨u, ?_, hcode⟩
  have hlen : D.elems.toList.length = 20160 := by
    rw [Array.length_toList, cert_elems_size C]
  rw [omega0_false_eq_codeSubgroup_a8Gens C.enum hlen]
  exact huK

private theorem code_lt_of_mem_gens (C : Cert D) {c : ℕ} (hc : c ∈ a8GensArr D) :
    c < 2 ^ 36 := by
  rcases Array.mem_append.mp hc with hc | hc
  · have hc1 : c = Code.one := by simpa using hc
    rw [hc1]
    exact Code.one_lt
  · exact C.enum.lt c (Array.mem_toList_iff.mpr
      ((mem_involutions_iff_of_a8InvolutionsOK (a8S2Of_spec C.s2).1).mp hc).1)

private theorem exists_involution_of_mem_gens (C : Cert D) {c : ℕ} (hc : c ∈ a8GensArr D) :
    ∃ u : V₀ ≃ₗ[ZMod 2] V₀, u ∈ Ω₀ false ∧ u * u = 1 ∧
      Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) c := by
  rcases Array.mem_append.mp hc with hc | hc
  · have hc1 : c = Code.one := by simpa using hc
    rw [hc1]
    exact ⟨1, (Ω₀ false).one_mem, one_mul 1, Code.hasCode_one⟩
  · have hinv := ((mem_involutions_iff_of_a8InvolutionsOK (a8S2Of_spec C.s2).1).mp hc).2
    have hcc : Code.mul c c = Code.one := (isInvCode_iff.1 hinv).2
    obtain ⟨u, huΩ, hcode⟩ :=
      exists_mem_omega_of_mem_elems C
        ((mem_involutions_iff_of_a8InvolutionsOK (a8S2Of_spec C.s2).1).mp hc).1
    have hu2 : u * u = 1 := by
      refine Code.HasCode.eq_of_equiv (m := Code.one) ?_ Code.hasCode_one
      rw [← hcc]
      exact hcode.mul hcode
    exact ⟨u, huΩ, hu2, hcode⟩


private theorem reps_size (C : Cert D) : D.reps.size = 2 :=
  (a8S2Of_spec C.s2).2.1

private theorem reps_invCode (C : Cert D) {i : ℕ} (hi : i < 2) :
    D.reps[i]! ∈ D.elems ∧ isInvCode D.reps[i]! = true := by
  have hsize : i < D.reps.size := by rw [reps_size C]; exact hi
  exact (a8S2Of_spec C.s2).2.2.1 (D.reps[i]!) (by
    rw [getElem!_pos _ i hsize]
    exact Array.getElem_mem hsize)

private theorem reps_mem_gens (C : Cert D) {i : ℕ} (hi : i < 2) :
    D.reps[i]! ∈ a8GensArr D := by
  have hinv : D.reps[i]! ∈ D.involutions := by
    rw [mem_involutions_iff_of_a8InvolutionsOK (a8S2Of_spec C.s2).1]
    exact reps_invCode C hi
  exact Array.mem_append_right _ hinv

private theorem rep_isHom (C : Cert D) {i : ℕ} (hi : i < 2) :
    isHomTab (liftTab (D.reps[i]!) 0) = true := by
  have h := (a8S4Of_spec C.s4).1 (D.reps[i]!) (reps_mem_gens C hi) 0 (by norm_num)
  rwa [C.qmulFlat_eq] at h

private theorem rootsOK_D (C : Cert D) : rootsOK D.innTabs D.theta = true :=
  (a8S3Of_spec C.s3).2

private theorem rootsOK_reps (C : Cert D) :
    rootsOK (innTabs ()) (repThetas D.reps) = true := by
  rw [← C.innTabs_eq, ← C.theta_eq]
  exact rootsOK_D C

private theorem root_eq_reps (C : Cert D) :
    D.root = repRoot (innTabs ()) (repThetas D.reps) := by
  rw [C.root_eq, C.innTabs_eq, C.theta_eq]

private theorem reps_hrep (C : Cert D) :
    ∀ i < 2, ∃ r ∈ Ω₀ false, r * r = 1 ∧
      Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) D.reps[i]! := by
  intro i hi
  exact exists_involution_of_mem_gens C (reps_mem_gens C hi)

private theorem a8Cand_of_eq_one {b : Bool × Bool} {p : ℕ × ℕ} (hg : p.1 = Code.one) :
    a8Cand D b p = candValOne D.innTabs (liftTab p.1 p.2) := by
  unfold a8Cand
  rw [hg]
  simp

private theorem a8Cand_of_ne_one {b : Bool × Bool} {p : ℕ × ℕ} (hg : p.1 ≠ Code.one) :
    a8Cand D b p = match D.witMap.get? p.1 with
      | some w => if (w.g == p.1) = true then
          candVal D.innTabs (liftTab p.1 p.2) w.psi w.tp w.itp
            (sOf D.root b.1 b.2 w.repIdx)
        else none
      | none => none := by
  unfold a8Cand
  have hg' : (p.1 == Code.one) = false := by simpa using hg
  rw [hg']
  rfl

private theorem cand_eq_sigma {C : Cert D} {σ : (Q0 ≃* Q0) → Q0}
    (hσ : IsSquareData (Ω₀ false) σ) {b : Bool × Bool}
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab D.reps[i]! 0) (rep_isHom C hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i))
    {p : ℕ × ℕ} (hp : p ∈ a0Pairs (a8GensArr D)) {v : ℕ}
    (hv : a8Cand D b p = some v) (h : isHomTab (liftTab p.1 p.2) = true) :
    v = enc (σ (ofTab (liftTab p.1 p.2) h)) := by
  obtain ⟨hg, hf, -⟩ := mem_a0Pairs.mp hp
  by_cases h1 : p.1 = Code.one
  · rw [a8Cand_of_eq_one h1] at hv
    have hv' : candValOne (innTabs ()) (tabOf (ofTab (liftTab p.1 p.2) h)) = some v := by
      rw [← tabOf_ofTab (liftTab p.1 p.2) h, C.innTabs_eq] at hv
      exact hv
    exact hσ.candValOne_eq hv'
  · rw [a8Cand_of_ne_one h1] at hv
    cases hw : D.witMap.get? p.1 with
    | none =>
      rw [hw] at hv
      simp at hv
    | some w =>
      rw [hw] at hv
      by_cases hwg : (w.g == p.1) = true
      · dsimp only at hv
        rw [if_pos hwg] at hv
        have hw' : (witMapOf D.wits).get? p.1 = some w := by
          rw [← C.witMap_eq]
          exact hw
        obtain ⟨-, hwmem⟩ := witMapOf_get?_eq_some hw'
        obtain ⟨-, hEk, hrepIdx, -, -, hpsi, htp, hitp, -⟩ :=
          witOK_spec (a8S2Of_spec C.s2).2.2.2.2 hwmem
        have hrep2 : w.repIdx < 2 := by rw [reps_size C] at hrepIdx; exact hrepIdx
        have hk : ∃ k : V₀ ≃ₗ[ZMod 2] V₀, k ∈ Ω₀ false ∧
            Code.HasCode (k : V₀ →ₗ[ZMod 2] V₀) w.k :=
          exists_mem_omega_of_mem_elems C hEk
        have hkt : isHomTab (liftTab w.k 0) = true := by
          have hk' := (a8S4Of_spec C.s4).2 w hwmem
          rwa [hpsi, C.qmulFlat_eq] at hk'
        have htp' : w.tp = compTab (compTab w.psi (repThetas D.reps)[w.repIdx]!)
            (invTab w.psi) := by
          rw [htp, C.theta_eq]
        let θ : Q0 ≃* Q0 := ofTab (liftTab p.1 p.2) h
        have htabθ : tabOf θ = liftTab p.1 p.2 := tabOf_ofTab _ h
        have hvC : candVal (innTabs ()) (tabOf θ) w.psi w.tp w.itp
            (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 w.repIdx) = some v := by
          simpa only [C.innTabs_eq, ← htabθ, root_eq_reps C] using hv
        exact hσ.candVal_wit_eq (reps_size C) (reps_hrep C)
          (fun i hi => rep_isHom C hi) hb hrep2 hk hkt hpsi htp' hitp hvC
      · dsimp only at hv
        rw [if_neg hwg] at hv
        simp at hv

private noncomputable def autOfPair (p : ℕ × ℕ) : Q0 ≃* Q0 :=
  if h : isHomTab (liftTab p.1 p.2) = true then ofTab (liftTab p.1 p.2) h else 1

private theorem autOfPair_eq {p : ℕ × ℕ} (h : isHomTab (liftTab p.1 p.2) = true) :
    autOfPair p = ofTab (liftTab p.1 p.2) h := by
  unfold autOfPair
  rw [dif_pos h]

private theorem pairHom (C : Cert D) {p : ℕ × ℕ} (hp : p ∈ a0Pairs (a8GensArr D)) :
    isHomTab (liftTab p.1 p.2) = true := by
  obtain ⟨hg, hf, -⟩ := mem_a0Pairs.mp hp
  have h := (a8S4Of_spec C.s4).1 p.1 hg p.2 hf
  rwa [C.qmulFlat_eq] at h

private theorem autOfPair_tab (C : Cert D) {p : ℕ × ℕ}
    (hp : p ∈ a0Pairs (a8GensArr D)) :
    tabOf (autOfPair p) = liftTab p.1 p.2 := by
  rw [autOfPair_eq (pairHom C hp)]
  exact tabOf_ofTab _ _

private theorem exists_code_of_mem_gens (C : Cert D) {c : ℕ} (hc : c ∈ a8GensArr D) :
    ∃ u : V₀ ≃ₗ[ZMod 2] V₀, u ∈ Ω₀ false ∧
      Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) c := by
  obtain ⟨u, huΩ, hrest⟩ := exists_involution_of_mem_gens C hc
  exact ⟨u, huΩ, hrest.2⟩

private theorem autOfPair_mem (C : Cert D) {p : ℕ × ℕ}
    (hp : p ∈ a0Pairs (a8GensArr D)) :
    autOfPair p ∈ ThetaOver (Ω₀ false) ∧ autOfPair p a0 = a0 := by
  obtain ⟨hg, hf, ha0⟩ := mem_a0Pairs.mp hp
  rw [autOfPair_eq (pairHom C hp)]
  constructor
  · rcases Array.mem_append.mp hg with hg | hg
    · have hc1 : p.1 = Code.one := by simpa using hg
      have hcode1 : Code.HasCode ((1 : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) p.1 :=
        hc1 ▸ Code.hasCode_one
      exact ofTab_liftTab_mem_thetaOver (Ω₀ false).one_mem (one_mul 1) hcode1
        (pairHom C hp)
    · obtain ⟨u, huΩ, hrest⟩ :=
        exists_involution_of_mem_gens C (Array.mem_append_right _ hg)
      obtain ⟨hu2, hcode⟩ := hrest
      exact ofTab_liftTab_mem_thetaOver huΩ hu2 hcode (pairHom C hp)
  · exact (ofTab_liftTab_apply_a0 (pairHom C hp)).mp ha0

private theorem autOfPair_injOn (C : Cert D) {p p' : ℕ × ℕ}
    (hp : p ∈ a0Pairs (a8GensArr D)) (hp' : p' ∈ a0Pairs (a8GensArr D))
    (h : autOfPair p = autOfPair p') : p = p' := by
  obtain ⟨hg, hf, -⟩ := mem_a0Pairs.mp hp
  obtain ⟨hg', hf', -⟩ := mem_a0Pairs.mp hp'
  obtain ⟨u, -, hcode⟩ := exists_code_of_mem_gens C hg
  obtain ⟨u', -, hcode'⟩ := exists_code_of_mem_gens C hg'
  have hv1 : ∀ x : Q0, (autOfPair p x).v = u x.v := by
    rw [autOfPair_eq (pairHom C hp)]
    exact v_ofTab_liftTab hcode (pairHom C hp)
  have hv2 : ∀ x : Q0, (autOfPair p' x).v = u' x.v := by
    rw [autOfPair_eq (pairHom C hp')]
    exact v_ofTab_liftTab hcode' (pairHom C hp')
  have hlin : u = u' := by
    apply LinearEquiv.ext
    intro w
    have hc := congrArg (fun φ : Q0 ≃* Q0 => (φ ⟨0, w⟩).v) h
    rw [hv1, hv2] at hc
    exact hc
  have hcode_eq : p.1 = p'.1 :=
    Code.HasCode.code_eq hcode (hlin.symm ▸ hcode')
      (code_lt_of_mem_gens C hg) (code_lt_of_mem_gens C hg')
  have hlift : liftTab p.1 p.2 = liftTab p'.1 p'.2 := by
    rw [← autOfPair_tab C hp, ← autOfPair_tab C hp', h]
  rw [hcode_eq] at hlift
  have hf_eq : p.2 = p'.2 := liftTab_injective hf hf' hlift
  exact Prod.ext hcode_eq hf_eq

private theorem image_autOfPair_eq (C : Cert D) :
    autOfPair '' {p : ℕ × ℕ | p ∈ a0Pairs (a8GensArr D)} =
      {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0} := by
  ext θ
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact autOfPair_mem C hp
  · rintro ⟨hθover, hθa0⟩
    obtain ⟨u, huΩ, hrest⟩ := hθover
    obtain ⟨hu2, hθv⟩ := hrest
    obtain ⟨c, hc_lt, hcode⟩ := exists_code u
    have hcgens : c ∈ a8GensArr D :=
      mem_involutions_of_involution C huΩ hu2 hcode hc_lt
    obtain ⟨f, hf, htab⟩ := exists_liftTab_eq hcode hθv
    have hfix : (liftTab c f)[a0N]! = a0N := by
      have h1 : (tabOf θ)[a0N]! = enc (θ a0) := by
        rw [← enc_a0]
        exact tabOf_getElem! θ a0
      rw [htab] at h1
      rwa [hθa0, enc_a0] at h1
    have hp : (c, f) ∈ a0Pairs (a8GensArr D) :=
      mem_a0Pairs.mpr ⟨hcgens, hf, hfix⟩
    refine ⟨(c, f), hp, ?_⟩
    rw [autOfPair_eq (pairHom C hp)]
    apply tabOf_injective
    rw [tabOf_ofTab]
    exact htab.symm

private theorem nodup_gens (C : Cert D) : (a8GensArr D).toList.Nodup := by
  rw [a8GensArr, C.involutions_eq]
  exact nodup_one_append_invsOf C.enum.nodup

private theorem dec_a0N : dec a0N = a0 := by
  rw [← enc_a0, dec_enc]

private theorem dec_z0N : dec z0N = z0 := by
  rw [← enc_z0, dec_enc]

private theorem image_filter_eq (C : Cert D) {σ : (Q0 ≃* Q0) → Q0}
    (hσ : IsSquareData (Ω₀ false) σ) {b : Bool × Bool}
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab D.reps[i]! 0) (rep_isHom C hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i))
    {v : ℕ} (hv0 : v < 128) :
    autOfPair '' {p : ℕ × ℕ | p ∈ a0Pairs (a8GensArr D) ∧
        (a8Cand D b p == some v) = true} =
      {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = dec v} := by
  ext θ
  constructor
  · rintro ⟨p, ⟨hp, hcand⟩, rfl⟩
    obtain ⟨hθmem, hθa0⟩ := autOfPair_mem C hp
    have hcand' : a8Cand D b p = some v := beq_iff_eq.mp hcand
    have hv : v = enc (σ (ofTab (liftTab p.1 p.2) (pairHom C hp))) :=
      cand_eq_sigma (C := C) hσ hb hp hcand' (pairHom C hp)
    have hθeq : ofTab (liftTab p.1 p.2) (pairHom C hp) = autOfPair p :=
      (autOfPair_eq (pairHom C hp)).symm
    have hσv : σ (autOfPair p) = dec v := by
      rw [hv, hθeq, dec_enc]
    exact ⟨hθmem, hθa0, hσv⟩
  · rintro ⟨hθmem, hθa0, hθσ⟩
    have himg : θ ∈ autOfPair '' {p : ℕ × ℕ | p ∈ a0Pairs (a8GensArr D)} := by
      rw [image_autOfPair_eq C]
      exact ⟨hθmem, hθa0⟩
    obtain ⟨p, hp, hFp⟩ := himg
    have hex : (a8Cand D b p).isSome = true := (a8S5Of_spec C.s5).2.2.2 b |>.1 p hp
    obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hex
    have hv'' : v' = enc (σ (ofTab (liftTab p.1 p.2) (pairHom C hp))) :=
      cand_eq_sigma (C := C) hσ hb hp hv' (pairHom C hp)
    have hθeq : ofTab (liftTab p.1 p.2) (pairHom C hp) = autOfPair p :=
      (autOfPair_eq (pairHom C hp)).symm
    have hσv : σ (autOfPair p) = dec v := by
      rw [hFp]
      exact hθσ
    have hv'eq : v' = v := by
      rw [hv'', hθeq, hσv, enc_dec hv0]
    refine ⟨p, ⟨hp, ?_⟩, hFp⟩
    rw [hv', hv'eq]
    exact beq_iff_eq.mpr rfl

private theorem ncard_eq_count (C : Cert D) {σ : (Q0 ≃* Q0) → Q0}
    (hσ : IsSquareData (Ω₀ false) σ) {b : Bool × Bool}
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab D.reps[i]! 0) (rep_isHom C hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas D.reps)) b.1 b.2 i))
    {v : ℕ} (hv0 : v < 128) :
    Set.ncard {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = dec v} =
      ((a0Pairs (a8GensArr D)).filter fun p => (a8Cand D b p == some v)).length := by
  rw [← image_filter_eq C hσ hb hv0]
  exact ncard_image_filter (nodup_a0Pairs (nodup_gens C))
    (fun p hp p' hp' h => autOfPair_injOn C hp hp' h)
    (fun p => a8Cand D b p == some v)

theorem a8Square_sound_of (hE : EnumCert a8Gens (a8Data ()).elems.toList)
    (hS : a8SquareCheck () = true) : A8SquareProp := by
  intro σ hσ
  have hS' : (a8S1Of (a8Data ()) && a8S2Of (a8Data ()) && a8S3Of (a8Data ()) &&
      a8S4Of (a8Data ()) && a8S5Of (a8Data ())) = true := by
    simpa only [a8SquareCheck] using hS
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := by
    simpa only [Bool.and_eq_true] using hS'
  let D : A8Data := a8Data ()
  let C : Cert D :=
    ⟨hE, h1, h2, h3, h4, h5, a8Data_theta, a8Data_root, a8Data_innTabs,
      a8Data_qmulFlat, a8Data_involutions, a8Data_witMap⟩
  obtain ⟨b, hb⟩ := IsSquareData.exists_bits hσ (reps_size C) (reps_hrep C)
    (fun i hi => rep_isHom C hi) (rootsOK_reps C)
  constructor
  · have hcount := ncard_eq_count (C := C) hσ hb (v := a0N) (by decide +kernel)
    have hset : {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = a0} =
        {θ : Q0 ≃* Q0 |
          θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = dec a0N} := by
      ext θ
      simp only [Set.mem_ofPred_eq]
      rw [dec_a0N]
    rw [hset, hcount]
    exact ((a8S5Of_spec h5).2.2.2 b).2.1
  · have hcount := ncard_eq_count (C := C) hσ hb (v := z0N) (by decide +kernel)
    have hset : {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = z0} =
        {θ : Q0 ≃* Q0 |
          θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = dec z0N} := by
      ext θ
      simp only [Set.mem_ofPred_eq]
      rw [dec_z0N]
    rw [hset, hcount]
    exact ((a8S5Of_spec h5).2.2.2 b).2.2

theorem a8Square_sound_of_cert
    (hE : EnumCert a8Gens (a8Data ()).elems.toList) : A8SquareProp :=
  a8Square_sound_of hE Certificates.certificate690003

end CFSG.GF2Type.Smith1979W3.Cert690

end
