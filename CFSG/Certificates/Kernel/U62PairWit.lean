module

public import CFSG.Certificates.Kernel.U62PairChecks

public section

namespace CFSG.KC.U62P.Snd

open CFSG.Fischer Matrix CFSG.KC.F4M CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.F4M.Aux
open CFSG.ComponentClassification.RankTwoHypIICover.U62
open CFSG.Sporadic.Schreier (evalCodes)
open CFSG.F4.Native (tvGens uPts)
open CFSG.KC.U6 (decA)
open CFSG.LargeExtraspecial.SMod20.Aut (frob4 fieldPerm fvec map_mulVec_fvec)
open CFSG.ComponentClassification.RankTwoSporadic (gammaE nE centDer)
open CFSG.ComponentClassification.RankTwoSporadic.Cert (MonoW)
open scoped commutatorElement

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec


theorem isom_of_unitary {g : Matrix (Fin 6) (Fin 6) F4}
    (h : gᵀ * g.map (fun a => a ^ 2) = 1) : IsIsom g := by
  intro x y
  rw [herm_eq_std, herm_eq_std]
  have e1 : fvec frob4 (g *ᵥ y) = (g.map (fun a => a ^ 2)) *ᵥ fvec frob4 y :=
    (map_mulVec_fvec frob4 g y).symm
  have hd : ∀ x y : W, hermStd x y = x ⬝ᵥ fvec frob4 y := by
    intro x y
    simp [hermStd, dotProduct, fvec, CFSG.LargeExtraspecial.SMod20.Aut.frob4_apply]
  rw [hd, hd, e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem exists_SU0_of_unitary {P : Matrix (Fin 6) (Fin 6) F4}
    (hu : Pᵀ * P.map (fun a => a ^ 2) = 1) (hdet : P.det = 1) :
    ∃ g : SU0, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = P := by
  have hne : P.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hne, ?_⟩, ?_⟩
  · rw [mem_SU0]
    refine ⟨?_, ?_⟩
    · apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        hdet, Units.val_one]
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact isom_of_unitary hu
  · exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _


theorem poolRep {PV NP : ℕ} (hpool : ∀ p < NP, poolAt PV p = true) :
    ∀ p < NP, ∃ c : SU0, RepSU (f72 PV p) c := by
  intro p hp
  have h := hpool p hp
  unfold poolAt at h
  rw [strictB_eq, bAnd_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hu : (decM (f72 PV p))ᵀ * (decM (f72 PV p)).map (fun a => a ^ 2) = 1 := by
    have := congrArg decM h1
    rwa [decM_mulK, decM_trn, decM_barK, decM_ONE] at this
  have hdet : (decM (f72 PV p)).det = 1 := by
    rw [det_sound, h2]
    rfl
  obtain ⟨g, hg⟩ := exists_SU0_of_unitary hu hdet
  exact ⟨g, hg⟩

theorem recRep {PV NP G1 G2 GG NG : ℕ} (hpool : ∀ p < NP, poolAt PV p = true)
    (hrec : ∀ g < NG, recAt PV NP G1 G2 GG g = true) :
    ∀ g < NG, ∃ c₁ c₂ : SU0, RepSU (f72 PV (f16 G1 g)) c₁ ∧ RepSU (f72 PV (f16 G2 g)) c₂ ∧
      RepSU (f72 GG g) (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
  intro g hg
  have h := hrec g hg
  unfold recAt at h
  rw [strictB_eq, strictB_eq, bAnd_eq_true, bAnd_eq_true, Nat.blt_eq, Nat.blt_eq,
    Nat.beq_eq] at h
  obtain ⟨ha, hb, he⟩ := h
  obtain ⟨c₁, h1⟩ := poolRep hpool _ ha
  obtain ⟨c₂, h2⟩ := poolRep hpool _ hb
  refine ⟨c₁, c₂, h1, h2, ?_⟩
  rw [he]
  unfold commK
  have := RepSU_mul (RepSU_mul h1 h2) (RepSU_mul (RepSU_inv h1) (RepSU_inv h2))
  rwa [← mul_assoc] at this


@[expose] def eMat (ρ ℓ : SU0) (m : ℕ) : SU0 := if m = 1 then ρ else if m = 2 then ℓ else ρ * ℓ

@[expose] def ePerm (r x : Equiv.Perm (Fin 693)) (m : ℕ) : Equiv.Perm (Fin 693) :=
  if m = 1 then r else if m = 2 then x else r * x

@[expose] def eFl (m : ℕ) : Equiv.Perm (Fin 693) := if m = 1 then 1 else fieldPerm frob4

theorem Nat_beq_false {m n : ℕ} (h : m ≠ n) : Nat.beq m n = false := by
  cases hh : Nat.beq m n
  · rfl
  · rw [Nat.beq_eq] at hh
    exact absurd hh h

theorem eltK_rep {R L : ℕ} {ρ ℓ : SU0} (hR : RepSU R ρ) (hL : RepSU L ℓ) (m : ℕ) :
    RepSU (eltK R L m) (eMat ρ ℓ m) := by
  unfold eltK eMat
  by_cases h1 : m = 1
  · subst h1
    exact hR
  · rw [Nat_beq_false h1, if_neg h1]
    by_cases h2 : m = 2
    · subst h2
      exact hL
    · rw [Nat_beq_false h2, if_neg h2]
      exact RepSU_mul hR hL

theorem ePerm_eq (ρ ℓ : SU0) (m : ℕ) :
    ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) m = piSU (eMat ρ ℓ m) * eFl m := by
  unfold ePerm eMat eFl
  by_cases h1 : m = 1
  · rw [if_pos h1, if_pos h1, if_pos h1, mul_one]
  · rw [if_neg h1, if_neg h1, if_neg h1]
    by_cases h2 : m = 2
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, map_mul, mul_assoc]


theorem commE_sound {C Tm : ℕ} {c ε : SU0} (hc : RepSU C c)
    (hε : RepSU Tm ε) {m : ℕ} (h : commE C Tm m = true) :
    piSU c * (piSU ε * eFl m) = (piSU ε * eFl m) * piSU c := by
  unfold commE at h
  by_cases h1 : m = 1
  · subst h1
    have h' : eqP (mulK C Tm) (mulK Tm C) = true := h
    have := piSU_eq_of_eqP (RepSU_mul hc hε) (RepSU_mul hε hc) h'
    rw [map_mul, map_mul] at this
    simpa [eFl] using this
  · rw [Nat_beq_false h1] at h
    have h' : eqP (mulK C Tm) (mulK Tm (barK C)) = true := h
    have := piSU_eq_of_eqP (RepSU_mul hc hε) (RepSU_mul hε (RepSU_barK hc)) h'
    rw [map_mul, map_mul, ← conj_frSU] at this
    rw [eFl, if_neg h1]
    calc piSU c * (piSU ε * fieldPerm frob4)
        = (piSU c * piSU ε) * fieldPerm frob4 := by rw [mul_assoc]
      _ = (piSU ε * (fieldPerm frob4 * piSU c * (fieldPerm frob4)⁻¹)) * fieldPerm frob4 := by
        rw [this]
      _ = piSU ε * fieldPerm frob4 * piSU c := by group


theorem gOK_unpack {T : WTab} {R L u : ℕ} (h : gOK T R L u = true) :
    f16 T.GL u < T.NG ∧ 0 < f8 T.GT u ∧ f8 T.GT u < 4 ∧
      (f8 T.GT u = 1 → isScal R = false) ∧
      commE (f72 T.PV (f16 T.G1 (f16 T.GL u))) (eltK R L (f8 T.GT u)) (f8 T.GT u) = true ∧
      commE (f72 T.PV (f16 T.G2 (f16 T.GL u))) (eltK R L (f8 T.GT u)) (f8 T.GT u) = true := by
  unfold gOK at h
  simp only [strictB_eq, bAnd_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, fun hm => ?_, h5, h6⟩
  rw [hm] at h4
  have h4' : CFSG.KLie.CT.notB (isScal R) = true := h4
  exact notB_eq_true.1 h4'


structure EntCtx (R L : ℕ) (ρ ℓ : SU0) : Prop where
  rR : RepSU R ρ
  rL : RepSU L ℓ
  rlt : R < 2 ^ 72
  hrr : piSU ρ * piSU ρ = 1
  hxx : (piSU ℓ * fieldPerm frob4) * (piSU ℓ * fieldPerm frob4) = 1
  hcomm : piSU ρ * (piSU ℓ * fieldPerm frob4) = (piSU ℓ * fieldPerm frob4) * piSU ρ
  hx1 : piSU ℓ * fieldPerm frob4 ≠ 1
  hrx1 : piSU ρ * (piSU ℓ * fieldPerm frob4) ≠ 1

@[expose] def Egrp (ρ ℓ : SU0) : Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.closure ({piSU ρ, piSU ℓ * fieldPerm frob4} : Set (Equiv.Perm (Fin 693)))

theorem ePerm_mem (ρ ℓ : SU0) (m : ℕ) :
    ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) m ∈ Egrp ρ ℓ := by
  have hr : piSU ρ ∈ Egrp ρ ℓ := Subgroup.subset_closure (by simp)
  have hx : piSU ℓ * fieldPerm frob4 ∈ Egrp ρ ℓ := Subgroup.subset_closure (by simp)
  unfold ePerm
  split_ifs
  · exact hr
  · exact hx
  · exact mul_mem hr hx

theorem ePerm_sq {R L : ℕ} {ρ ℓ : SU0} (hC : EntCtx R L ρ ℓ) (m : ℕ) :
    ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) m *
      ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) m = 1 := by
  unfold ePerm
  split_ifs
  · exact hC.hrr
  · exact hC.hxx
  · calc piSU ρ * (piSU ℓ * fieldPerm frob4) * (piSU ρ * (piSU ℓ * fieldPerm frob4))
        = piSU ρ * ((piSU ℓ * fieldPerm frob4) * piSU ρ) * (piSU ℓ * fieldPerm frob4) := by
          simp only [mul_assoc]
      _ = piSU ρ * (piSU ρ * (piSU ℓ * fieldPerm frob4)) * (piSU ℓ * fieldPerm frob4) := by
          rw [← hC.hcomm]
      _ = (piSU ρ * piSU ρ) * ((piSU ℓ * fieldPerm frob4) * (piSU ℓ * fieldPerm frob4)) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hC.hrr, hC.hxx, mul_one]

theorem piSU_mem_T46 (c : SU0) : piSU c ∈ T46 := by
  rw [← range_piSU]
  exact ⟨c, rfl⟩


theorem gOK_sound {T : WTab} {NP R L u : ℕ} {ρ ℓ : SU0}
    (hC : EntCtx R L ρ ℓ) (hpool : ∀ p < NP, poolAt T.PV p = true)
    (hrec : ∀ g < T.NG, recAt T.PV NP T.G1 T.G2 T.GG g = true) (hg : gOK T R L u = true) :
    ∃ γ : SU0, RepSU (f72 T.GG (f16 T.GL u)) γ ∧ piSU γ ∈ gammaE T46 (Egrp ρ ℓ) := by
  obtain ⟨hlt, hm0, hm4, hscal, hc1, hc2⟩ := gOK_unpack hg
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := recRep hpool hrec _ hlt
  have hε := eltK_rep hC.rR hC.rL (f8 T.GT u)
  refine ⟨c₁ * c₂ * c₁⁻¹ * c₂⁻¹, h3, ?_⟩
  have hcm1 := commE_sound h1 hε hc1
  have hcm2 := commE_sound h2 hε hc2
  rw [← ePerm_eq] at hcm1 hcm2
  have ht := ePerm_mem ρ ℓ (f8 T.GT u)
  have hne : ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) (f8 T.GT u) ≠ 1 := by
    unfold ePerm
    split_ifs with h1' h2'
    · intro hr
      have h5 := hscal h1'
      have h6 := (isScal_iff hC.rR hC.rlt).2 hr
      rw [h5] at h6
      exact Bool.noConfusion h6
    · exact hC.hx1
    · exact hC.hrx1
  refine Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ht (Subgroup.mem_iSup_of_mem hne ?_))
  have e : piSU (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) = ⁅piSU c₁, piSU c₂⁆ := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [e]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_inf.2 ⟨piSU_mem_T46 c₁, Subgroup.mem_centralizer_singleton_iff.2 hcm1⟩)
    (Subgroup.mem_inf.2 ⟨piSU_mem_T46 c₂, Subgroup.mem_centralizer_singleton_iff.2 hcm2⟩)


theorem alg_lin {G : Type*} [Group G] (a b : G) (ha : a * a = 1) :
    a * b * (a * b⁻¹) = ⁅a, b⁆ := by
  have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [commutatorElement_def, h]
  group

theorem alg_semi {G : Type*} [Group G] (a b Φ : G) (hΦ : Φ⁻¹ = Φ) (hx : (a * Φ) * (a * Φ) = 1) :
    a * (Φ * b * Φ⁻¹) * ((Φ * a * Φ⁻¹) * b⁻¹) = ⁅a * Φ, b⁆ := by
  have h1 : Φ * a * Φ⁻¹ = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [hΦ]
    simpa [mul_assoc] using hx
  rw [h1, commutatorElement_def]
  group

theorem nVal_sound {T : WTab} {NP R L f : ℕ} {ρ ℓ : SU0}
    (hC : EntCtx R L ρ ℓ) (hpool : ∀ p < NP, poolAt T.PV p = true)
    (hrec : ∀ g < T.NG, recAt T.PV NP T.G1 T.G2 T.GG g = true)
    (hg : ∀ l < f8 T.NC f, gOK T R L (f16 T.NS f + l) = true) :
    ∃ ν : SU0, RepSU (nVal T R L f) ν ∧ piSU ν ∈ nE T46 (Egrp ρ ℓ) := by
  obtain ⟨γ, hQγ, hγ, hγi⟩ := RepSU_prodK_prodRK (f16 T.NS f)
    (F := fun u => f72 T.GG (f16 T.GL u)) (fun g => piSU g ∈ gammaE T46 (Egrp ρ ℓ))
    (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
    (fun x hx => by rw [map_inv]; exact inv_mem hx) (by rw [map_one]; exact one_mem _)
    (f8 T.NC f) (fun l hl => gOK_sound hC hpool hrec (hg l hl))
  have hε := eltK_rep hC.rR hC.rL (f8 T.NE f)
  have hbe : Nat.beq 1 1 = true := rfl
  have hmem := ePerm_mem ρ ℓ (f8 T.NE f)
  have hsq := ePerm_sq hC (f8 T.NE f)
  have hpe := ePerm_eq ρ ℓ (f8 T.NE f)
  unfold nVal
  rw [strictN_eq, strictN_eq, strictN_eq, strictN_eq]
  by_cases hm : f8 T.NE f = 1
  · rw [hm] at hε hmem hsq hpe ⊢
    rw [hbe]
    have hε1 : eMat ρ ℓ 1 = ρ := by unfold eMat; rw [if_pos rfl]
    rw [hε1] at hε
    refine ⟨ρ * γ * (ρ * γ⁻¹), RepSU_mul (RepSU_mul hε hγ) (RepSU_mul hε hγi), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, alg_lin (piSU ρ) (piSU γ) hC.hrr]
    have hpe1 : ePerm (piSU ρ) (piSU ℓ * fieldPerm frob4) 1 = piSU ρ := by
      unfold ePerm; rw [if_pos rfl]
    rw [hpe1] at hmem
    exact Subgroup.commutator_mem_commutator hmem hQγ
  · rw [Nat_beq_false hm]
    refine ⟨eMat ρ ℓ (f8 T.NE f) * frSU γ * (frSU (eMat ρ ℓ (f8 T.NE f)) * γ⁻¹),
      RepSU_mul (RepSU_mul hε (RepSU_barK hγ)) (RepSU_mul (RepSU_barK hε) hγi), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, ← conj_frSU, ← conj_frSU]
    have hF : eFl (f8 T.NE f) = fieldPerm frob4 := by unfold eFl; rw [if_neg hm]
    rw [hF] at hpe
    rw [hpe] at hmem hsq
    rw [alg_semi (piSU (eMat ρ ℓ (f8 T.NE f))) (piSU γ) (fieldPerm frob4) fieldPerm_inv hsq]
    exact Subgroup.commutator_mem_commutator hmem hQγ


theorem allBlk_eq_true {b len : ℕ} {f : ℕ → Bool} :
    CFSG.KC.Enum.allBlk b f len = true ↔ ∀ l < len, f (b + l) = true := by
  induction len with
  | zero => exact ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (CFSG.KC.Enum.allBlk b f n) (f (Nat.add b n)) =
      true ↔ _
    rw [bAnd_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · rw [h]
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

theorem witAt_unpack {T : WTab} {R L w : ℕ} (h : witAt T R L w = true) :
    (∀ l < f8 T.WC w, ∀ l' < f8 T.NC (f16 T.WS w + l),
        gOK T R L (f16 T.NS (f16 T.WS w + l) + l') = true) ∧
      isScal (mulK (powK (wVal T R L w) (f8 T.WM w)) (powK (wVal T R L w) (f8 T.WM w))) = false ∧
      isScal (mulK (mulK (powK (wVal T R L w) (f8 T.WM w)) (powK (wVal T R L w) (f8 T.WM w)))
        (mulK (powK (wVal T R L w) (f8 T.WM w)) (powK (wVal T R L w) (f8 T.WM w)))) = true := by
  unfold witAt at h
  rw [bAnd_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun l hl l' hl' => ?_, ?_⟩
  · have := (allBlk_eq_true.1 h1) l hl
    simp only [bAnd_eq_true] at this
    exact allBlk_eq_true.1 this.2.2 l' hl'
  · have h3 : (strictB (powK (wVal T R L w) (f8 T.WM w)) fun z => strictB (mulK z z) fun z2 =>
        bAnd(CFSG.KLie.CT.notB (isScal z2), isScal (mulK z2 z2))) = true := h2
    rw [strictB_eq, strictB_eq, bAnd_eq_true] at h3
    exact ⟨notB_eq_true.1 h3.1, h3.2⟩


theorem wit_sound {T : WTab} {NP R L w : ℕ} {ρ ℓ : SU0}
    (hC : EntCtx R L ρ ℓ) (hpool : ∀ p < NP, poolAt T.PV p = true)
    (hrec : ∀ g < T.NG, recAt T.PV NP T.G1 T.G2 T.GG g = true) (hw : witAt T R L w = true) :
    ∃ z ∈ nE T46 (Egrp ρ ℓ), 4 ∣ orderOf z := by
  obtain ⟨hall, hnot, hfour⟩ := witAt_unpack hw
  obtain ⟨ω, hQω, hω⟩ := RepSU_prodK (f16 T.WS w) (F := nVal T R L)
    (fun g => piSU g ∈ nE T46 (Egrp ρ ℓ)) (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
    (by rw [map_one]; exact one_mem _) (f8 T.WC w)
    (fun l hl => nVal_sound hC hpool hrec (hall l hl))
  have hZ : RepSU (powK (wVal T R L w) (f8 T.WM w)) (ω ^ f8 T.WM w) := RepSU_powK hω _
  have hZ2 := RepSU_mul hZ hZ
  have hZ4 := RepSU_mul hZ2 hZ2
  have h2 : piSU (ω ^ f8 T.WM w * ω ^ f8 T.WM w) ≠ 1 := by
    intro h
    have := (isScal_iff hZ2 (mulK_lt _ _)).2 h
    rw [hnot] at this
    exact Bool.noConfusion this
  have h4 : piSU (ω ^ f8 T.WM w * ω ^ f8 T.WM w * (ω ^ f8 T.WM w * ω ^ f8 T.WM w)) = 1 :=
    (isScal_iff hZ4 (mulK_lt _ _)).1 hfour
  refine ⟨piSU (ω ^ f8 T.WM w), ?_, ?_⟩
  · rw [map_pow]
    exact pow_mem hQω _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simp only [map_mul] at h2 h4
    generalize piSU (ω ^ f8 T.WM w) = x at h2 h4 ⊢
    have hord : orderOf x = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (n := 1) (p := 2) (by rw [pow_one, sq]; exact h2)
        (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
            calc x ^ 4 = x * x * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
              _ = 1 := h4)
    rw [hord]
    norm_num


theorem anyBlk_eq_true {b len : ℕ} {f : ℕ → Bool} :
    anyBlk b f len = true ↔ ∃ l < len, f (b + l) = true := by
  induction len with
  | zero => exact ⟨fun h => Bool.noConfusion h, fun ⟨l, hl, _⟩ => absurd hl (Nat.not_lt_zero l)⟩
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) (anyBlk b f n) true (f (Nat.add b n)) = true ↔ _
    constructor
    · intro h
      cases hf : f (Nat.add b n)
      · rw [hf] at h
        obtain ⟨l, hl, hf'⟩ := ih.1 h
        exact ⟨l, Nat.lt_succ_of_lt hl, hf'⟩
      · exact ⟨n, Nat.lt_succ_self n, hf⟩
    · rintro ⟨l, hl, hf⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · cases hf' : f (Nat.add b n)
        · exact ih.2 ⟨l, hl, hf⟩
        · rfl
      · rw [show Nat.add b l = b + l from rfl, hf]

theorem entAt_unpack {T : ETab} {q j : ℕ} (h : entAt T q = true) (hj : j < 43)
    (hc : eqP (mulK (f72 T.LV (f16 T.EI q)) (barK (f72 T.RV j)))
      (mulK (f72 T.RV j) (f72 T.LV (f16 T.EI q))) = true) :
    ∃ w, witAt T.W (f72 T.RV j) (f72 T.LV (f16 T.EI q)) w = true := by
  unfold entAt at h
  rw [strictB_eq, bAnd_eq_true] at h
  obtain ⟨-, h2⟩ := h
  have h3 := allN_eq_true.1 h2 j hj
  rw [strictB_eq] at h3
  have h4 : anyBlk (f16 T.ES q) (fun w => bAnd(Nat.beq (f8 T.WJ w) j,
      witAt T.W (f72 T.RV j) (f72 T.LV (f16 T.EI q)) w)) (f8 T.EC q) = true := by
    rw [hc] at h3
    exact h3
  obtain ⟨l, -, hl⟩ := anyBlk_eq_true.1 h4
  exact ⟨f16 T.ES q + l, (bAnd_eq_true.1 hl).2⟩


theorem u62R_mem {j : ℕ} (hj : j < 43) : u62R j ∈ u62Sb := by
  have hj' : j < u62RWords.length := by rw [u62RWords_length]; exact hj
  have hmem : u62RWords.getD j [] ∈ u62RWords := by
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have hlet := u62RWords_letters _ hmem
  rw [u62R, evalCodes_u62SbG _ hlet]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact u62SbG_getD_mem (by have := hlet z hz; omega)


theorem monoW_of_checks {RV LV PO NO NP : ℕ} {T : ETab}
    (hRrep : ∀ j < 43, ∃ ρ : SU0, RepSU (f72 RV j) ρ ∧ piSU ρ = u62R j ∧
      isScal (mulK (f72 RV j) (f72 RV j)) = true ∧ isScal (f72 RV j) = false)
    (henum : ∀ s ∈ u62Sb, ∃ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ s = piSU ℓ)
    (hΦ : fieldPerm frob4 ∉ u62Sb)
    (hscan : ∀ i < 32768, scanAt LV PO T.EI NO i = true)
    (hLV : T.LV = LV) (hRV : T.RV = RV)
    (hpool : ∀ p < NP, poolAt T.W.PV p = true)
    (hrec : ∀ g < T.W.NG, recAt T.W.PV NP T.W.G1 T.W.G2 T.W.GG g = true)
    (hent : ∀ q < NO, entAt T q = true) :
    ∀ j < 43, ∀ s ∈ u62Sb, (s * fieldPerm frob4) ^ 2 = 1 →
      s * fieldPerm frob4 * u62R j = u62R j * (s * fieldPerm frob4) →
      MonoW T46 false (Subgroup.closure {u62R j, s * fieldPerm frob4}) := by
  intro j hj s hs hsq hcomm
  obtain ⟨ρ, hρ, hρr, hρρ, hρn⟩ := hRrep j hj
  obtain ⟨i, hi, ℓ, hℓ, rfl⟩ := henum s hs
  have hsq' : (piSU ℓ * fieldPerm frob4) * (piSU ℓ * fieldPerm frob4) = 1 := by rwa [sq] at hsq
  have hscal : isScal (mulK (f72 LV i) (barK (f72 LV i))) = true := by
    apply (isScal_iff (RepSU_mul hℓ (RepSU_barK hℓ)) (mulK_lt _ _)).2
    rw [map_mul, ← conj_frSU, fieldPerm_inv]
    calc piSU ℓ * (fieldPerm frob4 * piSU ℓ * fieldPerm frob4)
        = (piSU ℓ * fieldPerm frob4) * (piSU ℓ * fieldPerm frob4) := by simp only [mul_assoc]
      _ = 1 := hsq'
  have hsc := hscan i hi
  unfold scanAt at hsc
  rw [strictB_eq, hscal] at hsc
  have hsc' : (strictB (f16 PO i) fun q => bAnd(Nat.blt q NO, Nat.beq (f16 T.EI q) i)) = true :=
    hsc
  rw [strictB_eq, bAnd_eq_true, Nat.blt_eq, Nat.beq_eq] at hsc'
  obtain ⟨hq, hqi⟩ := hsc'
  have hentq := hent _ hq
  have hcomm' : piSU ℓ * fieldPerm frob4 * piSU ρ = piSU ρ * (piSU ℓ * fieldPerm frob4) := by
    rw [hρr]
    exact hcomm
  have hcomm2 : piSU (ℓ * frSU ρ) = piSU (ρ * ℓ) := by
    rw [map_mul, map_mul, ← conj_frSU]
    calc piSU ℓ * (fieldPerm frob4 * piSU ρ * (fieldPerm frob4)⁻¹)
        = (piSU ℓ * fieldPerm frob4 * piSU ρ) * (fieldPerm frob4)⁻¹ := by simp only [mul_assoc]
      _ = (piSU ρ * (piSU ℓ * fieldPerm frob4)) * (fieldPerm frob4)⁻¹ := by rw [hcomm']
      _ = piSU ρ * piSU ℓ := by group
  have hcond : eqP (mulK (f72 T.LV (f16 T.EI (f16 PO i))) (barK (f72 T.RV j)))
      (mulK (f72 T.RV j) (f72 T.LV (f16 T.EI (f16 PO i)))) = true := by
    rw [hLV, hRV, hqi]
    exact eqP_of_piSU_eq (RepSU_mul hℓ (RepSU_barK hρ)) (RepSU_mul hρ hℓ) (mulK_lt _ _)
      (mulK_lt _ _) hcomm2
  obtain ⟨w, hw⟩ := entAt_unpack hentq hj hcond
  rw [hLV, hRV, hqi] at hw
  have hρmem : piSU ρ ∈ u62Sb := by rw [hρr]; exact u62R_mem hj
  have hC : EntCtx (f72 RV j) (f72 LV i) ρ ℓ :=
    { rR := hρ
      rL := hℓ
      rlt := f72_lt _ _
      hrr := by
        rw [← map_mul]
        exact (isScal_iff (RepSU_mul hρ hρ) (mulK_lt _ _)).1 hρρ
      hxx := hsq'
      hcomm := hcomm'.symm
      hx1 := fun h => hΦ (by
        rw [eq_inv_of_mul_eq_one_right h]
        exact inv_mem hs)
      hrx1 := fun h => hΦ (by
        rw [← mul_assoc] at h
        rw [eq_inv_of_mul_eq_one_right h]
        exact inv_mem (mul_mem hρmem hs)) }
  obtain ⟨z, hz, h4⟩ := wit_sound hC hpool hrec hw
  rw [← hρr]
  exact Or.inl ⟨z, hz, h4⟩

end CFSG.KC.U62P.Snd

end
