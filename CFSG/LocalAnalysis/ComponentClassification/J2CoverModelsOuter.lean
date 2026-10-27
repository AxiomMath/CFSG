module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsTransfer

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

structure BinCocycle (G : Type*) [Group G] where
  toFun : G → G → ZMod 2
  isNormCocycle : IsNormCocycle toFun

@[ext] structure CocExt {G : Type*} [Group G] (f : BinCocycle G) where
  e : ZMod 2
  g : G

namespace CocExt

variable {G : Type*} [Group G] {f : BinCocycle G}

instance : Mul (CocExt f) := ⟨fun x y => ⟨x.e + y.e + f.toFun x.g y.g, x.g * y.g⟩⟩

instance : One (CocExt f) := ⟨⟨0, 1⟩⟩

instance : Inv (CocExt f) := ⟨fun x => ⟨x.e + f.toFun x.g⁻¹ x.g, x.g⁻¹⟩⟩

theorem mul_e (x y : CocExt f) : (x * y).e = x.e + y.e + f.toFun x.g y.g := rfl

theorem mul_g (x y : CocExt f) : (x * y).g = x.g * y.g := rfl

theorem one_e : (1 : CocExt f).e = 0 := rfl

theorem one_g : (1 : CocExt f).g = 1 := rfl

theorem inv_e (x : CocExt f) : x⁻¹.e = x.e + f.toFun x.g⁻¹ x.g := rfl

theorem inv_g (x : CocExt f) : x⁻¹.g = x.g⁻¹ := rfl

instance : Group (CocExt f) where
  mul_assoc x y z := by
    ext
    · simp only [mul_e, mul_g]
      have := f.isNormCocycle.2.2 x.g y.g z.g
      grind
    · simp only [mul_g, mul_assoc]
  one_mul x := by
    ext
    · simp only [mul_e, one_e, one_g, f.isNormCocycle.1, zero_add, add_zero]
    · simp only [mul_g, one_g, one_mul]
  mul_one x := by
    ext
    · simp only [mul_e, one_e, one_g, f.isNormCocycle.2.1, add_zero]
    · simp only [mul_g, one_g, mul_one]
  inv_mul_cancel x := by
    ext
    · simp only [mul_e, inv_e, inv_g, one_e]
      grind
    · simp only [mul_g, inv_g, one_g, inv_mul_cancel]

@[expose] def central : CocExt f := ⟨1, 1⟩

theorem central_mul (x : CocExt f) : central * x = x * central := by
  ext
  · simp only [central, mul_e, f.isNormCocycle.1, f.isNormCocycle.2.1]
    grind
  · simp only [central, mul_g, one_mul, mul_one]

theorem central_mul_central : (central : CocExt f) * central = 1 := by
  ext
  · simp only [central, mul_e, f.isNormCocycle.1, one_e]
    decide
  · simp only [central, mul_g, one_mul, one_g]

@[expose] def twistAut (β : G ≃* G) (lam : G → ZMod 2)
    (hlam : ∀ x y, f.toFun x y + f.toFun (β x) (β y) = lam x + lam y + lam (x * y)) :
    CocExt f ≃* CocExt f where
  toFun x := ⟨x.e + lam x.g, β x.g⟩
  invFun x := ⟨x.e + lam (β.symm x.g), β.symm x.g⟩
  left_inv x := by
    ext
    · simp only [MulEquiv.symm_apply_apply]
      grind
    · simp
  right_inv x := by
    ext
    · change x.e + lam (β.symm x.g) + lam (β.symm x.g) = x.e
      grind
    · simp
  map_mul' x y := by
    ext
    · simp only [mul_e, mul_g]
      have := hlam x.g y.g
      grind
    · simp only [mul_g, map_mul]

theorem twistAut_e (β : G ≃* G) (lam : G → ZMod 2) (hlam) (x : CocExt f) :
    (twistAut β lam hlam x).e = x.e + lam x.g := rfl

theorem twistAut_g (β : G ≃* G) (lam : G → ZMod 2) (hlam) (x : CocExt f) :
    (twistAut β lam hlam x).g = β x.g := rfl

theorem card_cocExt [Finite G] : Nat.card (CocExt f) = 2 * Nat.card G := by
  have e : CocExt f ≃ ZMod 2 × G := ⟨fun x => (x.e, x.g), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
    fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

end CocExt

@[expose, irreducible] noncomputable def uOut : Perm315 := permOfArr 315 outerU

@[expose, irreducible] noncomputable def bOut : Perm315 := gB * uOut * gB⁻¹

theorem bOut_eq : bOut = gB * uOut * gB⁻¹ := by rw [bOut]

theorem outerCheck_parts :
    isInvA 315 outerU outerU = true ∧ isInvA 315 (letterArr 1) bInvArr = true ∧
    eqA 315 (compA 315 bArr (compA 315 (letterArr 0) bArr)) repArrs[14]! = true ∧
    eqA 315 (compA 315 bArr (compA 315 (letterArr 1) bArr)) repArrs[5]! = true ∧
    (∀ a < 128, betaIdx a < 128 ∧
      eqA 315 (compA 315 bArr (compA 315 eltArrs[a]! bArr)) eltArrs[betaIdx a]! = true) ∧
    (∀ i < 4725, sigmaT[i]! < 4725 ∧ aCoefT[i]! < 128 ∧
      eqA 315 (compA 315 bArr (compA 315 repArrs[i]! bArr))
        (compA 315 eltArrs[aCoefT[i]!]! repArrs[sigmaT[i]!]!) = true) ∧
    (∀ i < 4725, i = 0 ∨ i = 17 ∨ i = 20 ∨ iTab i 1 ≠ i ∨ iTab i 2 ≠ i ∨ iTab i 3 ≠ i) ∧
    (∀ i ∈ [0, 17, 20], ∀ k < 128,
      eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!) = false) := by
  have h := outerCheck_eq
  simp only [outerCheck, Bool.and_eq_true, allLt_iff, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.not_eq_true', or_assoc,
    and_assoc] at h
  exact h

theorem rep_uOut : Rep 315 outerU uOut := by
  rw [uOut]
  exact (rep_permOfArr outerCheck_parts.1).1

theorem uOut_inv : uOut⁻¹ = uOut :=
  (rep_inv_of_isInvA rep_uOut outerCheck_parts.1).unique rep_uOut

theorem rep_bInvArr : Rep 315 bInvArr gB⁻¹ :=
  rep_inv_of_isInvA (rep_letterArr 1) outerCheck_parts.2.1

theorem rep_bArr : Rep 315 bArr bOut := by
  have h := rep_compA (rep_letterArr 1) (rep_compA rep_uOut rep_bInvArr)
  rw [show letter 1 = gB by simp [letter], ← mul_assoc, ← bOut_eq] at h
  unfold bArr
  exact h

theorem bOut_inv : bOut⁻¹ = bOut := by
  rw [bOut_eq, mul_inv_rev, mul_inv_rev, inv_inv, uOut_inv, mul_assoc]

theorem bOut_mul_self : bOut * bOut = 1 := by
  nth_rewrite 1 [← bOut_inv]
  exact inv_mul_cancel bOut

theorem bOut_conj_conj (x : Perm315) : bOut * (bOut * x * bOut⁻¹) * bOut⁻¹ = x := by
  rw [bOut_inv, ← mul_assoc, ← mul_assoc, bOut_mul_self, one_mul, mul_assoc, bOut_mul_self,
    mul_one]

theorem conj_eq_of_eqA {t : Array ℕ} {σ : Perm315} (ht : Rep 315 t σ) {r : Array ℕ}
    {ρ : Perm315} (hr : Rep 315 r ρ) (h : eqA 315 (compA 315 bArr (compA 315 t bArr)) r = true) :
    bOut * σ * bOut⁻¹ = ρ := by
  rw [bOut_inv, mul_assoc]
  exact eq_of_eqA (rep_compA rep_bArr (rep_compA ht rep_bArr)) hr h

theorem bOut_conj_gA : bOut * gA * bOut⁻¹ = rep 14 :=
  conj_eq_of_eqA (rep_letterArr 0) (rep_repArrs (by norm_num)) outerCheck_parts.2.2.1

theorem bOut_conj_gB : bOut * gB * bOut⁻¹ = rep 5 :=
  conj_eq_of_eqA (rep_letterArr 1) (rep_repArrs (by norm_num)) outerCheck_parts.2.2.2.1

theorem bOut_conj_mem {g : Perm315} (hg : g ∈ P) : bOut * g * bOut⁻¹ ∈ P := by
  have h : Subgroup.closure {gA, gB} ≤ P.comap (MulAut.conj bOut).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        bOut_conj_gA]
      exact rep_mem 14
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        bOut_conj_gB]
      exact rep_mem 5
  rw [P_eq] at hg
  have := h hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem bOut_conj_elt {a : ℕ} (ha : a < 128) :
    bOut * (elt a : Perm315) * bOut⁻¹ = elt (betaIdx a) :=
  conj_eq_of_eqA (rep_eltArrs ha) (rep_eltArrs ((outerCheck_parts.2.2.2.2.1 a ha).1))
    (outerCheck_parts.2.2.2.2.1 a ha).2

theorem bOut_conj_mem_S {s : Perm315} (hs : s ∈ S) : bOut * s * bOut⁻¹ ∈ S := by
  obtain ⟨x, hx, rfl⟩ := exists_elt hs
  rw [bOut_conj_elt hx]
  exact (elt _).2

theorem bOut_conj_rep {i : ℕ} (hi : i < 4725) :
    bOut * rep i * bOut⁻¹ = (elt aCoefT[i]! : Perm315) * rep sigmaT[i]! := by
  obtain ⟨h1, h2, h3⟩ := outerCheck_parts.2.2.2.2.2.1 i hi
  exact conj_eq_of_eqA (rep_repArrs hi) (rep_compA (rep_eltArrs h2) (rep_repArrs h1)) h3

@[expose] noncomputable def betaP : P ≃* P where
  toFun g := ⟨bOut * g * bOut⁻¹, bOut_conj_mem g.2⟩
  invFun g := ⟨bOut * g * bOut⁻¹, bOut_conj_mem g.2⟩
  left_inv g := Subtype.ext (bOut_conj_conj _)
  right_inv g := Subtype.ext (bOut_conj_conj _)
  map_mul' g h := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem betaP_coe (g : P) : (betaP g : Perm315) = bOut * g * bOut⁻¹ := rfl

@[expose] noncomputable def betaS : S ≃* S where
  toFun s := ⟨bOut * s * bOut⁻¹, bOut_conj_mem_S s.2⟩
  invFun s := ⟨bOut * s * bOut⁻¹, bOut_conj_mem_S s.2⟩
  left_inv s := Subtype.ext (bOut_conj_conj _)
  right_inv s := Subtype.ext (bOut_conj_conj _)
  map_mul' s t := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem betaS_coe (s : S) : (betaS s : Perm315) = bOut * s * bOut⁻¹ := rfl

theorem betaS_betaS (s : S) : betaS (betaS s) = s := Subtype.ext (by
  rw [betaS_coe, betaS_coe, bOut_conj_conj])

theorem betaS_elt {a : ℕ} (ha : a < 128) : betaS (elt a) = elt (betaIdx a) :=
  Subtype.ext (by rw [betaS_coe, bOut_conj_elt ha])

theorem betaIdx_lt {a : ℕ} (ha : a < 128) : betaIdx a < 128 :=
  (outerCheck_parts.2.2.2.2.1 a ha).1

theorem incl_betaS (s : S) : incl (betaS s) = betaP (incl s) :=
  Subtype.ext (by rw [incl_coe, betaS_coe, betaP_coe, incl_coe])

@[expose] noncomputable def sigmaIdx (i : Fin 4725) : Fin 4725 :=
  ⟨sigmaT[(i : ℕ)]!, (outerCheck_parts.2.2.2.2.2.1 i i.isLt).1⟩

@[expose] noncomputable def aElt (i : Fin 4725) : S := elt aCoefT[(i : ℕ)]!

theorem repP_coe (i : ℕ) : (repP i : Perm315) = rep i := rfl

theorem betaP_repP (i : Fin 4725) :
    (betaP (repP i) : Perm315) = (aElt i : Perm315) * rep (sigmaIdx i) := by
  rw [betaP_coe]
  exact bOut_conj_rep i.isLt

theorem bOut_not_mem : bOut ∉ P := by
  intro hb
  obtain ⟨⟨k, i⟩, hki⟩ := tv_surjective ⟨bOut, hb⟩
  have hb' : bOut = (elt k : Perm315) * rep i := (congrArg Subtype.val hki).symm
  have hfix : ∀ m < 3, iTab i (m + 1) = i := by
    intro m hm
    obtain ⟨h1, h2, h3, h4⟩ := decomp_elt i (a := m + 1) (by omega)
    have hm1 : (m + 1) < 128 := by omega
    have hr : rep i * (incl (elt (m + 1)) : Perm315) =
        ((elt k)⁻¹ * betaS (elt (m + 1)) * elt k : S) * rep i := by
      rw [incl_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, betaS_coe]
      have : rep i = (elt k : Perm315)⁻¹ * bOut := by rw [hb']; group
      rw [this]
      group
    have := (decomp_unique hr).2
    rw [h4] at this
    exact congrArg Fin.val this
  have hcase := outerCheck_parts.2.2.2.2.2.2.1 i i.isLt
  have hnot := outerCheck_parts.2.2.2.2.2.2.2
  have hrep := eq_of_eqA rep_bArr (rep_compA (rep_eltArrs k.isLt) (rep_repArrs i.isLt))
  rcases hcase with h | h | h | h | h | h
  · have := hnot 0 (by simp) k k.isLt
    rw [← h, (eqA_iff rep_bArr (rep_compA (rep_eltArrs k.isLt) (rep_repArrs i.isLt))).2 hb']
      at this
    exact Bool.noConfusion this
  · have := hnot 17 (by simp) k k.isLt
    rw [← h, (eqA_iff rep_bArr (rep_compA (rep_eltArrs k.isLt) (rep_repArrs i.isLt))).2 hb']
      at this
    exact Bool.noConfusion this
  · have := hnot 20 (by simp) k k.isLt
    rw [← h, (eqA_iff rep_bArr (rep_compA (rep_eltArrs k.isLt) (rep_repArrs i.isLt))).2 hb']
      at this
    exact Bool.noConfusion this
  · exact h (hfix 0 (by norm_num))
  · exact h (hfix 1 (by norm_num))
  · exact h (hfix 2 (by norm_num))

@[expose] noncomputable def fNorm : BinCocycle S := ⟨fCoc, isNormCocycle_fCoc⟩

abbrev Rf : Type := CocExt fNorm

@[expose] noncomputable def lamCoch : S → ZMod 2 := mk1 lamMask

theorem lambdaCheck_parts :
    lamBit 0 = false ∧
    (∀ a < 128, ∀ d < 128,
      (bitAt fRows a d ^^ bitAt fRows betaTab[a]! betaTab[d]!) = cobBit lamMask a d) ∧
    (∀ a < 128, (lamBit a ^^ lamBit betaTab[a]!) = false) ∧
    (∀ a < 128, (xorFold 4725 (fun i => cBit i a) ^^ muBit a ^^ muBit betaTab[a]!) = lamBit a) := by
  have h := lambdaCheck_eq
  simp only [lambdaCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem betaTab_get {a : ℕ} (ha : a < 128) : betaTab[a]! = betaIdx a := by
  unfold betaTab
  exact ofFn_getElem! _ ha

theorem invTab_get {a : ℕ} (ha : a < 128) : invTab[a]! = invIdx a := by
  unfold invTab
  exact ofFn_getElem! _ ha

theorem lamCoch_one : lamCoch 1 = 0 := by
  rw [lamCoch, ← elt_zero, mk1_elt _ (by norm_num)]
  rw [show maskBit lamMask 0 = lamBit 0 from rfl, lambdaCheck_parts.1]
  rfl

theorem cob_lamCoch (s t : S) :
    fCoc s t + fCoc (betaS s) (betaS t) = lamCoch s + lamCoch t + lamCoch (s * t) := by
  obtain ⟨a, ha, rfl⟩ := elt_surjective s
  obtain ⟨d, hd, rfl⟩ := elt_surjective t
  have h := lambdaCheck_parts.2.1 _ ha _ hd
  rw [betaTab_get ha, betaTab_get hd, cobBit, mulTab_get ha hd] at h
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := a) hd
  rw [← hm2, betaS_elt ha, betaS_elt hd, fCoc, tbl_elt _ ha hd,
    tbl_elt _ (betaIdx_lt ha) (betaIdx_lt hd), lamCoch, mk1_elt _ ha, mk1_elt _ hd,
    mk1_elt _ hm1]
  revert h
  cases bitAt fRows a d <;> cases bitAt fRows (betaIdx a) (betaIdx d) <;>
    cases maskBit lamMask a <;> cases maskBit lamMask d <;>
    cases maskBit lamMask (mulIdx a d) <;> decide

@[expose] noncomputable def tauR : Rf ≃* Rf := CocExt.twistAut betaS lamCoch cob_lamCoch

theorem tauR_e (x : Rf) : (tauR x).e = x.e + lamCoch x.g := rfl

theorem tauR_g (x : Rf) : (tauR x).g = betaS x.g := rfl

theorem tauR_central : tauR CocExt.central = CocExt.central := by
  refine CocExt.ext ?_ ?_
  · rw [tauR_e]
    change 1 + lamCoch 1 = 1
    rw [lamCoch_one, add_zero]
  · rw [tauR_g]
    change betaS 1 = 1
    exact map_one betaS

theorem lamCoch_betaS (s : S) : lamCoch s + lamCoch (betaS s) = 0 := by
  have ha := idx_lt s
  have h := lambdaCheck_parts.2.2.1 _ ha
  rw [betaTab_get ha] at h
  rw [← elt_idx s, betaS_elt ha, lamCoch, mk1_elt _ ha, mk1_elt _ (betaIdx_lt ha)]
  revert h
  rw [show lamBit (idx s) = maskBit lamMask (idx s) from rfl,
    show lamBit (betaIdx (idx s)) = maskBit lamMask (betaIdx (idx s)) from rfl]
  cases maskBit lamMask (idx s) <;> cases maskBit lamMask (betaIdx (idx s)) <;> decide

theorem tauR_tauR (x : Rf) : tauR (tauR x) = x := by
  refine CocExt.ext ?_ ?_
  · rw [tauR_e, tauR_e, tauR_g, add_assoc, lamCoch_betaS, add_zero]
  · rw [tauR_g, tauR_g, betaS_betaS]

@[expose] noncomputable def aRf (i : Fin 4725) : Rf := ⟨0, aElt i⟩

@[expose] noncomputable def cMul (i : Fin 4725) (g : P) : Rf :=
  (aRf i)⁻¹ * tauR ⟨0, factor i g⟩ * aRf (cosetAct i g)

@[expose] noncomputable def cCoef (i : Fin 4725) (g : P) : ZMod 2 := (cMul i g).e

@[expose] noncomputable def bigLam (g : P) : ZMod 2 := ∑ i : Fin 4725, cCoef i g

theorem cMul_snd (i : Fin 4725) (g : P) :
    (cMul i g).g = factor (sigmaIdx i) (betaP g) ∧
      cosetAct (sigmaIdx i) (betaP g) = sigmaIdx (cosetAct i g) := by
  have key : rep (sigmaIdx i) * (betaP g : Perm315) =
      ((aElt i)⁻¹ * betaS (factor i g) * aElt (cosetAct i g) : S) *
        rep (sigmaIdx (cosetAct i g)) := by
    have h1 := congrArg (fun x : Perm315 => bOut * x * bOut⁻¹) (rep_mul_eq i g)
    have h2 : bOut * (rep i * (g : Perm315)) * bOut⁻¹ =
        (bOut * rep i * bOut⁻¹) * (bOut * g * bOut⁻¹) := by group
    have h3 : bOut * ((factor i g : Perm315) * rep (cosetAct i g)) * bOut⁻¹ =
        (bOut * factor i g * bOut⁻¹) * (bOut * rep (cosetAct i g) * bOut⁻¹) := by group
    rw [h2, h3, ← betaP_coe, ← betaS_coe] at h1
    have h4 := betaP_repP i
    have h5 := betaP_repP (cosetAct i g)
    rw [betaP_coe, repP_coe] at h4 h5
    rw [h4, h5] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc rep (sigmaIdx i) * (betaP g : Perm315)
        = (aElt i : Perm315)⁻¹ * ((aElt i : Perm315) * rep (sigmaIdx i) * betaP g) := by group
      _ = _ := by rw [h1]; group
  obtain ⟨hf, hc⟩ := decomp_unique key
  refine ⟨?_, hc⟩
  rw [hf, cMul, CocExt.mul_g, CocExt.mul_g, CocExt.inv_g, tauR_g]
  rfl

theorem fNorm_toFun : fNorm.toFun = fCoc := rfl

theorem cMul_e_elt (i : Fin 4725) {a : ℕ} (ha : a < 128) :
    cCoef i (incl (elt a)) = if cBit i a then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := decomp_elt i ha
  obtain ⟨-, hs, -⟩ := outerCheck_parts.2.2.2.2.2.1 i i.isLt
  obtain ⟨-, hs', -⟩ := outerCheck_parts.2.2.2.2.2.1 (iTab i a) h2
  have hsi : (elt aCoefT[(i : ℕ)]!)⁻¹ = elt (invIdx aCoefT[(i : ℕ)]!) := (elt_inv hs).2
  have hsi' : invIdx aCoefT[(i : ℕ)]! < 128 := (elt_inv hs).1
  have hbp := betaIdx_lt h1
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := invIdx aCoefT[(i : ℕ)]!) hbp
  rw [cCoef, cMul, h3, h4]
  simp only [CocExt.mul_e, CocExt.mul_g, CocExt.inv_e, CocExt.inv_g, tauR_e, tauR_g, aRf,
    aElt, fNorm_toFun, zero_add, add_zero]
  rw [hsi, betaS_elt h1, ← hm2, fCoc, tbl_elt _ hsi' hs, tbl_elt _ hsi' hbp,
    tbl_elt _ hm1 hs', lamCoch, mk1_elt _ h1]
  have hc : cBit i a = (bitAt fRows (invIdx aCoefT[(i : ℕ)]!) aCoefT[(i : ℕ)]! ^^
      maskBit lamMask (pTab i a) ^^
      bitAt fRows (invIdx aCoefT[(i : ℕ)]!) (betaIdx (pTab i a)) ^^
      bitAt fRows (mulIdx (invIdx aCoefT[(i : ℕ)]!) (betaIdx (pTab i a))) aCoefT[iTab i a]!) := by
    rw [cBit, invTab_get hs, betaTab_get h1, mulTab_get hsi' hbp]
    rfl
  rw [hc]
  cases bitAt fRows (invIdx aCoefT[(i : ℕ)]!) aCoefT[(i : ℕ)]! <;>
    cases maskBit lamMask (pTab i a) <;>
    cases bitAt fRows (invIdx aCoefT[(i : ℕ)]!) (betaIdx (pTab i a)) <;>
    cases bitAt fRows (mulIdx (invIdx aCoefT[(i : ℕ)]!) (betaIdx (pTab i a))) aCoefT[iTab i a]! <;>
    decide

theorem lamCoch_eq (s : S) :
    lamCoch s = bigLam (incl s) + muCoch s + muCoch (betaS s) := by
  obtain ⟨a, ha, rfl⟩ := elt_surjective s
  have h := lambdaCheck_parts.2.2.2 _ ha
  rw [betaTab_get ha] at h
  rw [bigLam, Finset.sum_congr rfl fun i _ => cMul_e_elt i ha,
    sum_ite_xorFold (fun n => cBit n a) 4725, betaS_elt ha, lamCoch, muCoch, mk1_elt _ ha,
    mk1_elt _ ha, mk1_elt _ (betaIdx_lt ha)]
  revert h
  rw [show lamBit a = maskBit lamMask a from rfl, show muBit a = maskBit muMask a from rfl,
    show muBit (betaIdx a) = maskBit muMask (betaIdx a) from rfl]
  cases xorFold 4725 (fun i => cBit i a) <;> cases maskBit muMask a <;>
    cases maskBit muMask (betaIdx a) <;> cases maskBit lamMask a <;> decide

end CFSG.ComponentClassification.J2Cover.Models
