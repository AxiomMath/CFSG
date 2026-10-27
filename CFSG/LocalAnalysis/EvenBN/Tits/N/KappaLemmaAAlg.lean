module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaADefs
public import Certificates.Certificate561002

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix CFSG.LocalAnalysis.EvenBN.Tits.Model CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
open Certificates.KappaLemmaA (eqnMask eqnMask1 eqnMask2 eqnRhs combo maskTab modelOK comboOK
  table0OK table1OK prodEA)

@[expose] def kapA5 : Fin 3 → Matrix (Fin 5) (Fin 5) (ZMod 2) := Certificates.KappaLemmaA.kapA5

@[expose] def kapA4 (c : Fin 3) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => kapA5 c i.succ j.succ

@[expose] def tBase1 : Fin 64 → ZMod 2 := Certificates.KappaLemmaA.tBase1

@[expose] def tDir : Fin 64 → ZMod 2 := Certificates.KappaLemmaA.tDir

@[expose] def kapTc (s μ : ZMod 2) : Fin 64 → ZMod 2 := fun v => s * tBase1 v + μ * tDir v

theorem kapA5_zcol (c : Fin 3) (i : Fin 5) : kapA5 c i 0 = if i = 0 then 1 else 0 := by
  revert c i
  decide

theorem kapCheck_eq_true :
    Certificates.KappaLemmaA.check () = true :=
  Certificates.certificate561002

theorem kapCheck_parts :
    modelOK () = true ∧ comboOK () = true ∧ table0OK () = true ∧ table1OK () = true := by
  have h := kapCheck_eq_true
  simp only [Certificates.KappaLemmaA.check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem kapA_rep_prodEA
    (c : Fin 5 → ZMod 2) : Rep 1755 (prodEA c) (prodE c) :=
  rep_compA (rep_compA (rep_compA (rep_compA (rep_powA (rep_vA (by norm_num)) _)
    (rep_powA (rep_vA (by norm_num)) _)) (rep_powA (rep_vA (by norm_num)) _))
    (rep_powA (rep_vA (by norm_num)) _)) (rep_powA (rep_vA (by norm_num)) _)

theorem kapA_model_mem (c : Fin 3) :
    chainGen titsHArrs c.val ∈ titsH :=
  chainGen_H_mem c.isLt

theorem kapA_model_action
    (c : Fin 3) (j : Fin 5) :
    chainGen titsHArrs c.val * parrottV (basisV j) * (chainGen titsHArrs c.val)⁻¹ =
      prodE (fun i => kapA5 c i j) := by
  have h := kapCheck_parts.1
  simp only [modelOK, List.all_eq_true, List.mem_finRange, true_implies] at h
  have hh := chainGen_H_rep (i := c.val) c.isLt
  have hv : Rep 1755 (vA (12 - j.val)) (parrottV (12 - j.val)) := rep_vA (by omega)
  have key := eq_of_eqA (rep_compA hh hv) (rep_compA (kapA_rep_prodEA fun i => kapA5 c i j) hh)
    (h c j)
  rw [mul_inv_eq_iff_eq_mul]
  exact key

theorem kapA_expand {G : Type*} [Group G] (φ : G →* Multiplicative W4) (F : G → W4)
    (hF : ∀ g g', F (g * g') = F g + F g') (hker : ∀ g, φ g = 1 → F g = 0)
    (x : Fin 4 → G) (hx : ∀ k, φ (x k) = Multiplicative.ofAdd (Pi.single k 1)) (g : G) :
    F g = ∑ k, Multiplicative.toAdd (φ g) k • F (x k) := by
  have hF1 : F 1 = 0 := hker 1 (map_one φ)
  have hFpow : ∀ (y : G) (n : ℕ), F (y ^ n) = n • F y := by
    intro y n
    induction n with
    | zero => simp [hF1]
    | succ n ih => rw [pow_succ, hF, ih, succ_nsmul]
  have hs : ∀ (z : ZMod 2) (w : W4), z • w = z.val • w := fun z w => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  set a : W4 := Multiplicative.toAdd (φ g) with ha
  set g' : G := x 0 ^ (a 0).val * x 1 ^ (a 1).val * x 2 ^ (a 2).val * x 3 ^ (a 3).val with hg'
  have hφ : φ g' = φ g := by
    have e : (a 0).val • (Pi.single 0 1 : W4) + (a 1).val • (Pi.single 1 1 : W4) +
        (a 2).val • (Pi.single 2 1 : W4) + (a 3).val • (Pi.single 3 1 : W4) = a := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply]
      fin_cases i <;> simp [nsmul_eq_mul]
    rw [hg', map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hx, hx, hx, hx]
    simp only [← ofAdd_nsmul, ← ofAdd_add]
    rw [e]
    exact ofAdd_toAdd (φ g)
  have hFg : F g = F g' := by
    have hk : φ (g'⁻¹ * g) = 1 := by
      refine mul_left_cancel (a := φ g') ?_
      rw [mul_one, ← map_mul, show g' * (g'⁻¹ * g) = g by group]
      exact hφ.symm
    have hgg : g = g' * (g'⁻¹ * g) := by group
    rw [hgg, hF, hker _ hk, add_zero]
  rw [hFg, hg']
  simp only [hF, hFpow, Fin.sum_univ_four, hs]

theorem kapA_rep {V J : Type*} [Group V] [Group J]
    (eb : V →* Multiplicative W4) (fb : J →* Multiplicative W4)
    (heb : Function.Surjective eb) (hfb : Function.Surjective fb) (B : V → J → W4)
    (hBx : ∀ x x' q, B (x * x') q = B x q + B x' q)
    (hBq : ∀ x q q', B x (q * q') = B x q + B x q')
    (hBe : ∀ x q, eb x = 1 → B x q = 0) (hBf : ∀ x q, fb q = 1 → B x q = 0) :
    ∃ T : Fin 64 → ZMod 2,
      ∀ x q, B x q = betaT T (Multiplicative.toAdd (eb x)) (Multiplicative.toAdd (fb q)) := by
  choose xs hxs using fun k : Fin 4 => heb (Multiplicative.ofAdd (Pi.single k 1))
  choose qs hqs using fun l : Fin 4 => hfb (Multiplicative.ofAdd (Pi.single l 1))
  let T : Fin 64 → ZMod 2 := fun w =>
    B (xs ⟨w.val / 4 % 4, by omega⟩) (qs ⟨w.val % 4, by omega⟩) ⟨w.val / 16, by omega⟩
  have hT : ∀ i k l : Fin 4, T (idx3 i k l) = B (xs k) (qs l) i := by
    intro i k l
    have hi := i.isLt
    have hk := k.isLt
    have hl := l.isLt
    have e1 : (⟨(idx3 i k l).val / 4 % 4, by omega⟩ : Fin 4) = k :=
      Fin.ext (by simp [idx3]; omega)
    have e2 : (⟨(idx3 i k l).val % 4, by omega⟩ : Fin 4) = l := Fin.ext (by simp [idx3]; omega)
    have e3 : (⟨(idx3 i k l).val / 16, by omega⟩ : Fin 4) = i :=
      Fin.ext (by simp [idx3]; omega)
    show B (xs ⟨(idx3 i k l).val / 4 % 4, _⟩) (qs ⟨(idx3 i k l).val % 4, _⟩)
      ⟨(idx3 i k l).val / 16, _⟩ = _
    rw [e1, e2, e3]
  refine ⟨T, fun x q => ?_⟩
  have hx := kapA_expand eb (fun x => B x q) (fun g g' => hBx g g' q)
    (fun g hg => hBe g q hg) xs hxs x
  have hB : ∀ k, B (xs k) q = ∑ l, Multiplicative.toAdd (fb q) l • B (xs k) (qs l) := fun k =>
    kapA_expand fb (fun q => B (xs k) q) (fun q q' => hBq (xs k) q q')
      (fun q hq => hBf (xs k) q hq) qs hqs q
  funext i
  rw [hx]
  simp only [hB, betaT, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem kapA_zmod_eq_add {x y z : ZMod 2} (h : x + y = z) : x = z + y := by
  revert x y z
  decide

theorem kapA_zmod_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem kapA_list_sum_dot {ι : Type*} (l : List ι) (f : ι → Fin 64 → ZMod 2)
    (T : Fin 64 → ZMod 2) : (l.map f).sum ⬝ᵥ T = (l.map fun x => f x ⬝ᵥ T).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, add_dotProduct, ih, List.map_cons, List.sum_cons]

theorem kapA_list_sum_apply {ι : Type*} (l : List ι) (f : ι → Fin 64 → ZMod 2) (w : Fin 64) :
    (l.map f).sum w = (l.map fun x => f x w).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, Pi.add_apply, ih, List.map_cons, List.sum_cons]

theorem kapA_maskTab_get {n : ℕ} (hn : n < 211) (w : Fin 64) :
    ((maskTab ())[n]!)[w.val]! = eqnMask n w := by
  rw [maskTab, getElem!_ofFn_of_lt _ hn, getElem!_ofFn_of_lt _ w.isLt]

theorem kapA_comboOK_spec (h : comboOK () = true) {v : Fin 64} (hv : v ≠ 1) :
    (∀ n ∈ combo[v.val]!, n < 211) ∧
    ((combo[v.val]!).map eqnMask).sum =
      (Pi.single v 1 : Fin 64 → ZMod 2) + tDir v • (Pi.single 1 1 : Fin 64 → ZMod 2) ∧
    ((combo[v.val]!).map eqnRhs).sum = tBase1 v := by
  simp only [comboOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h v with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h hv
  · have hlt : ∀ n ∈ combo[v.val]!, n < 211 := fun n hn => by simpa using h1 n hn
    refine ⟨hlt, ?_, h3⟩
    funext w
    rw [kapA_list_sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (congrArg List.sum (List.map_congr_left fun n hn =>
      (kapA_maskTab_get (hlt n hn) w).symm)).trans (h2 w)

theorem kapA_betaT_single_right (T : Fin 64 → ZMod 2) (a : W4) (l i : Fin 4) :
    betaT T a (Pi.single l 1) i = ∑ k, T (idx3 i k l) * a k := by
  unfold betaT
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single l]
  · simp
  · intro l' _ hl'
    simp [hl']
  · simp

theorem kapA_betaT_single_left (T : Fin 64 → ZMod 2) (k i : Fin 4) (b : W4) :
    betaT T (Pi.single k 1) b i = ∑ l, T (idx3 i k l) * b l := by
  unfold betaT
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [hk']
  · simp

theorem kapA_eqn1_sound {T : Fin 64 → ZMod 2}
    (h1 : ∀ (c : Fin 3) (a b' : W4),
      betaT T (kapA4 c *ᵥ a) b' = kapA4 c *ᵥ betaT T a ((kapA4 c)ᵀ *ᵥ b'))
    (c : Fin 3) (i k l : Fin 4) : eqnMask1 c i k l ⬝ᵥ T = 0 := by
  have h := congrFun (h1 c (Pi.single k 1) (Pi.single l 1)) i
  have hL : betaT T (kapA4 c *ᵥ Pi.single k 1) (Pi.single l 1) i =
      ∑ k₂, T (idx3 i k₂ l) * kapA4 c k₂ k := by
    rw [kapA_betaT_single_right]
    refine Finset.sum_congr rfl fun k₂ _ => ?_
    rw [Matrix.mulVec_single_one]
    rfl
  have hR : (kapA4 c *ᵥ betaT T (Pi.single k 1) ((kapA4 c)ᵀ *ᵥ Pi.single l 1)) i =
      ∑ j, kapA4 c i j * ∑ l₂, T (idx3 j k l₂) * kapA4 c l l₂ := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kapA_betaT_single_left]
    refine congrArg _ (Finset.sum_congr rfl fun l₂ _ => ?_)
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hL, hR] at h
  have hdot : eqnMask1 c i k l ⬝ᵥ T = ∑ k₂, kapA4 c k₂ k * T (idx3 i k₂ l) +
      ∑ j, ∑ l₂, kapA4 c i j * kapA4 c l l₂ * T (idx3 j k l₂) := by
    simp only [eqnMask1, add_dotProduct, sum_dotProduct, single_dotProduct]
    rfl
  have e1 : ∑ k₂, kapA4 c k₂ k * T (idx3 i k₂ l) = ∑ k₂, T (idx3 i k₂ l) * kapA4 c k₂ k :=
    Finset.sum_congr rfl fun k₂ _ => mul_comm _ _
  have e2 : ∑ j, ∑ l₂, kapA4 c i j * kapA4 c l l₂ * T (idx3 j k l₂) =
      ∑ j, kapA4 c i j * ∑ l₂, T (idx3 j k l₂) * kapA4 c l l₂ :=
    Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l₂ _ => by ring
  rw [hdot, e1, e2, h]
  exact kapA_zmod_add_self _

theorem kapA_eqn2_sound {T : Fin 64 → ZMod 2} {s : ZMod 2}
    (h2 : ∀ a b : W4, b ⬝ᵥ betaT T a b = s * (b ⬝ᵥ a)) (a b : W4) :
    eqnMask2 a b ⬝ᵥ T = s * ∑ i, a i * b i := by
  have hdot : eqnMask2 a b ⬝ᵥ T = ∑ i, ∑ k, ∑ l, b i * a k * b l * T (idx3 i k l) := by
    simp only [eqnMask2, sum_dotProduct, single_dotProduct]
    rfl
  have e : ∑ i, ∑ k, ∑ l, b i * a k * b l * T (idx3 i k l) = b ⬝ᵥ betaT T a b := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [betaT]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hdot, e, h2 a b]
  refine congrArg _ ?_
  unfold dotProduct
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem kapA_eqn_sound {T : Fin 64 → ZMod 2} {s : ZMod 2}
    (h1 : ∀ (c : Fin 3) (a b' : W4),
      betaT T (kapA4 c *ᵥ a) b' = kapA4 c *ᵥ betaT T a ((kapA4 c)ᵀ *ᵥ b'))
    (h2 : ∀ a b : W4, b ⬝ᵥ betaT T a b = s * (b ⬝ᵥ a)) (n : ℕ) :
    eqnMask n ⬝ᵥ T = s * eqnRhs n := by
  by_cases hn : n < 192
  · rw [eqnMask, dite_eq_left hn, eqnRhs, ite_eq_left hn, mul_zero]
    exact kapA_eqn1_sound h1 _ _ _ _
  · rw [eqnMask, dite_eq_right hn, eqnRhs, ite_eq_right hn]
    exact kapA_eqn2_sound h2 _ _

theorem kapA_classify (s : ZMod 2) (T : Fin 64 → ZMod 2)
    (h1 : ∀ (c : Fin 3) (a b' : W4),
      betaT T (kapA4 c *ᵥ a) b' = kapA4 c *ᵥ betaT T a ((kapA4 c)ᵀ *ᵥ b'))
    (h2 : ∀ a b : W4, b ⬝ᵥ betaT T a b = s * (b ⬝ᵥ a)) :
    ∃ μ : ZMod 2, T = kapTc s μ := by
  have hc := kapCheck_parts.2.1
  refine ⟨T 1, funext fun v => ?_⟩
  by_cases hv : v = 1
  · subst hv
    have e1 : tBase1 1 = 0 := by decide
    have e2 : tDir 1 = 1 := by decide
    simp [kapTc, e1, e2]
  · obtain ⟨-, hm, hr⟩ := kapA_comboOK_spec hc hv
    have e : ((combo[v.val]!).map eqnMask).sum ⬝ᵥ T = s * tBase1 v := by
      rw [kapA_list_sum_dot, List.map_congr_left (fun n _ => kapA_eqn_sound h1 h2 n),
        List.sum_map_mul_left, hr]
    rw [hm] at e
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul] at e
    rw [kapA_zmod_eq_add e, kapTc]
    ring

theorem kapA_table0 (μ : ZMod 2) (a : W4) (ha : a 3 = 0) :
    betaT (kapTc 0 μ) a b0 = μ • ![a 1 + a 2, a 2, 0, 0] := by
  have h := kapCheck_parts.2.2.1
  simp only [table0OK, decide_eq_true_eq] at h
  have h' := h μ (a 0) (a 1) (a 2)
  have e : (![a 0, a 1, a 2, 0] : W4) = a := by
    funext i
    fin_cases i <;> simp [ha]
  rw [e] at h'
  exact h'

theorem kapA_table1 (μ : ZMod 2) :
    betaT (kapTc 1 μ) ![0, 0, 1, 0] b0 2 = 1 := by
  have h := kapCheck_parts.2.2.2
  simp only [table1OK, decide_eq_true_eq] at h
  exact h μ

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
