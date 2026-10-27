module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Elements
public import CFSG.RankThree.SubgroupLists.CliffordPrime

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

variable {F : Type} [Field F] {L : Fin 3 → Submodule F (Fin 3 → F)}

private theorem translate_mul (g h : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)) :
    translate (g * h) W = translate g (translate h W) := by
  simp only [CFSG.RankThree.SubgroupLists.translate, Units.val_mul, Matrix.toLin'_mul,
    Submodule.map_comp]

private theorem translate_one (W : Submodule F (Fin 3 → F)) :
    translate (1 : GL (Fin 3) F) W = W := by
  simp [CFSG.RankThree.SubgroupLists.translate]

private theorem injective_of_finrank (hi : DirectSum.IsInternal L)
    (h1 : ∀ i, Module.finrank F (L i) = 1) : Function.Injective L :=
  hi.submodule_iSupIndep.injective fun i h => by
    have := h1 i
    rw [h, finrank_bot] at this
    exact zero_ne_one this

open Classical in
private noncomputable def lineMap (L : Fin 3 → Submodule F (Fin 3 → F)) (g : GL (Fin 3) F)
    (i : Fin 3) : Fin 3 :=
  if h : ∃ j, translate g (L i) = L j then h.choose else i

private theorem translate_lineMap {g : GL (Fin 3) F} {i : Fin 3}
    (h : ∃ j, translate g (L i) = L j) : translate g (L i) = L (lineMap L g i) := by
  rw [lineMap, dif_pos h]
  exact h.choose_spec

private theorem lineMap_mul (hinj : Function.Injective L) {g h : GL (Fin 3) F}
    (hg : ∀ i, ∃ j, translate g (L i) = L j) (hh : ∀ i, ∃ j, translate h (L i) = L j) :
    lineMap L (g * h) = lineMap L g ∘ lineMap L h := by
  funext i
  have hgh : ∃ j, translate (g * h) (L i) = L j :=
    ⟨_, by rw [translate_mul, translate_lineMap (hh i), translate_lineMap (hg _)]⟩
  apply hinj
  rw [← translate_lineMap hgh, translate_mul, translate_lineMap (hh i), translate_lineMap (hg _)]
  rfl

private theorem lineMap_one (hinj : Function.Injective L) :
    lineMap L (1 : GL (Fin 3) F) = id := by
  funext i
  apply hinj
  rw [← translate_lineMap (L := L) ⟨i, translate_one _⟩, translate_one]
  rfl

private theorem translate_eq_of_lineMap_eq_id {g : GL (Fin 3) F}
    (hg : ∀ i, ∃ j, translate g (L i) = L j) (h : lineMap L g = id) (i : Fin 3) :
    translate g (L i) = L i := by
  rw [translate_lineMap (hg i), h]
  rfl

private theorem exists_gen {W : Submodule F (Fin 3 → F)} (h : Module.finrank F W = 1) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ W, ∃ c : F, c • v = u := by
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h
  refine ⟨v, v.2, fun h0 => hv (Subtype.ext h0), fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨u, hu⟩
  exact ⟨c, congrArg Subtype.val hc⟩

private theorem exists_eigen_of_translate_eq {W : Submodule F (Fin 3 → F)}
    (h1 : Module.finrank F W = 1) {g : GL (Fin 3) F} (hg : translate g W = W) :
    ∃ v ≠ 0, ∃ c : F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v := by
  obtain ⟨v, hvW, hv0, hall⟩ := exists_gen h1
  obtain ⟨c, hc⟩ := hall _ (hg ▸ mulVec_mem_translate hvW)
  exact ⟨v, hv0, c, hc.symm⟩

private theorem mul_comm_of_translate_eq (hi : DirectSum.IsInternal L)
    (h1 : ∀ i, Module.finrank F (L i) = 1) {g h : GL (Fin 3) F}
    (hg : ∀ i, translate g (L i) = L i) (hh : ∀ i, translate h (L i) = L i) :
    (g : Matrix (Fin 3) (Fin 3) F) * h = h * g := by
  choose v hvL hv0 hvall using fun i => exists_gen (h1 i)
  have eig : ∀ x : GL (Fin 3) F, (∀ i, translate x (L i) = L i) →
      ∀ i, ∃ c : F, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v i = c • v i := fun x hx i => by
    obtain ⟨c, hc⟩ := hvall i _ ((hx i) ▸ mulVec_mem_translate (hvL i))
    exact ⟨c, hc.symm⟩
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    rw [Submodule.span_range_eq_iSup, ← hi.submodule_iSup_eq_top]
    congr 1
    funext i
    refine le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr (hvL i)) fun u hu => ?_
    obtain ⟨c, rfl⟩ := hvall i u hu
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  apply Matrix.toLin'.injective
  refine LinearMap.ext_on_range hspan fun i => ?_
  obtain ⟨a, ha⟩ := eig g hg i
  obtain ⟨b, hb⟩ := eig h hh i
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb, Matrix.mulVec_smul, smul_smul,
    mul_comm a b]

private theorem klein_fin_three : ∀ x y : Fin 3 → Fin 3, x ∘ x = id → y ∘ y = id →
    (x ∘ y) ∘ (x ∘ y) = id → x = id ∨ y = id ∨ x ∘ y = id := by
  decide

private theorem iterate_six_fin_three : ∀ f g : Fin 3 → Fin 3, f ∘ g = id → f^[6] = id := by
  decide

private theorem exists_fix_of_klein (hinj : Function.Injective L)
    {G : Subgroup (GL (Fin 3) F)} (hG : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j)
    {a b : GL (Fin 3) F} (ha : a ∈ G) (hb : b ∈ G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab2 : (a * b) * (a * b) = 1) :
    lineMap L a = id ∨ lineMap L b = id ∨ lineMap L (a * b) = id := by
  have hm : ∀ x ∈ G, ∀ y ∈ G, lineMap L (x * y) = lineMap L x ∘ lineMap L y :=
    fun x hx y hy => lineMap_mul hinj (hG x hx) (hG y hy)
  have hab := G.mul_mem ha hb
  rw [hm a ha b hb]
  refine klein_fin_three _ _ ?_ ?_ ?_
  · rw [← hm a ha a ha, ha2, lineMap_one hinj]
  · rw [← hm b hb b hb, hb2, lineMap_one hinj]
  · rw [← hm a ha b hb, ← hm _ hab _ hab, hab2, lineMap_one hinj]

private theorem pow_reduce {ω : F} (h : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 ∧ ω ^ 4 = ω ∧ ω ^ 6 = 1 ∧ ω ^ 8 = ω ^ 2 ∧ ω ^ 2 = -ω - 1 := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * h
  refine ⟨h3, by linear_combination ω * h3, by linear_combination (ω ^ 3 + 1) * h3,
    by linear_combination (ω ^ 5 + ω ^ 2) * h3, by linear_combination h⟩

private theorem fin_sub_val : ∀ i j : Fin 3, (i - j).val = (i.val + 3 - j.val) % 3 := by
  decide

private theorem fourierMat_mul (hF3 : (3 : F) ≠ 0) {ω : F} (h : ω ^ 2 + ω + 1 = 0) :
    fourierMat ω 0 * fourierMat ω 1 = fourierMat ω 2 := by
  obtain ⟨h3, h4, -, -, h2⟩ := pow_reduce h
  ext i j
  simp only [fourierMat, Matrix.mul_apply, Fin.sum_univ_three, fin_sub_val]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf <;>
    (try simp only [h4, h2]) <;> ring_nf

private theorem fourierMat_mul_self (hF3 : (3 : F) ≠ 0) {ω : F} (h : ω ^ 2 + ω + 1 = 0)
    (k : Fin 3) : fourierMat ω k * fourierMat ω k = 1 := by
  obtain ⟨h3, h4, h6, h8, h2⟩ := pow_reduce h
  ext i j
  simp only [fourierMat, Matrix.mul_apply, Fin.sum_univ_three, fin_sub_val, Matrix.one_apply]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf <;>
    (try simp only [h3, h4, h6, h8, h2]) <;> ring_nf

private theorem diagSign_mul_self (i : Fin 3) :
    (diagSign i : GL (Fin 3) F) * diagSign i = 1 := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [diagSign, diagThree]

private theorem diagSign_zero_mul_one :
    (diagSign 0 : GL (Fin 3) F) * diagSign 1 = diagSign 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagSign, diagThree]

theorem false_of_isTransitiveMonomial_of_fourier {F : Type} [Field F] (hF2 : (2 : F) ≠ 0)
    (hF3 : (3 : F) ≠ 0) {ω : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) {G : Subgroup (GL (Fin 3) F)}
    (hG : IsTransitiveMonomial G) (hd : ∀ i : Fin 3, diagSign i ∈ G)
    (hf : ∀ k : Fin 3, ∃ d ∈ G, (d : Matrix (Fin 3) (Fin 3) F) = fourierMat (ω : F) k) :
    False := by
  obtain ⟨L, hi, h1, hpres, -⟩ := hG
  have hinj := injective_of_finrank hi h1
  have hω2 : (ω : F) ^ 2 + ω + 1 = 0 := by
    have h3 : (ω : F) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    have hne : (ω : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hω (Units.ext h)
    exact (mul_eq_zero.mp (by linear_combination h3 : ((ω : F) - 1) * _ = 0)).resolve_left hne
  choose f hfG hf using hf
  obtain ⟨i, hi'⟩ : ∃ i, lineMap L (diagSign i : GL (Fin 3) F) = id := by
    rcases exists_fix_of_klein hinj hpres (hd 0) (hd 1) (diagSign_mul_self 0)
      (diagSign_mul_self 1) (by rw [diagSign_zero_mul_one, diagSign_mul_self]) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, diagSign_zero_mul_one (F := F) ▸ h⟩
  have hf2 : ∀ k, f k * f k = 1 := fun k =>
    Units.ext (by rw [Units.val_mul, hf, fourierMat_mul_self hF3 hω2, Units.val_one])
  have hf01 : f 0 * f 1 = f 2 :=
    Units.ext (by rw [Units.val_mul, hf, hf, hf, fourierMat_mul hF3 hω2])
  obtain ⟨k, hk⟩ : ∃ k, lineMap L (f k) = id := by
    rcases exists_fix_of_klein hinj hpres (hfG 0) (hfG 1) (hf2 0) (hf2 1)
      (by rw [hf01, hf2]) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, hf01 ▸ h⟩
  apply diagSign_mul_fourierMat_ne hF2 hF3 hω hω3 i k
  rw [← hf k]
  exact mul_comm_of_translate_eq hi h1 (translate_eq_of_lineMap_eq_id (hpres _ (hd i)) hi')
    (translate_eq_of_lineMap_eq_id (hpres _ (hfG k)) hk)

theorem false_of_isTransitiveMonomial_of_noEigen {F : Type} [Field F]
    {G : Subgroup (GL (Fin 3) F)} (hG : IsTransitiveMonomial G) {y : GL (Fin 3) F} (hy : y ∈ G)
    {r : ℕ} (_hr : r.Prime) (hr6 : Nat.Coprime r 6) (hyr : orderOf y = r)
    (hno : ∀ (v : Fin 3 → F) (c : F), (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v → v = 0) :
    False := by
  obtain ⟨L, hi, h1, hpres, -⟩ := hG
  have hinj := injective_of_finrank hi h1
  have hm : ∀ x ∈ G, ∀ z ∈ G, lineMap L (x * z) = lineMap L x ∘ lineMap L z :=
    fun x hx z hz => lineMap_mul hinj (hpres x hx) (hpres z hz)
  have hpow : ∀ n : ℕ, lineMap L (y ^ n) = (lineMap L y)^[n] := by
    intro n
    induction n with
    | zero => rw [pow_zero, lineMap_one hinj, Function.iterate_zero]
    | succ n ih => rw [pow_succ, hm _ (G.pow_mem hy n) _ hy, ih, Function.iterate_succ]
  have hr1 : (lineMap L y)^[r] = id := by
    rw [← hpow, ← hyr, pow_orderOf_eq_one, lineMap_one hinj]
  have h6 : (lineMap L y)^[6] = id := iterate_six_fin_three _ (lineMap L y⁻¹) (by
    rw [← hm _ hy _ (G.inv_mem hy), mul_inv_cancel, lineMap_one hinj])
  have hid : lineMap L y = id := by
    funext x
    have := Function.IsPeriodicPt.gcd (congrFun hr1 x) (congrFun h6 x)
    rw [Nat.Coprime.gcd_eq_one hr6] at this
    exact this
  obtain ⟨v, hv0, c, hc⟩ :=
    exists_eigen_of_translate_eq (h1 0) (translate_eq_of_lineMap_eq_id (hpres y hy) hid 0)
  exact hv0 (hno v c hc)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
