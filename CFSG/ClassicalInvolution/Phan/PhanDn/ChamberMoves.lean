module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers
public import CFSG.ClassicalInvolution.Phan.PhanDn.FrameAdjacency
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.Frames.Product
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {m n : ℕ}

theorem FlipFrame.elt_zero (c : FlipFrame σ (m + 1)) (hm : 2 ≤ m) :
    c.elt 0 = c.line 0 := by
  have h : (0 : Fin (m + 1)) + 1 < m := by
    show (1 : ℕ) < m
    omega
  rw [c.elt_of_add_one_lt 0 h]
  change c.sub 1 = c.line 0
  rw [c.sub_succ (j := 0) (by omega), c.sub_zero, bot_sup_eq]
  rfl

theorem FlipFrame.elt_one (c : FlipFrame σ (m + 1)) (hm : 3 ≤ m) :
    c.elt 1 = c.line 0 ⊔ c.line 1 := by
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have h : (1 : Fin (m + 1)) + 1 < m := by
    rw [hv1]
    omega
  rw [c.elt_of_add_one_lt 1 h, hv1]
  change c.sub 2 = c.line 0 ⊔ c.line 1
  rw [c.sub_succ (j := 1) (by omega), c.sub_succ (j := 0) (by omega),
    c.sub_zero, bot_sup_eq]
  have h0i : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by ext; simp
  have h1i : (⟨1, by omega⟩ : Fin (m + 1)) = 1 := by
    ext
    simpa using hv1.symm
  rw [h0i, h1i]

theorem DChamber.eq_of_elt_eq (hσ : ∀ x, σ (σ x) = x) {c d : DChamber σ (m + 1)}
    (h : ∀ i, c.elt i = d.elt i) : c = d := by
  apply DChamber.ext
  exact congrArg FlipFrame.line
    (FlipFrame.eq_of_elt_eq hσ (c := c.toFlipFrame) (d := d.toFlipFrame) h)

theorem DChamber.eq_of_adj_zero (hσ : ∀ x, σ (σ x) = x) (hm : 2 ≤ m)
    {c d : DChamber σ (m + 1)} (h : (dChamberSystem σ m).adj 0 c d)
    (h0 : c.line 0 = d.line 0) : c = d := by
  rw [dChamberSystem_adj_iff] at h
  apply DChamber.eq_of_elt_eq hσ
  intro i
  by_cases hi : i = 0
  · rw [hi, FlipFrame.elt_zero c.toFlipFrame hm, FlipFrame.elt_zero d.toFlipFrame hm, h0]
  · exact h i hi

theorem even_finrank_map_inf_stdLag_iff
    {L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hL : ∀ y, quadPlus n K (L y) = quadPlus n K y)
    (hfam : Even (n - Module.finrank K
      ↥((stdLag n K).map L.toLinearMap ⊓ stdLag n K)))
    {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : (quadPlusForm n K).IsLagrangian W) :
    Even (n - Module.finrank K ↥(W.map L.toLinearMap ⊓ stdLag n K)) ↔
      Even (n - Module.finrank K ↥(W ⊓ stdLag n K)) := by
  have hQ : ∀ v, (quadPlusForm n K).Q (L.toLinearMap v) = (quadPlusForm n K).Q v := by
    intro v
    rw [show (quadPlusForm n K).Q = ⇑(quadPlus n K) from (coe_quadPlus n K).symm]
    exact hL v
  have hWL : (quadPlusForm n K).IsLagrangian (W.map L.toLinearMap) := hW.map hQ
  have hSL : (quadPlusForm n K).IsLagrangian ((stdLag n K).map L.toLinearMap) :=
    (isLagrangian_stdLag n K).map hQ
  have hZ : (quadPlusForm n K).IsLagrangian (stdLag n K) := isLagrangian_stdLag n K
  have hmap : W.map L.toLinearMap ⊓ (stdLag n K).map L.toLinearMap =
      (W ⊓ stdLag n K).map L.toLinearMap :=
    (Submodule.map_inf L.toLinearMap L.injective).symm
  have hP : n - Module.finrank K
      ↥(W.map L.toLinearMap ⊓ (stdLag n K).map L.toLinearMap) =
      n - Module.finrank K ↥(W ⊓ stdLag n K) := by
    rw [hmap, LinearEquiv.finrank_map_eq]
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm n K)
    (finrank_flipSpace n K) hWL hSL hZ
  rw [hP] at hpar
  have hCF : Even ((n - Module.finrank K ↥(W ⊓ stdLag n K)) +
      (n - Module.finrank K
        ↥((stdLag n K).map L.toLinearMap ⊓ stdLag n K))) ↔
      Even (n - Module.finrank K ↥(W ⊓ stdLag n K)) := by
    rw [Nat.even_add]
    simp [hfam]
  rw [Nat.even_add, hCF] at hpar
  exact hpar.symm

def FlipFrame.ofOrthonormal (v : Fin n → (Fin n ⊕ Fin n → K))
    (hQ : ∀ i, quadPlus n K (v i) = 0)
    (hpol : ∀ i j, i ≠ j → polar (quadPlus n K) (v i) (v j) = 0)
    (hh : ∀ i j, flipHerm σ (v i) (v j) = if i = j then 1 else 0) : FlipFrame σ n where
  line i := K ∙ v i
  isFlipflopPt_line i := by
    have hne : v i ≠ 0 := by
      intro h0
      have h1 : (0 : K) = 1 := by simpa [h0] using hh i i
      exact zero_ne_one h1
    refine ⟨⟨?_, ?_⟩, finrank_span_singleton hne⟩
    · intro u hu
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [QuadraticMap.map_smul, smul_eq_mul, hQ i, mul_zero]
    · intro u hu hper
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      have h := hper (v i) (Submodule.mem_span_singleton_self _)
      rw [flipHerm_smul_left, hh i i, if_pos rfl, mul_one] at h
      rw [h, zero_smul]
  polar_eq_zero i j hij u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpol i j hij]
    simp
  flipHerm_eq_zero i j hij u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [flipHerm_smul_left, flipHerm_smul_right, hh i j, if_neg hij]
    simp

theorem DChamber.exists_line_zero_eq (hσ : IsUnitaryInvolution σ) {k : ℕ} (hk : 1 ≤ k)
    {x : Submodule K (Fin (k + 1) ⊕ Fin (k + 1) → K)} (hx : IsFlipflopPt σ x) :
    ∃ c : DChamber σ (k + 1), c.line 0 = x := by
  have hxsub : IsFlipflopSub σ x := hx.1
  have hxdim : Module.finrank K x = 1 := hx.2
  obtain ⟨M, -, hM, -, hxM, -, hMeven, -⟩ :=
    hxsub.exists_solid_le hσ (by rw [hxdim]; omega)
  have hxne : x ≠ ⊥ := by
    intro hbot
    have h := hxdim
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hxne
  have hxu : x = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hxdim hu hu0
  have huu : flipHerm σ u u ≠ 0 := by
    intro h0
    apply hu0
    refine hxsub.nondeg u hu ?_
    intro w hw
    rw [hxu] at hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_right, h0, mul_zero]
  have hfixinv : σ ((flipHerm σ u u)⁻¹) = (flipHerm σ u u)⁻¹ := by
    rw [map_inv₀, flipHerm_self_mem_fixed hσ.invol u]
  obtain ⟨a, ha⟩ := hσ.norm_surj ((flipHerm σ u u)⁻¹) hfixinv (inv_ne_zero huu)
  let v0 : Fin (k + 1) ⊕ Fin (k + 1) → K := a • u
  have hv0Q : quadPlus (k + 1) K v0 = 0 := by
    rw [show v0 = a • u from rfl, QuadraticMap.map_smul, smul_eq_mul,
      hxsub.total u hu, mul_zero]
  have hv0h : flipHerm σ v0 v0 = 1 := by
    rw [show v0 = a • u from rfl, flipHerm_smul_left, flipHerm_smul_right,
      ← mul_assoc, mul_comm a (σ a), ha, inv_mul_cancel₀ huu]
  have hv00 : v0 ≠ 0 := by
    intro h0
    rw [h0, flipHerm_zero_right] at hv0h
    exact zero_ne_one hv0h
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ha
    exact huu (inv_eq_zero.mp ha.symm)
  have hxv0 : x = K ∙ v0 := by
    rw [hxu, show v0 = a • u from rfl,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha0) u]
  have hxM' : K ∙ v0 ≤ M := hxv0 ▸ hxM
  have hv0M : v0 ∈ M := hxM' (Submodule.mem_span_singleton_self v0)
  have hha : flipHerm σ v0 v0 ≠ 0 := by rw [hv0h]; exact one_ne_zero
  let N : Submodule K (Fin (k + 1) ⊕ Fin (k + 1) → K) :=
    M ⊓ flipOrth σ (K ∙ v0)
  have hNsub : IsFlipflopSub σ N := hM.1.inf_flipOrth_span hσ.invol hv0M hha
  have hspanN : K ∙ v0 ⊔ N = M := span_sup_inf_flipOrth hσ.invol hv0M hha
  have hdisj : Disjoint (K ∙ v0) N := (disjoint_span_flipOrth hha).mono_right inf_le_right
  have hNdim : Module.finrank K N = k := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ v0) N
    rw [hdisj.eq_bot, finrank_bot, add_zero, hspanN, hM.2,
      finrank_span_singleton hv00] at h
    omega
  obtain ⟨b, hb⟩ := exists_orthonormal_basis hσ.invol hσ.exists_ne
    (fun d hd hd0 => by
      obtain ⟨c, hc⟩ := hσ.norm_surj d hd hd0
      exact ⟨c, by rwa [mul_comm]⟩) hNsub
  let B : Module.Basis (Fin k) K N := b.reindex (finCongr hNdim)
  have hB : ∀ i j, flipHerm σ ((B i : N) : Fin (k + 1) ⊕ Fin (k + 1) → K)
      ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K) = if i = j then 1 else 0 := by
    intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp
  have hpolarM : ∀ p ∈ M, ∀ q ∈ M, polar (quadPlus (k + 1) K) p q = 0 := by
    intro p hp q hq
    have h := QuadraticMap.map_add (quadPlus (k + 1) K) p q
    rw [hM.1.total (p + q) (Submodule.add_mem _ hp hq), hM.1.total p hp,
      hM.1.total q hq] at h
    simpa using h.symm
  have hbN : ∀ j, flipHerm σ v0 ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K) = 0 :=
    fun j => mem_flipOrth_span_singleton.mp (Submodule.mem_inf.mp (B j).2).2
  let v : Fin (k + 1) → (Fin (k + 1) ⊕ Fin (k + 1) → K) :=
    Fin.cons v0 fun j => (B j : Fin (k + 1) ⊕ Fin (k + 1) → K)
  have hQv : ∀ i, quadPlus (k + 1) K (v i) = 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [v] using hv0Q
    · intro j
      simpa [v] using hNsub.total (B j : N) (B j).2
  have hpolv : ∀ i j, i ≠ j → polar (quadPlus (k + 1) K) (v i) (v j) = 0 := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · intro hij
        exact (hij rfl).elim
      · intro l _
        exact hpolarM v0 hv0M ((B l : N) : _) (Submodule.mem_inf.mp (B l).2).1
    · intro l
      refine Fin.cases ?_ ?_ j
      · intro _
        exact hpolarM ((B l : N) : _) (Submodule.mem_inf.mp (B l).2).1 v0 hv0M
      · intro m _
        exact hpolarM ((B l : N) : _) (Submodule.mem_inf.mp (B l).2).1
          ((B m : N) : _) (Submodule.mem_inf.mp (B m).2).1
  have hhv : ∀ i j, flipHerm σ (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simpa [v] using hv0h
      · intro l
        rw [show v 0 = v0 from rfl, show v (Fin.succ l) = (B l : N) from rfl, hbN l,
          if_neg (Fin.succ_ne_zero l).symm]
    · intro l
      refine Fin.cases ?_ ?_ j
      · rw [show v 0 = v0 from rfl, show v (Fin.succ l) = (B l : N) from rfl,
          if_neg (Fin.succ_ne_zero l)]
        exact (flipHerm_eq_zero_iff hσ.invol).mpr (hbN l)
      · intro m
        simpa [v] using hB l m
  let f : FlipFrame σ (k + 1) := FlipFrame.ofOrthonormal v hQv hpolv hhv
  have hNspan : Submodule.span K (Set.range fun j : Fin k =>
      ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K)) = N := by
    have h := congrArg (Submodule.map N.subtype) B.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
    have hrange : Set.range (fun j : Fin k =>
        ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K)) =
        Subtype.val '' Set.range (⇑B) := Set.range_comp _ _
    rw [hrange]
    exact h
  have hsup : (Finset.univ.sup fun j : Fin k =>
      K ∙ ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K)) = N := by
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_true]
    rw [← Submodule.span_range_eq_iSup]
    exact hNspan
  have hspan : f.spanAt Finset.univ = M := by
    rw [FlipFrame.spanAt, Fin.univ_succ, Finset.sup_cons, Finset.sup_map]
    change K ∙ v 0 ⊔ (Finset.univ.sup fun j : Fin k => K ∙ v (Fin.succ j)) = M
    have hvs : (fun j : Fin k => K ∙ v (Fin.succ j)) =
        fun j => K ∙ ((B j : N) : Fin (k + 1) ⊕ Fin (k + 1) → K) := by
      funext j
      simp [v]
    rw [show v 0 = v0 from rfl, hvs, hsup, hspanN]
  let c : DChamber σ (k + 1) :=
    { toFlipFrame := f
      even_ruling := by
        rw [hspan]
        exact hMeven }
  refine ⟨c, ?_⟩
  change K ∙ v 0 = x
  rw [show v 0 = v0 from rfl, hxv0]

private theorem flipHerm_self_ne_zero_of_isFlipflopPt {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) {a : Fin n ⊕ Fin n → K} (ha : a ∈ p) (ha0 : a ≠ 0) :
    flipHerm σ a a ≠ 0 := by
  intro h0
  have hline : p = K ∙ a :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp.2 ha ha0
  apply ha0
  refine hp.1.nondeg a ha ?_
  intro w hw
  rw [hline] at hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [flipHerm_smul_right, h0, mul_zero]

private theorem isFlipflopPt_inf_flipOrth_of_finrank_two (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U)
    (hU2 : Module.finrank K U = 2) {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) (hpU : p ≤ U) :
    IsFlipflopPt σ (U ⊓ flipOrth σ p) := by
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h := hp.2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hpa : p = K ∙ a :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp.2 ha ha0
  have haa : flipHerm σ a a ≠ 0 := flipHerm_self_ne_zero_of_isFlipflopPt hp ha ha0
  have haU : a ∈ U := hpU (hpa.symm ▸ Submodule.mem_span_singleton_self a)
  have hsub : IsFlipflopSub σ (U ⊓ flipOrth σ p) := by
    rw [hpa]
    exact hU.inf_flipOrth_span hσ haU haa
  have hsplit : K ∙ a ⊔ (U ⊓ flipOrth σ p) = U := by
    rw [hpa]
    exact span_sup_inf_flipOrth hσ haU haa
  have hdisj : Disjoint (K ∙ a) (U ⊓ flipOrth σ p) := by
    rw [hpa]
    exact (disjoint_span_flipOrth haa).mono_right inf_le_right
  have hdim : Module.finrank K ↥(U ⊓ flipOrth σ p) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) (U ⊓ flipOrth σ p)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hsplit, hU2,
      finrank_span_singleton ha0] at h
    omega
  exact ⟨hsub, hdim⟩

theorem DChamber.exists_adj_zero_line_eq (hσ : ∀ x, σ (σ x) = x) (hm : 1 ≤ m)
    (c : DChamber σ (m + 1)) {x : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hx : IsFlipflopPt σ x) (hxle : x ≤ c.line 0 ⊔ c.line 1) :
    ∃ d, (dChamberSystem σ m).adj 0 c d ∧ d.line 0 = x := by
  let k : Fin m := ⟨0, hm⟩
  have hk0 : k.castSucc = (0 : Fin (m + 1)) := Fin.ext rfl
  have hk1 : k.succ = (1 : Fin (m + 1)) := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_one']
    simp [k]
    exact (Nat.mod_eq_of_lt (show 1 < m + 1 by omega)).symm
  have hUeq : c.line 0 ⊔ c.line 1 = c.sub 2 := by
    have h := c.line_sup_line_eq hσ k
    rw [FlipFrame.sub_zero, flipOrth_bot, top_inf_eq, hk0, hk1] at h
    exact h
  let U := c.sub 2
  have hUsub : IsFlipflopSub σ U := c.isFlipflopSub_sub hσ 2
  have hU2 : Module.finrank K U = 2 := c.finrank_sub (by omega)
  have hxleU : x ≤ U := by
    rw [show U = c.line 0 ⊔ c.line 1 from hUeq.symm]
    exact hxle
  let L1 : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := U ⊓ flipOrth σ x
  have hL1 : IsFlipflopPt σ L1 :=
    isFlipflopPt_inf_flipOrth_of_finrank_two hσ hUsub hU2 hx hxleU
  have hL1U : L1 ≤ U := inf_le_left
  have hdisj : Disjoint x L1 := by
    rw [Submodule.disjoint_def]
    intro v hvx hvL
    have hvflip : v ∈ flipOrth σ x := (inf_le_right : L1 ≤ flipOrth σ x) hvL
    refine hx.1.nondeg v hvx ?_
    intro w hw
    exact (flipHerm_eq_zero_iff hσ).mpr (mem_flipOrth.mp hvflip w hw)
  have hdimsup : Module.finrank K ↥(x ⊔ L1) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq x L1
    rw [hdisj.eq_bot, finrank_bot, add_zero, hx.2, hL1.2] at h
    omega
  have hsplit : x ⊔ L1 = U :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hxleU hL1U) (by rw [hdimsup, hU2])
  let dline : Fin (m + 1) → Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    Function.update (Function.update c.line 0 x) 1 L1
  have h01 : (0 : Fin (m + 1)) ≠ 1 := by
    simp
    omega
  have hd0 : dline 0 = x := by
    dsimp only [dline]
    rw [Function.update_of_ne h01]
    rw [Function.update_self]
  have hd1 : dline 1 = L1 := by
    dsimp only [dline]
    rw [Function.update_self]
  have hdj : ∀ j, j ≠ 0 → j ≠ 1 → dline j = c.line j := by
    intro j hj0 hj1
    dsimp only [dline]
    rw [Function.update_of_ne hj1, Function.update_of_ne hj0]
  have hpolarU : ∀ p ∈ U, ∀ q ∈ U, polar (quadPlus (m + 1) K) p q = 0 := by
    intro p hp q hq
    have h := QuadraticMap.map_add (quadPlus (m + 1) K) p q
    rw [hUsub.total (p + q) (Submodule.add_mem _ hp hq), hUsub.total p hp,
      hUsub.total q hq] at h
    simpa using h.symm
  have hUorth : ∀ j, j ≠ 0 → j ≠ 1 → ∀ z ∈ U, ∀ w ∈ c.line j,
      polar (quadPlus (m + 1) K) z w = 0 ∧ flipHerm σ z w = 0 := by
    intro j hj0 hj1 z hz w hw
    have hz' : z ∈ c.line 0 ⊔ c.line 1 := hUeq ▸ hz
    obtain ⟨z0, hz0, z1, hz1, rfl⟩ := Submodule.mem_sup.mp hz'
    constructor
    · rw [QuadraticMap.polar_add_left,
        c.polar_eq_zero 0 j (fun h => hj0 h.symm) z0 hz0 w hw,
        c.polar_eq_zero 1 j (fun h => hj1 h.symm) z1 hz1 w hw]
      simp
    · rw [flipHerm_add_left,
        c.flipHerm_eq_zero 0 j (fun h => hj0 h.symm) z0 hz0 w hw,
        c.flipHerm_eq_zero 1 j (fun h => hj1 h.symm) z1 hz1 w hw]
      simp
  let f : FlipFrame σ (m + 1) :=
    { line := dline
      isFlipflopPt_line := fun i => by
        by_cases hi0 : i = 0
        · rw [hi0, hd0]
          exact hx
        · by_cases hi1 : i = 1
          · rw [hi1, hd1]
            exact hL1
          · rw [hdj i hi0 hi1]
            exact c.isFlipflopPt_line i
      polar_eq_zero := fun i j hij u hu v hv => by
        by_cases hi0 : i = 0
        · rw [hi0, hd0] at hu
          by_cases hj1 : j = 1
          · rw [hj1, hd1] at hv
            exact hpolarU u (hxleU hu) v (hL1U hv)
          · have hj0 : j ≠ 0 := fun h => hij (hi0.trans h.symm)
            rw [hdj j hj0 hj1] at hv
            exact (hUorth j hj0 hj1 u (hxleU hu) v hv).1
        · by_cases hi1 : i = 1
          · rw [hi1, hd1] at hu
            by_cases hj0 : j = 0
            · rw [hj0, hd0] at hv
              rw [QuadraticMap.polar_comm]
              exact hpolarU v (hxleU hv) u (hL1U hu)
            · have hj1 : j ≠ 1 := fun h => hij (hi1.trans h.symm)
              rw [hdj j hj0 hj1] at hv
              exact (hUorth j hj0 hj1 u (hL1U hu) v hv).1
          · by_cases hj0 : j = 0
            · rw [hj0, hd0] at hv
              rw [hdj i hi0 hi1] at hu
              rw [QuadraticMap.polar_comm]
              exact (hUorth i hi0 hi1 v (hxleU hv) u hu).1
            · by_cases hj1 : j = 1
              · rw [hj1, hd1] at hv
                rw [hdj i hi0 hi1] at hu
                rw [QuadraticMap.polar_comm]
                exact (hUorth i hi0 hi1 v (hL1U hv) u hu).1
              · rw [hdj i hi0 hi1] at hu
                rw [hdj j hj0 hj1] at hv
                exact c.polar_eq_zero i j hij u hu v hv
      flipHerm_eq_zero := fun i j hij u hu v hv => by
        by_cases hi0 : i = 0
        · rw [hi0, hd0] at hu
          by_cases hj1 : j = 1
          · rw [hj1, hd1] at hv
            exact (mem_flipOrth.mp ((inf_le_right : L1 ≤ flipOrth σ x) hv)) u hu
          · have hj0 : j ≠ 0 := fun h => hij (hi0.trans h.symm)
            rw [hdj j hj0 hj1] at hv
            exact (hUorth j hj0 hj1 u (hxleU hu) v hv).2
        · by_cases hi1 : i = 1
          · rw [hi1, hd1] at hu
            by_cases hj0 : j = 0
            · rw [hj0, hd0] at hv
              exact (flipHerm_eq_zero_iff hσ).mpr
                (mem_flipOrth.mp ((inf_le_right : L1 ≤ flipOrth σ x) hu) v hv)
            · have hj1 : j ≠ 1 := fun h => hij (hi1.trans h.symm)
              rw [hdj j hj0 hj1] at hv
              exact (hUorth j hj0 hj1 u (hL1U hu) v hv).2
          · by_cases hj0 : j = 0
            · rw [hj0, hd0] at hv
              rw [hdj i hi0 hi1] at hu
              exact (flipHerm_eq_zero_iff hσ).mpr
                (hUorth i hi0 hi1 v (hxleU hv) u hu).2
            · by_cases hj1 : j = 1
              · rw [hj1, hd1] at hv
                rw [hdj i hi0 hi1] at hu
                exact (flipHerm_eq_zero_iff hσ).mpr
                  (hUorth i hi0 hi1 v (hL1U hv) u hu).2
              · rw [hdj i hi0 hi1] at hu
                rw [hdj j hj0 hj1] at hv
                exact c.flipHerm_eq_zero i j hij u hu v hv }
  have hUspan : U ≤ c.spanAt Finset.univ := by
    rw [show U = c.sub 2 from rfl, FlipFrame.sub]
    exact c.spanAt_mono (Finset.filter_subset _ _)
  have hfspan_le : f.spanAt Finset.univ ≤ c.spanAt Finset.univ := by
    rw [FlipFrame.spanAt]
    refine Finset.sup_le fun i _ => ?_
    by_cases hi0 : i = 0
    · rw [hi0]
      exact (hd0 ▸ hxleU).trans hUspan
    · by_cases hi1 : i = 1
      · rw [hi1]
        exact (hd1 ▸ hL1U).trans hUspan
      · rw [show f.line i = c.line i from hdj i hi0 hi1]
        exact c.line_le_spanAt (Finset.mem_univ i)
  have hspan_le : c.spanAt Finset.univ ≤ f.spanAt Finset.univ := by
    have hxspan : x ≤ f.spanAt Finset.univ := by
      have h := f.line_le_spanAt (Finset.mem_univ (0 : Fin (m + 1)))
      rwa [show f.line 0 = x from hd0] at h
    have hL1span : L1 ≤ f.spanAt Finset.univ := by
      have h := f.line_le_spanAt (Finset.mem_univ (1 : Fin (m + 1)))
      rwa [show f.line 1 = L1 from hd1] at h
    have hUf : U ≤ f.spanAt Finset.univ := hsplit ▸ sup_le hxspan hL1span
    rw [FlipFrame.spanAt]
    refine Finset.sup_le fun i _ => ?_
    by_cases hi0 : i = 0
    · rw [hi0]
      exact (hUeq ▸ le_sup_left).trans hUf
    · by_cases hi1 : i = 1
      · rw [hi1]
        exact (hUeq ▸ le_sup_right).trans hUf
      · rw [← hdj i hi0 hi1]
        exact f.line_le_spanAt (Finset.mem_univ i)
  have hspan : f.spanAt Finset.univ = c.spanAt Finset.univ :=
    le_antisymm hfspan_le hspan_le
  let d : DChamber σ (m + 1) :=
    { toFlipFrame := f
      even_ruling := by
        rw [hspan]
        exact c.even_ruling }
  have hplane : c.line k.castSucc ⊔ c.line k.succ =
      d.line k.castSucc ⊔ d.line k.succ := by
    rw [hk0, hk1]
    rw [hUeq, show d.line 0 ⊔ d.line 1 = U from by rw [show d.line 0 = x from hd0,
      show d.line 1 = L1 from hd1, hsplit]]
  refine ⟨d, ?_, ?_⟩
  · rw [dChamberSystem_adj_iff]
    have hiff := FlipFrame.elt_eq_elt_iff_castSucc hσ (k := k)
      (c := c.toFlipFrame) (d := d.toFlipFrame)
    intro j hj
    refine (hiff.mpr ⟨?_, hplane⟩) j ?_
    · intro j hj1 hj2
      have hj0 : j ≠ 0 := fun h => hj1 (h.trans hk0.symm)
      have hj1' : j ≠ 1 := fun h => hj2 (h.trans hk1.symm)
      exact (hdj j hj0 hj1').symm
    · intro h
      exact hj (h.trans hk0)
  · exact hd0

theorem commuteTypes_zero (hσ : ∀ x, σ (σ x) = x) (hm : 3 ≤ m) {i : Fin (m + 1)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : CommuteTypes (dChamberSystem σ m) 0 i := by
  change ∀ x y z : DChamber σ (m + 1),
    (dChamberSystem σ m).adj 0 x y → (dChamberSystem σ m).adj i y z →
      ∃ y', (dChamberSystem σ m).adj i x y' ∧ (dChamberSystem σ m).adj 0 y' z
  intro x y z h0 hi
  rw [dChamberSystem_adj_iff] at h0 hi
  have h0i : (0 : Fin (m + 1)) ≠ i := fun h => hi0 h.symm
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    intro h
    have hv := congrArg (fun t : Fin (m + 1) => (t : ℕ)) h
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at hv
    exact Nat.one_ne_zero hv
  have hxle : x.line 0 ≤ z.line 0 ⊔ z.line 1 := by
    calc x.line 0 ≤ x.line 0 ⊔ x.line 1 := le_sup_left
      _ = x.elt 1 := (FlipFrame.elt_one x.toFlipFrame hm).symm
      _ = y.elt 1 := h0 1 h10
      _ = z.elt 1 := hi 1 (fun h => hi1 h.symm)
      _ = z.line 0 ⊔ z.line 1 := FlipFrame.elt_one z.toFlipFrame hm
  obtain ⟨d, hd0, hdline⟩ :=
    DChamber.exists_adj_zero_line_eq hσ (by omega) z (x := x.line 0)
      (x.isFlipflopPt_line 0) hxle
  rw [dChamberSystem_adj_iff] at hd0
  refine ⟨d, ?_, ?_⟩
  · rw [dChamberSystem_adj_iff]
    intro j hj
    by_cases hj0 : j = 0
    · have hji : j ≠ i := by rw [hj0]; exact h0i
      rw [hj0, FlipFrame.elt_zero x.toFlipFrame (by omega),
        FlipFrame.elt_zero d.toFlipFrame (by omega)]
      exact hdline.symm
    · rw [h0 j hj0, hi j hj, hd0 j hj0]
  · rw [dChamberSystem_adj_iff]
    intro j hj
    exact (hd0 j hj).symm

theorem connected_dChamberSystem_one (hσ : ∀ x, σ (σ x) = x) :
    (dChamberSystem σ 1).Connected := by
  intro c d
  let U := c.spanAt Finset.univ
  let Vd := d.alt
  let X := U ⊓ Vd
  have hUlag : (quadPlusForm 2 K).IsLagrangian U := c.isLagrangian_spanAt_univ hσ
  have hVlag : (quadPlusForm 2 K).IsLagrangian Vd := d.isLagrangian_alt hσ
  have hUsub : IsFlipflopSub σ U := c.isFlipflopSub_spanAt hσ Finset.univ
  have hVsub : IsFlipflopSub σ Vd := d.isFlipflopSub_alt hσ
  have hUdim : Module.finrank K U = 2 := by
    rw [show U = c.spanAt Finset.univ from rfl, c.finrank_spanAt]
    norm_num
  have hVdim : Module.finrank K Vd = 2 := by
    rw [show Vd = d.alt from rfl, d.finrank_alt hσ]
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm 2 K)
    (finrank_flipSpace 2 K) hUlag hVlag (isLagrangian_stdLag 2 K)
  let A := 2 - Module.finrank K ↥(U ⊓ Vd)
  let B := 2 - Module.finrank K ↥(Vd ⊓ stdLag 2 K)
  let C := 2 - Module.finrank K ↥(U ⊓ stdLag 2 K)
  have hC : Even C := c.even_ruling
  have hB : ¬ Even B := not_even_ruling_alt hσ 1 d
  have hAB : Even A ↔ Even B := by
    have h := hpar
    rw [Nat.even_add, Nat.even_add] at h
    simpa [A, B, C, hC] using h
  have hAodd : ¬ Even A := fun hA => hB (hAB.mp hA)
  have hAle : A ≤ 2 := Nat.sub_le 2 _
  have hA1 : A = 1 := by
    interval_cases A <;> simp_all [Nat.even_iff]
  have hA1' : 2 - Module.finrank K ↥X = 1 := by simpa [A] using hA1
  have hXdim : Module.finrank K ↥X = 1 := by
    have hXle : Module.finrank K ↥X ≤ 2 := by
      have := Submodule.finrank_mono (inf_le_left : X ≤ U)
      omega
    omega
  have hXsub : IsFlipflopSub σ X :=
    isFlipflopSub_inf_of_isLagrangian hσ hUsub hUlag hVsub hVlag (by omega)
  have hXpt : IsFlipflopPt σ X := ⟨hXsub, hXdim⟩
  let L1 : Submodule K (Fin 2 ⊕ Fin 2 → K) := U ⊓ flipOrth σ X
  have hL1 : IsFlipflopPt σ L1 :=
    isFlipflopPt_inf_flipOrth_of_finrank_two hσ hUsub hUdim hXpt inf_le_left
  have hL1U : L1 ≤ U := inf_le_left
  have hdisjX : Disjoint X L1 := by
    rw [Submodule.disjoint_def]
    intro v hvX hvL
    have hvflip : v ∈ flipOrth σ X := (inf_le_right : L1 ≤ flipOrth σ X) hvL
    refine hXsub.nondeg v hvX ?_
    intro w hw
    exact (flipHerm_eq_zero_iff hσ).mpr (mem_flipOrth.mp hvflip w hw)
  have hdimsupX : Module.finrank K ↥(X ⊔ L1) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq X L1
    rw [hdisjX.eq_bot, finrank_bot, add_zero, hXdim, hL1.2] at h
    omega
  have hsplitX : X ⊔ L1 = U :=
    Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left hL1U) (by rw [hdimsupX, hUdim])
  have hpolarU : ∀ p ∈ U, ∀ q ∈ U, polar (quadPlus 2 K) p q = 0 := by
    intro p hp q hq
    have h := QuadraticMap.map_add (quadPlus 2 K) p q
    rw [hUsub.total (p + q) (Submodule.add_mem _ hp hq), hUsub.total p hp,
      hUsub.total q hq] at h
    simpa using h.symm
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let eline : Fin 2 → Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    Function.update (Function.update c.line 0 X) 1 L1
  have he0 : eline 0 = X := by
    dsimp only [eline]
    rw [Function.update_of_ne h01, Function.update_self]
  have he1 : eline 1 = L1 := by
    dsimp only [eline]
    rw [Function.update_self]
  let eframe : FlipFrame σ 2 :=
    { line := eline
      isFlipflopPt_line := fun i => by
        fin_cases i
        · change IsFlipflopPt σ (eline 0)
          rw [he0]
          exact hXpt
        · change IsFlipflopPt σ (eline 1)
          rw [he1]
          exact hL1
      polar_eq_zero := fun i j hij u hu v hv => by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · change u ∈ eline 0 at hu
          change v ∈ eline 1 at hv
          rw [he0] at hu
          rw [he1] at hv
          exact hpolarU u ((inf_le_left : X ≤ U) hu) v (hL1U hv)
        · change u ∈ eline 1 at hu
          change v ∈ eline 0 at hv
          rw [he1] at hu
          rw [he0] at hv
          rw [QuadraticMap.polar_comm]
          exact hpolarU v ((inf_le_left : X ≤ U) hv) u (hL1U hu)
        · exact absurd rfl hij
      flipHerm_eq_zero := fun i j hij u hu v hv => by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · change u ∈ eline 0 at hu
          change v ∈ eline 1 at hv
          rw [he0] at hu
          rw [he1] at hv
          exact (mem_flipOrth.mp ((inf_le_right : L1 ≤ flipOrth σ X) hv)) u hu
        · change u ∈ eline 1 at hu
          change v ∈ eline 0 at hv
          rw [he1] at hu
          rw [he0] at hv
          exact (flipHerm_eq_zero_iff hσ).mpr
            ((mem_flipOrth.mp ((inf_le_right : L1 ≤ flipOrth σ X) hu)) v hv)
        · exact absurd rfl hij }
  have hle0 : eframe.line 0 = X := by
    change eline 0 = X
    exact he0
  have hle1 : eframe.line 1 = L1 := by
    change eline 1 = L1
    exact he1
  have hespan : eframe.spanAt Finset.univ = U := by
    apply le_antisymm
    · rw [FlipFrame.spanAt]
      refine Finset.sup_le fun i _ => ?_
      fin_cases i
      · change eframe.line 0 ≤ U
        rw [hle0]
        exact inf_le_left
      · change eframe.line 1 ≤ U
        rw [hle1]
        exact hL1U
    · rw [← hsplitX]
      refine sup_le ?_ ?_
      · have h := eframe.line_le_spanAt (Finset.mem_univ (0 : Fin 2))
        change eframe.line 0 ≤ eframe.spanAt Finset.univ at h
        rwa [hle0] at h
      · have h := eframe.line_le_spanAt (Finset.mem_univ (1 : Fin 2))
        change eframe.line 1 ≤ eframe.spanAt Finset.univ at h
        rwa [hle1] at h
  let e : DChamber σ 2 :=
    { toFlipFrame := eframe
      even_ruling := by
        rw [hespan]
        exact c.even_ruling }
  have hXsub1 : X ≤ e.sub 1 := by
    rw [e.sub_succ (j := 0) (by omega), e.sub_zero, bot_sup_eq]
    exact le_of_eq (show e.line 0 = X from hle0)
  have hXalte : X ≤ e.alt := by
    change X ≤ e.sub 1 ⊔ dFlipSub σ (e.line (Fin.last 1))
    exact le_sup_of_le_left hXsub1
  have hXaltd : X ≤ d.alt := inf_le_right
  obtain ⟨M, M', hM, hM', hXM, hXM', hMeven, hModd, huniq⟩ :=
    hXsub.exists_two_solids hσ (by omega)
  have healtlag : (quadPlusForm 2 K).IsLagrangian e.alt := e.isLagrangian_alt hσ
  have hdaltlag : (quadPlusForm 2 K).IsLagrangian d.alt := d.isLagrangian_alt hσ
  have healtodd : ¬ Even (2 - Module.finrank K ↥(e.alt ⊓ stdLag 2 K)) :=
    not_even_ruling_alt hσ 1 e
  have hdaltodd : ¬ Even (2 - Module.finrank K ↥(d.alt ⊓ stdLag 2 K)) :=
    not_even_ruling_alt hσ 1 d
  have healt : e.alt = M' := by
    rcases huniq e.alt healtlag hXalte with h | h
    · rw [h] at healtodd
      exact (healtodd hMeven).elim
    · exact h
  have hdalt : d.alt = M' := by
    rcases huniq d.alt hdaltlag hXaltd with h | h
    · rw [h] at hdaltodd
      exact (hdaltodd hMeven).elim
    · exact h
  have hEalt : e.alt = d.alt := healt.trans hdalt.symm
  refine ⟨[(0, e), (1, d)], ?_, ?_⟩
  · refine ⟨?_, ?_, trivial⟩
    · rw [dChamberSystem_adj_iff]
      intro j hj
      have hj1 : j = 1 := by
        fin_cases j
        · exact (hj rfl).elim
        · rfl
      rw [hj1, show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl,
        FlipFrame.elt_last c.toFlipFrame, FlipFrame.elt_last e.toFlipFrame,
        c.toFlipFrame.sub_of_le (by omega : 2 ≤ 2),
        e.toFlipFrame.sub_of_le (by omega : 2 ≤ 2), hespan]
    · rw [dChamberSystem_adj_iff]
      intro j hj
      have hj0 : j = 0 := by
        fin_cases j
        · rfl
        · exact (hj rfl).elim
      rw [hj0, FlipFrame.elt_of_add_one_eq e.toFlipFrame 0 (by simp),
        FlipFrame.elt_of_add_one_eq d.toFlipFrame 0 (by simp), hEalt]
  · rfl

end CFSG.ClassicalInvolution.PhanDn

end
