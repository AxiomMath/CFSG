module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.LieType.BorelTits.Families
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem quadPlusForm_Q (v : Fin n ⊕ Fin n → K) :
    (quadPlusForm n K).Q v = quadPlus n K v := by
  refine (congrFun (coe_quadPlus (n := n) (K := K)).symm v).trans ?_
  rfl

theorem quadPlusForm_polar (u v : Fin n ⊕ Fin n → K) :
    (quadPlusForm n K).polar.β u v = polar (quadPlus n K) u v := by
  rw [polar_quadPlus]
  rfl

@[expose] def dFlipSub (σ : K ≃+* K) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    Submodule K (Fin n ⊕ Fin n → K) :=
  Submodule.span K (dFlip σ '' W)

theorem dFlipSub_span_singleton (v : Fin n ⊕ Fin n → K) :
    dFlipSub σ (K ∙ v) = K ∙ dFlip σ v := by
  rw [dFlipSub]
  have himage : (dFlip σ '' (K ∙ v) : Set (Fin n ⊕ Fin n → K)) =
      (K ∙ dFlip σ v : Set (Fin n ⊕ Fin n → K)) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      refine Submodule.mem_span_singleton.mpr ⟨σ a, ?_⟩
      rw [dFlip_smul]
    · intro hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      refine ⟨σ.symm a • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v), ?_⟩
      rw [dFlip_smul, RingEquiv.apply_symm_apply]
  rw [himage, Submodule.span_eq]

variable (σ n) in
@[ext] structure FlipFrame where
  line : Fin n → Submodule K (Fin n ⊕ Fin n → K)
  isFlipflopPt_line : ∀ i, IsFlipflopPt σ (line i)
  polar_eq_zero : ∀ i j, i ≠ j → ∀ u ∈ line i, ∀ v ∈ line j,
    polar (quadPlus n K) u v = 0
  flipHerm_eq_zero : ∀ i j, i ≠ j → ∀ u ∈ line i, ∀ v ∈ line j, flipHerm σ u v = 0

namespace FlipFrame

variable {c d : FlipFrame σ n}

private theorem isFlipflopSub_of_isFlipflopPt {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : IsFlipflopSub σ p := by
  change IsFlipflopSub σ p ∧ Module.finrank K p = 1 at hp
  exact hp.1

private theorem finrank_eq_one_of_isFlipflopPt {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : Module.finrank K p = 1 := by
  change IsFlipflopSub σ p ∧ Module.finrank K p = 1 at hp
  exact hp.2

private def flipHermLeft (σ : K ≃+* K) (w : Fin n ⊕ Fin n → K) :
    Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {y | flipHerm σ y w = 0}
  zero_mem' := by simpa only [Set.mem_setOf_eq] using flipHerm_zero_left w
  add_mem' {y z} hy hz := by
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [flipHerm_add_left, hy, hz, add_zero]
  smul_mem' a y hy := by
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [flipHerm_smul_left, hy, mul_zero]

private def polarLeft (w : Fin n ⊕ Fin n → K) :
    Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {y | polar (quadPlus n K) y w = 0}
  zero_mem' := by simp
  add_mem' {y z} hy hz := by
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [QuadraticMap.polar_add_left, hy, hz, add_zero]
  smul_mem' a y hy := by
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [QuadraticMap.polar_smul_left, hy, smul_zero]

private def polarRight (w : Fin n ⊕ Fin n → K) :
    Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {y | polar (quadPlus n K) w y = 0}
  zero_mem' := by simp
  add_mem' {y z} hy hz := by
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [QuadraticMap.polar_add_right, hy, hz, add_zero]
  smul_mem' a y hy := by
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [QuadraticMap.polar_smul_right, hy, smul_zero]

@[expose] def spanAt (c : FlipFrame σ n) (S : Finset (Fin n)) :
    Submodule K (Fin n ⊕ Fin n → K) :=
  S.sup c.line

@[simp] theorem spanAt_empty (c : FlipFrame σ n) : c.spanAt ∅ = ⊥ :=
  Finset.sup_empty

theorem spanAt_insert (c : FlipFrame σ n) (i : Fin n) (S : Finset (Fin n)) :
    c.spanAt (insert i S) = c.line i ⊔ c.spanAt S :=
  Finset.sup_insert

theorem line_le_spanAt {c : FlipFrame σ n} {i : Fin n} {S : Finset (Fin n)} (h : i ∈ S) :
    c.line i ≤ c.spanAt S :=
  Finset.le_sup h

theorem spanAt_mono {c : FlipFrame σ n} {S T : Finset (Fin n)} (h : S ⊆ T) :
    c.spanAt S ≤ c.spanAt T :=
  Finset.sup_mono h

private theorem spanAt_le_flipHermLeft {c : FlipFrame σ n} {S : Finset (Fin n)}
    {w : Fin n ⊕ Fin n → K}
    (hw : ∀ i ∈ S, ∀ y ∈ c.line i, flipHerm σ y w = 0) :
    c.spanAt S ≤ flipHermLeft σ w := by
  rw [spanAt]
  exact Finset.sup_le fun i hi => fun y hy => hw i hi y hy

private theorem spanAt_le_polarLeft {c : FlipFrame σ n} {S : Finset (Fin n)}
    {w : Fin n ⊕ Fin n → K}
    (hw : ∀ i ∈ S, ∀ y ∈ c.line i, polar (quadPlus n K) y w = 0) :
    c.spanAt S ≤ polarLeft w := by
  rw [spanAt]
  exact Finset.sup_le fun i hi => fun y hy => hw i hi y hy

private theorem spanAt_le_polarRight {c : FlipFrame σ n} {S : Finset (Fin n)}
    {w : Fin n ⊕ Fin n → K}
    (hw : ∀ i ∈ S, ∀ y ∈ c.line i, polar (quadPlus n K) w y = 0) :
    c.spanAt S ≤ polarRight w := by
  rw [spanAt]
  exact Finset.sup_le fun i hi => fun y hy => hw i hi y hy

private theorem flipHerm_self_ne_zero_of_mem_point {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) {v : Fin n ⊕ Fin n → K} (hv : v ∈ p) (hv0 : v ≠ 0) :
    flipHerm σ v v ≠ 0 := by
  intro hvv
  refine hv0 ((isFlipflopSub_of_isFlipflopPt hp).nondeg v hv ?_)
  intro u hu
  have hspan : p = K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one (finrank_eq_one_of_isFlipflopPt hp) hv hv0
  rw [hspan] at hu
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [flipHerm_smul_right, hvv, mul_zero]

private theorem spanAt_le_flipOrth_line (c : FlipFrame σ n) {i : Fin n} {S : Finset (Fin n)}
    (hi : i ∉ S) : c.spanAt S ≤ flipOrth σ (c.line i) := by
  refine Finset.sup_le fun j hj => ?_
  have hji : j ≠ i := by
    rintro rfl
    exact hi hj
  intro v hv
  rw [mem_flipOrth]
  intro w hw
  exact c.flipHerm_eq_zero i j hji.symm w hw v hv

private theorem disjoint_line_spanAt {c : FlipFrame σ n} {i : Fin n} {S : Finset (Fin n)}
    (hi : i ∉ S) : Disjoint (c.line i) (c.spanAt S) := by
  rw [Submodule.disjoint_def]
  intro x hxi hxS
  by_contra hx0
  have hxorth : x ∈ flipOrth σ (c.line i) :=
    spanAt_le_flipOrth_line c hi hxS
  have hxx : flipHerm σ x x = 0 := hxorth x hxi
  exact flipHerm_self_ne_zero_of_mem_point (c.isFlipflopPt_line i) hxi hx0 hxx

theorem finrank_spanAt (c : FlipFrame σ n) (S : Finset (Fin n)) :
    Module.finrank K (c.spanAt S) = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [spanAt_empty, finrank_bot, Finset.card_empty]
  | insert i S hi ih =>
    have hdisj : Disjoint (c.line i) (c.spanAt S) := disjoint_line_spanAt hi
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (c.line i) (c.spanAt S)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at hdim
    rw [spanAt_insert, hdim, ih, finrank_eq_one_of_isFlipflopPt (c.isFlipflopPt_line i),
      Finset.card_insert_of_notMem hi]
    omega

private theorem polar_eq_zero_of_total {A : Submodule K (Fin n ⊕ Fin n → K)}
    (hA : ∀ a ∈ A, quadPlus n K a = 0) {a b : Fin n ⊕ Fin n → K} (ha : a ∈ A)
    (hb : b ∈ A) : polar (quadPlus n K) a b = 0 := by
  have h := QuadraticMap.map_add (quadPlus n K) a b
  rw [hA (a + b) (A.add_mem ha hb), hA a ha, hA b hb] at h
  simpa using h.symm

theorem isFlipflopSub_spanAt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n)
    (S : Finset (Fin n)) : IsFlipflopSub σ (c.spanAt S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [spanAt_empty]
    exact ⟨fun u hu => by
        rw [Submodule.mem_bot] at hu
        rw [hu]
        exact QuadraticMap.map_zero _,
      fun u hu _ => by
        rw [Submodule.mem_bot] at hu
        exact hu⟩
  | insert i S hi ih =>
    rw [spanAt_insert]
    refine ⟨?_, ?_⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
      have hxy : polar (quadPlus n K) x y = 0 := by
        have hle : c.spanAt S ≤ (quadPlusForm n K).polar.perp (c.line i) := by
          refine Finset.sup_le fun j hj => ?_
          have hji : j ≠ i := by
            rintro rfl
            exact hi hj
          intro v hv
          rw [ReflForm.mem_perp]
          intro u hu
          rw [quadPlusForm_polar]
          exact c.polar_eq_zero i j hji.symm u hu v hv
        have h := hle hy x hx
        rwa [quadPlusForm_polar] at h
      rw [QuadraticMap.map_add (quadPlus n K) x y, ih.total y hy,
        (isFlipflopSub_of_isFlipflopPt (c.isFlipflopPt_line i)).total x hx, hxy]
      abel
    · intro u hu hper
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
      have hle : c.spanAt S ≤ flipOrth σ (c.line i) := spanAt_le_flipOrth_line c hi
      have hx0 : x = 0 := by
        refine (isFlipflopSub_of_isFlipflopPt (c.isFlipflopPt_line i)).nondeg x hx ?_
        intro w hw
        have h1 := hper w (Submodule.mem_sup_left hw)
        have hyw : flipHerm σ y w = 0 := by
          rw [← flipHerm_conj hσ w y, hle hy w hw, map_zero]
        rw [flipHerm_add_left, hyw, add_zero] at h1
        exact h1
      have hy0 : y = 0 := by
        refine ih.nondeg y hy ?_
        intro v hv
        have h1 := hper v (Submodule.mem_sup_right hv)
        rw [flipHerm_add_left, hx0, flipHerm_zero_left, zero_add] at h1
        exact h1
      rw [hx0, hy0, add_zero]

theorem isLagrangian_spanAt_univ (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n) :
    (quadPlusForm n K).IsLagrangian (c.spanAt Finset.univ) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [quadPlusForm_Q]
    exact (c.isFlipflopSub_spanAt hσ Finset.univ).total u hu
  · have h1 := c.finrank_spanAt Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have hV : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    rw [h1, hV]

theorem line_eq_flipOrth_inf (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n)
    {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) :
    c.line i = flipOrth σ (c.spanAt S) ⊓ c.spanAt (insert i S) := by
  apply le_antisymm
  · intro u hu
    refine Submodule.mem_inf.mpr
      ⟨?_, c.line_le_spanAt (Finset.mem_insert_self i S) hu⟩
    rw [mem_flipOrth]
    intro v hv
    have hle : c.spanAt S ≤ flipOrth σ (c.line i) := spanAt_le_flipOrth_line c hi
    have huv : flipHerm σ u v = 0 := hle hv u hu
    rw [← flipHerm_conj hσ u v, huv, map_zero]
  · intro x hx
    obtain ⟨hxorth, hxspan⟩ := Submodule.mem_inf.mp hx
    rw [spanAt_insert] at hxspan
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxspan
    have hz0 : z = 0 := by
      refine (c.isFlipflopSub_spanAt hσ S).nondeg z hz ?_
      intro v hv
      have hle : c.spanAt S ≤ flipOrth σ (c.line i) := spanAt_le_flipOrth_line c hi
      have hyv : flipHerm σ v y = 0 := by
        rw [← flipHerm_conj hσ y v, hle hv y hy, map_zero]
      have h1 : flipHerm σ v (y + z) = 0 := by
        rw [mem_flipOrth] at hxorth
        exact hxorth v hv
      rw [flipHerm_add_right, hyv, zero_add] at h1
      rw [← flipHerm_conj hσ v z, h1, map_zero]
    rw [hz0, add_zero]
    exact hy

private theorem exists_ne_zero_mem_line (c : FlipFrame σ n) (i : Fin n) :
    ∃ v ∈ c.line i, v ≠ 0 := by
  have hp := c.isFlipflopPt_line i
  have hne : c.line i ≠ ⊥ := by
    intro hbot
    have hfin := finrank_eq_one_of_isFlipflopPt hp
    rw [hbot, finrank_bot] at hfin
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

theorem exists_gen (hσ : ∀ x, σ (σ x) = x)
    (hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a)
    (c : FlipFrame σ n) (i : Fin n) :
    ∃ v ∈ c.line i, quadPlus n K v = 0 ∧ flipHerm σ v v = 1 ∧ c.line i = K ∙ v := by
  have hp := c.isFlipflopPt_line i
  obtain ⟨u, hu, hu0⟩ := c.exists_ne_zero_mem_line i
  have hQu : quadPlus n K u = 0 := (isFlipflopSub_of_isFlipflopPt hp).total u hu
  have huu : flipHerm σ u u ≠ 0 := flipHerm_self_ne_zero_of_mem_point hp hu hu0
  have hfix : σ (flipHerm σ u u) = flipHerm σ u u := flipHerm_self_mem_fixed hσ u
  have hfixinv : σ ((flipHerm σ u u)⁻¹) = (flipHerm σ u u)⁻¹ := by
    rw [map_inv₀, hfix]
  obtain ⟨a, ha⟩ := hN ((flipHerm σ u u)⁻¹) hfixinv (inv_ne_zero huu)
  have hQv : quadPlus n K (a • u) = 0 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, hQu, mul_zero]
  have hvv : flipHerm σ (a • u) (a • u) = 1 := by
    rw [flipHerm_smul_left, flipHerm_smul_right, ← mul_assoc, ha, inv_mul_cancel₀ huu]
  have hv0 : a • u ≠ 0 := by
    intro hzero
    rw [hzero, flipHerm_zero_right] at hvv
    exact zero_ne_one hvv
  refine ⟨a • u, Submodule.smul_mem _ _ hu, hQv, hvv, ?_⟩
  exact eq_span_singleton_of_mem_of_finrank_eq_one (finrank_eq_one_of_isFlipflopPt hp)
    (Submodule.smul_mem _ _ hu) hv0

section Unitary

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_gen_unitaryInvolution (hK : Nat.card K = (p ^ f) ^ 2)
    (c : FlipFrame (unitaryInvolution K p f) n) (i : Fin n) :
    ∃ v ∈ c.line i, quadPlus n K v = 0 ∧
      flipHerm (unitaryInvolution K p f) v v = 1 ∧ c.line i = K ∙ v := by
  have hσ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := p) (f := f) hK).invol
  exact exists_gen hσ (fun a ha ha0 =>
    exists_mul_unitaryInvolution_eq_of_fixed hK ha ha0) c i

end Unitary

def stdFrame (σ : K ≃+* K) (n : ℕ) : FlipFrame σ n where
  line i := K ∙ stdE (K := K) (n := n) i
  isFlipflopPt_line i := by
    have h0 : stdE (K := K) (n := n) i ≠ 0 := by
      intro h
      have := congrFun h (.inl i)
      simp [stdE] at this
    exact (isFlipflopPt_span_singleton_iff h0).mpr
      ⟨quadPlus_stdE i, by rw [flipHerm_stdE_stdE]; simp⟩
  polar_eq_zero i j hij u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [polar_quadPlus]
    simp [stdE]
  flipHerm_eq_zero i j hij u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [flipHerm_smul_left, flipHerm_smul_right, flipHerm_stdE_stdE]
    simp [hij]

theorem stdFrame_spanAt_univ (σ : K ≃+* K) (n : ℕ) :
    (stdFrame σ n).spanAt Finset.univ =
      Submodule.span K (Set.range (stdE (K := K) (n := n))) := by
  rw [spanAt]
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr fun v hv => ?_
    obtain ⟨i, rfl⟩ := hv
    exact Finset.le_sup (f := fun i : Fin n => K ∙ stdE (K := K) (n := n) i)
      (Finset.mem_univ i) (Submodule.mem_span_singleton_self _)

theorem spanAt_eq_of_agree {c d : FlipFrame σ n} {S : Finset (Fin n)}
    (h : ∀ k ∈ S, c.line k = d.line k) : c.spanAt S = d.spanAt S :=
  Finset.sup_congr rfl h

def sub (c : FlipFrame σ n) (j : ℕ) : Submodule K (Fin n ⊕ Fin n → K) :=
  c.spanAt (Finset.univ.filter fun l => (l : ℕ) < j)

theorem finrank_sub (c : FlipFrame σ n) {j : ℕ} (hj : j ≤ n) :
    Module.finrank K (c.sub j) = j := by
  rw [sub, c.finrank_spanAt, ← Fintype.card_subtype]
  exact Fintype.card_fin_lt_of_le hj

theorem isFlipflopSub_sub (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n) (j : ℕ) :
    IsFlipflopSub σ (c.sub j) :=
  c.isFlipflopSub_spanAt hσ _

private theorem quadPlus_eq_zero_of_mem_sup {A B : Submodule K (Fin n ⊕ Fin n → K)}
    (hA : ∀ a ∈ A, quadPlus n K a = 0) (hB : ∀ b ∈ B, quadPlus n K b = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar (quadPlus n K) a b = 0)
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ A ⊔ B) : quadPlus n K w = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [QuadraticMap.map_add (quadPlus n K) a b, hA a ha, hB b hb, hAB a ha b hb]
  simp

private theorem nondeg_sup_of_orth {A B : Submodule K (Fin n ⊕ Fin n → K)}
    (hA : IsFlipflopSub σ A) (hB : IsFlipflopSub σ B)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, flipHerm σ b a = 0)
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ A ⊔ B)
    (hper : ∀ v ∈ A ⊔ B, flipHerm σ w v = 0) : w = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  have hx0 : x = 0 := by
    refine hA.nondeg x hx ?_
    intro a ha
    have h1 := hper a (Submodule.mem_sup_left ha)
    rw [flipHerm_add_left, hBA y hy a ha, add_zero] at h1
    exact h1
  have hy0 : y = 0 := by
    refine hB.nondeg y hy ?_
    intro b hb
    have h1 := hper b (Submodule.mem_sup_right hb)
    rw [flipHerm_add_left, hx0, flipHerm_zero_left, zero_add] at h1
    exact h1
  rw [hx0, hy0, add_zero]

section Twin

variable {m : ℕ}

def alt (c : FlipFrame σ (m + 1)) : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  c.sub m ⊔ dFlipSub σ (c.line (Fin.last m))

private theorem isFlipflopPt_dFlipSub_line (hσ : ∀ x, σ (σ x) = x)
    (c : FlipFrame σ n) (i : Fin n) :
    IsFlipflopPt σ (dFlipSub σ (c.line i)) := by
  obtain ⟨u, hu, hu0⟩ := c.exists_ne_zero_mem_line i
  have hline : c.line i = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_eq_one_of_isFlipflopPt (c.isFlipflopPt_line i)) hu hu0
  have hQu : quadPlus n K u = 0 :=
    (isFlipflopSub_of_isFlipflopPt (c.isFlipflopPt_line i)).total u hu
  have huu : flipHerm σ u u ≠ 0 :=
    flipHerm_self_ne_zero_of_mem_point (c.isFlipflopPt_line i) hu hu0
  have hQ : quadPlus n K (dFlip σ u) = 0 := by
    rw [quadPlus_dFlip, hQu, map_zero]
  have hh : flipHerm σ (dFlip σ u) (dFlip σ u) ≠ 0 := by
    rw [flipHerm_dFlip_dFlip hσ]
    exact fun h => huu ((map_eq_zero_iff σ σ.injective).mp h)
  have hd0 : dFlip σ u ≠ 0 := by
    intro hd
    exact hh (by rw [hd, flipHerm_zero_right])
  rw [hline, dFlipSub_span_singleton]
  exact (isFlipflopPt_span_singleton_iff hd0).mpr ⟨hQ, hh⟩

theorem isFlipflopSub_alt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    IsFlipflopSub σ c.alt := by
  obtain ⟨u, hu, hu0⟩ := c.exists_ne_zero_mem_line (Fin.last m)
  have hline : c.line (Fin.last m) = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_eq_one_of_isFlipflopPt (c.isFlipflopPt_line _)) hu hu0
  have huu : flipHerm σ u u ≠ 0 :=
    flipHerm_self_ne_zero_of_mem_point (c.isFlipflopPt_line _) hu hu0
  have hA : IsFlipflopSub σ (c.sub m) := c.isFlipflopSub_sub hσ m
  have hB : IsFlipflopSub σ (dFlipSub σ (c.line (Fin.last m))) :=
    isFlipflopSub_of_isFlipflopPt (isFlipflopPt_dFlipSub_line hσ c (Fin.last m))
  have hlast : ∀ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => (l : ℕ) < m),
      l ≠ Fin.last m := by
    intro l hl h
    subst h
    simp [Fin.val_last] at hl
  have hABp : ∀ a ∈ c.sub m, ∀ b ∈ dFlipSub σ (c.line (Fin.last m)),
      polar (quadPlus (m + 1) K) a b = 0 := by
    intro a ha b hb
    rw [hline, dFlipSub_span_singleton] at hb
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hau : flipHerm σ a u = 0 := by
      have hle : c.sub m ≤ flipHermLeft σ u := by
        refine spanAt_le_flipHermLeft ?_
        intro l hl y hy
        exact c.flipHerm_eq_zero l (Fin.last m) (hlast l hl) y hy u hu
      exact hle ha
    have hp : polar (quadPlus (m + 1) K) a (dFlip σ u) = flipHerm σ a u := rfl
    rw [QuadraticMap.polar_smul_right, hp, hau, smul_zero]
  have hAB : ∀ a ∈ c.sub m, ∀ b ∈ dFlipSub σ (c.line (Fin.last m)),
      flipHerm σ a b = 0 := by
    intro a ha b hb
    rw [hline, dFlipSub_span_singleton] at hb
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hau : polar (quadPlus (m + 1) K) a u = 0 := by
      have hle : c.sub m ≤ polarLeft u := by
        refine spanAt_le_polarLeft ?_
        intro l hl y hy
        exact c.polar_eq_zero l (Fin.last m) (hlast l hl) y hy u hu
      exact hle ha
    have hp : flipHerm σ a (dFlip σ u) = polar (quadPlus (m + 1) K) a u := by
      unfold flipHerm
      rw [dFlip_dFlip hσ]
    rw [flipHerm_smul_right, hp, hau, mul_zero]
  have hBA : ∀ b ∈ dFlipSub σ (c.line (Fin.last m)), ∀ a ∈ c.sub m,
      flipHerm σ b a = 0 := by
    intro b hb a ha
    rw [← flipHerm_conj hσ a b, hAB a ha b hb, map_zero]
  refine ⟨?_, ?_⟩
  · intro w hw
    exact quadPlus_eq_zero_of_mem_sup hA.total hB.total hABp hw
  · intro w hw hper
    exact nondeg_sup_of_orth hA hB hBA hw hper

theorem finrank_alt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    Module.finrank K c.alt = m + 1 := by
  obtain ⟨u, hu, hu0⟩ := c.exists_ne_zero_mem_line (Fin.last m)
  have hline : c.line (Fin.last m) = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_eq_one_of_isFlipflopPt (c.isFlipflopPt_line _)) hu hu0
  have huu : flipHerm σ u u ≠ 0 :=
    flipHerm_self_ne_zero_of_mem_point (c.isFlipflopPt_line _) hu hu0
  have hlast : ∀ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => (l : ℕ) < m),
      l ≠ Fin.last m := by
    intro l hl h
    subst h
    simp [Fin.val_last] at hl
  have hdisj : Disjoint (c.sub m) (dFlipSub σ (c.line (Fin.last m))) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [hline, dFlipSub_span_singleton] at hx'
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx'
    have hxu : polar (quadPlus (m + 1) K) u (t • dFlip σ u) = 0 := by
      have hle : c.sub m ≤ polarRight u := by
        refine spanAt_le_polarRight ?_
        intro l hl y hy
        exact c.polar_eq_zero (Fin.last m) l (hlast l hl).symm u hu y hy
      exact hle hx
    have hp : polar (quadPlus (m + 1) K) u (dFlip σ u) = flipHerm σ u u := rfl
    rw [QuadraticMap.polar_smul_right, hp, smul_eq_mul] at hxu
    have ht : t = 0 := (mul_eq_zero.mp hxu).resolve_right huu
    rw [ht, zero_smul]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (c.sub m)
    (dFlipSub σ (c.line (Fin.last m)))
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hdim
  rw [alt, hdim, c.finrank_sub (by omega),
    finrank_eq_one_of_isFlipflopPt (isFlipflopPt_dFlipSub_line hσ c (Fin.last m))]

theorem isLagrangian_alt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    (quadPlusForm (m + 1) K).IsLagrangian c.alt := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [quadPlusForm_Q]
    exact (c.isFlipflopSub_alt hσ).total w hw
  · have h1 := c.finrank_alt hσ
    have hV : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    rw [h1, hV]

theorem alt_inf_spanAt_univ (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    c.alt ⊓ c.spanAt Finset.univ = c.sub m := by
  obtain ⟨u, hu, hu0⟩ := c.exists_ne_zero_mem_line (Fin.last m)
  have hline : c.line (Fin.last m) = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_eq_one_of_isFlipflopPt (c.isFlipflopPt_line _)) hu hu0
  have hle : c.sub m ≤ c.alt ⊓ c.spanAt Finset.univ := by
    refine le_inf le_sup_left ?_
    rw [sub]
    exact c.spanAt_mono (Finset.filter_subset _ _)
  have hdvu_notmem : dFlip σ u ∉ c.spanAt Finset.univ := by
    intro hmem
    have hu_mem : u ∈ c.spanAt Finset.univ :=
      c.line_le_spanAt (Finset.mem_univ _) hu
    have hzero : polar (quadPlus (m + 1) K) u (dFlip σ u) = 0 :=
      polar_eq_zero_of_total (A := c.spanAt Finset.univ)
        (c.isFlipflopSub_spanAt hσ _).total hu_mem hmem
    exact (flipHerm_self_ne_zero_of_mem_point (c.isFlipflopPt_line _) hu hu0) hzero
  have hlt : c.alt ⊓ c.spanAt Finset.univ < c.alt := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hle' : c.alt ≤ c.spanAt Finset.univ := heq ▸ inf_le_right
    have hdvu_alt : dFlip σ u ∈ c.alt := by
      rw [alt]
      refine Submodule.mem_sup_right ?_
      rw [hline, dFlipSub_span_singleton]
      exact Submodule.mem_span_singleton_self _
    exact hdvu_notmem (hle' hdvu_alt)
  have hfinlt : Module.finrank K ↥(c.alt ⊓ c.spanAt Finset.univ) < m + 1 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [c.finrank_alt hσ] at this
  have hge : m ≤ Module.finrank K ↥(c.alt ⊓ c.spanAt Finset.univ) := by
    have := Submodule.finrank_mono hle
    rwa [c.finrank_sub (by omega)] at this
  have hfin : Module.finrank K ↥(c.alt ⊓ c.spanAt Finset.univ) = m := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by
    rw [c.finrank_sub (by omega), hfin])).symm

def elt (c : FlipFrame σ (m + 1)) (i : Fin (m + 1)) :
    Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  if i = Fin.last m then c.sub (m + 1)
  else if (i : ℕ) + 1 = m then c.alt
  else c.sub ((i : ℕ) + 1)

theorem isFlipflopSub_elt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1))
    (i : Fin (m + 1)) : IsFlipflopSub σ (c.elt i) := by
  rw [elt]
  by_cases hlast : i = Fin.last m
  · rw [if_pos hlast]
    exact c.isFlipflopSub_sub hσ (m + 1)
  · rw [if_neg hlast]
    by_cases halt : (i : ℕ) + 1 = m
    · rw [if_pos halt]
      exact c.isFlipflopSub_alt hσ
    · rw [if_neg halt]
      exact c.isFlipflopSub_sub hσ _

theorem finrank_elt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1))
    (i : Fin (m + 1)) :
    Module.finrank K (c.elt i) =
      if (i : ℕ) + 1 < m then (i : ℕ) + 1 else m + 1 := by
  rw [elt]
  by_cases hlast : i = Fin.last m
  · have hlt : ¬ (i : ℕ) + 1 < m := by
      rw [hlast]
      simp [Fin.val_last]
    rw [if_pos hlast, if_neg hlt, c.finrank_sub (by omega)]
  · rw [if_neg hlast]
    by_cases halt : (i : ℕ) + 1 = m
    · have hlt : ¬ (i : ℕ) + 1 < m := by omega
      rw [if_pos halt, if_neg hlt, c.finrank_alt hσ]
    · have hlt : (i : ℕ) + 1 < m := by
        have hi := i.is_lt
        have hne : (i : ℕ) ≠ m := by
          intro h
          exact hlast (Fin.ext (by simpa [Fin.val_last] using h))
        omega
      rw [if_neg halt, if_pos hlt, c.finrank_sub (by omega)]

theorem elt_last_inf_alt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    c.elt (Fin.last m) ⊓ c.alt = c.sub m := by
  rw [elt, if_pos rfl]
  have hlast : c.sub (m + 1) = c.spanAt Finset.univ := by
    rw [sub]
    congr 1
    exact Finset.filter_true_of_mem fun l _ => l.is_lt
  rw [hlast, inf_comm]
  exact c.alt_inf_spanAt_univ hσ

end Twin

end FlipFrame

theorem isFlipflopSub_inf_of_isLagrangian (hσ : ∀ x, σ (σ x) = x)
    {M N : Submodule K (Fin n ⊕ Fin n → K)}
    (hM : IsFlipflopSub σ M) (hML : (quadPlusForm n K).IsLagrangian M)
    (hN : IsFlipflopSub σ N) (hNL : (quadPlusForm n K).IsLagrangian N)
    (hMN : Module.finrank K ↥(M ⊓ N) + 1 = n) :
    IsFlipflopSub σ (M ⊓ N) := by
  have hV : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hMfin : Module.finrank K M = n := by
    have := hML.2
    omega
  have hNfin : Module.finrank K N = n := by
    have := hNL.2
    omega
  have hdim : Module.finrank K ↥(M ⊓ N) + 1 = Module.finrank K M := by
    rw [hMfin]
    exact hMN
  have hperp : (quadPlusForm n K).polar.perp (M ⊓ N) = M ⊔ N := by
    have hle : M ⊔ N ≤ (quadPlusForm n K).polar.perp (M ⊓ N) := by
      refine sup_le ?_ ?_
      · intro v hv
        rw [ReflForm.mem_perp]
        intro w hw
        rw [quadPlusForm_polar]
        have hle : M ≤ (quadPlusForm n K).polar.perp M := hML.1.isTotallyIsotropic
        have h := hle hw.1 v hv
        rw [quadPlusForm_polar, QuadraticMap.polar_comm] at h
        exact h
      · intro v hv
        rw [ReflForm.mem_perp]
        intro w hw
        rw [quadPlusForm_polar]
        have hle : N ≤ (quadPlusForm n K).polar.perp N := hNL.1.isTotallyIsotropic
        have h := hle hw.2 v hv
        rw [quadPlusForm_polar, QuadraticMap.polar_comm] at h
        exact h
    have h1 := (quadPlusForm n K).polar.finrank_perp (M ⊓ N)
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq M N
    have hfin : Module.finrank K ((quadPlusForm n K).polar.perp (M ⊓ N)) =
        Module.finrank K ↥(M ⊔ N) := by
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [← quadPlusForm_Q]
    exact hML.1 x hx.1
  · intro x hx hrad
    have hQx : quadPlus n K x = 0 := by
      rw [← quadPlusForm_Q]
      exact hML.1 x hx.1
    have hdx : dFlip σ x ∈ M ⊔ N := by
      rw [← hperp, ReflForm.mem_perp]
      intro y hy
      rw [quadPlusForm_polar]
      have hyx : flipHerm σ y x = 0 := by
        rw [← flipHerm_conj hσ x y, hrad y hy, map_zero]
      exact hyx
    have hQdx : (quadPlusForm n K).Q (dFlip σ x) = 0 := by
      rw [quadPlusForm_Q, quadPlus_dFlip, hQx, map_zero]
    rcases hML.mem_or_mem_of_mem_sup hNL hdim hdx hQdx with hdxM | hdxN
    · have hxM : ∀ v ∈ M, flipHerm σ x v = 0 := by
        intro v hv
        have hzero : flipHerm σ v x = 0 := by
          have hle : M ≤ (quadPlusForm n K).polar.perp M := hML.1.isTotallyIsotropic
          have h := hle hv (dFlip σ x) hdxM
          rw [quadPlusForm_polar, QuadraticMap.polar_comm] at h
          exact h
        rw [← flipHerm_conj hσ v x, hzero, map_zero]
      exact hM.nondeg x hx.1 hxM
    · have hxN : ∀ v ∈ N, flipHerm σ x v = 0 := by
        intro v hv
        have hzero : flipHerm σ v x = 0 := by
          have hle : N ≤ (quadPlusForm n K).polar.perp N := hNL.1.isTotallyIsotropic
          have h := hle hv (dFlip σ x) hdxN
          rw [quadPlusForm_polar, QuadraticMap.polar_comm] at h
          exact h
        rw [← flipHerm_conj hσ v x, hzero, map_zero]
      exact hN.nondeg x hx.2 hxN

end CFSG.ClassicalInvolution.PhanDn

end
