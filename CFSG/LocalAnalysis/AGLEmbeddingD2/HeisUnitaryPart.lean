module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitaryArith
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PartStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary

public section

namespace CFSG.AGLEmbeddingD2.HeisUnitary

open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Unitary CFSG.Quasithin
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Cuts

open Classical

@[expose] noncomputable def cutCount (L : ℕ → Prop) (x : ℕ) : ℕ := Nat.count (fun y => ¬ L y) x

variable {L : ℕ → Prop}

theorem cutCount_succ_of_linked {y : ℕ} (h : L y) : cutCount L (y + 1) = cutCount L y := by
  unfold cutCount
  rw [Nat.count_succ]
  simp [h]

theorem cutCount_succ_of_not_linked {y : ℕ} (h : ¬ L y) :
    cutCount L (y + 1) = cutCount L y + 1 := by
  unfold cutCount
  rw [Nat.count_succ]
  simp [h]

theorem cutCount_mono : Monotone (cutCount L) := Nat.count_monotone _

theorem linked_of_cutCount_eq {x y : ℕ} (h : cutCount L x = cutCount L y) {k : ℕ} (hk1 : x ≤ k)
    (hk2 : k < y) : L k := by
  by_contra hk
  have h1 := cutCount_succ_of_not_linked hk
  have h2 : cutCount L x ≤ cutCount L k := cutCount_mono hk1
  have h3 : cutCount L (k + 1) ≤ cutCount L y := cutCount_mono hk2
  omega

theorem cutCount_eq_of_between {x y z : ℕ} (h : cutCount L x = cutCount L y) (hxz : x ≤ z)
    (hzy : z ≤ y) : cutCount L z = cutCount L x := by
  have h1 := cutCount_mono (L := L) hxz
  have h2 := cutCount_mono (L := L) hzy
  omega

theorem cutCount_eq_of_forall_linked {x y : ℕ} (hxy : x ≤ y) (h : ∀ k, x ≤ k → k < y → L k) :
    cutCount L y = cutCount L x := by
  induction y, hxy using Nat.le_induction with
  | base => rfl
  | succ y hxy ih =>
    rw [cutCount_succ_of_linked (h y hxy (by omega)), ih (fun k hk1 hk2 => h k hk1 (by omega))]

theorem cutCount_reflect {n : ℕ} (hsym : ∀ y, y + 2 ≤ n → (L y ↔ L (n - 2 - y))) :
    ∀ x, x + 1 ≤ n → cutCount L (n - 1 - x) + cutCount L x = cutCount L (n - 1) := by
  intro x
  induction x with
  | zero => intro _; simp [cutCount, Nat.count_zero]
  | succ x ih =>
    intro hx
    have h1 := ih (by omega)
    have hL : L (n - 2 - x) ↔ L x := (hsym x (by omega)).symm
    have e1 : n - 1 - x = (n - 2 - x) + 1 := by omega
    have e2 : n - 1 - (x + 1) = n - 2 - x := by omega
    rw [e1] at h1
    rw [e2]
    by_cases hx' : L x
    · have hy' : L (n - 2 - x) := hL.2 hx'
      rw [cutCount_succ_of_linked hy'] at h1
      rw [cutCount_succ_of_linked hx']
      exact h1
    · have hy' : ¬ L (n - 2 - x) := fun h => hx' (hL.1 h)
      rw [cutCount_succ_of_not_linked hy'] at h1
      rw [cutCount_succ_of_not_linked hx']
      omega

end Cuts

section Links

@[expose] def linked (n : ℕ) (N : ℕ → Prop) (y : ℕ) : Prop := N (min y (n - 2 - y))

theorem linked_symm {n : ℕ} {N : ℕ → Prop} {y : ℕ} (hy : y + 2 ≤ n) :
    linked n N y ↔ linked n N (n - 2 - y) := by
  unfold linked
  rw [show n - 2 - (n - 2 - y) = y by omega, min_comm]

@[expose] def NoTriple (m : ℕ) (N : ℕ → Prop) : Prop :=
  ∀ a b c, a + 2 ≤ b → b + 2 ≤ c → c + 1 < m → N a → N b → N c → False

theorem false_of_oneSided {n : ℕ} {N : ℕ → Prop} (hnt : NoTriple (n / 2) N) {x y : ℕ}
    (hxy : x + 9 ≤ y) (hy : y < n) (h : cutCount (linked n N) x = cutCount (linked n N) y)
    (hone : 2 * y + 1 < n ∨ n < 2 * x + 1) : False := by
  have hl := fun k hk1 hk2 => linked_of_cutCount_eq h (k := k) hk1 hk2
  rcases hone with hone | hone
  · have l0 : linked n N x := hl x le_rfl (by omega)
    have l2 : linked n N (x + 2) := hl (x + 2) (by omega) (by omega)
    have l4 : linked n N (x + 4) := hl (x + 4) (by omega) (by omega)
    unfold linked at l0 l2 l4
    rw [min_eq_left (by omega)] at l0 l2 l4
    exact hnt x (x + 2) (x + 4) (by omega) (by omega) (by omega) l0 l2 l4
  · have l0 : linked n N x := hl x le_rfl (by omega)
    have l2 : linked n N (x + 2) := hl (x + 2) (by omega) (by omega)
    have l4 : linked n N (x + 4) := hl (x + 4) (by omega) (by omega)
    unfold linked at l0 l2 l4
    rw [min_eq_right (by omega)] at l0 l2 l4
    exact hnt (n - 2 - (x + 4)) (n - 2 - (x + 2)) (n - 2 - x) (by omega) (by omega) (by omega)
      l4 l2 l0

theorem false_of_big_symmetric {n : ℕ} {N : ℕ → Prop} (hnt : NoTriple (n / 2) N) {x y : ℕ}
    (hxy : x + 19 ≤ y) (hsym : y + x + 1 = n)
    (h : cutCount (linked n N) x = cutCount (linked n N) y) : False := by
  have hl := fun k hk1 hk2 => linked_of_cutCount_eq h (k := k) hk1 hk2
  have l0 : linked n N x := hl x le_rfl (by omega)
  have l2 : linked n N (x + 2) := hl (x + 2) (by omega) (by omega)
  have l4 : linked n N (x + 4) := hl (x + 4) (by omega) (by omega)
  unfold linked at l0 l2 l4
  rw [min_eq_left (by omega)] at l0 l2 l4
  exact hnt x (x + 2) (x + 4) (by omega) (by omega) (by omega) l0 l2 l4

theorem all_nodes_of_block_five {n : ℕ} {N : ℕ → Prop} (hn : n = 5 ∨ n = 6) {x y : ℕ}
    (hxy : x + 4 ≤ y) (hy : y < n) (h : cutCount (linked n N) x = cutCount (linked n N) y) :
    ∀ j, j < n / 2 → N j := by
  have hl := fun k hk1 hk2 => linked_of_cutCount_eq h (k := k) hk1 hk2
  intro j hj
  rcases hn with rfl | rfl
  · have hx : x = 0 := by omega
    subst hx
    have l0 := hl 0 le_rfl (by omega)
    have l1 := hl 1 (by omega) (by omega)
    unfold linked at l0 l1
    norm_num at l0 l1
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> assumption
  · have hx : x = 0 ∨ x = 1 := by omega
    rcases hx with rfl | rfl
    · have l0 := hl 0 le_rfl (by omega)
      have l1 := hl 1 (by omega) (by omega)
      have l2 := hl 2 (by omega) (by omega)
      unfold linked at l0 l1 l2
      norm_num at l0 l1 l2
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> assumption
    · have l1 := hl 1 le_rfl (by omega)
      have l2 := hl 2 (by omega) (by omega)
      have l3 := hl 3 (by omega) (by omega)
      have l4 := hl 4 (by omega) (by omega)
      unfold linked at l1 l2 l3 l4
      norm_num at l1 l2 l3 l4
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> assumption

theorem exists_minmax_of_card {n : ℕ} (A : Finset (Fin n)) {K : ℕ} (hK : 1 ≤ K)
    (hA : K ≤ A.card) : ∃ x y : Fin n, x ∈ A ∧ y ∈ A ∧ x.val + (K - 1) ≤ y.val ∧
      ∀ z ∈ A, x ≤ z ∧ z ≤ y := by
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  refine ⟨A.min' hne, A.max' hne, A.min'_mem hne, A.max'_mem hne, ?_, fun z hz =>
    ⟨A.min'_le z hz, A.le_max' z hz⟩⟩
  have hsub : A.card ≤ (Finset.Icc (A.min' hne).val (A.max' hne).val).card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => by
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨A.min'_le i hi, A.le_max' i hi⟩) (fun i _ j _ h => Fin.ext h)
  rw [Nat.card_Icc] at hsub
  have := (A.min'_le _ (A.max'_mem hne))
  have h2 : (A.min' hne).val ≤ (A.max' hne).val := this
  omega

open Classical in
theorem class_card_cases {n : ℕ} {N : ℕ → Prop} (hnt : NoTriple (n / 2) N) (c : ℕ) :
    Fintype.card {i : Fin n // cutCount (linked n N) i.val = c} < 10 ∨
      (cutCount (linked n N) (n - 1) = 2 * c ∧
        Fintype.card {i : Fin n // cutCount (linked n N) i.val = c} < 20 ∧
        ∀ i : Fin n, cutCount (linked n N) i.val = c → cutCount (linked n N) (Fin.rev i).val = c)
    := by
  rw [Fintype.card_subtype]
  set A : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => cutCount (linked n N) i.val = c)
    with hA
  have hmem : ∀ i : Fin n, i ∈ A ↔ cutCount (linked n N) i.val = c := fun i => by
    simp [hA]
  by_cases h10 : A.card < 10
  · exact Or.inl h10
  right
  have hsymm : ∀ y, y + 2 ≤ n → (linked n N y ↔ linked n N (n - 2 - y)) :=
    fun y hy => linked_symm hy
  obtain ⟨x, y, hx, hy, hxy, hall⟩ := exists_minmax_of_card A (K := 10) (by norm_num)
    (not_lt.1 h10)
  rw [hmem] at hx hy
  have hxy9 : x.val + 9 ≤ y.val := by simpa using hxy
  have hxyc : cutCount (linked n N) x.val = cutCount (linked n N) y.val := hx.trans hy.symm
  have hnotone : ¬ (2 * y.val + 1 < n ∨ n < 2 * x.val + 1) := fun hone =>
    false_of_oneSided hnt hxy9 y.2 hxyc hone
  have hxn := x.2
  have hyn := y.2
  have hT : cutCount (linked n N) (n - 1) = 2 * c := by
    set z : ℕ := max x.val (n - 1 - y.val) with hz
    have hzx : x.val ≤ z := le_max_left _ _
    have hzy : z ≤ y.val := max_le (by omega) (by omega)
    have hz1 : cutCount (linked n N) z = c := (cutCount_eq_of_between hxyc hzx hzy).trans hx
    have hrz1 : x.val ≤ n - 1 - z := by omega
    have hrz2 : n - 1 - z ≤ y.val := by omega
    have hz2 : cutCount (linked n N) (n - 1 - z) = c :=
      (cutCount_eq_of_between hxyc hrz1 hrz2).trans hx
    have := cutCount_reflect hsymm z (by omega)
    omega
  have hrev : ∀ i : Fin n, cutCount (linked n N) i.val = c →
      cutCount (linked n N) (Fin.rev i).val = c := by
    intro i hi
    have := cutCount_reflect hsymm i.val (by omega)
    rw [Fin.val_rev]
    have e : n - (i.val + 1) = n - 1 - i.val := by omega
    rw [e]
    omega
  refine ⟨hT, ?_, hrev⟩
  by_contra h20
  obtain ⟨x', y', hx', hy', hxy', hall'⟩ := exists_minmax_of_card A (K := 20) (by norm_num)
    (not_lt.1 h20)
  have hx'' := (hmem x').1 hx'
  have hy'' := (hmem y').1 hy'
  have hxy19 : x'.val + 19 ≤ y'.val := by simpa using hxy'
  have h1 : (Fin.rev x') ∈ A := (hmem _).2 (hrev x' hx'')
  have h2 : (Fin.rev y') ∈ A := (hmem _).2 (hrev y' hy'')
  have h3 := (hall' _ h1).2
  have h4 := (hall' _ h2).1
  rw [Fin.le_def, Fin.val_rev] at h3 h4
  have hx'n := x'.2
  have hy'n := y'.2
  exact false_of_big_symmetric hnt hxy19 (by omega) (hx''.trans hy''.symm)

open Classical in
theorem class_card_small {n : ℕ} {N : ℕ → Prop} (hn : n = 5 ∨ n = 6) {j : ℕ} (hj : j < n / 2)
    (hjN : ¬ N j) (c : ℕ) : Fintype.card {i : Fin n // cutCount (linked n N) i.val = c} < 5 := by
  rw [Fintype.card_subtype]
  set A : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => cutCount (linked n N) i.val = c)
    with hA
  have hmem : ∀ i : Fin n, i ∈ A ↔ cutCount (linked n N) i.val = c := fun i => by
    simp [hA]
  by_contra h5
  obtain ⟨x, y, hx, hy, hxy, -⟩ := exists_minmax_of_card A (K := 5) (by norm_num) (not_lt.1 h5)
  rw [hmem] at hx hy
  have hxy4 : x.val + 4 ≤ y.val := by simpa using hxy
  exact hjN (all_nodes_of_block_five hn hxy4 y.2 (hx.trans hy.symm) j hj)

end Links

section Class

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def classHerm (h : UnitaryFieldData p f F) {C : Type} [Fintype C]
    (r : C → C) : (C → F) →ₛₗ[h.bar] (C → F) →ₗ[F] F :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id F) (fun x y => ∑ i, h.bar (x i) * y (r i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem classHerm_apply (h : UnitaryFieldData p f F) {C : Type} [Fintype C] (r : C → C)
    (x y : C → F) : classHerm h r x y = ∑ i, h.bar (x i) * y (r i) := rfl

theorem classHerm_isSymm (h : UnitaryFieldData p f F) {C : Type} [Fintype C] (r : C → C)
    (hr : ∀ i, r (r i) = i) : (classHerm h r).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [classHerm_apply, classHerm_apply, map_sum]
  let e : C ≃ C := Function.Involutive.toPerm r hr
  have h1 : ∑ i, h.bar (y (r i)) * x (r (r i)) = ∑ i, h.bar (y i) * x (r i) :=
    Equiv.sum_comp e (fun j => h.bar (y j) * x (r j))
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.bar_bar, hr, mul_comm]

theorem classHerm_separatingLeft (h : UnitaryFieldData p f F) {C : Type} [Fintype C]
    [DecidableEq C] (r : C → C) (hr : ∀ i, r (r i) = i) : (classHerm h r).SeparatingLeft := by
  intro x hx
  funext i
  have h1 := hx (Pi.single (r i) 1)
  rw [classHerm_apply, Finset.sum_eq_single i] at h1
  · rw [Pi.single_eq_same, mul_one] at h1
    exact (map_eq_zero_iff h.bar h.bar.injective).1 h1
  · intro j _ hji
    have : r j ≠ r i := fun e => hji (by simpa [hr] using congrArg r e)
    rw [Pi.single_eq_of_ne this, mul_zero]
  · simp

theorem classHerm_mulVec (h : UnitaryFieldData p f F) {C : Type} [Fintype C] [DecidableEq C]
    (r : C → C) (g : Matrix C C F)
    (hg : ∀ u v : C, ∑ i, h.bar (g i u) * g (r i) v = if v = r u then 1 else 0)
    (x y : C → F) : classHerm h r (g.mulVec x) (g.mulVec y) = classHerm h r x y := by
  rw [classHerm_apply, classHerm_apply]
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ i, h.bar (∑ u, g i u * x u) * ∑ v, g (r i) v * y v
      = ∑ i, ∑ u, ∑ v, (h.bar (x u) * y v) * (h.bar (g i u) * g (r i) v) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [map_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ = ∑ u, ∑ v, ∑ i, (h.bar (x u) * y v) * (h.bar (g i u) * g (r i) v) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ u, ∑ v, (h.bar (x u) * y v) * (if v = r u then 1 else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum, hg]
    _ = ∑ u, h.bar (x u) * y (r u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp [mul_ite]

theorem isMulCommutative_of_unitary_class [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    {C : Type} [Fintype C] [DecidableEq C] (r : C → C) (hr : ∀ i, r (r i) = i)
    (hN : 1 ≤ Fintype.card C) (h : Fintype.card C / orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) < 5)
    {R : Subgroup (GL C F)} (hR : IsPGroup 5 R)
    (hu : ∀ g ∈ R, ∀ u v : C, ∑ i, unitaryInvolution F 2 f ((g : Matrix C C F) i u) *
      (g : Matrix C C F) (r i) v = if v = r u then 1 else 0) : IsMulCommutative R := by
  have hf : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    subst this
    have h1 : Nat.card F = 1 := by rw [hF]; norm_num
    have := Finite.one_lt_card (α := F)
    omega
  let h₀ : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hbar : ∀ c, h₀.bar c = unitaryInvolution F 2 f c := fun c => by
    rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  let S : FormSpace F F := ⟨C → F, fun x y => classHerm h₀ r x y⟩
  have hS : IsHermitianSpace h₀ S := ⟨classHerm h₀ r, fun _ _ => rfl,
    classHerm_isSymm h₀ r hr, classHerm_separatingLeft h₀ r hr⟩
  obtain ⟨ψ, hψ⟩ := exists_injective_isom_statedGU (q := 2 ^ f) rfl S hS
    (n := Fintype.card C) (Module.finrank_fintype_fun_eq_card F)
  set M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun F C) with hMdef
  have hM : ∀ (g : GL C F) (v : C → F), (M.symm g) v = (g : Matrix C C F).mulVec v := fun g v => by
    have := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
      (Pi.basisFun F C) (M.symm g) v
    rw [← hMdef, MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hmem : ∀ g : R, M.symm (g : GL C F) ∈ S.isom := fun g x y => by
    change classHerm h₀ r (M.symm (g : GL C F) x) (M.symm (g : GL C F) y) = classHerm h₀ r x y
    rw [hM, hM]
    exact classHerm_mulVec h₀ r _ (fun u v => by
      simpa only [hbar] using hu g g.2 u v) x y
  let ι : R →* S.isom :=
    { toFun := fun g => ⟨M.symm (g : GL C F), hmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (M.symm.injective (congrArg Subtype.val hab))
  let θ : R →* StatedGU (Fintype.card C) (2 ^ f) F := ψ.comp ι
  have hθ : Function.Injective θ := hψ.comp hι
  have hrange : IsPGroup 5 θ.range := hR.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hc := isMulCommutative_of_isPGroup_five_statedGU hF (not_five_dvd_two_pow f) hN h hrange
  refine ⟨⟨fun a b => ?_⟩⟩
  have := hc.is_comm.comm ⟨θ a, a, rfl⟩ ⟨θ b, b, rfl⟩
  have h1 : θ (a * b) = θ (b * a) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val this
  exact hθ h1

end Class

section Part

open CFSG.LieType.Universal.Unitary.SUExtras CFSG.AGLEmbeddingD2.PartStab

variable {F : Type} [Field F] [Finite F] {f n : ℕ}

@[expose] def partSU (σ : F ≃+* F) (s : Fin n → ℕ) : Subgroup (SU σ n) :=
  (partStab F s).comap (SU σ n).subtype

theorem mem_partSU {σ : F ≃+* F} {s : Fin n → ℕ} {g : SU σ n} :
    g ∈ partSU σ s ↔ IsPartDiag s (mat σ n g) := Iff.rfl

@[expose] def SmallBlock (f d : ℕ) : Prop := (f % 2 = 1 ∧ d < 10) ∨ (f % 2 = 0 ∧ d < 5)

theorem isMulCommutative_of_le_partSU [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (s : Fin n → ℕ) {Q : Subgroup (SU (unitaryInvolution F 2 f) n)} (hQ : IsPGroup 5 Q)
    (hQs : Q ≤ partSU (unitaryInvolution F 2 f) s)
    (hcls : ∀ c : ℕ, SmallBlock f (Fintype.card {i : Fin n // s i = c}) ∨
      (1 ≤ Fintype.card {i : Fin n // s i = c} ∧
        Fintype.card {i : Fin n // s i = c} / orderOf (-(((2 ^ f : ℕ)) : ZMod 5)) < 5 ∧
        ∀ i : Fin n, s i = c → s (Fin.rev i) = c)) : IsMulCommutative Q := by
  classical
  let σ := unitaryInvolution F 2 f
  let Θ : Q →* partStab F s :=
    { toFun := fun g => ⟨((g : SU σ n) : GL (Fin n) F), hQs g.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hΘ : Function.Injective Θ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : partStab F s => (z : GL (Fin n) F)) hab))
  have hcomm : ∀ (c : ℕ) (a b : Q), (blockHom s c).comp Θ a * (blockHom s c).comp Θ b =
      (blockHom s c).comp Θ b * (blockHom s c).comp Θ a := by
    intro c a b
    set Θc := (blockHom s c).comp Θ with hΘc
    have hrange : IsPGroup 5 Θc.range := hQ.of_surjective Θc.rangeRestrict
      Θc.rangeRestrict_surjective
    have hcm : IsMulCommutative Θc.range := by
      rcases hcls c with hsm | ⟨hN, hlt, hr⟩
      · refine isMulCommutative_of_isPGroup_five_GL_fintype (f := 2 * f)
          (by rw [hF, ← pow_mul, mul_comm]) ?_ Θc.range hrange
        rcases hsm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨by omega, h2⟩)
        · exact Or.inr (Or.inr ⟨by omega, h2⟩)
      · refine isMulCommutative_of_unitary_class hF (C := {i : Fin n // s i = c})
          (fun i => ⟨Fin.rev i.1, hr i.1 i.2⟩) (fun i => Subtype.ext (Fin.rev_rev _)) hN hlt
          hrange ?_
        rintro _ ⟨x, rfl⟩ u v
        have hx : IsPartDiag s (mat σ n (x : SU σ n)) := hQs x.2
        have key := sum_mat_mul_mat (x : SU σ n) u.1 v.1
        have hsplit := Fintype.sum_subtype_add_sum_subtype (fun t : Fin n => s t = c)
          (fun t => σ (mat σ n (x : SU σ n) t u.1) * mat σ n (x : SU σ n) (Fin.rev t) v.1)
        have hzero : ∑ t : {t : Fin n // ¬ s t = c},
            σ (mat σ n (x : SU σ n) t.1 u.1) * mat σ n (x : SU σ n) (Fin.rev t.1) v.1 = 0 := by
          refine Finset.sum_eq_zero fun t _ => ?_
          rw [hx t.1 u.1 (by rw [u.2]; exact t.2), map_zero, zero_mul]
        rw [hzero, add_zero, key] at hsplit
        change ∑ t : {t : Fin n // s t = c}, σ (mat σ n (x : SU σ n) t.1 u.1) *
          mat σ n (x : SU σ n) (Fin.rev t.1) v.1 = _
        rw [hsplit]
        simp only [Subtype.ext_iff]
    have := hcm.is_comm.comm ⟨Θc a, a, rfl⟩ ⟨Θc b, b, rfl⟩
    exact congrArg Subtype.val this
  refine ⟨⟨fun a b => ?_⟩⟩
  apply hΘ
  apply injective_pi_blockHom s
  funext c
  change (blockHom s c) (Θ (a * b)) = (blockHom s c) (Θ (b * a))
  rw [map_mul, map_mul, map_mul, map_mul]
  exact hcomm c a b

end Part

section Member

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.CurtisTits
  CFSG.AGLEmbeddingD2.PartStab CFSG.AGLEmbeddingD2.ParabLevi

@[expose] def nodeSet {n : ℕ} (I : Set (Fin (n / 2))) (k : ℕ) : Prop :=
  ∃ h : k < n / 2, (⟨k, h⟩ : Fin (n / 2)) ∈ I

@[expose] noncomputable def blkOf (n : ℕ) (N : ℕ → Prop) (x : Fin n) : ℕ :=
  cutCount (linked n N) x.val

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

theorem levelTorus_le_partSU (s : Fin n → ℕ) (k : Fin (n / 2)) :
    levelTorus (unitaryInvolution F 2 f) k ≤ partSU (unitaryInvolution F 2 f) s := by
  intro g hg
  rw [mem_partSU]
  obtain ⟨t, ht⟩ := levelTorus_le_diagSubgroup k hg
  intro a b hab
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  rw [mat_apply, ht, diagonal_apply_ne _ hne]

omit [Finite F] [CharP F 2] in
theorem isPartDiag_of_isBlk_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) {s : Fin n → ℕ}
    (h1 : s (lowIdx k) = s (lowIdx ⟨k.val + 1, hk⟩))
    (h2 : s (Fin.rev (lowIdx k)) = s (Fin.rev (lowIdx ⟨k.val + 1, hk⟩)))
    {M : Matrix (Fin n) (Fin n) F} (hM : IsBlk (blkShort k hk) M) : IsPartDiag s M := by
  intro a b hab
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  have hcond : ¬(blkShort k hk a = blkShort k hk b ∧ blkShort k hk a ≠ 0) := by
    rintro ⟨e, h0⟩
    apply hab
    have hv : blkShort k hk a = 1 ∨ blkShort k hk a = 2 := by
      unfold blkShort at h0 ⊢
      split_ifs at h0 ⊢ <;> simp_all
    rcases hv with hv | hv
    · have hv' : blkShort k hk b = 1 := e ▸ hv
      rw [blkShort_eq_one_iff] at hv hv'
      rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl <;>
        first | rfl | exact h1 | exact h1.symm
    · have hv' : blkShort k hk b = 2 := e ▸ hv
      rw [blkShort_eq_two_iff] at hv hv'
      rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl <;>
        first | rfl | exact h2 | exact h2.symm
  rw [hM a b hcond]
  exact Matrix.one_apply_ne hne

omit [Finite F] [CharP F 2] in
theorem isPartDiag_of_isBlk_last {k : Fin (n / 2)} {s : Fin n → ℕ}
    (hs : ∀ a b : Fin n, blkLast k a = 1 → blkLast k b = 1 → s a = s b)
    {M : Matrix (Fin n) (Fin n) F} (hM : IsBlk (blkLast k) M) : IsPartDiag s M := by
  intro a b hab
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  have hcond : ¬(blkLast k a = blkLast k b ∧ blkLast k a ≠ 0) := by
    rintro ⟨e, h0⟩
    have h1 := blkLast_eq_one_of_ne_zero h0
    exact hab (hs a b h1 (e ▸ h1))
  rw [hM a b hcond]
  exact Matrix.one_apply_ne hne

variable (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem rankOne_short_le_partSU {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) {s : Fin n → ℕ}
    (h1 : s (lowIdx k) = s (lowIdx ⟨k.val + 1, hk⟩))
    (h2 : s (Fin.rev (lowIdx k)) = s (Fin.rev (lowIdx ⟨k.val + 1, hk⟩))) :
    rankOne (rootDatum hF n).rootGroup k ≤ partSU (unitaryInvolution F 2 f) s :=
  fun _ hg => isPartDiag_of_isBlk_short hk h1 h2
    (isBlk_short_of_mem (hσ := unitaryInvolution_involutive hF) hk hg).1

include hF in
theorem rankOne_last_le_partSU {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) {s : Fin n → ℕ}
    (hs : ∀ a b : Fin n, blkLast k a = 1 → blkLast k b = 1 → s a = s b) :
    rankOne (rootDatum hF n).rootGroup k ≤ partSU (unitaryInvolution F 2 f) s :=
  fun _ hg => isPartDiag_of_isBlk_last hs
    (isBlk_last_of_mem (hσ := unitaryInvolution_involutive hF) hk hg)

variable {N : ℕ → Prop}

theorem blkOf_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (hN : N k.val) :
    blkOf n N (lowIdx k) = blkOf n N (lowIdx ⟨k.val + 1, hk⟩) ∧
      blkOf n N (Fin.rev (lowIdx k)) = blkOf n N (Fin.rev (lowIdx ⟨k.val + 1, hk⟩)) := by
  have hk' := k.isLt
  constructor
  · simp only [blkOf, val_lowIdx]
    refine (cutCount_succ_of_linked ?_).symm
    unfold linked
    rw [min_eq_left (by omega)]
    exact hN
  · simp only [blkOf, Fin.val_rev, val_lowIdx]
    have e1 : n - (k.val + 1) = (n - (k.val + 1 + 1)) + 1 := by omega
    rw [e1]
    refine cutCount_succ_of_linked ?_
    unfold linked
    rw [show min (n - (k.val + 1 + 1)) (n - 2 - (n - (k.val + 1 + 1))) = k.val by omega]
    exact hN

theorem blkOf_last {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) (hN : N k.val) :
    ∀ a b : Fin n, blkLast k a = 1 → blkLast k b = 1 → blkOf n N a = blkOf n N b := by
  have hk' := k.isLt
  have hlink : ∀ y, k.val ≤ y → y < n - 1 - k.val → linked n N y := by
    intro y hy1 hy2
    unfold linked
    rw [show min y (n - 2 - y) = k.val by omega]
    exact hN
  have hconst : cutCount (linked n N) (n - 1 - k.val) = cutCount (linked n N) k.val :=
    cutCount_eq_of_forall_linked (by omega) fun y h1 h2 => hlink y h1 (by omega)
  have hval : ∀ a : Fin n, blkLast k a = 1 → blkOf n N a = cutCount (linked n N) k.val := by
    intro a ha
    rw [blkLast_eq_one_iff] at ha
    have hrange : k.val ≤ a.val ∧ a.val ≤ n - 1 - k.val := by
      rcases ha with rfl | rfl | ha
      · simp only [val_lowIdx]
        omega
      · simp only [Fin.val_rev, val_lowIdx]
        omega
      · have := congrArg Fin.val ha
        simp only [Fin.val_rev] at this
        omega
    exact cutCount_eq_of_between hconst.symm hrange.1 hrange.2
  intro a b ha hb
  rw [hval a ha, hval b hb]

theorem leviM_le_of_forall {K : Type*} [Group K] {D : UniversalRootDatum K} {I : Set (Fin D.rank)}
    {S : Subgroup K} (h : ∀ i ∈ I, rankOne D.rootGroup i ≤ S) : leviM D I ≤ S :=
  iSup₂_le h

include hF in
theorem torus_sup_leviM_le_partSU (I : Set (Fin (n / 2))) :
    (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ⊔ leviM (rootDatum hF n) I ≤
      partSU (unitaryInvolution F 2 f) (blkOf n (nodeSet I)) := by
  refine sup_le (iSup_le fun k => levelTorus_le_partSU _ k) (leviM_le_of_forall fun k hk => ?_)
  have hN : nodeSet I k.val := ⟨k.isLt, hk⟩
  by_cases hs : k.val + 1 < n / 2
  · exact rankOne_short_le_partSU hF hs (blkOf_short hs hN).1 (blkOf_short hs hN).2
  · exact rankOne_last_le_partSU hF hs (blkOf_last hs hN)

end Member

end CFSG.AGLEmbeddingD2.HeisUnitary
