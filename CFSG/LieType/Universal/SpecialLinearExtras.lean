module

public import CFSG.LieType.Universal.SpecialLinearRoots
public import CFSG.LieType.Steinberg.Extras

public section

namespace CFSG.LieType.Universal.SpecialLinear

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

section Level

variable {n : ℕ} {R : Type*} [CommRing R] (s : Fin n → ℤ)

private def IdBelow (h : ℤ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ a b, s b - s a < h → M a b = (1 : Matrix (Fin n) (Fin n) R) a b

private theorem idBelow_one (h : ℤ) : IdBelow s h (1 : Matrix (Fin n) (Fin n) R) :=
  fun _ _ _ => rfl

private theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) R}
    (hM : IdBelow s h M) (hN : IdBelow s h N) {a b : Fin n} (hab : a ≠ b)
    (hlev : s b - s a ≤ h) : (M * N) a b = M a b + N a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM a a (by simpa using hh), hN b b (by simpa using hh)]
    simp [add_comm]
  · intro c _ ⟨hca, hcb⟩
    by_cases hc : s c - s a < h
    · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · rw [hN c b (by omega), Matrix.one_apply_ne hcb, mul_zero]
  · simp
  · simp

private theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) R}
    (hM : IdBelow s h M) (hN : IdBelow s h N) : IdBelow s h (M * N) := by
  intro a b hab
  by_cases hab' : a = b
  · subst hab'
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hM a a (by simpa using hh), hN a a (by simpa using hh)]
      simp
    · intro c _ hca
      by_cases hc : s c - s a < h
      · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
      · rw [hN c a (by omega), Matrix.one_apply_ne hca, mul_zero]
    · simp
  · rw [mul_apply_of_idBelow s hh hM hN hab' hab.le, hM a b hab, hN a b hab,
      Matrix.one_apply_ne hab', add_zero]

private theorem idBelow_transvection {h : ℤ} {p q : Fin n} (hlev : h ≤ s q - s p) (c : R) :
    IdBelow s h (Matrix.transvection p q c) := by
  intro a b hab
  have : ¬ (p = a ∧ q = b) := by
    rintro ⟨rfl, rfl⟩
    omega
  simp [Matrix.transvection, this]

private theorem transvection_apply_same {p q : Fin n} (hpq : p ≠ q) (c : R) :
    Matrix.transvection p q c p q = c := by
  simp [Matrix.transvection, Matrix.one_apply_ne hpq]

private theorem idBelow_list_prod {ι : Type*} {h : ℤ} (hh : 0 < h) (L : List ι)
    (f : ι → Matrix (Fin n) (Fin n) R) (hf : ∀ x ∈ L, IdBelow s h (f x)) :
    IdBelow s h (L.map f).prod ∧ ∀ a b, a ≠ b → s b - s a ≤ h →
      (L.map f).prod a b = (L.map fun x => f x a b).sum := by
  induction L with
  | nil => exact ⟨by simpa using idBelow_one s h, fun a b hab _ => by
      simp [Matrix.one_apply_ne hab]⟩
  | cons x L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun y hy => hf y (List.mem_cons_of_mem x hy)
    have hx := hf x List.mem_cons_self
    refine ⟨?_, fun a b hab hlev => ?_⟩
    · simpa using idBelow_mul s hh hx ih1
    · simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [mul_apply_of_idBelow s hh hx ih1 hab hlev, ih2 a b hab hlev]

private theorem eq_of_list_prod_eq {ι : Type*} (L : List ι) (hL : L.Nodup) (p q : ι → Fin n)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, p x = p y → q x = q y → x = y)
    (hlev : ∀ x ∈ L, 1 ≤ s (q x) - s (p x))
    (hsort : L.Pairwise fun x y => s (q x) - s (p x) ≤ s (q y) - s (p y))
    (c d : ι → R)
    (h : (L.map fun x => Matrix.transvection (p x) (q x) (c x)).prod =
      (L.map fun x => Matrix.transvection (p x) (q x) (d x)).prod) :
    ∀ x ∈ L, c x = d x := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.pairwise_cons] at hsort
    have hx1 := hlev x List.mem_cons_self
    have hpq : p x ≠ q x := by
      intro e
      rw [e] at hx1
      omega
    have htail : ∀ e : ι → R,
        IdBelow s (s (q x) - s (p x))
          (L.map fun y => Matrix.transvection (p y) (q y) (e y)).prod ∧
        (L.map fun y => Matrix.transvection (p y) (q y) (e y)).prod (p x) (q x) = 0 := by
      intro e
      obtain ⟨h1, h2⟩ := idBelow_list_prod s (by omega) L
        (fun y => Matrix.transvection (p y) (q y) (e y))
        (fun y hy => idBelow_transvection s (hsort.1 y hy) (e y))
      refine ⟨h1, ?_⟩
      rw [h2 _ _ hpq le_rfl]
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hne : ¬ (p y = p x ∧ q y = q x) := fun ⟨e1, e2⟩ => by
        have hyx : y = x := hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self e1 e2
        exact hL.1 (hyx ▸ hy)
      simp [Matrix.transvection, Matrix.one_apply_ne hpq, hne]
    have hentry : ∀ e : ι → R, (Matrix.transvection (p x) (q x) (e x) *
        (L.map fun y => Matrix.transvection (p y) (q y) (e y)).prod) (p x) (q x) = e x := by
      intro e
      obtain ⟨h1, h2⟩ := htail e
      rw [mul_apply_of_idBelow s (by omega) (idBelow_transvection s le_rfl (e x)) h1 hpq le_rfl,
        h2, add_zero, transvection_apply_same hpq]
    simp only [List.map_cons, List.prod_cons] at h
    have hcx : c x = d x := by rw [← hentry c, ← hentry d, h]
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hcx
    · refine ih hL.2 (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b
        (List.mem_cons_of_mem x hb)) (fun a ha => hlev a (List.mem_cons_of_mem x ha)) hsort.2 ?_
        y hy
      rw [hcx] at h
      have h' := congrArg (fun M => Matrix.transvection (p x) (q x) (-(d x)) * M) h
      simpa [← Matrix.mul_assoc, Matrix.transvection_mul_transvection_same _ _ hpq] using h'

end Level

variable (m : ℕ) (F : Type) [Field F]

@[expose] noncomputable def rootDatum : UniversalRootDatum (SpecialLinearGroup (Fin (m + 1)) F) where
  rank := m
  cartan := CartanMatrix.A m
  isFiniteType := isFiniteType_A m
  divisible := ∅
  rootGroup := rootGroup m F

private theorem toStd_add (v w : Fin m → ℤ) : toStd m (v + w) = toStd m v + toStd m w := by
  funext a
  simp only [toStd, Pi.add_apply]
  split_ifs <;> ring

theorem ht_eq_sum_toStd (v : Fin m → ℤ) :
    ht v = ∑ a : Fin (m + 1), ((m : ℤ) - a) * toStd m v a := by
  let f : (Fin m → ℤ) →+ ℤ :=
    { toFun := ht
      map_zero' := by simp [ht]
      map_add' := fun v w => by simp [ht, Finset.sum_add_distrib] }
  let g : (Fin m → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ a : Fin (m + 1), ((m : ℤ) - a) * toStd m v a
      map_zero' := by simp [toStd_zero]
      map_add' := fun v w => by simp [toStd_add, mul_add, Finset.sum_add_distrib] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin m → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change ht (Pi.single k x) = ∑ a : Fin (m + 1), ((m : ℤ) - a) * toStd m (Pi.single k x) a
    rw [hs, toStd_smul, toStd_single]
    simp [ht, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  exact DFunLike.congr_fun hfg v

theorem ht_eq {γ : Fin m → ℤ} {i j : Fin (m + 1)}
    (h : toStd m γ = Pi.single i 1 - Pi.single j 1) : ht γ = (j : ℤ) - i := by
  rw [ht_eq_sum_toStd, h]
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

open _root_.Classical in
noncomputable def idx (γ : Fin m → ℤ) : Fin (m + 1) × Fin (m + 1) :=
  if h : ∃ i j : Fin (m + 1), i ≠ j ∧ toStd m γ = Pi.single i 1 - Pi.single j 1 then
    (h.choose, h.choose_spec.choose) else (0, 0)

theorem idx_spec {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    (idx m γ).1 ≠ (idx m γ).2 ∧
      toStd m γ = Pi.single (idx m γ).1 1 - Pi.single (idx m γ).2 1 := by
  rw [roots_eq] at hγ
  unfold idx
  split_ifs with h
  · exact h.choose_spec.choose_spec
  · exact absurd hγ h

theorem ht_eq_idx {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    ht γ = ((idx m γ).2 : ℤ) - (idx m γ).1 :=
  ht_eq m (idx_spec m hγ).2

theorem rootGroup_eq_idx {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    rootGroup m F γ = rootSubgroup m F (idx_spec m hγ).1 :=
  rootGroup_eq m F (idx_spec m hγ).1 (idx_spec m hγ).2

theorem idx_injective {γ δ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅)
    (hδ : δ ∈ roots (isFiniteType_A m) ∅) (h1 : (idx m γ).1 = (idx m δ).1)
    (h2 : (idx m γ).2 = (idx m δ).2) : γ = δ :=
  toStd_injective m (by rw [(idx_spec m hγ).2, (idx_spec m hδ).2, h1, h2])

private theorem rootGroup_ne_bot {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    rootGroup m F γ ≠ ⊥ := by
  rw [rootGroup_eq_idx m F hγ]
  intro hbot
  have hmem := transvection_mem_rootSubgroup (m := m) (idx_spec m hγ).1 (1 : F)
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin (m + 1)) F =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (idx m γ).1 (idx m γ).2) hmem
  simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply_ne (idx_spec m hγ).1] at h1

private theorem two_smul_not_mem {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    2 • γ ∉ roots (isFiniteType_A m) ∅ := by
  intro h2
  obtain ⟨hne, hstd⟩ := idx_spec m hγ
  rw [roots_eq] at h2
  obtain ⟨k, l, -, h'⟩ := h2
  rw [two_nsmul, toStd_add, hstd] at h'
  have := congrFun h' (idx m γ).1
  simp [Pi.single_apply, hne] at this
  split_ifs at this <;> omega

private theorem toStd_add_of_eq {γ δ : Fin m → ℤ} {i j l : Fin (m + 1)}
    (hγ : toStd m γ = Pi.single i 1 - Pi.single j 1)
    (hδ : toStd m δ = Pi.single j 1 - Pi.single l 1) :
    toStd m (γ + δ) = Pi.single i 1 - Pi.single l 1 := by
  rw [toStd_add, hγ, hδ]
  abel

private theorem mem_openCone_add {γ δ : Fin m → ℤ} (h : γ + δ ∈ roots (isFiniteType_A m) ∅) :
    γ + δ ∈ openCone (roots (isFiniteType_A m) ∅) γ δ :=
  ⟨h, 1, 1, one_pos, one_pos, by simp⟩

private theorem commutator_mem {γ δ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅)
    (hδ : δ ∈ roots (isFiniteType_A m) ∅) (hind : LinIndepPair γ δ)
    {x y : SpecialLinearGroup (Fin (m + 1)) F} (hx : x ∈ rootGroup m F γ)
    (hy : y ∈ rootGroup m F δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_A m) ∅) γ δ, rootGroup m F ε := by
  have hγ' := hγ
  have hδ' := hδ
  rw [roots_eq] at hγ' hδ'
  obtain ⟨i, j, hij, hγs⟩ := hγ'
  obtain ⟨k, l, hkl, hδs⟩ := hδ'
  rw [rootGroup_eq m F hij hγs, mem_rootSubgroup] at hx
  rw [rootGroup_eq m F hkl hδs, mem_rootSubgroup] at hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hsum_ne : γ + δ ≠ 0 := fun h0 => by
    have := hind 1 1 (by simpa using h0)
    simp at this
  have hmem : ∀ {p r : Fin (m + 1)} (hpr : p ≠ r) (c : F),
      toStd m (γ + δ) = Pi.single p 1 - Pi.single r 1 →
      SpecialLinearGroup.transvection hpr c ∈
        ⨆ ε ∈ openCone (roots (isFiniteType_A m) ∅) γ δ, rootGroup m F ε := by
    intro p r hpr c hst
    have hroot : γ + δ ∈ roots (isFiniteType_A m) ∅ := by
      rw [roots_eq]
      exact ⟨p, r, hpr, hst⟩
    refine (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_A m) ∅) γ δ) =>
      rootGroup m F ε) (γ + δ) (mem_openCone_add m hroot)) ?_
    rw [rootGroup_eq m F hpr hst]
    exact transvection_mem_rootSubgroup hpr c
  by_cases hjk : j = k
  · subst hjk
    have hli : i ≠ l := by
      rintro rfl
      apply hsum_ne
      apply toStd_injective m
      rw [toStd_add, hγs, hδs, toStd_zero]
      abel
    rw [SpecialLinearGroup.commutatorElement_transvection hij hkl hli]
    exact hmem hli _ (toStd_add_of_eq m hγs hδs)
  · by_cases hli : l = i
    · subst hli
      have hkj : k ≠ j := Ne.symm hjk
      rw [← commutatorElement_inv, SpecialLinearGroup.commutatorElement_transvection hkl hij hkj]
      refine inv_mem (hmem hkj _ ?_)
      rw [add_comm γ δ]
      exact toStd_add_of_eq m hδs hγs
    · have hcomm := SpecialLinearGroup.commute_transvection hij hkl hjk hli a b
      rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
      exact one_mem _

theorem prodInjective_of (s : Fin (m + 1) → ℤ) (L : List (Fin m → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅)
    (hlev : ∀ γ ∈ L, 1 ≤ s (idx m γ).2 - s (idx m γ).1)
    (hsort : L.Pairwise fun γ δ => s (idx m γ).2 - s (idx m γ).1 ≤ s (idx m δ).2 - s (idx m δ).1) :
    ProdInjectiveFor (rootGroup m F) L := by
  intro f g hf hg hfg
  have hcoef : ∀ e : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F,
      (∀ γ ∈ L, e γ ∈ rootGroup m F γ) → ∃ c : (Fin m → ℤ) → F, ∀ γ ∈ L,
        (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          Matrix.transvection (idx m γ).1 (idx m γ).2 (c γ) := by
    intro e he
    have : ∀ γ, ∃ c : F, γ ∈ L → (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        Matrix.transvection (idx m γ).1 (idx m γ).2 c := by
      intro γ
      by_cases hγ : γ ∈ L
      · have hmem := he γ hγ
        rw [rootGroup_eq_idx m F (hroots γ hγ), mem_rootSubgroup] at hmem
        obtain ⟨c, hc⟩ := hmem
        exact ⟨c, fun _ => by rw [← hc]; rfl⟩
      · exact ⟨0, fun h => absurd h hγ⟩
    choose c hc using this
    exact ⟨c, fun γ hγ => hc γ hγ⟩
  obtain ⟨c, hc⟩ := hcoef f hf
  obtain ⟨d, hd⟩ := hcoef g hg
  have hcoe : ∀ (e : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F) (c' : (Fin m → ℤ) → F),
      (∀ γ ∈ L, (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        Matrix.transvection (idx m γ).1 (idx m γ).2 (c' γ)) →
      (((L.map e).prod : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (L.map fun γ => Matrix.transvection (idx m γ).1 (idx m γ).2 (c' γ)).prod := by
    intro e c' he
    rw [← SpecialLinearGroup.coeMonoidHom_apply, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun γ hγ => he γ hγ)
  have hmat := (hcoe f c hc).symm.trans ((congrArg _ hfg).trans (hcoe g d hd))
  have hcd := eq_of_list_prod_eq s L hL (fun γ => (idx m γ).1) (fun γ => (idx m γ).2)
    (fun γ hγ δ hδ h1 h2 => idx_injective m (hroots γ hγ) (hroots δ hδ) h1 h2) hlev hsort c d hmat
  intro γ hγ
  exact Subtype.ext (by rw [hc γ hγ, hd γ hγ, hcd γ hγ])

private theorem idBelow_of_mem_iSup (s : Fin (m + 1) → ℤ) (P : Set (Fin m → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ roots (isFiniteType_A m) ∅ ∧ 1 ≤ s (idx m γ).2 - s (idx m γ).1)
    {x : SpecialLinearGroup (Fin (m + 1)) F} (hx : x ∈ ⨆ γ ∈ P, rootGroup m F γ) :
    IdBelow s 1 (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : SpecialLinearGroup (Fin (m + 1)) F =>
    IdBelow s 1 (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (fun γ y hy => ?_) ?_
    fun y z hy hz => ?_
  · obtain ⟨hr, hl⟩ := hP γ.1 γ.2
    rw [rootGroup_eq_idx m F hr, mem_rootSubgroup] at hy
    obtain ⟨c, rfl⟩ := hy
    exact idBelow_transvection s hl c
  · simpa using idBelow_one s 1
  · simpa using idBelow_mul s one_pos hy hz

private theorem eq_one_of_idBelow {x : SpecialLinearGroup (Fin (m + 1)) F}
    (hpos : IdBelow (fun a : Fin (m + 1) => (a : ℤ)) 1 (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hneg : IdBelow (fun a : Fin (m + 1) => -(a : ℤ)) 1
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) : x = 1 := by
  ext a b
  change (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b
  rcases le_or_gt (b : ℕ) a with h | h
  · exact hpos a b (by simp only; omega)
  · exact hneg a b (by simp only; omega)

private theorem lev_pos {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) (h : 0 < ht γ) :
    1 ≤ (fun a : Fin (m + 1) => (a : ℤ)) (idx m γ).2 - (fun a : Fin (m + 1) => (a : ℤ)) (idx m γ).1 := by
  have := ht_eq_idx m hγ
  simp only
  omega

private theorem lev_neg {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) (h : ht γ < 0) :
    1 ≤ (fun a : Fin (m + 1) => -(a : ℤ)) (idx m γ).2 -
      (fun a : Fin (m + 1) => -(a : ℤ)) (idx m γ).1 := by
  have := ht_eq_idx m hγ
  simp only
  omega

private theorem posPart_inf_negPart :
    (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_A m) ∅ ∧ 0 < ht γ}, rootGroup m F γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_A m) ∅ ∧ ht γ < 0}, rootGroup m F γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_idBelow m F
    (idBelow_of_mem_iSup m F _ _ (fun γ hγ => ⟨hγ.1, lev_pos m hγ.1 hγ.2⟩) hxp)
    (idBelow_of_mem_iSup m F _ _ (fun γ hγ => ⟨hγ.1, lev_neg m hγ.1 hγ.2⟩) hxn)

private theorem torus_le_diagonalTorus' (k : Fin m) :
    torus m F k ≤ SpecialLinearGroup.diagonalTorus F (m + 1) := by
  rw [torus, Subgroup.closure_le]
  rintro h ⟨t, ht⟩
  exact SpecialLinearGroup.mem_diagonalTorus_iff.mpr (by rw [ht]; exact isDiag_diagonal _)

private theorem isDiag_of_mem_torus {k : Fin m} {h : SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ torus m F k) : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
  SpecialLinearGroup.mem_diagonalTorus_iff.mp (torus_le_diagonalTorus' m F k hh)

private theorem isDiag_mul' {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : M.IsDiag)
    (hN : N.IsDiag) : (M * N).IsDiag := by
  rw [← hM.diagonal_diag, ← hN.diagonal_diag, diagonal_mul_diagonal]
  exact isDiag_diagonal _

private theorem commute_of_isDiag {x y : SpecialLinearGroup (Fin (m + 1)) F}
    (hx : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    (hy : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) : Commute x y := by
  apply Subtype.ext
  change x.1 * y.1 = y.1 * x.1
  rw [← hx.diagonal_diag, ← hy.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private noncomputable def diagHom (k : Fin m) : Fˣ →* SpecialLinearGroup (Fin (m + 1)) F where
  toFun t := SpecialLinearGroup.diag2nUnit (Fin.castSucc_lt_succ (i := k)).ne t
  map_one' := by
    ext a b
    simp [Matrix.one_apply]
  map_mul' s t := by
    apply Subtype.ext
    change (SpecialLinearGroup.diag2nUnit _ (s * t)).1 =
      (SpecialLinearGroup.diag2nUnit _ s).1 * (SpecialLinearGroup.diag2nUnit _ t).1
    rw [SpecialLinearGroup.diag2nUnit_coe, SpecialLinearGroup.diag2nUnit_coe,
      SpecialLinearGroup.diag2nUnit_coe, diagonal_mul_diagonal]
    congr 1
    funext r
    split_ifs <;> simp [mul_comm]

private theorem torus_eq_range (k : Fin m) : torus m F k = (diagHom m F k).range := by
  apply le_antisymm
  · rw [torus, Subgroup.closure_le]
    rintro h ⟨t, ht⟩
    refine ⟨t, Subtype.ext ?_⟩
    change (SpecialLinearGroup.diag2nUnit _ t).1 = _
    rw [SpecialLinearGroup.diag2nUnit_coe, ht]
    congr 1
    funext r
    simp only [Function.update_apply, Pi.one_apply]
    have := (Fin.castSucc_lt_succ (i := k)).ne
    split_ifs <;> simp_all
  · rintro _ ⟨t, rfl⟩
    refine Subgroup.subset_closure ⟨t, ?_⟩
    change (SpecialLinearGroup.diag2nUnit _ t).1 = _
    rw [SpecialLinearGroup.diag2nUnit_coe]
    congr 1
    funext r
    simp only [Function.update_apply, Pi.one_apply]
    have := (Fin.castSucc_lt_succ (i := k)).ne
    split_ifs <;> simp_all

private noncomputable def prefixProd (k : Fin m) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : F :=
  ∏ a ∈ Finset.univ.filter (fun a : Fin (m + 1) => a.val ≤ k.val), M a a

private theorem prefixProd_mul {k : Fin m} {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : M.IsDiag) (hN : N.IsDiag) : prefixProd m F k (M * N) =
      prefixProd m F k M * prefixProd m F k N := by
  rw [prefixProd, prefixProd, prefixProd, ← Finset.prod_mul_distrib, ← hM.diagonal_diag,
    ← hN.diagonal_diag, diagonal_mul_diagonal]
  simp

private theorem prefixProd_diagHom (j k : Fin m) (t : Fˣ) :
    prefixProd m F k (diagHom m F j t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      if j = k then (t : F) else 1 := by
  have hpq := (Fin.castSucc_lt_succ (i := j)).ne
  change ∏ a ∈ Finset.univ.filter (fun a : Fin (m + 1) => a.val ≤ k.val),
    (SpecialLinearGroup.diag2nUnit hpq t).1 a a = _
  have hsplit : ∀ a : Fin (m + 1), (SpecialLinearGroup.diag2nUnit hpq t).1 a a =
      (if a = j.castSucc then (t : F) else 1) * (if a = j.succ then ((t⁻¹ : Fˣ) : F) else 1) := by
    intro a
    rw [SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_apply_eq]
    split_ifs with h1 h2 <;> simp_all
  simp only [hsplit, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
  rcases lt_trichotomy j.val k.val with h | h | h
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (Fin.ne_of_val_ne h.ne)]
    simp
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (Fin.ext h)]
    simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (Fin.ne_of_val_ne h.ne')]
    simp

private theorem torus_iSupIndep : iSupIndep (torus m F) := by
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  rw [torus_eq_range] at hxk
  obtain ⟨t, rfl⟩ := hxk
  have hP : ((diagHom m F k t : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag ∧
      prefixProd m F k (diagHom m F k t : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [iSup_subtype'] at hx
    refine Subgroup.iSup_induction _ hx (C := fun x : SpecialLinearGroup (Fin (m + 1)) F =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag ∧
        prefixProd m F k (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1)
      (fun j y hy => ?_) ?_ fun y z hy hz => ?_
    · have hy' := hy
      rw [torus_eq_range] at hy'
      obtain ⟨s, rfl⟩ := hy'
      exact ⟨isDiag_of_mem_torus m F hy, by rw [prefixProd_diagHom, ite_eq_right j.2]⟩
    · refine ⟨by simp, ?_⟩
      simp [prefixProd]
    · refine ⟨isDiag_mul' m F hy.1 hz.1, ?_⟩
      change prefixProd m F k (y.1 * z.1) = 1
      rw [prefixProd_mul m F hy.1 hz.1, hy.2, hz.2, one_mul]
  rw [prefixProd_diagHom, ite_eq_left rfl] at hP
  have ht : t = 1 := Units.ext hP.2
  rw [ht, map_one]

private theorem torus_inf_posPart :
    (⨆ i, torus m F i) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_A m) ∅ ∧ 0 < ht γ}, rootGroup m F γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  have hdiag : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
    refine Subgroup.iSup_induction _ hxt (C := fun x : SpecialLinearGroup (Fin (m + 1)) F =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) (fun k y hy => isDiag_of_mem_torus m F hy)
      (by simp) fun y z hy hz => isDiag_mul' m F hy hz
  have hpos := idBelow_of_mem_iSup m F (fun a : Fin (m + 1) => (a : ℤ)) _
    (fun γ hγ => ⟨hγ.1, lev_pos m hγ.1 hγ.2⟩) hxp
  ext a b
  change (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b
  by_cases hab : a = b
  · subst hab
    exact hpos a a (by simp)
  · rw [hdiag hab, Matrix.one_apply_ne hab]

section Block

variable {m F}

private def IsBlock (p q : Fin (m + 1)) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : Prop :=
  ∀ a b, (a ≠ p ∧ a ≠ q) ∨ (b ≠ p ∧ b ≠ q) →
    M a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b

private def toBlock (p q : Fin (m + 1)) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![M p p, M p q; M q p, M q q]

variable {p q : Fin (m + 1)}

private theorem mul_apply_block (hpq : p ≠ q) {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsBlock p q M) {a : Fin (m + 1)} (ha : a = p ∨ a = q) (b : Fin (m + 1)) :
    (M * N) a b = M a p * N p b + M a q * N q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add p q hpq]
  · intro c _ ⟨hcp, hcq⟩
    have hac : a ≠ c := by
      rintro rfl
      rcases ha with rfl | rfl <;> contradiction
    rw [hM a c (Or.inr ⟨hcp, hcq⟩), Matrix.one_apply_ne hac, zero_mul]
  · simp
  · simp

private theorem isBlock_mul {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hM : IsBlock p q M)
    (hN : IsBlock p q N) : IsBlock p q (M * N) := by
  intro a b hab
  rcases hab with hab | hab
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hM a a (Or.inl hab), Matrix.one_apply_eq, one_mul, hN a b (Or.inl hab)]
    · intro c _ hca
      rw [hM a c (Or.inl hab), Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · simp
  · rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [hN b b (Or.inr hab), Matrix.one_apply_eq, mul_one, hM a b (Or.inr hab)]
    · intro c _ hcb
      rw [hN c b (Or.inr hab), Matrix.one_apply_ne hcb, mul_zero]
    · simp

private theorem toBlock_mul (hpq : p ≠ q) {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsBlock p q M) : toBlock p q (M * N) = toBlock p q M * toBlock p q N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, mul_apply_block hpq hM (Or.inl rfl),
      mul_apply_block hpq hM (Or.inr rfl)]

private theorem eq_of_toBlock_eq {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : IsBlock p q M) (hN : IsBlock p q N) (h : toBlock p q M = toBlock p q N) : M = N := by
  ext a b
  by_cases ha : a = p ∨ a = q
  · by_cases hb : b = p ∨ b = q
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · simpa [toBlock] using congrFun (congrFun h 0) 0
      · simpa [toBlock] using congrFun (congrFun h 0) 1
      · simpa [toBlock] using congrFun (congrFun h 1) 0
      · simpa [toBlock] using congrFun (congrFun h 1) 1
    · rw [not_or] at hb
      rw [hM a b (Or.inr hb), hN a b (Or.inr hb)]
  · rw [not_or] at ha
    rw [hM a b (Or.inl ha), hN a b (Or.inl ha)]

private theorem isBlock_transvection {a b : Fin (m + 1)} (hab : (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (c : F) : IsBlock p q (Matrix.transvection a b c) := by
  intro x y hxy
  have : ¬ (a = x ∧ b = y) := by
    rintro ⟨rfl, rfl⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      contradiction
  simp [Matrix.transvection, this]

private theorem toBlock_transvection_pq (hpq : p ≠ q) (c : F) :
    toBlock p q (Matrix.transvection p q c) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBlock, Matrix.transvection, hpq, hpq.symm]

private theorem toBlock_transvection_qp (hpq : p ≠ q) (c : F) :
    toBlock p q (Matrix.transvection q p c) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBlock, Matrix.transvection, hpq, hpq.symm]

private theorem isBlock_diag2nUnit (hpq : p ≠ q) (t : Fˣ) :
    IsBlock p q (SpecialLinearGroup.diag2nUnit hpq t).1 := by
  intro a b hab
  rw [SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · simp [h]

private theorem toBlock_diag2nUnit (hpq : p ≠ q) (t : Fˣ) :
    toBlock p q (SpecialLinearGroup.diag2nUnit hpq t).1 = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] := by
  rw [SpecialLinearGroup.diag2nUnit_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, hpq, hpq.symm]

end Block

private theorem castSucc_ne_succ' (k : Fin m) : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne

private theorem rootGroup_single' (k : Fin m) :
    rootGroup m F (Pi.single k 1) = rootSubgroup m F (castSucc_ne_succ' m k) :=
  rootGroup_eq m F _ (toStd_single m k)

private theorem rootGroup_neg_single' (k : Fin m) :
    rootGroup m F (-Pi.single k 1) = rootSubgroup m F (castSucc_ne_succ' m k).symm :=
  rootGroup_eq m F _ (by rw [toStd_neg, toStd_single, neg_sub])

private theorem block_of_mem_rankOne (k : Fin m) {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ CurtisTits.rankOne (rootGroup m F) k) :
    IsBlock k.castSucc k.succ g.1 ∧ (toBlock k.castSucc k.succ g.1).det = 1 := by
  have hpq := castSucc_ne_succ' m k
  rw [CurtisTits.rankOne, rootGroup_single', rootGroup_neg_single', sup_eq_iSup] at hg
  refine Subgroup.iSup_induction _ hg (C := fun g : SpecialLinearGroup (Fin (m + 1)) F =>
    IsBlock k.castSucc k.succ g.1 ∧ (toBlock k.castSucc k.succ g.1).det = 1)
    (fun b x hx => ?_) ?_ fun x y hx hy => ?_
  · cases b
    · rw [Bool.cond_false, mem_rootSubgroup] at hx
      obtain ⟨c, rfl⟩ := hx
      exact ⟨isBlock_transvection (Or.inr ⟨rfl, rfl⟩) c, by
        rw [show (SpecialLinearGroup.transvection hpq.symm c).1 = Matrix.transvection _ _ c from rfl,
          toBlock_transvection_qp hpq, Matrix.det_fin_two_of]
        ring⟩
    · rw [Bool.cond_true, mem_rootSubgroup] at hx
      obtain ⟨c, rfl⟩ := hx
      exact ⟨isBlock_transvection (Or.inl ⟨rfl, rfl⟩) c, by
        rw [show (SpecialLinearGroup.transvection hpq c).1 = Matrix.transvection _ _ c from rfl,
          toBlock_transvection_pq hpq, Matrix.det_fin_two_of]
        ring⟩
  · refine ⟨fun a b _ => rfl, ?_⟩
    change (toBlock k.castSucc k.succ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).det = 1
    rw [toBlock, Matrix.det_fin_two_of]
    simp [hpq, hpq.symm]
  · refine ⟨isBlock_mul hx.1 hy.1, ?_⟩
    change (toBlock k.castSucc k.succ (x.1 * y.1)).det = 1
    rw [toBlock_mul hpq hx.1, Matrix.det_mul, hx.2, hy.2, one_mul]

private theorem toBlock_weylRep (k : Fin m) :
    toBlock k.castSucc k.succ (weylRep m F k).1 = !![0, 1; -1, 0] ∧
      IsBlock k.castSucc k.succ (weylRep m F k).1 := by
  have hpq := castSucc_ne_succ' m k
  have h1 := isBlock_transvection (F := F) (p := k.castSucc) (q := k.succ)
    (Or.inl ⟨rfl, rfl⟩) 1
  have h2 := isBlock_transvection (F := F) (p := k.castSucc) (q := k.succ)
    (Or.inr ⟨rfl, rfl⟩) (-1)
  have e : (weylRep m F k).1 = Matrix.transvection k.castSucc k.succ 1 *
      Matrix.transvection k.succ k.castSucc (-1) * Matrix.transvection k.castSucc k.succ 1 := rfl
  refine ⟨?_, by rw [e]; exact isBlock_mul (isBlock_mul h1 h2) h1⟩
  rw [e, toBlock_mul hpq (isBlock_mul h1 h2), toBlock_mul hpq h1, toBlock_transvection_pq hpq,
    toBlock_transvection_qp hpq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diag2nUnit_mem_torus' (k : Fin m) (t : Fˣ) :
    SpecialLinearGroup.diag2nUnit (castSucc_ne_succ' m k) t ∈ torus m F k := by
  rw [torus_eq_range]
  exact ⟨t, rfl⟩

private theorem rankOne_bruhat (k : Fin m) (g : SpecialLinearGroup (Fin (m + 1)) F)
    (hg : g ∈ CurtisTits.rankOne (rootGroup m F) k) :
    (∃ h ∈ torus m F k, ∃ u ∈ rootGroup m F (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup m F (Pi.single k 1), ∃ h ∈ torus m F k,
        ∃ v ∈ rootGroup m F (Pi.single k 1), g = u * weylRep m F k * h * v := by
  have hpq := castSucc_ne_succ' m k
  obtain ⟨hblk, hdet⟩ := block_of_mem_rankOne m F k hg
  rw [toBlock, Matrix.det_fin_two_of] at hdet
  obtain ⟨a, ha'⟩ : ∃ a, g.1 k.castSucc k.castSucc = a := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, g.1 k.castSucc k.succ = b := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, g.1 k.succ k.castSucc = c := ⟨_, rfl⟩
  obtain ⟨d, hd'⟩ : ∃ d, g.1 k.succ k.succ = d := ⟨_, rfl⟩
  simp only [ha', hb', hc', hd'] at hdet
  have hX : ∀ e : F, SpecialLinearGroup.transvection hpq e ∈ rootGroup m F (Pi.single k 1) := by
    intro e
    rw [rootGroup_single']
    exact transvection_mem_rootSubgroup hpq e
  have hT : ∀ e : F, IsBlock k.castSucc k.succ (SpecialLinearGroup.transvection hpq e).1 :=
    fun e => isBlock_transvection (Or.inl ⟨rfl, rfl⟩) e
  have hTb : ∀ e : F, toBlock k.castSucc k.succ (SpecialLinearGroup.transvection hpq e).1 =
      !![1, e; 0, 1] := fun e => toBlock_transvection_pq hpq e
  by_cases hc : c = 0
  · left
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, hc] at hdet
      simp at hdet
    refine ⟨SpecialLinearGroup.diag2nUnit hpq (Units.mk0 a ha), diag2nUnit_mem_torus' m F k _,
      SpecialLinearGroup.transvection hpq (b / a), hX _, ?_⟩
    apply Subtype.ext
    change g.1 = (SpecialLinearGroup.diag2nUnit hpq (Units.mk0 a ha)).1 *
      (SpecialLinearGroup.transvection hpq (b / a)).1
    refine eq_of_toBlock_eq hblk (isBlock_mul (isBlock_diag2nUnit hpq _) (hT _)) ?_
    rw [toBlock_mul hpq (isBlock_diag2nUnit hpq _), toBlock_diag2nUnit, hTb]
    have hd : d = a⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, ha', hb', hc', hd', hc, hd]
    field_simp
  · right
    refine ⟨SpecialLinearGroup.transvection hpq (a / c), hX _,
      SpecialLinearGroup.diag2nUnit hpq (Units.mk0 (-c) (neg_ne_zero.mpr hc)),
      diag2nUnit_mem_torus' m F k _, SpecialLinearGroup.transvection hpq (d / c), hX _, ?_⟩
    obtain ⟨hW, hWb⟩ := toBlock_weylRep m F k
    apply Subtype.ext
    change g.1 = (SpecialLinearGroup.transvection hpq (a / c)).1 * (weylRep m F k).1 *
      (SpecialLinearGroup.diag2nUnit hpq (Units.mk0 (-c) (neg_ne_zero.mpr hc))).1 *
      (SpecialLinearGroup.transvection hpq (d / c)).1
    refine eq_of_toBlock_eq hblk (isBlock_mul (isBlock_mul (isBlock_mul (hT _) hWb)
      (isBlock_diag2nUnit hpq _)) (hT _)) ?_
    rw [toBlock_mul hpq (isBlock_mul (isBlock_mul (hT _) hWb) (isBlock_diag2nUnit hpq _)),
      toBlock_mul hpq (isBlock_mul (hT _) hWb), toBlock_mul hpq (hT _), hTb, hTb, hW,
      toBlock_diag2nUnit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, ha', hb', hc', hd']
    · field_simp
    · rw [div_mul_cancel₀ a hc]
      field_simp
      linear_combination -hdet
    · field_simp

private theorem eq_one_of_mem_normalizer (k : Fin m) (u : SpecialLinearGroup (Fin (m + 1)) F)
    (hu : u ∈ rootGroup m F (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup m F (-Pi.single k 1) :
      Set (SpecialLinearGroup (Fin (m + 1)) F))) : u = 1 := by
  have hpq := castSucc_ne_succ' m k
  rw [rootGroup_single', mem_rootSubgroup] at hu
  obtain ⟨c, rfl⟩ := hu
  have hy : SpecialLinearGroup.transvection hpq.symm (1 : F) ∈ rootGroup m F (-Pi.single k 1) := by
    rw [rootGroup_neg_single']
    exact transvection_mem_rootSubgroup _ _
  have hconj := (Subgroup.mem_normalizer_iff.mp hn _).mp hy
  rw [rootGroup_neg_single', mem_rootSubgroup] at hconj
  obtain ⟨d, hd⟩ := hconj
  have hT : ∀ (e : F), IsBlock k.castSucc k.succ (Matrix.transvection k.castSucc k.succ e) :=
    fun e => isBlock_transvection (Or.inl ⟨rfl, rfl⟩) e
  have hT' : ∀ (e : F), IsBlock k.castSucc k.succ (Matrix.transvection k.succ k.castSucc e) :=
    fun e => isBlock_transvection (Or.inr ⟨rfl, rfl⟩) e
  have hmat := congrArg (fun g : SpecialLinearGroup (Fin (m + 1)) F =>
    toBlock k.castSucc k.succ g.1 0 0) hd
  rw [SpecialLinearGroup.transvection_inv] at hmat
  change toBlock k.castSucc k.succ (Matrix.transvection k.succ k.castSucc d) 0 0 =
    toBlock k.castSucc k.succ (Matrix.transvection k.castSucc k.succ c *
      Matrix.transvection k.succ k.castSucc 1 * Matrix.transvection k.castSucc k.succ (-c)) 0 0
    at hmat
  rw [toBlock_mul hpq (isBlock_mul (hT c) (hT' 1)), toBlock_mul hpq (hT c),
    toBlock_transvection_pq hpq, toBlock_transvection_pq hpq, toBlock_transvection_qp hpq,
    toBlock_transvection_qp hpq] at hmat
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hmat
  rw [hmat, SpecialLinearGroup.transvection_coeff_zero]

theorem steinbergExtras :
    SteinbergExtras (rootDatum m F) (weylRep m F) (torus m F) where
  ne_bot _ hγ := rootGroup_ne_bot m F hγ
  two_smul_le _ hγ h2 := absurd h2 (two_smul_not_mem m hγ)
  commutator_mem _ hγ _ hδ hind _ hx _ hy := commutator_mem m F hγ hδ hind hx hy
  prodInjective_pos L hL hmem hsort := by
    have hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅ := fun γ hγ => ((hmem γ).1 hγ).1
    refine prodInjective_of m F (fun a => (a : ℤ)) L hL hroots
      (fun γ hγ => lev_pos m (hroots γ hγ) ((hmem γ).1 hγ).2.1) ?_
    refine hsort.imp_of_mem fun {γ δ} hγ hδ h => ?_
    have h' : ht (ι := Fin m) γ ≤ ht δ := h
    have h1 := ht_eq_idx m (hroots γ hγ)
    have h2 := ht_eq_idx m (hroots δ hδ)
    omega
  prodInjective_neg L hL hmem hsort := by
    have hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅ := fun γ hγ => ((hmem γ).1 hγ).1
    refine prodInjective_of m F (fun a => -(a : ℤ)) L hL hroots
      (fun γ hγ => lev_neg m (hroots γ hγ) ((hmem γ).1 hγ).2.1) ?_
    refine hsort.imp_of_mem fun {γ δ} hγ hδ h => ?_
    have h' : ht (ι := Fin m) δ ≤ ht γ := h
    have h1 := ht_eq_idx m (hroots γ hγ)
    have h2 := ht_eq_idx m (hroots δ hδ)
    omega
  posPart_inf_negPart := posPart_inf_negPart m F
  rankOne_bruhat := rankOne_bruhat m F
  eq_one_of_mem_normalizer := eq_one_of_mem_normalizer m F
  torus_commute _ _ _ hh _ hh' := commute_of_isDiag m F (isDiag_of_mem_torus m F hh)
    (isDiag_of_mem_torus m F hh')
  torus_iSupIndep := torus_iSupIndep m F
  torus_inf_posPart := torus_inf_posPart m F

end CFSG.LieType.Universal.SpecialLinear
