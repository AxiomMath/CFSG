module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LieType.Steinberg.Extras

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

section Level

variable (s : Fin n ⊕ Fin n → ℤ)

@[expose] def IdBelow (h : ℤ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  ∀ a b, s b - s a < h → M a b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b

theorem idBelow_one (h : ℤ) : IdBelow s h (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  fun _ _ _ => rfl

theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h)
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hM : IdBelow s h M) (hN : IdBelow s h N) {a b : Fin n ⊕ Fin n} (hab : a ≠ b)
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

theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
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

theorem idBelow_list_prod {ι : Type*} {h : ℤ} (hh : 0 < h) (L : List ι)
    (f : ι → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hf : ∀ x ∈ L, IdBelow s h (f x)) :
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

end Level

theorem idBelow_mat_elt (σ : ℤ) {h : ℤ} {r : RootSubgroupIndex n}
    (hr : h ≤ σ * (lvl (pos1 r).2 - lvl (pos1 r).1)) (c : F) :
    IdBelow (fun a => σ * lvl a) h (mat n F (elt r c)) := by
  intro a b hab
  have hE : E F r a b = 0 := by
    by_contra hE
    have h1 := lvl_of_E_ne_zero hE
    have h2 : σ * lvl b - σ * lvl a = σ * (lvl (pos1 r).2 - lvl (pos1 r).1) := by
      rw [← h1]
      ring
    simp only at hab
    linarith
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, hE, smul_zero, add_zero]

theorem eq_of_list_prod_eq (σ : ℤ) {κ : Type*} (L : List κ) (hL : L.Nodup)
    (r : κ → RootSubgroupIndex n)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, stdVec (r x) = stdVec (r y) → x = y)
    (hlev : ∀ x ∈ L, 1 ≤ σ * (lvl (pos1 (r x)).2 - lvl (pos1 (r x)).1))
    (hsort : L.Pairwise fun x y => σ * (lvl (pos1 (r x)).2 - lvl (pos1 (r x)).1) ≤
      σ * (lvl (pos1 (r y)).2 - lvl (pos1 (r y)).1))
    (c d : κ → F)
    (h : (L.map fun x => elt (r x) (c x)).prod = (L.map fun x => elt (r x) (d x)).prod) :
    ∀ x ∈ L, c x = d x := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.pairwise_cons] at hsort
    have hx1 := hlev x List.mem_cons_self
    have hpq := pos1_ne (r x)
    have hlevpq : σ * lvl (pos1 (r x)).2 - σ * lvl (pos1 (r x)).1 =
        σ * (lvl (pos1 (r x)).2 - lvl (pos1 (r x)).1) := by ring
    have htail : ∀ e : κ → F,
        IdBelow (fun a => σ * lvl a) (σ * (lvl (pos1 (r x)).2 - lvl (pos1 (r x)).1))
          (mat n F (L.map fun y => elt (r y) (e y)).prod) ∧
        mat n F (L.map fun y => elt (r y) (e y)).prod (pos1 (r x)).1 (pos1 (r x)).2 = 0 := by
      intro e
      rw [map_list_prod, List.map_map]
      obtain ⟨h1, h2⟩ := idBelow_list_prod (fun a => σ * lvl a) (by omega) L
        (fun y => mat n F (elt (r y) (e y)))
        (fun y hy => idBelow_mat_elt σ (hsort.1 y hy) (e y))
      refine ⟨h1, ?_⟩
      rw [Function.comp_def, h2 _ _ hpq hlevpq.le]
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hE : E F (r y) (pos1 (r x)).1 (pos1 (r x)).2 = 0 := by
        by_contra hE
        have hw := hasDeg_E (r y) _ _ hE
        rw [wt_pos1] at hw
        have hyx := hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hw.symm
        exact hL.1 (hyx ▸ hy)
      rw [mat_elt, Matrix.add_apply, Matrix.one_apply_ne hpq, Matrix.smul_apply, hE, smul_zero,
        zero_add]
    have hentry : ∀ e : κ → F, mat n F (elt (r x) (e x) * (L.map fun y => elt (r y) (e y)).prod)
        (pos1 (r x)).1 (pos1 (r x)).2 = e x := by
      intro e
      obtain ⟨h1, h2⟩ := htail e
      rw [map_mul, mul_apply_of_idBelow (fun a => σ * lvl a) (by omega)
        (idBelow_mat_elt σ le_rfl (e x)) h1 hpq hlevpq.le, h2, add_zero, mat_elt_apply_pos1]
    simp only [List.map_cons, List.prod_cons] at h
    have hcx : c x = d x := by rw [← hentry c, ← hentry d, h]
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hcx
    · refine ih hL.2 (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b
        (List.mem_cons_of_mem x hb)) (fun a ha => hlev a (List.mem_cons_of_mem x ha)) hsort.2 ?_
        y hy
      rw [hcx] at h
      exact mul_left_cancel h

theorem prodInjective_of (σ : ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanC n) ∅)
    (hlev : ∀ γ ∈ L, 1 ≤ σ * ht γ)
    (hsort : L.Pairwise fun γ δ => σ * ht γ ≤ σ * ht δ) :
    ProdInjectiveFor (rootGroup n F) L := by
  intro f g hf hg hfg
  have hr : ∀ γ : {γ // γ ∈ L}, ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ.1 :=
    fun γ => exists_stdVec_of_mem_roots (hroots γ.1 γ.2)
  choose r hr using hr
  have hcoef : ∀ e : (Fin n → ℤ) → StatedSp n F, (∀ γ ∈ L, e γ ∈ rootGroup n F γ) →
      ∃ c : {γ // γ ∈ L} → F, ∀ γ, e γ.1 = elt (r γ) (c γ) := by
    intro e he
    have : ∀ γ : {γ // γ ∈ L}, ∃ c : F, e γ.1 = elt (r γ) c :=
      fun γ => (mem_rootGroup_iff (hr γ)).1 (he γ.1 γ.2)
    choose c hc using this
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcoef f hf
  obtain ⟨d, hd⟩ := hcoef g hg
  have hprod : ∀ (e : (Fin n → ℤ) → StatedSp n F) (c' : {γ // γ ∈ L} → F),
      (∀ γ, e γ.1 = elt (r γ) (c' γ)) →
      (L.map e).prod = (L.attach.map fun γ => elt (r γ) (c' γ)).prod := by
    intro e c' he
    calc (L.map e).prod = ((L.attach.map Subtype.val).map e).prod := by
          rw [List.attach_map_subtype_val]
      _ = (L.attach.map fun γ => elt (r γ) (c' γ)).prod := by
          rw [List.map_map]
          exact congrArg List.prod (List.map_congr_left fun γ _ => he γ)
  have hlvl : ∀ γ : {γ // γ ∈ L}, lvl (pos1 (r γ)).2 - lvl (pos1 (r γ)).1 = ht γ.1 :=
    fun γ => (ht_eq_lvl (hr γ)).symm
  have hsort' : L.attach.Pairwise fun γ δ => σ * ht γ.1 ≤ σ * ht δ.1 := by
    have := hsort
    rw [← List.attach_map_subtype_val L, List.pairwise_map] at this
    exact this
  have hcd := eq_of_list_prod_eq σ L.attach (List.nodup_attach.mpr hL) r
    (fun γ _ δ _ h => Subtype.ext (toStd_inj ((hr γ).symm.trans (h.trans (hr δ)))))
    (fun γ _ => by rw [hlvl]; exact hlev γ.1 γ.2)
    (hsort'.imp fun {γ δ} h => by rw [hlvl, hlvl]; exact h)
    c d ((hprod f c hc).symm.trans (hfg.trans (hprod g d hd)))
  intro γ hγ
  rw [hc ⟨γ, hγ⟩, hd ⟨γ, hγ⟩, hcd ⟨γ, hγ⟩ (List.mem_attach _ _)]

theorem idBelow_of_mem_iSup (σ : ℤ) (P : Set (Fin n → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ roots (isFiniteType_cartanC n) ∅ ∧ 1 ≤ σ * ht γ)
    {x : StatedSp n F} (hx : x ∈ ⨆ γ ∈ P, rootGroup n F γ) :
    IdBelow (fun a => σ * lvl a) 1 (mat n F x) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : StatedSp n F =>
    IdBelow (fun a => σ * lvl a) 1 (mat n F x)) (fun γ y hy => ?_) ?_ fun y z hy hz => ?_
  · obtain ⟨hroot, hl⟩ := hP γ.1 γ.2
    obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hroot
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hy
    exact idBelow_mat_elt σ (by rw [← ht_eq_lvl hr]; exact hl) c
  · simpa using idBelow_one (F := F) (fun a => σ * lvl a) 1
  · rw [map_mul]
    exact idBelow_mul _ one_pos hy hz

theorem eq_one_of_idBelow {x : StatedSp n F}
    (hpos : IdBelow (fun a => (1 : ℤ) * lvl a) 1 (mat n F x))
    (hneg : IdBelow (fun a => (-1 : ℤ) * lvl a) 1 (mat n F x)) : x = 1 := by
  apply mat_injective
  rw [map_one]
  ext a b
  rcases le_or_gt (lvl b) (lvl a) with h | h
  · exact hpos a b (by linarith)
  · exact hneg a b (by linarith)

theorem posPart_inf_negPart :
    (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanC n) ∅ ∧ 0 < ht γ}, rootGroup n F γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanC n) ∅ ∧ ht γ < 0}, rootGroup n F γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_idBelow
    (idBelow_of_mem_iSup 1 _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxp)
    (idBelow_of_mem_iSup (-1) _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxn)

end CFSG.LieType.Universal.Symplectic.SpExtras
