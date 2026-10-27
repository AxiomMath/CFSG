module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpInvolution
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpSplit
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpTwoRankGrp

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank Module
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {K : Type} [Field K] {r : ℕ}

section Pm

theorem pm_of_mk_eq_one [NeZero r] {x : StatedSp r K}
    (h : (QuotientGroup.mk x : StatedProj (StatedSp r K)) = 1) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ mat r K x = ε • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have h' := h
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h'
  obtain ⟨c, hc⟩ := h'
  have hm : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K := by
    rw [hc]; exact x.2
  have hcc := scalar_sq_eq_one_of_mem_statedSp c hm
  have hcc' : (c : K) * c = 1 := by simpa using congrArg Units.val hcc
  refine ⟨c, ?_, ?_⟩
  · have : ((c : K) - 1) * ((c : K) + 1) = 0 := by linear_combination hcc'
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rw [mat_apply, ← hc, scalar_matrix_eq]

@[expose] noncomputable def zNeg (r : ℕ) (K : Type) [Field K] : StatedSp r K :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1 : Kˣ), neg_scalar_mem_statedSp⟩

theorem mat_zNeg : mat r K (zNeg r K) = -(1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [mat_apply]
  show (((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1 : Kˣ) : GL (Fin r ⊕ Fin r) K)) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
  rw [scalar_matrix_eq]
  simp

theorem mk_zNeg [NeZero r] : (QuotientGroup.mk (zNeg r K) : StatedProj (StatedSp r K)) = 1 :=
  mk_eq_one_of_mulVec _ (-1) (fun w => by
    rw [mat_zNeg]; simp [Matrix.neg_mulVec])

end Pm

section Core

@[expose] noncomputable def Gl (g : StatedSp r K) :
    (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) :=
  Matrix.mulVecLin (mat r K g)

theorem Gl_apply (g : StatedSp r K) (w : Fin r ⊕ Fin r → K) : Gl g w = mat r K g *ᵥ w := rfl

theorem sympNondeg_top : SympNondeg (⊤ : Submodule K (Fin r ⊕ Fin r → K)) := fun _ _ h =>
  eq_zero_of_forall_form_eq_zero fun w => h w Submodule.mem_top

theorem finrank_top_three : finrank K (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)) = 6 := by
  rw [finrank_top, Module.finrank_pi]
  simp

variable (h2 : (2 : K) ≠ 0)

include h2 in
theorem exists_planes (g : StatedSp 3 K) (hg2 : ∀ w, mat 3 K g *ᵥ (mat 3 K g *ᵥ w) = w)
    (hg1 : ∃ w, mat 3 K g *ᵥ w ≠ w) (hg1' : ∃ w, mat 3 K g *ᵥ w ≠ -w) :
    ∃ (P P' : Submodule K (Fin 3 ⊕ Fin 3 → K)) (ε₀ : K), (ε₀ = 1 ∨ ε₀ = -1) ∧
      SympNondeg P ∧ SympNondeg P' ∧ finrank K P = 2 ∧ finrank K P' = 4 ∧
      (∀ x ∈ P, ∀ y ∈ P', form x y = 0) ∧
      (∀ w, ∃ x ∈ P, ∃ y ∈ P', w = x + y) ∧
      (∀ x, x ∈ P ↔ mat 3 K g *ᵥ x = ε₀ • x) ∧
      (∀ y, y ∈ P' ↔ mat 3 K g *ᵥ y = (-ε₀) • y) := by
  set s : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) := Gl g with hs
  have hsU : ∀ u ∈ (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)), s u ∈ (⊤ : Submodule K _) :=
    fun _ _ => Submodule.mem_top
  have hs2 : ∀ u ∈ (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)), s (s u) = u := fun u _ => hg2 u
  have hiso : ∀ u ∈ (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)), ∀ v ∈ (⊤ : Submodule K _),
      form (s u) (s v) = form u v := fun u _ v _ => form_mulVec g u v
  obtain ⟨hp, hm, hsum⟩ := involution_split h2 sympNondeg_top hsU hs2 hiso
  rw [finrank_top_three] at hsum
  have hevp := even_finrank_of_nondeg _ hp
  have hevm := even_finrank_of_nondeg _ hm
  have hP1 : eigSub ⊤ s 1 ≠ ⊥ := by
    intro h
    obtain ⟨w, hw⟩ := hg1'
    apply hw
    have h0 := plus_part hsU hs2 (Submodule.mem_top (x := w))
    rw [h] at h0
    have h00 : (2⁻¹ : K) • (w + s w) = 0 := (Submodule.mem_bot K).1 h0
    have := (smul_eq_zero.1 h00).resolve_left (inv_ne_zero h2)
    exact eq_neg_of_add_eq_zero_right this
  have hP2 : eigSub ⊤ s (-1) ≠ ⊥ := by
    intro h
    obtain ⟨w, hw⟩ := hg1
    apply hw
    have h0 := minus_part hsU hs2 (Submodule.mem_top (x := w))
    rw [h] at h0
    have h00 : (2⁻¹ : K) • (w - s w) = 0 := (Submodule.mem_bot K).1 h0
    have := (smul_eq_zero.1 h00).resolve_left (inv_ne_zero h2)
    exact (sub_eq_zero.1 this).symm
  have hge1 := two_le_finrank_of_nondeg _ hp hP1
  have hge2 := two_le_finrank_of_nondeg _ hm hP2
  have horth : ∀ x ∈ eigSub ⊤ s 1, ∀ y ∈ eigSub ⊤ s (-1), form x y = 0 := fun x hx y hy =>
    eigSub_orth h2 hiso hx hy
  have hdec : ∀ w, ∃ x ∈ eigSub ⊤ s 1, ∃ y ∈ eigSub ⊤ s (-1), w = x + y := fun w =>
    ⟨_, plus_part hsU hs2 (Submodule.mem_top (x := w)), _,
      minus_part hsU hs2 (Submodule.mem_top (x := w)), (plus_add_minus h2).symm⟩
  have hmem1 : ∀ x, x ∈ eigSub ⊤ s 1 ↔ mat 3 K g *ᵥ x = (1 : K) • x := fun x => by
    rw [mem_eigSub]; simp [hs, Gl_apply]
  have hmem2 : ∀ x, x ∈ eigSub ⊤ s (-1) ↔ mat 3 K g *ᵥ x = (-1 : K) • x := fun x => by
    rw [mem_eigSub]; simp [hs, Gl_apply]
  obtain ⟨a, ha⟩ := hevp
  obtain ⟨b, hb⟩ := hevm
  have hd : finrank K (eigSub ⊤ s 1) = 2 ∨ finrank K (eigSub ⊤ s 1) = 4 := by omega
  rcases hd with hd | hd
  · refine ⟨eigSub ⊤ s 1, eigSub ⊤ s (-1), 1, Or.inl rfl, hp, hm, hd, by omega, horth, hdec,
      hmem1, fun y => by rw [hmem2]⟩
  · refine ⟨eigSub ⊤ s (-1), eigSub ⊤ s 1, -1, Or.inr rfl, hm, hp, by omega, hd, ?_, ?_,
      hmem2, fun y => by rw [hmem1]; simp⟩
    · intro x hx y hy
      rw [form_antisymm, horth y hy x hx, neg_zero]
    · intro w
      obtain ⟨x, hx, y, hy, e⟩ := hdec w
      exact ⟨y, hy, x, hx, by rw [e, add_comm]⟩

include h2 in
theorem fixes_plane (P : Submodule K (Fin r ⊕ Fin r → K)) (hPn : SympNondeg P)
    (hPd : finrank K P = 2) (g : StatedSp r K) (hgP : ∀ x ∈ P, mat r K g *ᵥ x ∈ P)
    (hg2 : ∀ x ∈ P, mat r K g *ᵥ (mat r K g *ᵥ x) = x) {p : Fin r ⊕ Fin r → K} (hp : p ∈ P)
    (hp0 : p ≠ 0) (hgp : mat r K g *ᵥ p = p) : ∀ x ∈ P, mat r K g *ᵥ x = x := by
  obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P, form p y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hp0 (hPn p hp hcon)
  set q : Fin r ⊕ Fin r → K := (form p y)⁻¹ • y with hq
  have hqP : q ∈ P := P.smul_mem _ hyP
  have hpq : form p q = 1 := by rw [hq, form_smul_right, inv_mul_cancel₀ hy]
  have hqp : form q p = -1 := by rw [form_antisymm, hpq]
  have hpp := form_self p
  have hqq := form_self q
  have hli : LinearIndependent K ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have e1 := congrArg (form p) hab
    have e2 := congrArg (fun x => form x q) hab
    simp only [form_add_right, form_smul_right, form_add_left, form_smul_left, form_zero_right,
      form_zero_left, hpq, hpp, hqq] at e1 e2
    constructor
    · simpa using e2
    · simpa using e1
  have hrange : Set.range ![p, q] = {p, q} := by
    ext x; simp; tauto
  have hspan : Submodule.span K {p, q} = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hp
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hqP
    · rw [hPd, ← hrange]
      have := finrank_span_eq_card hli
      simpa using this
  have hGq : mat r K g *ᵥ q = q := by
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 (hspan ▸ hgP q hqP)
    have e1 : form p (mat r K g *ᵥ q) = 1 := by
      have := form_mulVec g p q
      rw [hgp] at this
      rw [this, hpq]
    rw [← hcd] at e1
    simp only [form_add_right, form_smul_right, hpq, hpp] at e1
    have hd : d = 1 := by linear_combination e1
    subst hd
    have e2 := hg2 q hqP
    rw [← hcd, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgp] at e2
    have e3 : (2 * c) • p = 0 := by
      have e4 : c • p + (1 : K) • (mat r K g *ᵥ q) = q := e2
      rw [← hcd] at e4
      calc (2 * c) • p = (c • p + (1 : K) • (c • p + (1 : K) • q)) - q := by module
        _ = 0 := by rw [e4, sub_self]
    have hc : c = 0 := by
      have := (smul_eq_zero.1 e3).resolve_right hp0
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [← hcd, hc]; simp
  intro x hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hspan ▸ hx)
  rw [← hab, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgp, hGq]

structure PmGroup (Bt : Subgroup (StatedSp r K)) : Prop where
  neg : zNeg r K ∈ Bt
  sq : ∀ g ∈ Bt, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
    ∀ w, mat r K g *ᵥ (mat r K g *ᵥ w) = ε • w
  comm : ∀ g ∈ Bt, ∀ h ∈ Bt, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
    ∀ w, mat r K g *ᵥ (mat r K h *ᵥ w) = ε • (mat r K h *ᵥ (mat r K g *ᵥ w))

theorem mulVec_injective_of_sp (g : StatedSp r K) {x y : Fin r ⊕ Fin r → K}
    (h : mat r K g *ᵥ x = mat r K g *ᵥ y) : x = y := by
  have := congrArg (fun z => mat r K g⁻¹ *ᵥ z) h
  simpa only [mulVec_inv_mulVec] using this

omit h2 in
theorem planes_preserved {Bt : Subgroup (StatedSp 3 K)} (hB : PmGroup Bt) {g₀ : StatedSp 3 K}
    (hg₀ : g₀ ∈ Bt) {P P' : Submodule K (Fin 3 ⊕ Fin 3 → K)} {ε₀ : K}
    (hP : ∀ x, x ∈ P ↔ mat 3 K g₀ *ᵥ x = ε₀ • x)
    (hP' : ∀ y, y ∈ P' ↔ mat 3 K g₀ *ᵥ y = (-ε₀) • y) (hd : finrank K P = 2)
    (hd' : finrank K P' = 4) {h : StatedSp 3 K} (hh : h ∈ Bt) :
    (∀ x ∈ P, mat 3 K h *ᵥ x ∈ P) ∧ (∀ y ∈ P', mat 3 K h *ᵥ y ∈ P') := by
  obtain ⟨ε, hε, hc⟩ := hB.comm g₀ hg₀ h hh
  have hxP : ∀ x ∈ P, mat 3 K g₀ *ᵥ (mat 3 K h *ᵥ x) = (ε * ε₀) • (mat 3 K h *ᵥ x) := by
    intro x hx
    rw [hc, (hP x).1 hx, Matrix.mulVec_smul, smul_smul]
  have hyP : ∀ y ∈ P', mat 3 K g₀ *ᵥ (mat 3 K h *ᵥ y) = (ε * -ε₀) • (mat 3 K h *ᵥ y) := by
    intro y hy
    rw [hc, (hP' y).1 hy, Matrix.mulVec_smul, smul_smul]
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      have hmap : ∀ y ∈ P', mat 3 K h *ᵥ y ∈ P := by
        intro y hy
        rw [hP]
        rw [hyP y hy, hε]
        simp
      let f : P' →ₗ[K] P := (Gl h).restrict (fun y hy => hmap y hy)
      have hf : Function.Injective f := by
        intro y₁ y₂ e
        refine Subtype.ext (mulVec_injective_of_sp h ?_)
        have := congrArg Subtype.val e
        exact this
      have := LinearMap.finrank_le_finrank_of_injective hf
      omega
  subst hε1
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [hP, hxP x hx, one_mul]
  · rw [hP', hyP y hy, one_mul]


theorem eq_of_agree {P P' : Submodule K (Fin r ⊕ Fin r → K)}
    (hdec : ∀ w, ∃ x ∈ P, ∃ y ∈ P', w = x + y) {g g' : StatedSp r K}
    (hP : ∀ x ∈ P, mat r K g *ᵥ x = mat r K g' *ᵥ x)
    (hP' : ∀ y ∈ P', mat r K g *ᵥ y = mat r K g' *ᵥ y) : g = g' := by
  refine Sp_ext_mulVec fun w => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec w
  rw [Matrix.mulVec_add, Matrix.mulVec_add, hP x hx, hP' y hy]

include h2 in
theorem stab_bound {Bt : Subgroup (StatedSp 3 K)} (hB : PmGroup Bt)
    {P P' : Submodule K (Fin 3 ⊕ Fin 3 → K)} (hPn : SympNondeg P) (hPn' : SympNondeg P')
    (hd : finrank K P = 2) (hd' : finrank K P' = 4)
    (hdec : ∀ w, ∃ x ∈ P, ∃ y ∈ P', w = x + y)
    (hpres : ∀ g ∈ Bt, (∀ x ∈ P, mat 3 K g *ᵥ x ∈ P) ∧ (∀ y ∈ P', mat 3 K g *ᵥ y ∈ P'))
    {p : Fin 3 ⊕ Fin 3 → K} (hp : p ∈ P) (hp0 : p ≠ 0) :
    Nat.card {g : Bt // mat 3 K g.1 *ᵥ p = p} ≤ 4 := by
  classical
  have hS2 : ∀ g : Bt, mat 3 K g.1 *ᵥ p = p → ∀ w, mat 3 K g.1 *ᵥ (mat 3 K g.1 *ᵥ w) = w := by
    intro g hg w
    obtain ⟨ε, hε, hsq⟩ := hB.sq g.1 g.2
    have e := hsq p
    rw [hg, hg] at e
    have : (ε - 1) • p = 0 := by rw [sub_smul, ← e, one_smul, sub_self]
    have hε1 : ε = 1 := by
      have := (smul_eq_zero.1 this).resolve_right hp0
      linear_combination this
    rw [hsq w, hε1, one_smul]
  have hSP : ∀ g : Bt, mat 3 K g.1 *ᵥ p = p → ∀ x ∈ P, mat 3 K g.1 *ᵥ x = x := fun g hg =>
    fixes_plane h2 P hPn hd g.1 (hpres g.1 g.2).1 (fun x _ => hS2 g hg x) hp hp0 hg
  have hScomm : ∀ g g' : Bt, mat 3 K g.1 *ᵥ p = p → mat 3 K g'.1 *ᵥ p = p →
      ∀ w, mat 3 K g.1 *ᵥ (mat 3 K g'.1 *ᵥ w) = mat 3 K g'.1 *ᵥ (mat 3 K g.1 *ᵥ w) := by
    intro g g' hg hg' w
    obtain ⟨ε, hε, hc⟩ := hB.comm g.1 g.2 g'.1 g'.2
    have e := hc p
    rw [hg', hg, hg'] at e
    have : (ε - 1) • p = 0 := by rw [sub_smul, ← e, one_smul, sub_self]
    have hε1 : ε = 1 := by
      have := (smul_eq_zero.1 this).resolve_right hp0
      linear_combination this
    rw [hc w, hε1, one_smul]
  by_cases ha : ∀ g : Bt, mat 3 K g.1 *ᵥ p = p →
      ((∀ y ∈ P', mat 3 K g.1 *ᵥ y = y) ∨ (∀ y ∈ P', mat 3 K g.1 *ᵥ y = -y))
  ·
    let φ : {g : Bt // mat 3 K g.1 *ᵥ p = p} → Bool := fun g =>
      decide (∀ y ∈ P', mat 3 K g.1.1 *ᵥ y = y)
    have hinj : Function.Injective φ := by
      intro g g' e
      refine Subtype.ext (Subtype.ext (eq_of_agree hdec (g := g.1.1) (g' := g'.1.1)
        (fun x hx => ?_) (fun y hy => ?_)))
      · rw [hSP g.1 g.2 x hx, hSP g'.1 g'.2 x hx]
      · by_cases hy1 : ∀ y ∈ P', mat 3 K g.1.1 *ᵥ y = y
        · have : φ g = true := decide_eq_true hy1
          have hg' : ∀ y ∈ P', mat 3 K g'.1.1 *ᵥ y = y := by
            have h' : φ g' = true := by rw [← e, this]
            exact of_decide_eq_true h'
          rw [hy1 y hy, hg' y hy]
        · have hneg := (ha g.1 g.2).resolve_left hy1
          have : φ g = false := decide_eq_false hy1
          have hg'1 : ¬ ∀ y ∈ P', mat 3 K g'.1.1 *ᵥ y = y := by
            have h' : φ g' = false := by rw [← e, this]
            exact of_decide_eq_false h'
          have hneg' := (ha g'.1 g'.2).resolve_left hg'1
          rw [hneg y hy, hneg' y hy]
    have := Nat.card_le_card_of_injective φ hinj
    simp at this
    omega
  · push Not at ha
    obtain ⟨g₁, hg₁p, ⟨y₁, hy₁P, hy₁⟩, ⟨y₂, hy₂P, hy₂⟩⟩ := ha
    set s : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) := Gl g₁.1 with hs
    have hsU : ∀ u ∈ P', s u ∈ P' := fun u hu => (hpres g₁.1 g₁.2).2 u hu
    have hs2 : ∀ u ∈ P', s (s u) = u := fun u _ => hS2 g₁ hg₁p u
    have hiso : ∀ u ∈ P', ∀ v ∈ P', form (s u) (s v) = form u v := fun u _ v _ =>
      form_mulVec g₁.1 u v
    obtain ⟨hWp, hWm, hsum⟩ := involution_split h2 hPn' hsU hs2 hiso
    rw [hd'] at hsum
    have hW1 : eigSub P' s 1 ≠ ⊥ := by
      intro h
      apply hy₂
      have h0 := plus_part hsU hs2 hy₂P
      rw [h] at h0
      have := (smul_eq_zero.1 ((Submodule.mem_bot K).1 h0)).resolve_left (inv_ne_zero h2)
      exact eq_neg_of_add_eq_zero_right this
    have hW2 : eigSub P' s (-1) ≠ ⊥ := by
      intro h
      apply hy₁
      have h0 := minus_part hsU hs2 hy₁P
      rw [h] at h0
      have := (smul_eq_zero.1 ((Submodule.mem_bot K).1 h0)).resolve_left (inv_ne_zero h2)
      exact (sub_eq_zero.1 this).symm
    have hge1 := two_le_finrank_of_nondeg _ hWp hW1
    have hge2 := two_le_finrank_of_nondeg _ hWm hW2
    have hd1 : finrank K (eigSub P' s 1) = 2 := by omega
    have hd2 : finrank K (eigSub P' s (-1)) = 2 := by omega
    have hplane : ∀ ε : K, SympNondeg (eigSub P' s ε) → finrank K (eigSub P' s ε) = 2 →
        ∀ g : {g : Bt // mat 3 K g.1 *ᵥ p = p},
          (∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = u) ∨
            (∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = -u) := by
      intro ε hnd hdim g
      have hcomm := hScomm g.1 g₁ g.2 hg₁p
      refine involution_plane (s := Gl g.1.1) h2 hnd hdim ?_ ?_ ?_
      · intro u hu
        rw [mem_eigSub] at hu ⊢
        refine ⟨(hpres g.1.1 g.1.2).2 u hu.1, ?_⟩
        show mat 3 K g₁.1 *ᵥ (mat 3 K g.1.1 *ᵥ u) = ε • (mat 3 K g.1.1 *ᵥ u)
        have h1 : mat 3 K g₁.1 *ᵥ u = ε • u := hu.2
        rw [← hcomm u, h1, Matrix.mulVec_smul]
      · intro u _
        exact hS2 g.1 g.2 u
      · intro u _ v _
        exact form_mulVec g.1.1 u v
    have hagree : ∀ ε : K, (ε = 1 ∨ ε = -1) → ∀ g g' : {g : Bt // mat 3 K g.1 *ᵥ p = p},
        decide (∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = u) =
          decide (∀ u ∈ eigSub P' s ε, mat 3 K g'.1.1 *ᵥ u = u) →
        ∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = mat 3 K g'.1.1 *ᵥ u := by
      intro ε hε g g' e u hu
      have hnd : SympNondeg (eigSub P' s ε) ∧ finrank K (eigSub P' s ε) = 2 := by
        rcases hε with rfl | rfl
        · exact ⟨hWp, hd1⟩
        · exact ⟨hWm, hd2⟩
      by_cases hy : ∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = u
      · have e1 : decide (∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = u) = true := decide_eq_true hy
        rw [e1] at e
        have hy' := of_decide_eq_true e.symm
        rw [hy u hu, hy' u hu]
      · have hneg := (hplane ε hnd.1 hnd.2 g).resolve_left hy
        have e1 : decide (∀ u ∈ eigSub P' s ε, mat 3 K g.1.1 *ᵥ u = u) = false :=
          decide_eq_false hy
        rw [e1] at e
        have hy' := of_decide_eq_false e.symm
        have hneg' := (hplane ε hnd.1 hnd.2 g').resolve_left hy'
        rw [hneg u hu, hneg' u hu]
    let φ : {g : Bt // mat 3 K g.1 *ᵥ p = p} → Bool × Bool := fun g =>
      (decide (∀ u ∈ eigSub P' s 1, mat 3 K g.1.1 *ᵥ u = u),
        decide (∀ u ∈ eigSub P' s (-1), mat 3 K g.1.1 *ᵥ u = u))
    have hinj : Function.Injective φ := by
      intro g g' e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      refine Subtype.ext (Subtype.ext (eq_of_agree hdec (g := g.1.1) (g' := g'.1.1)
        (fun x hx => ?_) (fun y hy => ?_)))
      · rw [hSP g.1 g.2 x hx, hSP g'.1 g'.2 x hx]
      · have hy1 := plus_part hsU hs2 hy
        have hy2 := minus_part hsU hs2 hy
        have hsplit := plus_add_minus h2 (s := s) (u := y)
        rw [← hsplit, Matrix.mulVec_add, Matrix.mulVec_add,
          hagree 1 (Or.inl rfl) g g' e1 _ hy1, hagree (-1) (Or.inr rfl) g g' e2 _ hy2]
    have := Nat.card_le_card_of_injective φ hinj
    simp at this
    omega

noncomputable abbrev actBt (Bt : Subgroup (StatedSp r K)) :
    MulAction Bt (Fin r ⊕ Fin r → K) :=
  MulAction.compHom _ ((mat r K).comp Bt.subtype)

theorem card_submodule_three [Finite K] (hK : Nat.card K = 3)
    (P : Submodule K (Fin 3 ⊕ Fin 3 → K)) : Nat.card P = 3 ^ finrank K P := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ← Nat.card_eq_fintype_card,
    hK]

include h2 in
theorem card_le_of_involution [Finite K] (hK : Nat.card K = 3) {Bt : Subgroup (StatedSp 3 K)}
    (hB : PmGroup Bt) {g₀ : StatedSp 3 K} (hg₀ : g₀ ∈ Bt)
    (hg2 : ∀ w, mat 3 K g₀ *ᵥ (mat 3 K g₀ *ᵥ w) = w) (hg1 : ∃ w, mat 3 K g₀ *ᵥ w ≠ w)
    (hg1' : ∃ w, mat 3 K g₀ *ᵥ w ≠ -w) : Nat.card Bt ≤ 32 := by
  classical
  obtain ⟨P, P', ε₀, hε₀, hPn, hPn', hd, hd', horth, hdec, hP, hP'⟩ := exists_planes h2 g₀ hg2 hg1 hg1'
  have hpres : ∀ g ∈ Bt, (∀ x ∈ P, mat 3 K g *ᵥ x ∈ P) ∧ (∀ y ∈ P', mat 3 K g *ᵥ y ∈ P') :=
    fun g hg => planes_preserved hB hg₀ hP hP' hd hd' hg
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h] at hd
    simp at hd
  obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
  let _ := actBt Bt
  have hT : ∀ g : Bt, g • p ∈ ((P : Set (Fin 3 ⊕ Fin 3 → K)) \ {0}) := by
    intro g
    refine ⟨(hpres g.1 g.2).1 p hpP, ?_⟩
    intro h0
    apply hp0
    exact mulVec_injective_of_sp g.1 (by
      have : mat 3 K g.1 *ᵥ p = 0 := h0
      rw [this, Matrix.mulVec_zero])
  have hTfin : ((P : Set (Fin 3 ⊕ Fin 3 → K)) \ {0}).Finite := Set.toFinite _
  have hTcard : ((P : Set (Fin 3 ⊕ Fin 3 → K)) \ {0}).ncard ≤ 8 := by
    have h9 : (P : Set (Fin 3 ⊕ Fin 3 → K)).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]
      have := card_submodule_three hK P
      rw [hd] at this
      simpa using this
    have h0 : (0 : Fin 3 ⊕ Fin 3 → K) ∈ (P : Set (Fin 3 ⊕ Fin 3 → K)) := P.zero_mem
    rw [Set.ncard_sdiff_singleton_of_mem h0, h9]
  have hstab : Nat.card (MulAction.stabilizer Bt p) ≤ 4 := by
    have := stab_bound h2 hB hPn hPn' hd hd' hdec hpres hpP hp0
    refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_))) this
    rw [MulAction.mem_stabilizer_iff]
    rfl
  exact card_le_of_stabilizer p hT hTfin hTcard hstab


theorem mulVec_zNeg (w : Fin r ⊕ Fin r → K) : mat r K (zNeg r K) *ᵥ w = -w := by
  rw [mat_zNeg]; simp [Matrix.neg_mulVec]

include h2 in
theorem zNeg_ne_one [NeZero r] : zNeg r K ≠ 1 := by
  intro h
  have e := mulVec_zNeg (K := K) (r := r) (Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩) 1)
  rw [h, map_one, Matrix.one_mulVec] at e
  have e2 := congrFun e (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)
  simp at e2
  apply h2
  linear_combination e2

include h2 in
theorem card_le_of_no_involution [Finite K] {Bt : Subgroup (StatedSp 3 K)} (hB : PmGroup Bt)
    (hnc : ∀ g ∈ Bt, (∀ w, mat 3 K g *ᵥ (mat 3 K g *ᵥ w) = w) →
      (∀ w, mat 3 K g *ᵥ w = w) ∨ (∀ w, mat 3 K g *ᵥ w = -w)) : Nat.card Bt ≤ 8 := by
  classical
  let z : Bt := ⟨zNeg 3 K, hB.neg⟩
  have hz1 : z ≠ 1 := fun h => zNeg_ne_one h2 (congrArg Subtype.val h)
  have hzz : z * z = 1 := by
    refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
    show mat 3 K (zNeg 3 K * zNeg 3 K) *ᵥ w = mat 3 K 1 *ᵥ w
    rw [map_mul, ← Matrix.mulVec_mulVec, mulVec_zNeg, mulVec_zNeg, neg_neg, map_one,
      Matrix.one_mulVec]
  have hcomm : ∀ g h : Bt, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = z := by
    intro g h
    obtain ⟨ε, hε, hc⟩ := hB.comm g.1 g.2 h.1 h.2
    have hx : ∀ w, mat 3 K (g * h * g⁻¹ * h⁻¹ : Bt).1 *ᵥ w = ε • w := by
      intro w
      have e := hc (mat 3 K g.1⁻¹ *ᵥ (mat 3 K h.1⁻¹ *ᵥ w))
      rw [mulVec_mulVec_inv, mulVec_mulVec_inv] at e
      show mat 3 K (g.1 * h.1 * g.1⁻¹ * h.1⁻¹) *ᵥ w = _
      rw [map_mul, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      exact e
    rcases hε with rfl | rfl
    · left
      refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
      rw [hx w, one_smul]
      show w = mat 3 K 1 *ᵥ w
      rw [map_one, Matrix.one_mulVec]
    · right
      refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
      rw [hx w, neg_smul, one_smul]
      show -w = mat 3 K (zNeg 3 K) *ᵥ w
      rw [mulVec_zNeg]
  have hsq : ∀ g : Bt, g ≠ 1 → g ≠ z → g * g = z := by
    intro g hg1 hgz
    obtain ⟨ε, hε, hs⟩ := hB.sq g.1 g.2
    rcases hε with rfl | rfl
    · exfalso
      rcases hnc g.1 g.2 (fun w => by rw [hs w, one_smul]) with h | h
      · apply hg1
        refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
        show mat 3 K g.1 *ᵥ w = mat 3 K 1 *ᵥ w
        rw [h w, map_one, Matrix.one_mulVec]
      · apply hgz
        refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
        show mat 3 K g.1 *ᵥ w = mat 3 K (zNeg 3 K) *ᵥ w
        rw [h w, mulVec_zNeg]
    · refine Subtype.ext (Sp_ext_mulVec fun w => ?_)
      show mat 3 K (g.1 * g.1) *ᵥ w = mat 3 K (zNeg 3 K) *ᵥ w
      rw [map_mul, ← Matrix.mulVec_mulVec, hs w, mulVec_zNeg, neg_smul, one_smul]
  exact card_le_eight z hz1 hzz hcomm hsq

include h2 in
theorem card_le_thirtytwo [Finite K] (hK : Nat.card K = 3) {Bt : Subgroup (StatedSp 3 K)}
    (hB : PmGroup Bt) : Nat.card Bt ≤ 32 := by
  by_cases hex : ∃ g ∈ Bt, (∀ w, mat 3 K g *ᵥ (mat 3 K g *ᵥ w) = w) ∧
      (∃ w, mat 3 K g *ᵥ w ≠ w) ∧ (∃ w, mat 3 K g *ᵥ w ≠ -w)
  · obtain ⟨g, hg, hg2, hg1, hg1'⟩ := hex
    exact card_le_of_involution h2 hK hB hg hg2 hg1 hg1'
  · have := card_le_of_no_involution h2 hB (fun g hg hg2 => by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hcon
      exact hex ⟨g, hg, hg2, ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩)
    omega


end Core

section PSp

theorem pmGroup_comap [NeZero r] (B : Subgroup (StatedProj (StatedSp r K)))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    PmGroup (B.comap (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)))) where
  neg := by
    rw [Subgroup.mem_comap]
    show (QuotientGroup.mk (zNeg r K) : StatedProj (StatedSp r K)) ∈ B
    rw [mk_zNeg]
    exact B.one_mem
  sq := by
    intro g hg
    rw [Subgroup.mem_comap] at hg
    have h1 := h2 _ hg
    have h1' : (QuotientGroup.mk (g * g) : StatedProj (StatedSp r K)) = 1 := by
      rw [QuotientGroup.mk_mul]; exact h1
    obtain ⟨ε, hε, hm⟩ := pm_of_mk_eq_one h1'
    refine ⟨ε, hε, fun w => ?_⟩
    rw [Matrix.mulVec_mulVec, ← map_mul, hm, Matrix.smul_mulVec, Matrix.one_mulVec]
  comm := by
    intro g hg h hh
    rw [Subgroup.mem_comap] at hg hh
    have h1 := hc _ hg _ hh
    have h1' : (QuotientGroup.mk (g * h * (h * g)⁻¹) : StatedProj (StatedSp r K)) = 1 := by
      have : (QuotientGroup.mk (g * h) : StatedProj (StatedSp r K)) =
          QuotientGroup.mk (h * g) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h1
      rw [QuotientGroup.mk_mul, this, QuotientGroup.mk_inv]
      exact mul_inv_cancel _
    obtain ⟨ε, hε, hm⟩ := pm_of_mk_eq_one h1'
    refine ⟨ε, hε, fun w => ?_⟩
    have e : g * h = (g * h * (h * g)⁻¹) * (h * g) := by group
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul, e, map_mul, hm,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]

theorem two_rank_psp63 [Finite K] (h2 : (2 : K) ≠ 0) (hK : Nat.card K = 3)
    (B : Subgroup (StatedProj (StatedSp 3 K))) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2B : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ 4 := by
  classical
  have hB := pmGroup_comap B hc h2B
  have h32 := card_le_thirtytwo h2 hK hB
  set Bt := B.comap (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf
    (StatedSp 3 K))) with hBt
  have hσ : ∀ b : B, ∃ g : StatedSp 3 K, (QuotientGroup.mk g : StatedProj (StatedSp 3 K)) = b.1 :=
    fun b => QuotientGroup.mk_surjective b.1
  choose σ hσ using hσ
  have hσB : ∀ b : B, σ b ∈ Bt := fun b => by
    rw [hBt, Subgroup.mem_comap]
    show (QuotientGroup.mk (σ b) : StatedProj (StatedSp 3 K)) ∈ B
    rw [hσ b]; exact b.2
  let F : B × Bool → Bt := fun x =>
    if x.2 then ⟨σ x.1 * zNeg 3 K, Bt.mul_mem (hσB x.1) hB.neg⟩ else ⟨σ x.1, hσB x.1⟩
  have hFmk : ∀ x, (QuotientGroup.mk (F x).1 : StatedProj (StatedSp 3 K)) = x.1.1 := by
    rintro ⟨b, t⟩
    cases t
    · simp [F, hσ b]
    · simp [F, hσ b, QuotientGroup.mk_mul, mk_zNeg]
  have hFinj : Function.Injective F := by
    rintro ⟨b, t⟩ ⟨b', t'⟩ e
    have hb : b = b' := Subtype.ext (by rw [← hFmk (b, t), ← hFmk (b', t'), e])
    subst hb
    have e' := congrArg Subtype.val e
    cases t <;> cases t'
    · rfl
    · exfalso
      simp only [F, Bool.false_eq_true, ↓reduceIte] at e'
      exact zNeg_ne_one h2 (mul_left_cancel (a := σ b) (by rw [mul_one]; exact e'.symm))
    · exfalso
      simp only [F, Bool.false_eq_true, ↓reduceIte] at e'
      exact zNeg_ne_one h2 (mul_left_cancel (a := σ b) (by rw [mul_one]; exact e'))
    · rfl
  have := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_prod] at this
  simp at this
  omega

end PSp

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
