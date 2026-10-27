module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFStepC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section D6outer




variable {n : ℕ}


section D6

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem prod4_perm {Z : Type*} [Group Z] (f : Fin 4 → Z) (hc : ∀ i j, f i * f j = f j * f i)
    (σ : Equiv.Perm (Fin 4)) :
    f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3) = f 0 * f 1 * f 2 * f 3 := by
  have hperm : (List.ofFn (f ∘ σ)).Perm (List.ofFn f) := Equiv.Perm.ofFn_comp_perm σ f
  have hpw : (List.ofFn (f ∘ σ)).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact hc _ _
  have := hperm.prod_eq' hpw
  simpa [List.ofFn_succ, mul_assoc] using this

theorem e8_closure {Z : Type*} [Group Z] {p q r : Z} (hp : p * p = 1) (hq : q * q = 1)
    (hr : r * r = 1) (hpq : p * q = q * p) (hpr : p * r = r * p) (hqr : q * r = r * q) :
    ∀ g ∈ Subgroup.closure ({p, q, r} : Set Z), g = 1 ∨ g = p ∨ g = q ∨ g = r ∨ g = p * q ∨
      g = p * r ∨ g = q * r ∨ g = p * q * r := by
  intro g hg
  have hA : ∀ g ∈ Subgroup.closure ({p, q} : Set Z), g = 1 ∨ g = p ∨ g = q ∨ g = p * q :=
    klein_closure hp hq hpq
  have hpA : p ∈ Subgroup.closure ({p, q} : Set Z) := Subgroup.subset_closure (by simp)
  have hqA : q ∈ Subgroup.closure ({p, q} : Set Z) := Subgroup.subset_closure (by simp)
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hstep : ∀ x : Z, (x ∈ Subgroup.closure ({p, q} : Set Z) ∨
      x * r ∈ Subgroup.closure ({p, q} : Set Z)) → ∀ y ∈ ({p, q, r} : Set Z),
      (x * y ∈ Subgroup.closure ({p, q} : Set Z) ∨ x * y * r ∈ Subgroup.closure ({p, q} : Set Z)) := by
    intro x hxr y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy
    · rw [hy]
      rcases hxr with h1 | h1
      · exact Or.inl (Subgroup.mul_mem _ h1 hpA)
      · refine Or.inr ?_
        have : x * p * r = x * r * p := by
          calc x * p * r = x * (p * r) := mul_assoc _ _ _
            _ = x * (r * p) := by rw [hpr]
            _ = x * r * p := (mul_assoc _ _ _).symm
        rw [this]; exact Subgroup.mul_mem _ h1 hpA
    · rw [hy]
      rcases hxr with h1 | h1
      · exact Or.inl (Subgroup.mul_mem _ h1 hqA)
      · refine Or.inr ?_
        have : x * q * r = x * r * q := by
          calc x * q * r = x * (q * r) := mul_assoc _ _ _
            _ = x * (r * q) := by rw [hqr]
            _ = x * r * q := (mul_assoc _ _ _).symm
        rw [this]; exact Subgroup.mul_mem _ h1 hqA
    · rw [hy]
      rcases hxr with h1 | h1
      · refine Or.inr ?_
        rw [mul_assoc, hr, mul_one]; exact h1
      · exact Or.inl h1
  have hmain : g ∈ Subgroup.closure ({p, q} : Set Z) ∨ g * r ∈ Subgroup.closure ({p, q} : Set Z) := by
    refine Subgroup.closure_induction_right (p := fun g _ =>
      g ∈ Subgroup.closure ({p, q} : Set Z) ∨ g * r ∈ Subgroup.closure ({p, q} : Set Z)) ?_ ?_ ?_ hg
    · exact Or.inl (Subgroup.one_mem _)
    · intro x hx y hy hxr
      exact hstep x hxr y hy
    · intro x hx y hy hxr
      have hy' : y⁻¹ = y := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy | hy <;> rw [hy]
        · exact hpi
        · exact hqi
        · exact hri
      rw [hy']
      exact hstep x hxr y hy
  rcases hmain with h1 | h1
  · rcases hA g h1 with e | e | e | e <;> rw [e] <;> simp
  · have hg' : g = (g * r) * r := by rw [mul_assoc, hr, mul_one]
    rcases hA (g * r) h1 with e | e | e | e <;> rw [hg', e] <;> simp [mul_assoc]

theorem exists_gen_sq {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {W₁ J : Subgroup Y} {z : Y}
    (hW₁ : W₁ ∈ WSet Ω) (hJΩ : J ∈ Ω) (hJD : J ∈ DSet Ω W₁) (h2 : IsPGroup 2 ↥J)
    (hJq : Q8Facts J z) : ∃ g, g ∈ J ∧ g ∈ W₁ ∧ g * g = z := by
  have hJsyl : IsSylow2In J J := ⟨le_rfl, h2, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨-, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW₁ hJD hJΩ hJsyl
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥(J ⊓ W₁) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgJ : (g : Y) ∈ J := g.2.1
  have hgW : (g : Y) ∈ W₁ := g.2.2
  refine ⟨g, hgJ, hgW, ?_⟩
  rcases hJq.sq_cases _ hgJ with e | e
  · exfalso
    have h2' : orderOf g ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply Subtype.ext
      show (g : Y) ^ 2 = 1
      rw [pow_two]; exact e
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  · exact e

theorem Q8Facts.three_classes {M : Subgroup Y} {z : Y} (h : Q8Facts M z) {k₁ k₂ k₃ b : Y}
    (hk₁ : k₁ ∈ M) (hk₂ : k₂ ∈ M) (hk₃ : k₃ ∈ M) (hb : b ∈ M) (h1 : k₁ * k₁ = z)
    (h2 : k₂ * k₂ = z) (h3 : k₃ * k₃ = z) (hb2 : b * b = z) (h21 : k₂ ≠ k₁) (h21' : k₂ ≠ k₁ * z)
    (h31 : k₃ ≠ k₁) (h31' : k₃ ≠ k₁ * z) (h32 : k₃ ≠ k₂) (h32' : k₃ ≠ k₂ * z) :
    b = k₁ ∨ b = k₁ * z ∨ b = k₂ ∨ b = k₂ * z ∨ b = k₃ ∨ b = k₃ * z := by
  by_cases e1 : b = k₁
  · exact Or.inl e1
  by_cases e2 : b = k₁ * z
  · exact Or.inr (Or.inl e2)
  by_cases e3 : b = k₂
  · exact Or.inr (Or.inr (Or.inl e3))
  by_cases e4 : b = k₂ * z
  · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
  have p1 := h.prod3 k₁ hk₁ k₂ hk₂ b hb h1 h2 hb2 h21 h21' e1 e2 e3 e4
  have p2 := h.prod3 k₁ hk₁ k₂ hk₂ k₃ hk₃ h1 h2 h3 h21 h21' h31 h31' h32 h32'
  have hzz := h.z_sq
  rcases p1 with q1 | q1 <;> rcases p2 with q2 | q2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    exact mul_left_cancel (q1.trans q2.symm)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    apply mul_left_cancel (a := k₁ * k₂)
    rw [q1, ← mul_assoc, q2, hzz]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    apply mul_left_cancel (a := k₁ * k₂)
    rw [q1, ← mul_assoc, q2, one_mul]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    exact mul_left_cancel (q1.trans q2.symm)

theorem WFFrame.frameInv_canonical (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R))) {s' : Y}
    (hs' : s' ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W₁) :
    ∃ b : Fin 4 → Y, (∀ i, b i ∈ M i ∧ b i ∈ W₁ ∧ b i * b i = t) ∧
      s' = b 0 * b 1 * b 2 * b 3 := by
  obtain ⟨J', b', hinj, hJ'mem, hb', rfl⟩ := hs'
  have hπ : ∀ i, ∃ j, M j = J' i := fun i => hfr.surj _ (hJ'mem i)
  choose π hπM using hπ
  have hπinj : Function.Injective π := fun i j e => hinj (by rw [← hπM i, ← hπM j, e])
  have hπbij : Function.Bijective π := (Finite.injective_iff_bijective).mp hπinj
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective π hπbij
  have hab := Q3CL.Thompson.commutes_of_mem_WSet h.hyp hW₁
  have hc : ∀ i j, b' i * b' j = b' j * b' i := fun i j =>
    hab _ (Subgroup.mem_inf.mp (hb' i).1).2 _ (Subgroup.mem_inf.mp (hb' j).1).2
  refine ⟨fun l => b' (σ.symm l), ?_, ?_⟩
  · intro l
    have hl : π (σ.symm l) = l := σ.apply_symm_apply l
    have hmem := (hb' (σ.symm l)).1
    have hJl : J' (σ.symm l) = M l := by rw [← hπM, hl]
    rw [hJl] at hmem
    refine ⟨(Subgroup.mem_inf.mp hmem).1, (Subgroup.mem_inf.mp hmem).2, ?_⟩
    exact T7A.sq_eq_of_orderOf_four (h.uniqInv (hfr.mem l)) (Subgroup.mem_inf.mp hmem).1
      (hb' (σ.symm l)).2
  · exact (prod4_perm b' hc σ.symm).symm

theorem WFFrame.frame_basic (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {W₁ : Subgroup Y}
    {b : Fin 4 → Y} (hb : ∀ i, b i ∈ M i ∧ b i ∈ W₁ ∧ b i * b i = t) :
    (b 0 * b 1 * b 2 * b 3) * (b 0 * b 1 * b 2 * b 3) = 1 ∧
      t * (b 0 * b 1 * b 2 * b 3) = (b 0 * b 1 * b 2 * b 3) * t ∧
      b 0 * b 1 * b 2 * b 3 ≠ 1 ∧ b 0 * b 1 * b 2 * b 3 ≠ t ∧
      b 0 * b 1 * b 2 * b 3 ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W₁ := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hcr : ∀ p q : Fin 4, p ≠ q → Commute (b p) (b q) := fun p q hpq =>
    hfr.cross h hpq (hb p).1 (hb q).1
  have hcc : ∀ p q : Fin 4, Commute (b p) (b q) := fun p q => by
    by_cases hpq : p = q
    · subst hpq; exact Commute.refl _
    · exact hcr p q hpq
  refine ⟨?_, ?_, ?_⟩
  · rw [prod4_sq_comm (hcc 0 1) (hcc 0 2) (hcc 0 3) (hcc 1 2) (hcc 1 3) (hcc 2 3), (hb 0).2.2,
      (hb 1).2.2, (hb 2).2.2, (hb 3).2.2, ht, one_mul, ht]
  · have hti : ∀ p, Commute t (b p) := fun p => hfr.t_comm h p (hb p).1
    exact ((((hti 0).mul_right (hti 1)).mul_right (hti 2)).mul_right (hti 3)).eq
  · have := frame_prod_ne (h.q8 (hfr.mem 0)) (hb 0).1 (hb 1).1 (hb 2).1 (hb 3).1 (hb 0).2.2
      (fun m hm m' hm' => hfr.cross h (i := 0) (j := 1) (by decide) hm hm')
      (fun m hm m' hm' => hfr.cross h (i := 0) (j := 2) (by decide) hm hm')
      (fun m hm m' hm' => hfr.cross h (i := 0) (j := 3) (by decide) hm hm')
    refine ⟨this.1, this.2, ?_⟩
    exact ⟨M, b, hfr.inj, hfr.mem, fun i => ⟨Subgroup.mem_inf.mpr ⟨(hb i).1, (hb i).2.1⟩,
      orderOf_four_of_sq (hb i).2.2 ht (h.q8 (hfr.mem 0)).z_ne⟩, rfl⟩

theorem WFFrame.r1 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {W₁ W₂ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R))) (ht₁ : t ∈ W₁)
    (hW₂ : W₂ ∈ WSet (CoreAssembly.conjClass (tightCore R))) (ht₂ : t ∈ W₂)
    {b₁ b₂ : Fin 4 → Y} (hb₁ : ∀ i, b₁ i ∈ M i ∧ b₁ i ∈ W₁ ∧ b₁ i * b₁ i = t)
    (hb₂ : ∀ i, b₂ i ∈ M i ∧ b₂ i ∈ W₂ ∧ b₂ i * b₂ i = t) {i j : Fin 4} (hij : i ≠ j)
    (hi : b₂ i = b₁ i ∨ b₂ i = b₁ i * t) (hj : b₂ j = b₁ j ∨ b₂ j = b₁ j * t) :
    b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3 = b₁ 0 * b₁ 1 * b₁ 2 * b₁ 3 ∨
      b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3 = (b₁ 0 * b₁ 1 * b₁ 2 * b₁ 3) * t := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have ht1 := (h.q8 (hfr.mem 0)).z_ne
  obtain ⟨hs₁2, hts₁, -, -, hs₁F⟩ := hfr.frame_basic h hb₁
  obtain ⟨hs₂2, hts₂, -, -, hs₂F⟩ := hfr.frame_basic h hb₂
  have hmemW₂ : ∀ p, (b₂ p = b₁ p ∨ b₂ p = b₁ p * t) → b₁ p ∈ W₂ := by
    intro p hp
    rcases hp with e | e
    · rw [← e]; exact (hb₂ p).2.1
    · have : b₁ p = b₂ p * t := by
        rw [e, mul_assoc, ht, mul_one]
      rw [this]; exact W₂.mul_mem (hb₂ p).2.1 ht₂
  have hi₂ := hmemW₂ i hi
  have hj₂ := hmemW₂ j hj
  have ho : ∀ p, orderOf (b₁ p) = 4 := fun p => orderOf_four_of_sq (hb₁ p).2.2 ht ht1
  have hne : M i ≠ M j := fun e => hij (hfr.inj e)
  have hN₁ := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W₁ hW₁ ht₁ (M i) (hfr.mem i) (M j) (hfr.mem j) hne
    (b₁ i) (Subgroup.mem_inf.mpr ⟨(hb₁ i).1, (hb₁ i).2.1⟩) (b₁ j)
    (Subgroup.mem_inf.mpr ⟨(hb₁ j).1, (hb₁ j).2.1⟩) (ho i) (ho j) _ hs₁F
  have hN₂ := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W₂ hW₂ ht₂ (M i) (hfr.mem i) (M j) (hfr.mem j) hne
    (b₁ i) (Subgroup.mem_inf.mpr ⟨(hb₁ i).1, hi₂⟩) (b₁ j)
    (Subgroup.mem_inf.mpr ⟨(hb₁ j).1, hj₂⟩) (ho i) (ho j) _ hs₂F
  obtain ⟨y₀, hy₀C, hy₀F⟩ := h.exists_fuse_pair hW₁ ht₁ (hfr.mem i) (hfr.mem j) hne
    (Subgroup.mem_inf.mpr ⟨(hb₁ i).1, (hb₁ i).2.1⟩) (Subgroup.mem_inf.mpr ⟨(hb₁ j).1, (hb₁ j).2.1⟩)
    (ho i) (ho j)
  obtain ⟨bf, hbf, hfeq⟩ := hfr.frameInv_canonical h hW₁ hy₀F
  obtain ⟨-, -, hf1, hft, -⟩ := hfr.frame_basic h hbf
  rw [← hfeq] at hf1 hft
  have hy₀' := Subgroup.mem_centralizer_singleton_iff.mp hy₀C
  have hf₁ : y₀ * t * y₀⁻¹ ∈ Subgroup.closure ({t, b₁ 0 * b₁ 1 * b₁ 2 * b₁ 3} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp (hN₁ hy₀C) t).mp (Subgroup.subset_closure (by simp))
  have hf₂ : y₀ * t * y₀⁻¹ ∈ Subgroup.closure ({t, b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp (hN₂ hy₀C) t).mp (Subgroup.subset_closure (by simp))
  have hk₁ := klein_closure ht hs₁2 hts₁ _ hf₁
  have hk₂ := klein_closure ht hs₂2 hts₂ _ hf₂
  have hff : y₀ * t * y₀⁻¹ ≠ 1 ∧ y₀ * t * y₀⁻¹ ≠ t := ⟨hf1, hft⟩
  rcases hk₁ with e1 | e1 | e1 | e1
  · exact absurd e1 hff.1
  · exact absurd e1 hff.2
  · rcases hk₂ with e2 | e2 | e2 | e2
    · exact absurd e2 hff.1
    · exact absurd e2 hff.2
    · left; exact e2.symm.trans e1
    · right
      have : b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3 = t * (y₀ * t * y₀⁻¹) := by
        rw [e2, ← mul_assoc, ht, one_mul]
      rw [this, e1, hts₁]
  · rcases hk₂ with e2 | e2 | e2 | e2
    · exact absurd e2 hff.1
    · exact absurd e2 hff.2
    · right
      have : b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3 = y₀ * t * y₀⁻¹ := e2.symm
      rw [this, e1]; exact hts₁
    · left
      have : b₂ 0 * b₂ 1 * b₂ 2 * b₂ 3 = t * (y₀ * t * y₀⁻¹) := by
        rw [e2, ← mul_assoc, ht, one_mul]
      rw [this, e1, ← mul_assoc, ht, one_mul]

theorem WFFrame.classes_distinct (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {i : Fin 4}
    (hmv : ¬ ∀ m ∈ M i, x * m = m * x) :
    (x * a i * x⁻¹ ≠ a i ∧ x * a i * x⁻¹ ≠ a i * t) ∧
      ((x * x) * a i * (x * x)⁻¹ ≠ a i ∧ (x * x) * a i * (x * x)⁻¹ ≠ a i * t) ∧
      ((x * x) * a i * (x * x)⁻¹ ≠ x * a i * x⁻¹ ∧
        (x * x) * a i * (x * x)⁻¹ ≠ (x * a i * x⁻¹) * t) := by
  have hq := h.q8 (hfr.mem i)
  have hk := hfr.haM i
  have hk2 := hfr.sq h i
  have hxM' : ∀ m ∈ M i, x * m * x⁻¹ ∈ M i := fun m hm => hfr.act_mem hxM i hm
  have hxxz : (x * x) * t = t * (x * x) := by
    calc (x * x) * t = x * (x * t) := mul_assoc _ _ _
      _ = x * (t * x) := by rw [hxt]
      _ = (x * t) * x := (mul_assoc _ _ _).symm
      _ = (t * x) * x := by rw [hxt]
      _ = t * (x * x) := mul_assoc _ _ _
  have hk₂ : x * a i * x⁻¹ ∈ M i := hxM' _ hk
  have hs2 : x * a i * x⁻¹ * (x * a i * x⁻¹) = t := hfr.act_sq h hxt i
  have hnc2 : ¬ ∀ m ∈ M i, (x * x) * m = m * (x * x) := fun hc => hmv (cent_of_sq_cent hxo hc)
  have n1 := hq.not_zfix_of_not_cent hxo hxt hxM' hmv hk hk2
  have n2 := hq.not_zfix_of_not_cent hxo hxt hxM' hmv hk₂ hs2
  have n3 := hq.not_zfix_of_not_cent (odd_orderOf_mul_self hxo) hxxz (sq_normalizes hxM') hnc2 hk hk2
  unfold ZFix at n1 n2 n3
  push Not at n1 n2 n3
  have e3 : x * (x * a i * x⁻¹) * x⁻¹ = (x * x) * a i * (x * x)⁻¹ := by group
  rw [e3] at n2
  exact ⟨n1, n3, n2⟩

theorem WFFrame.r3 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {W' : Subgroup Y}
    (hW' : W' ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW' : t ∈ W') {b : Fin 4 → Y}
    (hb : ∀ i, b i ∈ M i ∧ b i ∈ W' ∧ b i * b i = t) :
    (b 0 * b 1 * b 2 * b 3 = a 0 * a 1 * a 2 * a 3 ∨
        b 0 * b 1 * b 2 * b 3 = (a 0 * a 1 * a 2 * a 3) * t) ∨
      (b 0 * b 1 * b 2 * b 3 = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ ∨
        b 0 * b 1 * b 2 * b 3 = (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * t) ∨
      (b 0 * b 1 * b 2 * b 3 = (x * x) * (a 0 * a 1 * a 2 * a 3) * (x * x)⁻¹ ∨
        b 0 * b 1 * b 2 * b 3 = ((x * x) * (a 0 * a 1 * a 2 * a 3) * (x * x)⁻¹) * t) := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have ht1 := (h.q8 (hfr.mem 0)).z_ne
  obtain ⟨g, hg0, hg1, hg2⟩ : ∃ g : Fin 3 → Y, g 0 = 1 ∧ g 1 = x ∧ g 2 = x * x :=
    ⟨![1, x, x * x], rfl, rfl, rfl⟩
  have hcls : ∀ i, ∃ c : Fin 3, b i = g c * a i * (g c)⁻¹ ∨ b i = (g c * a i * (g c)⁻¹) * t := by
    intro i
    obtain ⟨⟨h21, h21'⟩, ⟨h31, h31'⟩, ⟨h32, h32'⟩⟩ := hfr.classes_distinct h hxo hxt hxM (hmv i)
    have hq := h.q8 (hfr.mem i)
    have hu : x * a i * x⁻¹ ∈ M i := hfr.act_mem hxM i (hfr.haM i)
    have hu' : (x * x) * a i * (x * x)⁻¹ ∈ M i := by
      have e : (x * x) * a i * (x * x)⁻¹ = x * (x * a i * x⁻¹) * x⁻¹ := by group
      rw [e]; exact hfr.act_mem hxM i hu
    have hsq' : (x * x) * a i * (x * x)⁻¹ * ((x * x) * a i * (x * x)⁻¹) = t := by
      calc (x * x) * a i * (x * x)⁻¹ * ((x * x) * a i * (x * x)⁻¹) =
          (x * x) * (a i * a i) * (x * x)⁻¹ := by group
        _ = t := by
          rw [hfr.sq h i]
          have hxxt : (x * x) * t = t * (x * x) := by
            calc (x * x) * t = x * (x * t) := mul_assoc _ _ _
              _ = x * (t * x) := by rw [hxt]
              _ = (x * t) * x := (mul_assoc _ _ _).symm
              _ = (t * x) * x := by rw [hxt]
              _ = t * (x * x) := mul_assoc _ _ _
          rw [hxxt]; group
    have := hq.three_classes (hfr.haM i) hu hu' (hb i).1
      (hfr.sq h i) (hfr.act_sq h hxt i) hsq' (hb i).2.2 h21 h21' h31 h31' h32 h32'
    rcases this with e | e | e | e | e | e
    · exact ⟨0, Or.inl (by rw [hg0]; simpa using e)⟩
    · exact ⟨0, Or.inr (by rw [hg0]; simpa using e)⟩
    · exact ⟨1, Or.inl (by rw [hg1]; exact e)⟩
    · exact ⟨1, Or.inr (by rw [hg1]; exact e)⟩
    · exact ⟨2, Or.inl (by rw [hg2]; exact e)⟩
    · exact ⟨2, Or.inr (by rw [hg2]; exact e)⟩
  choose κ hκ using hcls
  obtain ⟨i, j, hij, hκij⟩ := Fintype.exists_ne_map_eq_of_card_lt κ (by simp)
  obtain ⟨c, hc⟩ : ∃ c, c = κ j := ⟨_, rfl⟩
  have hgc : ∀ c, g c = 1 ∨ g c = x ∨ g c = x * x := by
    intro c
    fin_cases c
    exacts [Or.inl hg0, Or.inr (Or.inl hg1), Or.inr (Or.inr hg2)]
  have hxxt : (x * x) * t = t * (x * x) := by
    calc (x * x) * t = x * (x * t) := mul_assoc _ _ _
      _ = x * (t * x) := by rw [hxt]
      _ = (x * t) * x := (mul_assoc _ _ _).symm
      _ = (t * x) * x := by rw [hxt]
      _ = t * (x * x) := mul_assoc _ _ _
  have hgM : ∀ l, g c * a l * (g c)⁻¹ ∈ M l := by
    intro l
    rcases hgc c with e | e | e
    · rw [e]; simpa using hfr.haM l
    · rw [e]; exact hfr.act_mem hxM l (hfr.haM l)
    · rw [e]
      have e' : (x * x) * a l * (x * x)⁻¹ = x * (x * a l * x⁻¹) * x⁻¹ := by group
      rw [e']; exact hfr.act_mem hxM l (hfr.act_mem hxM l (hfr.haM l))
  have hgsq : ∀ l, (g c * a l * (g c)⁻¹) * (g c * a l * (g c)⁻¹) = t := by
    intro l
    rcases hgc c with e | e | e
    · rw [e]; simpa using hfr.sq h l
    · rw [e]; exact hfr.act_sq h hxt l
    · rw [e]
      calc (x * x) * a l * (x * x)⁻¹ * ((x * x) * a l * (x * x)⁻¹) =
          (x * x) * (a l * a l) * (x * x)⁻¹ := by group
        _ = t := by rw [hfr.sq h l, hxxt]; group
  have hgt : g c * t = t * g c := by
    rcases hgc c with e | e | e
    · rw [e]; simp
    · rw [e]; exact hxt
    · rw [e]; exact hxxt
  have hW₁ : conjSub (g c) W ∈ WSet (CoreAssembly.conjClass (tightCore R)) :=
    WSet.conj h.hyp.conjInvariant h.hW (g c)
  have ht₁ : t ∈ conjSub (g c) W := by
    have := conj_mem_conjSub (n := g c) h.t_mem
    rwa [show g c * t * (g c)⁻¹ = t from mul_inv_eq_iff_eq_mul.mpr hgt] at this
  have hb₁ : ∀ l, g c * a l * (g c)⁻¹ ∈ M l ∧ g c * a l * (g c)⁻¹ ∈ conjSub (g c) W ∧
      (g c * a l * (g c)⁻¹) * (g c * a l * (g c)⁻¹) = t :=
    fun l => ⟨hgM l, conj_mem_conjSub (hfr.haW l), hgsq l⟩
  have hi : b i = g c * a i * (g c)⁻¹ ∨ b i = (g c * a i * (g c)⁻¹) * t := by
    rw [hc, ← hκij]; exact hκ i
  have hj : b j = g c * a j * (g c)⁻¹ ∨ b j = (g c * a j * (g c)⁻¹) * t := by
    rw [hc]; exact hκ j
  have hr := hfr.r1 hB h hW₁ ht₁ hW' htW' (b₁ := fun l => g c * a l * (g c)⁻¹) (b₂ := b) hb₁ hb
    hij hi hj
  have hprod : (g c * a 0 * (g c)⁻¹) * (g c * a 1 * (g c)⁻¹) * (g c * a 2 * (g c)⁻¹) *
      (g c * a 3 * (g c)⁻¹) = g c * (a 0 * a 1 * a 2 * a 3) * (g c)⁻¹ := by group
  have hr' : b 0 * b 1 * b 2 * b 3 = g c * (a 0 * a 1 * a 2 * a 3) * (g c)⁻¹ ∨
      b 0 * b 1 * b 2 * b 3 = (g c * (a 0 * a 1 * a 2 * a 3) * (g c)⁻¹) * t := by
    rw [← hprod]; exact hr
  rcases hgc c with e | e | e
  · left; rw [e] at hr'; simpa using hr'
  · right; left; rw [e] at hr'; exact hr'
  · right; right; rw [e] at hr'; exact hr'

end D6

end D6outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
