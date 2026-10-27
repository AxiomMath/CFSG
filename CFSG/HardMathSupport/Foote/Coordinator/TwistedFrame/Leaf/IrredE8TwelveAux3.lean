module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux3b
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux3c

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

abbrev V8 : Type := Fin Tag.E8.rank → ℤ

@[expose] def sig1 : Finset V8 :=
  {![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![2, 2, 3, 4, 3, 2, 1, 1],
    ![0, 1, 1, 2, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 2, 1],
    ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1]}

@[expose] def dl : Finset V8 := deg1Roots \ sig1

@[expose] def a0 : V8 := ![0, 0, 0, 0, 0, 0, 1, 0]
@[expose] def a2 : V8 := ![2, 2, 3, 4, 3, 2, 1, 0]
@[expose] def a1 : V8 := ![0, 1, 1, 2, 2, 2, 1, 0]
@[expose] def lf1 : V8 := ![0, 1, 0, 0, 0, 0, 0, 0]
@[expose] def lf2 : V8 := ![0, 0, 1, 0, 0, 0, 0, 0]
@[expose] def lf4 : V8 := ![0, 0, 0, 0, 1, 0, 0, 0]
@[expose] def cn : V8 := ![0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def wp (u : V8) : V8 :=
  TwClass.wordE8Twelve.foldr (reflect Tag.E8) u

section Ops

variable {L : Type} [Field L]

@[expose] def actOp (a : V8 → V8 → ℤ) (γ : V8) (t : L) : (V8 → L) →ₗ[L] (V8 → L) where
  toFun v := actFun a γ t v
  map_add' v v' := by
    funext ν
    simp only [actFun, Pi.add_apply]
    ring
  map_smul' c v := by
    funext ν
    simp only [actFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] def tripleOp (a : V8 → V8 → ℤ) (γ₀ γ₁ γ₂ : V8) (q : ℕ) (s₁ s₂ x : L) :
    (V8 → L) →ₗ[L] (V8 → L) :=
  actOp a γ₀ x ∘ₗ actOp a γ₁ (s₁ * x ^ q) ∘ₗ actOp a γ₂ (s₂ * x ^ (q ^ 2))

@[expose] def TripleStable (a : V8 → V8 → ℤ) (Z : Submodule L (V8 → L)) (γ₀ γ₁ γ₂ : V8) (q : ℕ)
    (s₁ s₂ ε : L) : Prop :=
  ∀ x : L, x ^ (q ^ 3) = ε * x → ∀ z ∈ Z, tripleOp a γ₀ γ₁ γ₂ q s₁ s₂ x z ∈ Z

@[expose] def SingleStable (a : V8 → V8 → ℤ) (Z : Submodule L (V8 → L)) (γ : V8) (q : ℕ)
    (ε : L) : Prop :=
  ∀ x : L, x ^ q = ε * x → ∀ z ∈ Z, actOp a γ x z ∈ Z

structure SignData (L : Type) [Field L] where
  s₁ : L
  s₂ : L
  ε : L
  hs₁ : s₁ ≠ 0
  hs₂ : s₂ ≠ 0
  hε : ε ≠ 0

namespace CoreAux

theorem sig1_data : ∀ ν ∈ deg1L, (ν ∈ sig1 ↔ ν ∉ dlL) := by
  decide +kernel

theorem mem_dl_iff {ν : V8} : ν ∈ dl ↔ ν ∈ dlL := by
  constructor
  · intro h
    rw [dl, Finset.mem_sdiff] at h
    have hν := deg1_data.1 ν h.1
    by_contra h'
    exact h.2 ((sig1_data ν hν).2 h')
  · intro h
    have hν : ν ∈ deg1L := list_data.2.2.1 ν h
    rw [dl, Finset.mem_sdiff]
    exact ⟨deg1_data.2.1 ν hν, fun hs => (sig1_data ν hν).1 hs h⟩

theorem gens_data : ∀ γ ∈ gensL, γ ∈ [a0, a1, a2, cn, lf1, lf2, lf4, -a0, -a1, -a2, -cn, -lf1,
    -lf2, -lf4] := by
  decide +kernel

theorem gens_cases {γ : V8} (hγ : γ ∈ gensL) : γ = a0 ∨ γ = a1 ∨ γ = a2 ∨ γ = cn ∨ γ = lf1 ∨
    γ = lf2 ∨ γ = lf4 ∨ γ = -a0 ∨ γ = -a1 ∨ γ = -a2 ∨ γ = -cn ∨ γ = -lf1 ∨ γ = -lf2 ∨
    γ = -lf4 := by
  simpa using gens_data γ hγ

theorem adm_unit {a : V8 → V8 → ℤ} (ha : Adm a) {γ μ : V8} (hγ : γ ∈ gensL) (hμ : μ ∈ deg1L)
    (h : γ + μ ∈ deg1L) : a γ μ = 1 ∨ a γ μ = -1 := by
  have hr : γ + μ ∈ rootFinset .E8 := (Finset.mem_filter.1 (deg1_data.2.1 _ h)).1
  exact (abs_eq zero_le_one).1
    ((ha γ (deg1_data.2.2 γ hγ) (list_data.1 γ hγ) μ (deg1_data.2.1 μ hμ)).1 hr)

theorem adm_cast_ne_zero {a : V8 → V8 → ℤ} (ha : Adm a) {γ μ : V8} (hγ : γ ∈ gensL)
    (hμ : μ ∈ deg1L) (h : γ + μ ∈ deg1L) : (a γ μ : L) ≠ 0 := by
  rcases adm_unit ha hγ hμ h with h' | h' <;> simp [h']

theorem adm_zero {a : V8 → V8 → ℤ} (ha : Adm a) {γ μ : V8} (hγ : γ ∈ gensL) (hμ : μ ∈ deg1L)
    (h : γ + μ ∉ deg1L) : a γ μ = 0 := by
  refine (ha γ (deg1_data.2.2 γ hγ) (list_data.1 γ hγ) μ (deg1_data.2.1 μ hμ)).2 fun hr => h ?_
  refine deg1_data.1 _ (Finset.mem_filter.2 ⟨hr, ?_⟩)
  rw [Pi.add_apply, list_data.1 γ hγ, list_data.2.1 μ hμ, zero_add]

end CoreAux

theorem core {L : Type} [Field L] [IsAlgClosed L] {a : V8 → V8 → ℤ} (ha : Adm a) (q : ℕ)
    (hq : 2 ≤ q) (hqL : (q : L) = 0) (Z : Submodule L (V8 → L)) (hsupp : ∀ v ∈ Z, ∀ ν, ν ∉ dl → v ν = 0)
    (hne : Z ≠ ⊥) (Sa Sb Sc Sd : SignData L) (εe εf : L) (hεe : εe ≠ 0) (hεf : εf ≠ 0)
    (hA : TripleStable a Z a0 a2 a1 q Sa.s₁ Sa.s₂ Sa.ε)
    (hB : TripleStable a Z (-a0) (-a2) (-a1) q Sb.s₁ Sb.s₂ Sb.ε)
    (hC : TripleStable a Z lf1 lf2 lf4 q Sc.s₁ Sc.s₂ Sc.ε)
    (hD : TripleStable a Z (-lf1) (-lf2) (-lf4) q Sd.s₁ Sd.s₂ Sd.ε)
    (hE : SingleStable a Z cn q εe) (hF : SingleStable a Z (-cn) q εf)
    (hσ : ∀ μ ∈ dl, (Pi.single μ (1 : L) : V8 → L) ∈ Z →
      (Pi.single (wp μ) (1 : L) : V8 → L) ∈ Z) :
    ∀ μ ∈ dl, (Pi.single μ (1 : L) : V8 → L) ∈ Z := by
  classical
  have hA' := CoreAux.triple_extract a hq hqL Z a0 a2 a1 Sa.hs₁ Sa.hs₂ Sa.hε hA
  have hB' := CoreAux.triple_extract a hq hqL Z (-a0) (-a2) (-a1) Sb.hs₁ Sb.hs₂ Sb.hε hB
  have hC' := CoreAux.triple_extract a hq hqL Z lf1 lf2 lf4 Sc.hs₁ Sc.hs₂ Sc.hε hC
  have hD' := CoreAux.triple_extract a hq hqL Z (-lf1) (-lf2) (-lf4) Sd.hs₁ Sd.hs₂ Sd.hε hD
  have hE' := CoreAux.single_extract a hq hqL Z cn hεe hE
  have hF' := CoreAux.single_extract a hq hqL Z (-cn) hεf hF
  have hst : ∀ γ ∈ CoreAux.gensL, ∀ z ∈ Z, CoreAux.eOp a γ z ∈ Z := by
    intro γ hγ z hz
    rcases CoreAux.gens_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [(hA' z hz).1, (hA' z hz).2.2, (hA' z hz).2.1, hE' z hz, (hC' z hz).1, (hC' z hz).2.1,
      (hC' z hz).2.2, (hB' z hz).1, (hB' z hz).2.2, (hB' z hz).2.1, hF' z hz, (hD' z hz).1,
      (hD' z hz).2.1, (hD' z hz).2.2]
  have hpos : ∀ γ ∈ CoreAux.pos7L, ∀ z ∈ Z, CoreAux.eOp a γ z ∈ Z :=
    fun γ hγ => hst γ (CoreAux.list_data.2.2.2.1 γ hγ).1
  have hdlZ : ∀ v ∈ Z, ∀ ν, v ν ≠ 0 → ν ∈ CoreAux.dlL := fun v hv ν hν =>
    CoreAux.mem_dl_iff.1 (by by_contra h; exact hν (hsupp v hv ν h))
  have hex0 : ∀ v : V8 → L, v ≠ 0 → ∃ ν, v ν ≠ 0 := fun v hv => by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨v, hvZ, hv0, hvtop⟩ :
      ∃ v ∈ Z, v ≠ 0 ∧ ∀ γ ∈ CoreAux.pos7L, CoreAux.eOp a γ v = 0 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ n : ℕ, ∃ v ∈ Z, v ≠ 0 ∧
        ∀ ν, v ν ≠ 0 → (n : ℤ) ≤ CFSG.Blueprint.Chevalley.height ν := by
      intro n
      induction n with
      | zero =>
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        exact ⟨v, hv, hv0, fun ν hν => by
          simpa using (CoreAux.list_data.2.2.2.2.1 ν (hdlZ v hv ν hν)).1⟩
      | succ n ih =>
        obtain ⟨v, hv, hv0, hvh⟩ := ih
        obtain ⟨γ, hγ, hγv⟩ := hcon v hv hv0
        refine ⟨CoreAux.eOp a γ v, hpos γ hγ v hv, hγv, fun ν hν => ?_⟩
        have h1 : v (ν - γ) ≠ 0 := by
          intro h
          apply hν
          rw [CoreAux.eOp_apply, h, mul_zero]
        have h2 := hvh _ h1
        have h3 := (CoreAux.list_data.2.2.2.1 γ hγ).2
        have h4 : CFSG.Blueprint.Chevalley.height (ν - γ) =
            CFSG.Blueprint.Chevalley.height ν - CFSG.Blueprint.Chevalley.height γ := by
          simp [CFSG.Blueprint.Chevalley.height, Finset.sum_sub_distrib]
        push_cast
        linarith
    obtain ⟨v, hv, hv0, hvh⟩ := key 30
    obtain ⟨ν, hν⟩ := hex0 v hv0
    have h1 := hvh ν hν
    have h2 := (CoreAux.list_data.2.2.2.2.1 ν (hdlZ v hv ν hν)).2
    push_cast at h1
    linarith
  have hvsupp : ∀ ν, v ν ≠ 0 → ν ∈ CoreAux.topsL := by
    intro ν hν
    have hdl := hdlZ v hvZ ν hν
    rcases CoreAux.top_data ν hdl with h | ⟨γ, hγ, hγν⟩
    · exact h
    · exfalso
      have hz := congrFun (hvtop γ hγ) (ν + γ)
      rw [CoreAux.eOp_apply, add_sub_cancel_right, Pi.zero_apply] at hz
      exact hν ((mul_eq_zero.1 hz).resolve_left (CoreAux.adm_cast_ne_zero ha
        (CoreAux.list_data.2.2.2.1 γ hγ).1 (CoreAux.list_data.2.2.1 ν hdl) hγν))
  obtain ⟨ν₀, hν₀⟩ := hex0 v hv0
  obtain ⟨⟨T, g, s, c⟩, he, hTe⟩ := CoreAux.low_data.2 ν₀ (hvsupp ν₀ hν₀)
  simp only at hTe
  subst hTe
  obtain ⟨hg, hT1, hgT, hTs, hoth, hc⟩ := CoreAux.low_data.1 _ he
  simp only at hg hT1 hgT hTs hoth hc
  have hEv : CoreAux.eOp a g v = Pi.single s ((a g T : L) * v T) := by
    funext μ
    rw [CoreAux.eOp_apply]
    by_cases hμ : μ - g = T
    · have hμs : μ = s := by rw [← hTs, ← hμ, sub_add_cancel]
      rw [hμ, hμs, Pi.single_eq_same]
    · have hμs : μ ≠ s := by
        rintro rfl
        exact hμ (by rw [← hTs, add_sub_cancel_right])
      rw [Pi.single_eq_of_ne hμs]
      by_cases hv : v (μ - g) = 0
      · rw [hv, mul_zero]
      · have htop := hvsupp _ hv
        have h0 := CoreAux.adm_zero ha hg
          (CoreAux.list_data.2.2.1 _ (CoreAux.list_data.2.2.2.2.2 _ htop)) (hoth (μ - g) htop hμ)
        rw [h0, Int.cast_zero, zero_mul]
  have hs : (Pi.single s (1 : L) : V8 → L) ∈ Z := by
    have hmem := hst g hg v hvZ
    rw [hEv] at hmem
    have hc0 : (a g T : L) * v T ≠ 0 :=
      mul_ne_zero (CoreAux.adm_cast_ne_zero ha hg hT1 hgT) hν₀
    have e : (Pi.single s (1 : L) : V8 → L) =
        ((a g T : L) * v T)⁻¹ • Pi.single s ((a g T : L) * v T) := by
      funext μ
      by_cases h : μ = s
      · subst h
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul,
          inv_mul_cancel₀ hc0]
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact Z.smul_mem _ hmem
  have hall := CoreAux.certOK_sound (fun μ => (Pi.single μ (1 : L) : V8 → L) ∈ Z)
    (fun μ γ hγ hμ hγμ hP => by
      have h1 := hst γ hγ _ hP
      rw [CoreAux.eOp_single, mul_one] at h1
      rcases CoreAux.adm_unit ha hγ hμ hγμ with h | h
      · rwa [h, Int.cast_one] at h1
      · have h2 := Z.neg_mem h1
        rwa [h, Int.cast_neg, Int.cast_one, Pi.single_neg, neg_neg] at h2)
    (fun μ hμ hP => hσ μ (CoreAux.mem_dl_iff.2 hμ) hP) hc hs
  intro μ hμ
  exact hall μ (CoreAux.mem_dl_iff.1 hμ)

end Ops

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
