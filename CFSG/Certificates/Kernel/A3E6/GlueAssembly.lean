module

public import CFSG.Certificates.Kernel.A3E6.GlueFrame

public section

namespace CFSG.StandardType.LieCore.A3E6K

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm iform_add_left iform_add_right
  iform_smul_left iform_smul_right iform_sub_left iform_sub_right iform_self_pos)
open Matrix

@[expose] def gπ : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.perm .E6

theorem graph_cartan (i j : Fin Tag.E6.rank) : Tag.E6.cartan (gπ i) (gπ j) = Tag.E6.cartan i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem graph_symm (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan (gπ i) (gπ j) = Tag.E6.symmetrizedCartan i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem graph_isRoot {γ : E6V} (h : IsRoot Tag.E6 γ) : IsRoot Tag.E6 (permLattice gπ γ) := by
  induction h with
  | basis j =>
    rw [permLattice_single]
    exact IsRoot.basis _
  | reflect i _ ih =>
    rw [permLattice_reflect graph_cartan]
    exact IsRoot.reflect _ ih

theorem graph_iform (x y : E6V) : iform (permLattice gπ x) (permLattice gπ y) = iform x y := by
  simp only [iform, permLattice, Function.comp_apply]
  refine Fintype.sum_equiv gπ.symm _ _ fun i => ?_
  refine Fintype.sum_equiv gπ.symm _ _ fun j => ?_
  have h := graph_symm (gπ.symm i) (gπ.symm j)
  simp only [Equiv.apply_symm_apply] at h
  rw [h]

@[expose] def rrT : E6V := ![2, 2, 3, 4, 3, 2]

theorem graph_rr : permLattice gπ rr = -rr + (3 : ℤ) • rrT := by
  funext j
  fin_cases j <;> decide


theorem rr_weyl (x : WeylGroup Tag.E6) : ∀ i, (3 : ℤ) ∣ (x • rr) i - rr i := by
  induction x using (coxeterSystem Tag.E6).simple_induction_left with
  | one => intro i; simp
  | mul_simple_left x j ih =>
    intro i
    rw [mul_smul, simple_smul]
    have h0 : (3 : ℤ) ∣ ∑ l, Tag.E6.cartan j l * rr l := by
      fin_cases j <;> decide
    have h1 : (3 : ℤ) ∣ ∑ l, Tag.E6.cartan j l * ((x • rr) l - rr l) :=
      Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (ih l) _
    have hc : (3 : ℤ) ∣ ∑ l, Tag.E6.cartan j l * (x • rr) l := by
      have e : ∑ l, Tag.E6.cartan j l * (x • rr) l = ∑ l, Tag.E6.cartan j l * rr l +
          ∑ l, Tag.E6.cartan j l * ((x • rr) l - rr l) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact dvd_add h0 h1
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : (3 : ℤ) ∣ (∑ l, Tag.E6.cartan j l * (x • rr) l) * (Pi.single j 1 : E6V) i :=
      dvd_mul_of_dvd_left hc _
    have e : (x • rr) i - (∑ l, Tag.E6.cartan j l * (x • rr) l) * (Pi.single j 1 : E6V) i -
        rr i = ((x • rr) i - rr i) - (∑ l, Tag.E6.cartan j l * (x • rr) l) *
          (Pi.single j 1 : E6V) i := by ring
    rw [e]
    exact dvd_sub (ih i) h2

@[expose] noncomputable def toLinW (x : WeylGroup Tag.E6) : E6V →ₗ[ℤ] E6V :=
  (DistribSMul.toAddMonoidHom E6V x).toIntLinearMap

theorem toLinW_apply (x : WeylGroup Tag.E6) (u : E6V) : toLinW x u = x • u := rfl

@[expose] def graphL : E6V →ₗ[ℤ] E6V := LinearMap.funLeft ℤ ℤ gπ.symm

theorem graphL_apply (u : E6V) : graphL u = permLattice gπ u := rfl

theorem weyl_zsmul (x : WeylGroup Tag.E6) (k : ℤ) (u : E6V) : x • (k • u) = k • (x • u) :=
  map_zsmul (DistribSMul.toAddMonoidHom E6V x) k u

theorem pair_closure {S : Set E6V} {c : Fin Tag.E6.rank → ZMod 3}
    (hS : ∀ γ ∈ S, IsRoot Tag.E6 γ ∧ ggLiePair γ c = 0) {y : WeylGroup Tag.E6}
    (hy : y ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ S, s = rootReflection γ}) :
    ∀ u, ggLiePair (y • u) c = ggLiePair u c := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    intro u
    rw [rootReflection_smul_e6 (hS γ hγ).1, pair_sub, pair_zsmul, (hS γ hγ).2]
    ring
  | one => intro u; rw [one_smul]
  | mul x y _ _ hx hy => intro u; rw [mul_smul, hx, hy]
  | inv x _ hx => intro u; rw [← hx (x⁻¹ • u), smul_inv_smul]

theorem sum_single (u : E6V) : u = ∑ k, u k • (Pi.single k 1 : E6V) := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem pair_lang {w : WeylGroup Tag.E6} {c : Fin Tag.E6.rank → ZMod 3}
    (hl : ∀ γ : E6V, IsRoot Tag.E6 γ →
      ggLiePair (w • permLattice gπ γ) c = 2 * ggLiePair γ c) (u : E6V) :
    ggLiePair (w • permLattice gπ u) c = 2 * ggLiePair u c := by
  set M := (pairL c).comp ((toLinW w).comp graphL) with hMdef
  have hM : ∀ v, M v = ggLiePair (w • permLattice gπ v) c := fun v => by
    rw [hMdef, LinearMap.comp_apply, LinearMap.comp_apply, graphL_apply, toLinW_apply]
    rfl
  have hP : ∀ v, pairL c v = ggLiePair v c := fun v => rfl
  rw [← hM, ← hP, sum_single u, map_sum, map_sum]
  simp only [map_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hM, hP, hl _ (IsRoot.basis k), zsmul_eq_mul, zsmul_eq_mul]
  ring

theorem pqr_mem_perp {f : Frame} (hf : FrameFacts f) :
    f.p ∈ f.perp ∧ f.q ∈ f.perp ∧ f.r ∈ f.perp := by
  have h0 := perp_of_frame hf (b := f.b₀) (Or.inl rfl)
  have h1 := perp_of_frame hf (b := f.b₁) (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨⟨hf.hp, ?_, ?_⟩, ⟨hf.hq, ?_, ?_⟩, ⟨hf.hr, ?_, ?_⟩⟩ <;> rw [iform_comm]
  exacts [h0.1, h1.1, h0.2.1, h1.2.1, h0.2.2, h1.2.2]

theorem twisted_core {Fs : Set Frame} (hcov : Cover Fs) (hfr : ∀ f ∈ Fs, FrameFacts f)
    (htw : ∀ f ∈ Fs, TwFacts f) (w : WeylGroup Tag.E6) (c₁ c₂ : Fin Tag.E6.rank → ZMod 3)
    (hl₁ : ∀ γ : E6V, IsRoot Tag.E6 γ →
      ggLiePair (w • permLattice gπ γ) c₁ = 2 * ggLiePair γ c₁)
    (hl₂ : ∀ γ : E6V, IsRoot Tag.E6 γ →
      ggLiePair (w • permLattice gπ γ) c₂ = 2 * ggLiePair γ c₂)
    (m : E6V) (hm : m ∈ a3Ker Tag.E6 c₁ c₂) (hn : (a3Comp Tag.E6 c₁ c₂ m).ncard = 12)
    (w' : WeylGroup Tag.E6)
    (hw'cl : w' ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
      ∃ γ ∈ a3Comp Tag.E6 c₁ c₂ m, s = rootReflection γ})
    (hw'eq : ∀ γ ∈ a3Comp Tag.E6 c₁ c₂ m, w • permLattice gπ γ = w' • γ) : False := by
  obtain ⟨f, hf, hCP, -, -⟩ := comp_eq_frame hcov hfr hm hn
  have hff := hfr f hf
  obtain ⟨hpP, hqP, hrP⟩ := pqr_mem_perp hff
  have hpC : f.p ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hpP
  have hqC : f.q ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hqP
  have hrC : f.r ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hrP
  set L := (toLinW (w'⁻¹ * w)).comp graphL with hLdef
  have hLu : ∀ u, L u = w'⁻¹ • (w • permLattice gπ u) := fun u => by
    rw [hLdef, LinearMap.comp_apply, graphL_apply, toLinW_apply, mul_smul]
  have hfixC : ∀ γ ∈ a3Comp Tag.E6 c₁ c₂ m, L γ = γ := by
    intro γ hγ
    rw [hLu, hw'eq γ hγ, inv_smul_smul]
  have hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (L γ) := by
    intro γ hγ
    rw [hLu]
    exact IsRoot.smul (IsRoot.smul (graph_isRoot hγ) w) w'⁻¹
  have hform : ∀ x y, iform (L x) (L y) = iform x y := by
    intro x y
    rw [hLu, hLu, iform_smul, iform_smul, graph_iform]
  obtain ⟨sw, e₀, e₁, e₂, hs⟩ := images_of_fix hff L hroot hform
    ⟨hfixC _ hpC, hfixC _ hqC, hfixC _ hrC⟩
  set z := LinearMap.toMatrix' L
  have hz : ∀ u, z *ᵥ u = L u := fun u => LinearMap.toMatrix'_mulVec L u
  have hfixes : Fixes f z := by
    simp only [Fixes, hz]
    exact ⟨hfixC _ hpC, hfixC _ hqC, hfixC _ hrC⟩
  have hcol : ColImages f z sw e₀ e₁ e₂ := by
    simp only [ColImages, hz]
    exact hs
  have hrr : ∀ i, (3 : ℤ) ∣ (z *ᵥ rr) i + rr i := by
    intro i
    obtain ⟨d, hd⟩ := rr_weyl (w'⁻¹ * w) i
    rw [hz, hLu, ← mul_smul, graph_rr, smul_add, smul_neg, weyl_zsmul]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    exact ⟨((w'⁻¹ * w) • rrT) i - d, by linarith⟩
  obtain ⟨g, hg, hgP, hgadj, hgc⟩ := htw f hf z sw e₀ e₁ e₂ hfixes hcol hrr
  have htwo : ∀ a : ZMod 3, 2 * a = -a := by decide
  have hneg : ∀ c : Fin Tag.E6.rank → ZMod 3, (∀ γ : E6V, IsRoot Tag.E6 γ →
      ggLiePair (w • permLattice gπ γ) c = 2 * ggLiePair γ c) →
      (∀ δ ∈ a3Comp Tag.E6 c₁ c₂ m, ggLiePair δ c = 0) →
      ∀ γ, ggLiePair (z *ᵥ γ) c = -ggLiePair γ c := by
    intro c hl hCc γ
    rw [hz, hLu, pair_closure (S := a3Comp Tag.E6 c₁ c₂ m)
      (fun δ hδ => ⟨hδ.1.1, hCc δ hδ⟩) (Subgroup.inv_mem _ hw'cl), pair_lang hl, htwo]
  have g₁ := hgc c₁ (hneg c₁ hl₁ fun δ hδ => hδ.1.2.1) hpC.1.2.1 hqC.1.2.1 hrC.1.2.1
  have g₂ := hgc c₂ (hneg c₂ hl₂ fun δ hδ => hδ.1.2.2) hpC.1.2.2 hqC.1.2.2 hrC.1.2.2
  have hgC : g ∈ a3Comp Tag.E6 c₁ c₂ m := by
    rcases hgadj with h | h | h
    · exact mem_comp_of_adj hpC hg g₁ g₂ h
    · exact mem_comp_of_adj hqC hg g₁ g₂ h
    · exact mem_comp_of_adj hrC hg g₁ g₂ h
  rw [hCP] at hgC
  exact hgP ⟨hgC.2.1, hgC.2.2⟩

theorem a3SpecTwE6_of_frames {Fs : Set Frame} (hcov : Cover Fs) (hfr : ∀ f ∈ Fs, FrameFacts f)
    (htw : ∀ f ∈ Fs, TwFacts f) : A3SpecTwE6 := by
  intro w c₁ c₂ _ hl₁ hl₂ m hm hn _ hin
  obtain ⟨w', hcl, heq⟩ := hin
  exact twisted_core hcov hfr htw w c₁ c₂ hl₁ hl₂ m hm hn w' hcl heq

theorem weyl_eq_of_cols {f : Frame} (hf : FrameFacts f) {x y : WeylGroup Tag.E6}
    (h : ∀ j : Fin 6, x • f.col j = y • f.col j) : x = y := by
  refine eq_of_smul_eq_smul (α := E6V) fun u => ?_
  have h8 : ∀ g : WeylGroup Tag.E6,
      (8 : ℤ) • (g • u) = ∑ j : Fin 6, (f.A *ᵥ u) j • g • f.col j := by
    intro g
    rw [← weyl_zsmul, ← Frame.B_mulVec_A f hf u, Frame.mulVec_eq_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => weyl_zsmul g _ _
  have h88 : (8 : ℤ) • (x • u) = (8 : ℤ) • (y • u) := by
    rw [h8 x, h8 y]
    exact Finset.sum_congr rfl fun j _ => by rw [h j]
  exact smul_right_injective E6V (by norm_num : (8 : ℤ) ≠ 0) h88

theorem untwisted_core {Fs : Set Frame} (hcov : Cover Fs) (hfr : ∀ f ∈ Fs, FrameFacts f)
    (hun : ∀ f ∈ Fs, UnFacts f) (c₁ c₂ : Fin Tag.E6.rank → ZMod 3) (m : E6V)
    (hm : m ∈ a3Ker Tag.E6 c₁ c₂) (hn : (a3Comp Tag.E6 c₁ c₂ m).ncard = 12) :
    ∃ β₀ β₁ : E6V,
        IsRoot Tag.E6 β₀ ∧ IsRoot Tag.E6 β₁ ∧ iform β₀ β₁ = 0 ∧
        (∀ γ, IsRoot Tag.E6 γ →
          ((∀ ψ ∈ a3Comp Tag.E6 c₁ c₂ m, iform ψ γ = 0) ↔
            (γ = β₀ ∨ γ = -β₀ ∨ γ = β₁ ∨ γ = -β₁))) ∧
        (∀ γ, IsRoot Tag.E6 γ →
          ((iform γ β₀ = 0 ∧ iform γ β₁ = 0) ↔ γ ∈ a3Comp Tag.E6 c₁ c₂ m)) ∧
        (∃ ψ₀ ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ ψ₁ ∈ a3Comp Tag.E6 c₁ c₂ m,
          iform ψ₀ ψ₁ = 0) ∧
        (∀ ψ ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ x ∈ a3Comp Tag.E6 c₁ c₂ m,
          ∃ y ∈ a3Comp Tag.E6 c₁ c₂ m, ψ = x + y) ∧
        (∀ x : WeylGroup Tag.E6, (∀ γ ∈ a3Comp Tag.E6 c₁ c₂ m, x • γ = γ) →
          x = 1 ∨ x = rootReflection β₀ ∨ x = rootReflection β₁ ∨
            x = rootReflection β₀ * rootReflection β₁) := by
  obtain ⟨f, hf, hCP, horth, hsum⟩ := comp_eq_frame hcov hfr hm hn
  have hff := hfr f hf
  obtain ⟨hpP, hqP, hrP⟩ := pqr_mem_perp hff
  have hpC : f.p ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hpP
  have hqC : f.q ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hqP
  have hrC : f.r ∈ a3Comp Tag.E6 c₁ c₂ m := by rw [hCP]; exact hrP
  refine ⟨f.b₀, f.b₁, hff.hb₀, hff.hb₁, hff.hbb, ?_, ?_, horth, hsum, ?_⟩
  · intro γ hγ
    constructor
    · intro h
      refine (hff.perp_iff γ hγ).mp ⟨?_, ?_, ?_⟩ <;> rw [iform_comm]
      exacts [h _ hpC, h _ hqC, h _ hrC]
    · intro h ψ hψ
      rw [hCP] at hψ
      obtain ⟨-, h0, h1⟩ := hψ
      rcases h with rfl | rfl | rfl | rfl
      · exact h0
      · rw [iform_neg_right, h0, neg_zero]
      · exact h1
      · rw [iform_neg_right, h1, neg_zero]
  · intro γ hγ
    rw [hCP]
    exact ⟨fun h => ⟨hγ, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  · intro x hx
    obtain ⟨sw, e₀, e₁, e₂, hs⟩ := images_of_fix hff (toLinW x)
      (fun γ h => by rw [toLinW_apply]; exact IsRoot.smul h x)
      (fun a b => by rw [toLinW_apply, toLinW_apply]; exact iform_smul x a b)
      ⟨by rw [toLinW_apply]; exact hx _ hpC, by rw [toLinW_apply]; exact hx _ hqC,
        by rw [toLinW_apply]; exact hx _ hrC⟩
    simp only [toLinW_apply] at hs
    set z := LinearMap.toMatrix' (toLinW x)
    have hz : ∀ u, z *ᵥ u = x • u := fun u => by
      rw [LinearMap.toMatrix'_mulVec, toLinW_apply]
    have hfixes : Fixes f z := by
      simp only [Fixes, hz]
      exact ⟨hx _ hpC, hx _ hqC, hx _ hrC⟩
    have hcol : ColImages f z sw e₀ e₁ e₂ := by
      simp only [ColImages, hz]
      exact hs
    have hrr : ∀ i, (3 : ℤ) ∣ (z *ᵥ rr) i - rr i := by
      intro i
      rw [hz]
      exact rr_weyl x i
    obtain ⟨rfl, rfl⟩ := hun f hf z sw e₀ e₁ e₂ hfixes hcol hrr
    obtain ⟨he₀, he₁, -, hx0, hx1, hxv⟩ := hs
    simp only [Bool.false_eq_true, ↓reduceIte] at hx0 hx1
    rw [one_smul] at hxv
    have hb0 := perp_of_frame hff (b := f.b₀) (Or.inl rfl)
    have hb1 := perp_of_frame hff (b := f.b₁) (Or.inr (Or.inr (Or.inl rfl)))
    have hb10 : iform f.b₁ f.b₀ = 0 := by rw [iform_comm]; exact hff.hbb
    have hb0v : iform f.b₀ f.v = 0 := by rw [iform_comm]; exact hff.vb₀
    have hb1v : iform f.b₁ f.v = 0 := by rw [iform_comm]; exact hff.vb₁
    have s₀ := fun {u : E6V} (h : iform f.b₀ u = 0) =>
      rootReflection_smul_of_iform_eq_zero hff.hb₀ h
    have s₁ := fun {u : E6V} (h : iform f.b₁ u = 0) =>
      rootReflection_smul_of_iform_eq_zero hff.hb₁ h
    have s₀₀ := rootReflection_smul_self hff.hb₀
    have s₁₁ := rootReflection_smul_self hff.hb₁
    rcases he₀ with rfl | rfl <;> rcases he₁ with rfl | rfl
    · refine Or.inl (weyl_eq_of_cols hff fun j => ?_)
      fin_cases j <;> simp [Frame.col, hx _ hpC, hx _ hqC, hx _ hrC, hx0, hx1, hxv]
    · refine Or.inr (Or.inr (Or.inl (weyl_eq_of_cols hff fun j => ?_)))
      fin_cases j <;> simp [Frame.col, hx _ hpC, hx _ hqC, hx _ hrC, hx0, hx1, hxv,
        s₁ hb1.1, s₁ hb1.2.1, s₁ hb1.2.2, s₁ hb10, s₁ hb1v, s₁₁]
    · refine Or.inr (Or.inl (weyl_eq_of_cols hff fun j => ?_))
      fin_cases j <;> simp [Frame.col, hx _ hpC, hx _ hqC, hx _ hrC, hx0, hx1, hxv,
        s₀ hb0.1, s₀ hb0.2.1, s₀ hb0.2.2, s₀ hff.hbb, s₀ hb0v, s₀₀]
    · refine Or.inr (Or.inr (Or.inr (weyl_eq_of_cols hff fun j => ?_)))
      fin_cases j <;> simp [Frame.col, hx _ hpC, hx _ hqC, hx _ hrC, hx0, hx1, hxv, mul_smul,
        s₀ hb0.1, s₀ hb0.2.1, s₀ hb0.2.2, s₀ hff.hbb, s₀ hb0v, s₀₀,
        s₁ hb1.1, s₁ hb1.2.1, s₁ hb1.2.2, s₁ hb10, s₁ hb1v, s₁₁]

theorem a3SpecE6Struct_of_frames {Fs : Set Frame} (hcov : Cover Fs)
    (hfr : ∀ f ∈ Fs, FrameFacts f) (hun : ∀ f ∈ Fs, UnFacts f) : A3SpecE6Struct := by
  intro c₁ c₂ _ m hm hn
  exact untwisted_core hcov hfr hun c₁ c₂ m hm hn

end CFSG.StandardType.LieCore.A3E6K
