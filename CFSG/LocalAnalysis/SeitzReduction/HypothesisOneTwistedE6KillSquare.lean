module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

section ModN

variable {G : Type*} [Group G]

noncomputable def twKillQ (V N : Subgroup G) [(N.subgroupOf V).Normal] (g : G) :
    V ⧸ N.subgroupOf V := by
  classical
  exact if h : g ∈ V then ((⟨g, h⟩ : V) : V ⧸ N.subgroupOf V) else 1

variable {V N : Subgroup G} [(N.subgroupOf V).Normal]

theorem twKillQ_of_mem {g : G} (hg : g ∈ V) :
    twKillQ V N g = ((⟨g, hg⟩ : V) : V ⧸ N.subgroupOf V) := by
  unfold twKillQ
  split_ifs
  rfl

theorem twKillQ_mul {g h : G} (hg : g ∈ V) (hh : h ∈ V) :
    twKillQ V N (g * h) = twKillQ V N g * twKillQ V N h := by
  rw [twKillQ_of_mem (mul_mem hg hh), twKillQ_of_mem hg, twKillQ_of_mem hh, ← QuotientGroup.mk_mul]
  rfl

theorem twKillQ_inv {g : G} (hg : g ∈ V) : twKillQ V N g⁻¹ = (twKillQ V N g)⁻¹ := by
  rw [twKillQ_of_mem (inv_mem hg), twKillQ_of_mem hg, ← QuotientGroup.mk_inv]
  rfl

theorem twKillQ_one : twKillQ V N (1 : G) = 1 := by
  rw [twKillQ_of_mem (one_mem V)]
  rfl

theorem twKillQ_eq_one_iff {g : G} (hg : g ∈ V) : twKillQ V N g = 1 ↔ g ∈ N := by
  rw [twKillQ_of_mem hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem twKillQ_eq_iff {g h : G} (hg : g ∈ V) (hh : h ∈ V) :
    twKillQ V N g = twKillQ V N h ↔ g⁻¹ * h ∈ N := by
  rw [twKillQ_of_mem hg, twKillQ_of_mem hh, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem twKillQ_commute {g h : G} (hg : g ∈ V) (hh : h ∈ V) (hc : ⁅g, h⁆ ∈ N) :
    Commute (twKillQ V N g) (twKillQ V N h) := by
  have hm : ⁅g, h⁆ ∈ V := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have h1 := (twKillQ_eq_one_iff hm).2 hc
  rw [commutatorElement_def, twKillQ_mul (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    twKillQ_mul (mul_mem hg hh) (inv_mem hg), twKillQ_mul hg hh, twKillQ_inv hg, twKillQ_inv hh] at h1
  change twKillQ V N g * twKillQ V N h = twKillQ V N h * twKillQ V N g
  calc twKillQ V N g * twKillQ V N h
      = twKillQ V N g * twKillQ V N h * (twKillQ V N g)⁻¹ * (twKillQ V N h)⁻¹ * (twKillQ V N h * twKillQ V N g) := by
        group
    _ = twKillQ V N h * twKillQ V N g := by rw [h1, one_mul]

theorem twKillQ_mem_of_commute {g h : G} (hg : g ∈ V) (hh : h ∈ V)
    (hc : Commute (twKillQ V N g) (twKillQ V N h)) : ⁅g, h⁆ ∈ N := by
  have hm : ⁅g, h⁆ ∈ V := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  rw [← twKillQ_eq_one_iff hm, commutatorElement_def,
    twKillQ_mul (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    twKillQ_mul (mul_mem hg hh) (inv_mem hg), twKillQ_mul hg hh, twKillQ_inv hg, twKillQ_inv hh, hc.eq]
  group

theorem twKill_conj_mul {a x y : G} (haa : a * a = 1) : a * (x * y) * a = (a * x * a) * (a * y * a) := by
  calc a * (x * y) * a = a * x * (a * a) * y * a := by rw [haa]; group
    _ = (a * x * a) * (a * y * a) := by group

theorem twKill_comm4 {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : G}
    (h01 : Commute b₀ a₁) (h02 : Commute b₀ a₂) (h03 : Commute b₀ a₃)
    (h12 : Commute b₁ a₂) (h13 : Commute b₁ a₃) (h23 : Commute b₂ a₃) :
    a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃) = a₀ * a₁ * a₂ * a₃ * (b₀ * b₁ * b₂ * b₃) := by
  have e1 : b₀ * (a₁ * a₂ * a₃) = a₁ * a₂ * a₃ * b₀ := ((h01.mul_right h02).mul_right h03).eq
  have e2 : b₁ * (a₂ * a₃) = a₂ * a₃ * b₁ := (h12.mul_right h13).eq
  have e3 : b₂ * a₃ = a₃ * b₂ := h23.eq
  calc a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃)
      = a₀ * b₀ * (a₁ * (b₁ * (a₂ * (b₂ * a₃) * b₃))) := by group
    _ = a₀ * b₀ * (a₁ * (b₁ * (a₂ * (a₃ * b₂) * b₃))) := by rw [e3]
    _ = a₀ * b₀ * (a₁ * ((b₁ * (a₂ * a₃)) * b₂ * b₃)) := by group
    _ = a₀ * b₀ * (a₁ * ((a₂ * a₃ * b₁) * b₂ * b₃)) := by rw [e2]
    _ = a₀ * (b₀ * (a₁ * a₂ * a₃)) * (b₁ * b₂ * b₃) := by group
    _ = a₀ * (a₁ * a₂ * a₃ * b₀) * (b₁ * b₂ * b₃) := by rw [e1]
    _ = _ := by group

end ModN

section LayerAlgebra

variable {Q : Type*} [Group Q] {K : Type*} [Field K]

@[expose] def twKillP (X : Fin 4 → K → Q) (a₀ a₁ a₂ a₃ : K) : Q := X 0 a₀ * X 1 a₁ * X 2 a₂ * X 3 a₃

variable {X : Fin 4 → K → Q}

theorem twKillP_mul (hadd : ∀ k a b, X k a * X k b = X k (a + b))
    (hc : ∀ k l a b, Commute (X k a) (X l b)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : K) :
    twKillP X a₀ a₁ a₂ a₃ * twKillP X b₀ b₁ b₂ b₃ =
      twKillP X (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) := by
  unfold twKillP
  rw [← hadd 0, ← hadd 1, ← hadd 2, ← hadd 3,
    twKill_comm4 (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _)]

theorem twKillP_zero (hadd : ∀ k a b, X k a * X k b = X k (a + b)) (k : Fin 4) : X k 0 = 1 := by
  have h := hadd k 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h

theorem twKillP_zero_zero (hadd : ∀ k a b, X k a * X k b = X k (a + b)) : twKillP X 0 0 0 0 = 1 := by
  simp only [twKillP, twKillP_zero hadd, mul_one]

theorem twKillP_commute (hadd : ∀ k a b, X k a * X k b = X k (a + b))
    (hc : ∀ k l a b, Commute (X k a) (X l b)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : K) :
    Commute (twKillP X a₀ a₁ a₂ a₃) (twKillP X b₀ b₁ b₂ b₃) := by
  change _ * _ = _ * _
  rw [twKillP_mul hadd hc, twKillP_mul hadd hc, add_comm a₀, add_comm a₁, add_comm a₂, add_comm a₃]

theorem twKillP_commute_of {y : Q} (hy : ∀ k a, Commute y (X k a)) (a₀ a₁ a₂ a₃ : K) :
    Commute y (twKillP X a₀ a₁ a₂ a₃) := by
  unfold twKillP
  exact (((hy 0 a₀).mul_right (hy 1 a₁)).mul_right (hy 2 a₂)).mul_right (hy 3 a₃)

theorem twKillP_conj (hadd : ∀ k a b, X k a * X k b = X k (a + b))
    (hc : ∀ k l a b, Commute (X k a) (X l b)) {a : Q} (haa : a * a = 1) {c c' : K}
    (h0 : ∀ g, a * X 0 g * a = twKillP X g (c * g) (c' * g) (c * c' * g))
    (h1 : ∀ g, a * X 1 g * a = twKillP X 0 g 0 (c' * g))
    (h2 : ∀ g, a * X 2 g * a = twKillP X 0 0 g (c * g))
    (h3 : ∀ g, a * X 3 g * a = X 3 g) (d₀ d₁ d₂ d₃ : K) :
    a * twKillP X d₀ d₁ d₂ d₃ * a =
      twKillP X d₀ (d₁ + c * d₀) (d₂ + c' * d₀) (d₃ + c * c' * d₀ + c' * d₁ + c * d₂) := by
  have e : a * twKillP X d₀ d₁ d₂ d₃ * a = (a * X 0 d₀ * a) * (a * X 1 d₁ * a) *
      (a * X 2 d₂ * a) * (a * X 3 d₃ * a) := by
    unfold twKillP
    calc a * (X 0 d₀ * X 1 d₁ * X 2 d₂ * X 3 d₃) * a
        = a * X 0 d₀ * (a * a) * X 1 d₁ * (a * a) * X 2 d₂ * (a * a) * X 3 d₃ * a := by
          rw [haa]; group
      _ = _ := by group
  have h3' : X 3 d₃ = twKillP X 0 0 0 d₃ := by
    simp only [twKillP, twKillP_zero hadd, one_mul]
  rw [e, h0, h1, h2, h3, h3', twKillP_mul hadd hc, twKillP_mul hadd hc, twKillP_mul hadd hc]
  congr 1 <;> ring

end LayerAlgebra

section Square

variable {K : Type} [Field K]

set_option maxHeartbeats 400000 in
theorem twKill_square_step [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) {δt : K}
    (hδt : δt + σ δt = 1) {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {c : K}
    (hc : c ≠ 0) : TwKillSquareStep σ J i c := by
  intro R δ z n hR hRρ hmin hne hδa hδa' hz hFz hn hFn hcoc
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set c' := σ c with hc'def
  have hc' : c' ≠ 0 := fun h => hc (by rw [← hσσ c, ← hc'def, h, map_zero])
  set α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i 1 with hα
  set α' : Fin TwistTag.E6.tag.rank → ℤ := Pi.single (TwistTag.E6.perm i) 1 with hα'
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδJ := hδΨ.1
  have hδr : IsRoot TwistTag.E6.tag δ := hδJ.2.1
  have hδp : 0 < height δ := hδJ.2.2
  have hs1 := hmin.not_isRoot_sub hR (Or.inl rfl)
  have hs2 := hmin.not_isRoot_sub hR (Or.inr rfl)
  obtain ⟨hρδ, hθr, hn1, hn2, hn3, hn4⟩ := twKill_square_facts hne hδr hδp hs1 hs2 hδa hδa'
  have hαJ : α ∈ parabolicPosRoots TwistTag.E6.tag J := twKill_single_mem hi
  have hα'J : α' ∈ parabolicPosRoots TwistTag.E6.tag J := twKill_single_mem (hJ i hi)
  have hidR : ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J, ∀ x ∈ R,
      IsRoot TwistTag.E6.tag (x + γ) → x + γ ∈ R := fun γ hγ x hx hr => by
    have h := hR.ideal γ hγ x hx 1 1 le_rfl le_rfl
      (by rw [one_smul, one_smul, add_comm]; exact hr)
    rwa [one_smul, one_smul, add_comm] at h
  have hβ₁R : δ + α ∈ R := hidR α hαJ δ hδR hδa
  have hβ₂R : δ + α' ∈ R := hidR α' hα'J δ hδR hδa'
  have hθR : δ + α + α' ∈ R := hidR α' hα'J _ hβ₁R hθr
  have hRpos : ∀ β ∈ R, IsRoot TwistTag.E6.tag β ∧ 0 < height β := fun β hβ =>
    (hR.subset hβ).1.2
  have hRJ : R ⊆ parabolicPosRoots TwistTag.E6.tag J := fun x hx => (hR.subset hx).1
  have hdα : twKillDeg i α = 0 := twKillDeg_single (Or.inl rfl)
  have hdα' : twKillDeg i α' = 0 := twKillDeg_single (Or.inr rfl)
  have hlα : twKillLev i α = 1 := twKillLev_single (Or.inl rfl)
  have hlα' : twKillLev i α' = 1 := twKillLev_single (Or.inr rfl)
  have hdβ₁ : twKillDeg i (δ + α) = twKillDeg i δ := by rw [twKillDeg_add, hdα, add_zero]
  have hdβ₂ : twKillDeg i (δ + α') = twKillDeg i δ := by rw [twKillDeg_add, hdα', add_zero]
  have hdθ : twKillDeg i (δ + α + α') = twKillDeg i δ := by
    rw [twKillDeg_add, twKillDeg_add, hdα, hdα', add_zero, add_zero]
  have hm1 : 1 ≤ twKillDeg i δ := by
    obtain ⟨-, hne'⟩ := hδΨ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne'
    exact one_le_twKillDeg hδr hδp hne'.1 hne'.2
  have hneq : ∀ v w : Fin TwistTag.E6.tag.rank → ℤ, twKillLev i v ≠ twKillLev i w → v ≠ w :=
    fun v w h e => h (by rw [e])
  have hlβ₁ : twKillLev i (δ + α) = twKillLev i δ + 1 := by rw [twKillLev_add, hlα]
  have hlβ₂ : twKillLev i (δ + α') = twKillLev i δ + 1 := by rw [twKillLev_add, hlα']
  have hlθ : twKillLev i (δ + α + α') = twKillLev i δ + 2 := by
    rw [twKillLev_add, twKillLev_add, hlα, hlα']
    ring
  have hβ₁β₂ : δ + α ≠ δ + α' := fun e => by
    have := congrFun e i
    simp only [Pi.add_apply, hα, hα', Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hne)] at this
    omega
  have d01 : δ ≠ δ + α := hneq _ _ (by rw [hlβ₁]; omega)
  have d02 : δ ≠ δ + α' := hneq _ _ (by rw [hlβ₂]; omega)
  have d03 : δ ≠ δ + α + α' := hneq _ _ (by rw [hlθ]; omega)
  have d13 : δ + α ≠ δ + α + α' := hneq _ _ (by rw [hlβ₁, hlθ]; omega)
  have d23 : δ + α' ≠ δ + α + α' := hneq _ _ (by rw [hlβ₂, hlθ]; omega)
  have hRs := twKillAdm_sdiff_square hR hmin (twKill_hstr J i) (twKill_hstr J (TwistTag.E6.perm i))
    hn1 hn2 hn3 hn4
  set Rs := R \ {δ, δ + α, δ + α', δ + α + α'} with hRsdef
  have hρα : permLattice TwistTag.E6.perm α = α' := twKill_perm_single i
  have hρα' : permLattice TwistTag.E6.perm α' = α := twKill_perm_single_perm i
  have hρβ₁ : permLattice TwistTag.E6.perm (δ + α) = δ + α' := by
    rw [show permLattice TwistTag.E6.perm (δ + α) =
      permLattice TwistTag.E6.perm δ + permLattice TwistTag.E6.perm α from rfl, hρδ, hρα]
  have hρβ₂ : permLattice TwistTag.E6.perm (δ + α') = δ + α := by
    rw [show permLattice TwistTag.E6.perm (δ + α') =
      permLattice TwistTag.E6.perm δ + permLattice TwistTag.E6.perm α' from rfl, hρδ, hρα']
  have hρθ : permLattice TwistTag.E6.perm (δ + α + α') = δ + α + α' := by
    rw [show permLattice TwistTag.E6.perm (δ + α + α') =
      permLattice TwistTag.E6.perm (δ + α) + permLattice TwistTag.E6.perm α' from rfl, hρβ₁,
      hρα']
    abel
  have hRsρ : ∀ β ∈ Rs, permLattice TwistTag.E6.perm β ∈ Rs := fun β hβ =>
    ⟨hRρ β hβ.1, fun h => hβ.2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h | h | h
      · left
        rw [← permLattice_twistedE6_perm_perm β, h, hρδ]
      · right; right; left
        rw [← permLattice_twistedE6_perm_perm β, h, hρβ₁]
      · right; left
        rw [← permLattice_twistedE6_perm_perm β, h, hρβ₂]
      · right; right; right
        rw [← permLattice_twistedE6_perm_perm β, h, hρθ])⟩
  have hhigh : ∀ x ∈ R, twKillDeg i δ < twKillDeg i x → x ∈ Rs := by
    intro x hx hlt
    refine ⟨hx, fun h => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact lt_irrefl _ hlt
    · rw [hdβ₁] at hlt; exact lt_irrefl _ hlt
    · rw [hdβ₂] at hlt; exact lt_irrefl _ hlt
    · rw [hdθ] at hlt; exact lt_irrefl _ hlt
  have hRsJ : Rs ⊆ parabolicPosRoots TwistTag.E6.tag J := fun x hx => (hRs.subset hx).1
  have hRspos : ∀ β ∈ Rs, IsRoot TwistTag.E6.tag β ∧ 0 < height β := fun β hβ =>
    (hRs.subset hβ).1.2
  have hRsclosed : ∀ β ∈ Rs, ∀ γ ∈ Rs, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • β + b • γ) → a • β + b • γ ∈ Rs :=
    fun β hβ γ hγ a b ha hb hr => hRs.ideal β (hRs.subset hβ).1 γ hγ a b ha hb hr
  have hnorm : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K Rs, v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K Rs :=
    fun v hv m hm => classKill_conj_mem hRsJ hRs.ideal hv hm
  have hNV : rootSpan TwistTag.E6.tag K Rs ≤
      rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_rootSpan_mono hRsJ
  have hdegpos : ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J \ {α, α'}, 1 ≤ twKillDeg i γ := by
    intro γ hγ
    obtain ⟨hγJ, hγne⟩ := hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγne
    exact one_le_twKillDeg hγJ.2.1 hγJ.2.2 hγne.1 hγne.2
  have hβm : ∀ β ∈ R, twKillDeg i β = twKillDeg i δ → ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • γ + b • β) → a • γ + b • β ∈ Rs := by
    intro β hβ hβd γ hγ a b ha hb hr
    refine hhigh _ (hR.ideal γ (hRJ hγ) β hβ a b ha hb hr) ?_
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, hβd]
    have h1 := hmin.deg_le γ hγ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hβT : ∀ β ∈ R, twKillDeg i β = twKillDeg i δ →
      ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J \ {α, α'}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • γ + b • β) → a • γ + b • β ∈ Rs := by
    intro β hβ hβd γ hγ a b ha hb hr
    refine hhigh _ (hR.ideal γ hγ.1 β hβ a b ha hb hr) ?_
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, hβd]
    have h1 := hdegpos γ hγ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hq2 : ∀ γ, (γ = α ∨ γ = α') → ∀ β ∈ R, twKillDeg i β = twKillDeg i δ →
      ∀ p q : ℕ, 1 ≤ p → 2 ≤ q → IsRoot TwistTag.E6.tag (p • γ + q • β) → p • γ + q • β ∈ Rs := by
    intro γ hγ β hβ hβd p q hp hq hr
    have hγJ : γ ∈ parabolicPosRoots TwistTag.E6.tag J := by rcases hγ with rfl | rfl <;> assumption
    refine hhigh _ (hR.ideal γ hγJ β hβ p q hp (by omega) hr) ?_
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, hβd]
    have hγd : twKillDeg i γ = 0 := by rcases hγ with rfl | rfl <;> assumption
    rw [hγd]
    have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith
  set V := rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) with hVdef
  set N := rootSpan TwistTag.E6.tag K Rs with hNdef
  have : (N.subgroupOf V).Normal :=
    ⟨fun x hx b => Subgroup.mem_subgroupOf.2 (hnorm b.1 b.2 x.1 (Subgroup.mem_subgroupOf.1 hx))⟩
  set L : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ := ![δ, δ + α, δ + α', δ + α + α'] with hL
  have hLR : ∀ k, L k ∈ R := by
    intro k
    fin_cases k
    exacts [hδR, hβ₁R, hβ₂R, hθR]
  have hLd : ∀ k, twKillDeg i (L k) = twKillDeg i δ := by
    intro k
    fin_cases k
    exacts [rfl, hdβ₁, hdβ₂, hdθ]
  have hLV : ∀ k a, pinnedX TwistTag.E6.tag K (L k) a ∈ V := fun k a =>
    classKill_pinnedX_mem (hRJ (hLR k)) a
  set X : Fin 4 → K → V ⧸ N.subgroupOf V := fun k a => twKillQ V N (pinnedX TwistTag.E6.tag K (L k) a)
    with hX
  have hadd : ∀ k a b, X k a * X k b = X k (a + b) := fun k a b => by
    simp only [hX]
    rw [← twKillQ_mul (hLV k a) (hLV k b), ← pinnedX_add]
  have hcX : ∀ k l a b, Commute (X k a) (X l b) := fun k l a b =>
    twKillQ_commute (hLV k a) (hLV l b)
      (twKill_commutator_mem hRJ hnorm (hRJ (hLR l)) (hβm _ (hLR l) (hLd l))
        (classKill_pinnedX_mem (hLR k) a) b)
  have hzV : z ∈ V := classKill_rootSpan_mono (fun x hx => (twKillPerp_subset hx).1) hz
  have hzU : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \ {α, α'}) :=
    classKill_rootSpan_mono twKillPerp_subset hz
  have hzX : ∀ k a, Commute (twKillQ V N z) (X k a) := fun k a =>
    twKillQ_commute hzV (hLV k a)
      (twKill_commutator_mem Set.sdiff_subset hnorm (hRJ (hLR k)) (hβT _ (hLR k) (hLd k)) hzU a)
  set A₁ := pinnedX TwistTag.E6.tag K α c with hA₁
  set A₂ := pinnedX TwistTag.E6.tag K α' c' with hA₂
  have hA : twKillA σ i c = A₁ * A₂ := by
    simp only [twKillA, hne, ↓reduceIte]
    rfl
  have hA₁V : A₁ ∈ V := classKill_pinnedX_mem hαJ c
  have hA₂V : A₂ ∈ V := classKill_pinnedX_mem hα'J c'
  have hA₁₁ : A₁ * A₁ = 1 := classKill_pinnedX_mul_self _ _
  have hA₂₂ : A₂ * A₂ = 1 := classKill_pinnedX_mul_self _ _
  have hA₁₂ : A₁ * A₂ = A₂ * A₁ := (twKill_commute_pair hne c c').eq
  have hδ₁ : δ ∈ parabolicPosRoots TwistTag.E6.tag J \ {α} := ⟨hδJ, fun h => hδΨ.2 (Or.inl h)⟩
  have hδ₂ : δ ∈ parabolicPosRoots TwistTag.E6.tag J \ {α'} :=
    ⟨hδJ, fun h => hδΨ.2 (Or.inr h)⟩
  have hβ₂Ψ := hR.subset hβ₂R
  have hβ₁Ψ := hR.subset hβ₁R
  have hβ₂₁ : δ + α' ∈ parabolicPosRoots TwistTag.E6.tag J \ {α} :=
    ⟨hβ₂Ψ.1, fun h => hβ₂Ψ.2 (Or.inl h)⟩
  have hβ₁₂ : δ + α ∈ parabolicPosRoots TwistTag.E6.tag J \ {α'} :=
    ⟨hβ₁Ψ.1, fun h => hβ₁Ψ.2 (Or.inr h)⟩
  have hθ' : δ + α' + α = δ + α + α' := add_right_comm _ _ _
  have cb₁δ := classKill_conj_bottom (twKill_hstr J i) hnorm hδ₁ hδa hs1
    (hq2 α (Or.inl rfl) δ hδR rfl) c
  have cb₂δ := classKill_conj_bottom (twKill_hstr J (TwistTag.E6.perm i)) hnorm hδ₂ hδa' hs2
    (hq2 α' (Or.inr rfl) δ hδR rfl) c'
  have cb₁β₂ := classKill_conj_bottom (twKill_hstr J i) hnorm hβ₂₁ (by rw [hθ']; exact hθr)
    (by rw [show δ + α' - α = δ - α + α' by abel]; exact hn2)
    (hq2 α (Or.inl rfl) _ hβ₂R hdβ₂) c
  have cb₂β₁ := classKill_conj_bottom (twKill_hstr J (TwistTag.E6.perm i)) hnorm hβ₁₂ hθr hn1
    (hq2 α' (Or.inr rfl) _ hβ₁R hdβ₁) c'
  rw [hθ'] at cb₁β₂
  have cm₁β₁ := classKill_comm_add_single hi (twKill_hstr J i) hδ₁ hδa c
  have cm₂β₂ := classKill_comm_add_single (hJ i hi) (twKill_hstr J (TwistTag.E6.perm i)) hδ₂
    hδa' c'
  have hθp : 0 < height (δ + α + α') := (hRpos _ hθR).2
  have hαp : (0 : ℤ) < height α := by rw [hα, height_single]; omega
  have hα'p : (0 : ℤ) < height α' := by rw [hα', height_single]; omega
  have hαθ : α ≠ δ + α + α' := fun e => by
    have := congrArg (twKillLev i) e
    rw [hlθ, hlα] at this
    have := hmin.lev_le δ hδR rfl
    have h0 : 0 ≤ twKillLev i δ := by
      simp only [twKillLev]
      exact Finset.sum_nonneg fun l _ => by
        split_ifs
        · exact (IsRoot.height_pos_iff hδr).1 hδp l
        · exact le_rfl
    omega
  have hα'θ : α' ≠ δ + α + α' := fun e => by
    have := congrArg (twKillLev i) e
    rw [hlθ, hlα'] at this
    have h0 : 0 ≤ twKillLev i δ := by
      simp only [twKillLev]
      exact Finset.sum_nonneg fun l _ => by
        split_ifs
        · exact (IsRoot.height_pos_iff hδr).1 hδp l
        · exact le_rfl
    omega
  have cm₁θ : ∀ e : K, Commute A₁ (pinnedX TwistTag.E6.tag K (δ + α + α') e) := fun e =>
    commute_pinnedX_of_not_isRoot_add_E6 (isRoot_single _ i) hθr hαθ (twKill_ne_neg hαp hθp)
      (by rw [add_comm]; exact hn3) c e
  have cm₂θ : ∀ e : K, Commute A₂ (pinnedX TwistTag.E6.tag K (δ + α + α') e) := fun e =>
    commute_pinnedX_of_not_isRoot_add_E6 (isRoot_single _ _) hθr hα'θ (twKill_ne_neg hα'p hθp)
      (by rw [add_comm]; exact hn4) c' e
  have hconjQ : ∀ {a x y : ModGL TwistTag.E6.tag K}, a ∈ V → x ∈ V → y ∈ V →
      y⁻¹ * (a * x * a) ∈ N → twKillQ V N a * twKillQ V N x * twKillQ V N a = twKillQ V N y := by
    intro a x y ha hx hy h
    rw [← twKillQ_mul ha hx, ← twKillQ_mul (mul_mem ha hx) ha]
    exact ((twKillQ_eq_iff hy (mul_mem (mul_mem ha hx) ha)).2 h).symm
  have hcommQ : ∀ {a x : ModGL TwistTag.E6.tag K}, a ∈ V → x ∈ V → a * x = x * a → a * a = 1 →
      twKillQ V N a * twKillQ V N x * twKillQ V N a = twKillQ V N x := by
    intro a x ha hx h haa
    rw [← twKillQ_mul ha hx, ← twKillQ_mul (mul_mem ha hx) ha, h, mul_assoc, haa, mul_one]
  have hXm : ∀ (k : Fin 4) (a : K) (l : Fin 4) (b : K),
      twKillQ V N (pinnedX TwistTag.E6.tag K (L k) a * pinnedX TwistTag.E6.tag K (L l) b) =
        X k a * X l b := fun k a l b => twKillQ_mul (hLV k a) (hLV l b)
  set a₁ := twKillQ V N A₁ with ha₁
  set a₂ := twKillQ V N A₂ with ha₂
  have qa11 : a₁ * a₁ = 1 := by rw [ha₁, ← twKillQ_mul hA₁V hA₁V, hA₁₁, twKillQ_one]
  have qa22 : a₂ * a₂ = 1 := by rw [ha₂, ← twKillQ_mul hA₂V hA₂V, hA₂₂, twKillQ_one]
  have qA : twKillQ V N (twKillA σ i c) = a₁ * a₂ := by rw [hA, twKillQ_mul hA₁V hA₂V]
  have qa12 : a₁ * a₂ = a₂ * a₁ := by rw [← twKillQ_mul hA₁V hA₂V, hA₁₂, twKillQ_mul hA₂V hA₁V]
  have q₁δ : ∀ g, a₁ * X 0 g * a₁ = X 1 (c * g) * X 0 g := fun g =>
    (hconjQ hA₁V (hLV 0 g) (mul_mem (hLV 1 _) (hLV 0 g)) (cb₁δ g)).trans (hXm 1 _ 0 g)
  have q₂δ : ∀ g, a₂ * X 0 g * a₂ = X 2 (c' * g) * X 0 g := fun g =>
    (hconjQ hA₂V (hLV 0 g) (mul_mem (hLV 2 _) (hLV 0 g)) (cb₂δ g)).trans (hXm 2 _ 0 g)
  have q₁β₂ : ∀ g, a₁ * X 2 g * a₁ = X 3 (c * g) * X 2 g := fun g =>
    (hconjQ hA₁V (hLV 2 g) (mul_mem (hLV 3 _) (hLV 2 g)) (cb₁β₂ g)).trans (hXm 3 _ 2 g)
  have q₂β₁ : ∀ g, a₂ * X 1 g * a₂ = X 3 (c' * g) * X 1 g := fun g =>
    (hconjQ hA₂V (hLV 1 g) (mul_mem (hLV 3 _) (hLV 1 g)) (cb₂β₁ g)).trans (hXm 3 _ 1 g)
  have q₁β₁ : ∀ g, a₁ * X 1 g * a₁ = X 1 g := fun g =>
    hcommQ hA₁V (hLV 1 g) (cm₁β₁ g) hA₁₁
  have q₂β₂ : ∀ g, a₂ * X 2 g * a₂ = X 2 g := fun g =>
    hcommQ hA₂V (hLV 2 g) (cm₂β₂ g) hA₂₂
  have q₁θ : ∀ g, a₁ * X 3 g * a₁ = X 3 g := fun g =>
    hcommQ hA₁V (hLV 3 g) (cm₁θ g).eq hA₁₁
  have q₂θ : ∀ g, a₂ * X 3 g * a₂ = X 3 g := fun g =>
    hcommQ hA₂V (hLV 3 g) (cm₂θ g).eq hA₂₂
  have hX0 : ∀ a, X 0 a = twKillP X a 0 0 0 := fun a => by simp only [twKillP, twKillP_zero hadd, mul_one]
  have hX1 : ∀ a, X 1 a = twKillP X 0 a 0 0 := fun a => by
    simp only [twKillP, twKillP_zero hadd, mul_one, one_mul]
  have hX2 : ∀ a, X 2 a = twKillP X 0 0 a 0 := fun a => by
    simp only [twKillP, twKillP_zero hadd, mul_one, one_mul]
  have hX3 : ∀ a, X 3 a = twKillP X 0 0 0 a := fun a => by
    simp only [twKillP, twKillP_zero hadd, one_mul]
  have hAconj : ∀ x, twKillQ V N (twKillA σ i c) * x * twKillQ V N (twKillA σ i c) =
      a₁ * (a₂ * x * a₂) * a₁ := fun x => by
    rw [qA]
    calc a₁ * a₂ * x * (a₁ * a₂) = a₁ * a₂ * x * (a₂ * a₁) := by rw [qa12]
      _ = a₁ * (a₂ * x * a₂) * a₁ := by group
  have hA0 : ∀ g, twKillQ V N (twKillA σ i c) * X 0 g * twKillQ V N (twKillA σ i c) =
      twKillP X g (c * g) (c' * g) (c * c' * g) := fun g => by
    rw [hAconj, q₂δ, twKill_conj_mul qa11, q₁β₂, q₁δ, hX0, hX1, hX2, hX3, twKillP_mul hadd hcX,
      twKillP_mul hadd hcX, twKillP_mul hadd hcX]
    congr 1 <;> ring
  have hA1 : ∀ g, twKillQ V N (twKillA σ i c) * X 1 g * twKillQ V N (twKillA σ i c) =
      twKillP X 0 g 0 (c' * g) := fun g => by
    rw [hAconj, q₂β₁, twKill_conj_mul qa11, q₁θ, q₁β₁, hX1, hX3, twKillP_mul hadd hcX]
    congr 1 <;> ring
  have hA2 : ∀ g, twKillQ V N (twKillA σ i c) * X 2 g * twKillQ V N (twKillA σ i c) =
      twKillP X 0 0 g (c * g) := fun g => by
    rw [hAconj, q₂β₂, q₁β₂, hX2, hX3, twKillP_mul hadd hcX]
    congr 1 <;> ring
  have hA3 : ∀ g, twKillQ V N (twKillA σ i c) * X 3 g * twKillQ V N (twKillA σ i c) = X 3 g :=
    fun g => by rw [hAconj, q₂θ, q₁θ]
  have hAV : twKillA σ i c ∈ V := twKillA_mem σ hJ hi c
  have qAA : twKillQ V N (twKillA σ i c) * twKillQ V N (twKillA σ i c) = 1 := by
    rw [← twKillQ_mul hAV hAV, twKillA_mul_self, twKillQ_one]
  have hm0 : ∀ a, pinnedX TwistTag.E6.tag K δ a ∈ V := hLV 0
  have hm1 : ∀ a, pinnedX TwistTag.E6.tag K (δ + α) a ∈ V := hLV 1
  have hm2 : ∀ a, pinnedX TwistTag.E6.tag K (δ + α') a ∈ V := hLV 2
  have hm3 : ∀ a, pinnedX TwistTag.E6.tag K (δ + α + α') a ∈ V := hLV 3
  have hQ4 : ∀ a₀ a₁ a₂ a₃ : K, twKillQ V N (pinnedX TwistTag.E6.tag K δ a₀ *
      pinnedX TwistTag.E6.tag K (δ + α) a₁ * pinnedX TwistTag.E6.tag K (δ + α') a₂ *
      pinnedX TwistTag.E6.tag K (δ + α + α') a₃) = twKillP X a₀ a₁ a₂ a₃ := fun a₀ a₁ a₂ a₃ => by
    rw [twKillQ_mul (mul_mem (mul_mem (hm0 _) (hm1 _)) (hm2 _)) (hm3 _),
      twKillQ_mul (mul_mem (hm0 _) (hm1 _)) (hm2 _), twKillQ_mul (hm0 _) (hm1 _)]
    rfl
  have hm4 : ∀ a₀ a₁ a₂ a₃ : K, pinnedX TwistTag.E6.tag K δ a₀ *
      pinnedX TwistTag.E6.tag K (δ + α) a₁ * pinnedX TwistTag.E6.tag K (δ + α') a₂ *
      pinnedX TwistTag.E6.tag K (δ + α + α') a₃ ∈ V := fun a₀ a₁ a₂ a₃ =>
    mul_mem (mul_mem (mul_mem (hm0 _) (hm1 _)) (hm2 _)) (hm3 _)
  have hRsn : ∀ k, L k ∉ Rs := by
    intro k hk
    apply hk.2
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hPdet : ∀ a₀ a₁ a₂ a₃ : K, twKillP X a₀ a₁ a₂ a₃ = 1 →
      a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
    intro a₀ a₁ a₂ a₃ h
    have h' := (twKillQ_eq_one_iff (hm4 a₀ a₁ a₂ a₃)).1 (by rw [hQ4]; exact h)
    exact twKill_detect₄ hRspos hRsclosed (hRpos _ hδR) (hRpos _ hβ₁R) (hRpos _ hβ₂R)
      (hRpos _ hθR) d01 d02 d03 hβ₁β₂ d13 d23 (hRsn 0) (hRsn 1) (hRsn 2) (hRsn 3) h'
  have hPP : ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : K, twKillP X a₀ a₁ a₂ a₃ = twKillP X b₀ b₁ b₂ b₃ →
      a₀ + b₀ = 0 ∧ a₁ + b₁ = 0 ∧ a₂ + b₂ = 0 ∧ a₃ + b₃ = 0 := by
    intro a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ h
    apply hPdet
    rw [← twKillP_mul hadd hcX, h, twKillP_mul hadd hcX]
    simp only [CharTwo.add_self_eq_zero]
    exact twKillP_zero_zero hadd
  have hLinj : Function.Injective L := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact absurd hab d01 | exact absurd hab d02 | exact absurd hab d03
      | exact absurd hab hβ₁β₂ | exact absurd hab d13 | exact absurd hab d23
      | exact absurd hab.symm d01 | exact absurd hab.symm d02 | exact absurd hab.symm d03
      | exact absurd hab.symm hβ₁β₂ | exact absurd hab.symm d13 | exact absurd hab.symm d23
  have hRclosed : ∀ β ∈ R, ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • β + b • γ) → a • β + b • γ ∈ R :=
    fun β hβ γ hγ a b ha hb hr => hR.ideal β (hRJ hβ) γ hγ a b ha hb hr
  obtain ⟨d, hd⟩ := classKill_split hRpos hRclosed L hLinj hLR hn
  have hrange : Set.range L = {δ, δ + α, δ + α', δ + α + α'} := by
    rw [hL]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  have hprod : (List.ofFn fun j => pinnedX TwistTag.E6.tag K (L j) (d j)).prod =
      pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1) *
        pinnedX TwistTag.E6.tag K (δ + α') (d 2) * pinnedX TwistTag.E6.tag K (δ + α + α') (d 3) := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc, ← mul_assoc]
    rfl
  rw [hrange, hprod] at hd
  set Y := pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1) *
    pinnedX TwistTag.E6.tag K (δ + α') (d 2) * pinnedX TwistTag.E6.tag K (δ + α + α') (d 3)
    with hY
  set n' := Y⁻¹ * n with hn'def
  have hn_eq : n = Y * n' := by rw [hn'def]; group
  have hYV : Y ∈ V := hm4 _ _ _ _
  have hYR : Y ∈ rootSpan TwistTag.E6.tag K R :=
    mul_mem (mul_mem (mul_mem (classKill_pinnedX_mem hδR _) (classKill_pinnedX_mem hβ₁R _))
      (classKill_pinnedX_mem hβ₂R _)) (classKill_pinnedX_mem hθR _)
  have hQY : twKillQ V N Y = twKillP X (d 0) (d 1) (d 2) (d 3) := hQ4 _ _ _ _
  have hcoc' : twKillA σ i c * (z * (Y * n')) * twKillA σ i c = (z * (Y * n'))⁻¹ := by
    rw [← hn_eq]
    exact hcoc
  have hzY : ⁅z, Y⁆ ∈ N := twKillQ_mem_of_commute hzV hYV (by rw [hQY]; exact twKillP_commute_of hzX _ _ _ _)
  have hYY : Y * Y ∈ N := by
    rw [← twKillQ_eq_one_iff (mul_mem hYV hYV), twKillQ_mul hYV hYV, hQY, twKillP_mul hadd hcX]
    simp only [CharTwo.add_self_eq_zero]
    exact twKillP_zero_zero hadd
  have hcz := twKill_cocycle hNV hnorm hAV hzV hYV hd (twKillA_comm_perp σ hJ hi c hz) hzY hYY hcoc'
  have hAYA : twKillA σ i c * Y * twKillA σ i c ∈ rootSpan TwistTag.E6.tag K R := by
    have := classKill_conj_mem hRJ hR.ideal hAV hYR
    rwa [inv_eq_of_mul_eq_one_right (twKillA_mul_self σ i c)] at this
  have hW : Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c) ∈ rootSpan TwistTag.E6.tag K R :=
    mul_mem (inv_mem hYR) hAYA
  have hzzR : z * z ∈ rootSpan TwistTag.E6.tag K R := by
    have e : z * z = (z * z * (Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c))) *
        (Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c))⁻¹ := by group
    rw [e]
    exact mul_mem (classKill_rootSpan_mono Set.sdiff_subset hcz) (inv_mem hW)
  have hzzN : z * z ∈ N := by
    have h := classKill_rootSpan_inf_le_inter (S := twKillPerp J i) (T := R)
      (fun β hβ => (twKillPerp_subset hβ).1.2) twKillPerp_closed hRpos hRclosed
      (mul_mem hz hz) hzzR
    refine classKill_rootSpan_mono ?_ h
    rintro x ⟨hxP, hxR⟩
    refine ⟨hxR, fun h => ?_⟩
    have hx1 := not_isRoot_add_sub_of_classKillPair hi (twKill_hstr J i) hxP.1.1 hxP.1.2
    have hx2 := not_isRoot_add_sub_of_classKillPair (hJ i hi) (twKill_hstr J (TwistTag.E6.perm i))
      hxP.2.1 hxP.2.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact hx1.1 hδa
    · exact hx1.2 (by rw [add_sub_cancel_right]; exact hδr)
    · exact hx2.2 (by rw [add_sub_cancel_right]; exact hδr)
    · exact hx1.2 (by rw [show δ + α + α' - α = δ + α' by abel]; exact hδa')
  have hWN : Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c) ∈ N := by
    have e : Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c) =
        (z * z)⁻¹ * (z * z * (Y⁻¹ * (twKillA σ i c * Y * twKillA σ i c))) := by group
    rw [e]
    exact mul_mem (inv_mem hzzN) hcz
  have hMd : twKillP X (d 0) (d 1) (d 2) (d 3) = twKillP X (d 0) (d 1 + c * d 0) (d 2 + c' * d 0)
      (d 3 + c * c' * d 0 + c' * d 1 + c * d 2) := by
    have hAYAV : twKillA σ i c * Y * twKillA σ i c ∈ V := mul_mem (mul_mem hAV hYV) hAV
    have h1 := (twKillQ_eq_iff hYV hAYAV).2 hWN
    rw [twKillQ_mul (mul_mem hAV hYV) hAV, twKillQ_mul hAV hYV, hQY,
      twKillP_conj hadd hcX qAA hA0 hA1 hA2 hA3] at h1
    exact h1
  obtain ⟨-, e1, e2, e3⟩ := hPP _ _ _ _ _ _ _ _ hMd
  have hcd0 : c * d 0 = 0 := by linear_combination e1 - d 1 * h2
  have hd0 : d 0 = 0 := (mul_eq_zero.1 hcd0).resolve_left hc
  have hrel : c' * d 1 + c * d 2 = 0 := by
    rw [hd0] at e3
    linear_combination e3 - d 3 * h2
  have hβ₁r : IsRoot TwistTag.E6.tag (δ + α) := hδa
  have hFY : twistHom TwistTag.E6 K σ Y = pinnedX TwistTag.E6.tag K δ (σ (d 0)) *
      pinnedX TwistTag.E6.tag K (δ + α') (σ (d 1)) * pinnedX TwistTag.E6.tag K (δ + α) (σ (d 2)) *
      pinnedX TwistTag.E6.tag K (δ + α + α') (σ (d 3)) := by
    rw [hY, map_mul, map_mul, map_mul, twKill_F_pinnedX σ hδr, twKill_F_pinnedX σ hδa,
      twKill_F_pinnedX σ hδa', twKill_F_pinnedX σ hθr, hρδ, hρβ₁, hρβ₂, hρθ]
  have hFYV : twistHom TwistTag.E6 K σ Y ∈ V := by
    rw [hFY]
    exact mul_mem (mul_mem (mul_mem (hm0 _) (hm2 _)) (hm1 _)) (hm3 _)
  have hQFY : twKillQ V N (twistHom TwistTag.E6 K σ Y) =
      twKillP X (σ (d 0)) (σ (d 2)) (σ (d 1)) (σ (d 3)) := by
    rw [hFY, twKillQ_mul (mul_mem (mul_mem (hm0 _) (hm2 _)) (hm1 _)) (hm3 _),
      twKillQ_mul (mul_mem (hm0 _) (hm2 _)) (hm1 _), twKillQ_mul (hm0 _) (hm2 _)]
    change X 0 _ * X 2 _ * X 1 _ * X 3 _ = _
    rw [hX0, hX1, hX2, hX3, twKillP_mul hadd hcX, twKillP_mul hadd hcX, twKillP_mul hadd hcX]
    congr 1 <;> ring
  have hFn' : twistHom TwistTag.E6 K σ n' ∈ N :=
    twKill_F_mem_rootSpan σ (fun β hβ => (hRspos β hβ).1) hRsρ hd
  have hYF : Y⁻¹ * twistHom TwistTag.E6 K σ Y ∈ N := by
    have h1 : twistHom TwistTag.E6 K σ Y * twistHom TwistTag.E6 K σ n' = Y * n' := by
      rw [← map_mul, ← hn_eq, hFn]
    have e : Y⁻¹ * twistHom TwistTag.E6 K σ Y = n' * (twistHom TwistTag.E6 K σ n')⁻¹ := by
      calc Y⁻¹ * twistHom TwistTag.E6 K σ Y
          = Y⁻¹ * (twistHom TwistTag.E6 K σ Y * twistHom TwistTag.E6 K σ n') *
            (twistHom TwistTag.E6 K σ n')⁻¹ := by group
        _ = Y⁻¹ * (Y * n') * (twistHom TwistTag.E6 K σ n')⁻¹ := by rw [h1]
        _ = n' * (twistHom TwistTag.E6 K σ n')⁻¹ := by group
    rw [e]
    exact mul_mem hd (inv_mem hFn')
  have hEq : twKillP X (d 0) (d 1) (d 2) (d 3) = twKillP X (σ (d 0)) (σ (d 2)) (σ (d 1)) (σ (d 3)) := by
    rw [← hQY, ← hQFY]
    exact (twKillQ_eq_iff hYV hFYV).2 hYF
  obtain ⟨-, -, f2, f3⟩ := hPP _ _ _ _ _ _ _ _ hEq
  have hσd1 : σ (d 1) = d 2 := by linear_combination f2 - d 2 * h2
  have hσd3 : σ (d 3) = d 3 := by linear_combination f3 - d 3 * h2
  set e₀ := d 1 * c⁻¹ with he₀
  set s₀ := d 3 + c' * d 1 with hs₀
  set t := δt * s₀ with ht
  set e₁ := σ (t * c⁻¹) with he₁
  have hσe₁ : σ e₁ = t * c⁻¹ := hσσ _
  have hσc' : σ c' = c := hσσ c
  have hσs : σ s₀ = s₀ := by
    rw [hs₀, map_add, map_mul, hσd3, hσc', hσd1]
    linear_combination hrel - c' * d 1 * h2
  have hts : t + σ t = s₀ := by
    rw [ht, map_mul, hσs, ← add_mul, hδt, one_mul]
  have hc'e₁ : c' * e₁ = σ t := by
    rw [he₁, hc'def, ← map_mul, mul_comm (t) c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hk1 : c * e₀ + d 1 = 0 := by
    rw [he₀, mul_comm (d 1), ← mul_assoc, mul_inv_cancel₀ hc, one_mul, CharTwo.add_self_eq_zero]
  have hk2 : c' * e₀ + d 2 = 0 := by
    rw [he₀]
    field_simp
    linear_combination hrel
  have hk3 : c * c' * e₀ + c' * e₁ + c * σ e₁ + d 3 = 0 := by
    rw [hc'e₁, hσe₁]
    have h3 : c * c' * e₀ = c' * d 1 := by
      rw [he₀]
      field_simp
    have h4 : c * (t * c⁻¹) = t := by field_simp
    rw [h3, h4]
    linear_combination hts + (c' * d 1 + d 3) * h2
  set p := pinnedX TwistTag.E6.tag K δ e₀ * pinnedX TwistTag.E6.tag K (δ + α) e₁ *
    pinnedX TwistTag.E6.tag K (δ + α') (σ e₁) with hp
  have hp' : p = pinnedX TwistTag.E6.tag K δ e₀ * pinnedX TwistTag.E6.tag K (δ + α) e₁ *
      pinnedX TwistTag.E6.tag K (δ + α') (σ e₁) * pinnedX TwistTag.E6.tag K (δ + α + α') 0 := by
    rw [pinnedX_zero, mul_one]
  have hpV : p ∈ V := by rw [hp']; exact hm4 _ _ _ _
  have hQp : twKillQ V N p = twKillP X e₀ e₁ (σ e₁) 0 := by rw [hp']; exact hQ4 _ _ _ _
  have hQApA : twKillQ V N (twKillA σ i c * p * twKillA σ i c) =
      twKillP X e₀ (e₁ + c * e₀) (σ e₁ + c' * e₀) (0 + c * c' * e₀ + c' * e₁ + c * σ e₁) := by
    rw [twKillQ_mul (mul_mem hAV hpV) hAV, twKillQ_mul hAV hpV, hQp,
      twKillP_conj hadd hcX qAA hA0 hA1 hA2 hA3]
  have hApAV : twKillA σ i c * p * twKillA σ i c ∈ V := mul_mem (mul_mem hAV hpV) hAV
  have hzp : ⁅z, twKillA σ i c * p * twKillA σ i c⁆ ∈ N :=
    twKillQ_mem_of_commute hzV hApAV (by rw [hQApA]; exact twKillP_commute_of hzX _ _ _ _)
  have hYp : ⁅Y, p⁆ ∈ N :=
    twKillQ_mem_of_commute hYV hpV (by rw [hQY, hQp]; exact twKillP_commute hadd hcX _ _ _ _ _ _ _ _)
  have hPinv : ∀ a₀ a₁ a₂ a₃ : K, (twKillP X a₀ a₁ a₂ a₃)⁻¹ = twKillP X a₀ a₁ a₂ a₃ := by
    intro a₀ a₁ a₂ a₃
    refine inv_eq_of_mul_eq_one_right ?_
    rw [twKillP_mul hadd hcX]
    simp only [CharTwo.add_self_eq_zero]
    exact twKillP_zero_zero hadd
  have hk : twKillA σ i c * p * twKillA σ i c * p⁻¹ * Y ∈ N := by
    rw [← twKillQ_eq_one_iff (mul_mem (mul_mem hApAV (inv_mem hpV)) hYV),
      twKillQ_mul (mul_mem hApAV (inv_mem hpV)) hYV, twKillQ_mul hApAV (inv_mem hpV), twKillQ_inv hpV,
      hQApA, hQp, hQY, hPinv, twKillP_mul hadd hcX, twKillP_mul hadd hcX, hd0]
    convert twKillP_zero_zero hadd using 2
    · ring_nf
      linear_combination e₀ * h2
    · linear_combination hk1 + e₁ * h2
    · linear_combination hk2 + σ e₁ * h2
    · linear_combination hk3
  have hres := twKill_kill hNV hnorm hAV hzV hYV hpV hd hzp hYp hk
  rw [← hn_eq] at hres
  have hσe₀ : σ e₀ = e₀ := by
    rw [he₀, map_mul, map_inv₀, hσd1, ← hc'def]
    field_simp
    linear_combination -hrel + d 2 * c * h2
  have hcomm₁₂ : pinnedX TwistTag.E6.tag K (δ + α) e₁ * pinnedX TwistTag.E6.tag K (δ + α') (σ e₁) =
      pinnedX TwistTag.E6.tag K (δ + α') (σ e₁) * pinnedX TwistTag.E6.tag K (δ + α) e₁ := by
    have := commute_pinnedX_permLattice_twistedE6 (K := K) hδa e₁ (σ e₁)
    rw [hρβ₁] at this
    exact this.eq
  have hFp : twistHom TwistTag.E6 K σ p = p := by
    have h1 : twistHom TwistTag.E6 K σ p = pinnedX TwistTag.E6.tag K δ (σ e₀) *
        pinnedX TwistTag.E6.tag K (δ + α') (σ e₁) * pinnedX TwistTag.E6.tag K (δ + α) (σ (σ e₁)) := by
      rw [hp, map_mul, map_mul, twKill_F_pinnedX σ hδr, twKill_F_pinnedX σ hδa,
        twKill_F_pinnedX σ hδa', hρδ, hρβ₁, hρβ₂]
    rw [h1, hσe₀, hσσ e₁, hp, mul_assoc, mul_assoc, hcomm₁₂]
  have hFA := twKillA_F hσσ (i := i) (c := c) (fun h => absurd h hne)
  set n'' := z⁻¹ * (twKillA σ i c * p * twKillA σ i c * (z * n) * p⁻¹) with hn''
  have hFn'' : twistHom TwistTag.E6 K σ n'' = n'' := by
    rw [hn'']
    simp only [map_mul, map_inv, hFz, hFn, hFp, hFA]
  have hpU : p ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \ {α, α'}) :=
    mul_mem (mul_mem (classKill_pinnedX_mem hδΨ _) (classKill_pinnedX_mem hβ₁Ψ _))
      (classKill_pinnedX_mem hβ₂Ψ _)
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hRpos β hβ).1
  refine ⟨Rs, hRs, hRsρ, Set.ncard_lt_ncard (LE.le.ssubset_of_mem_notMem Set.sdiff_subset hδR
    (fun h => h.2 (Or.inl rfl))) hfin, p, hpU, hFp, z, hz, hFz, n'', hres, hFn'', ?_⟩
  rw [hn'', mul_inv_cancel_left]

end Square

end CFSG.SeitzReduction
