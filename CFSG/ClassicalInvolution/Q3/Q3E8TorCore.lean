module

public import CFSG.ClassicalInvolution.Q3.Q3E8TorStmt
public import CFSG.ClassicalInvolution.Q3.Q3E8BF5HJ
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelLeviStab

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
  CFSG.ClassicalInvolution.ModelFacts.ChevAut CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section Small

theorem gf3_cases (c : GaloisField 3 1) : c = 0 ∨ c = 1 ∨ c = -1 := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have h : c ^ 3 = c := by
    have hc := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, card_gf3] at hc
    exact hc
  have h0 : c * (c - 1) * (c + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h1))

theorem ringEquiv_gf3_eq_one (φ : GaloisField 3 1 ≃+* GaloisField 3 1) : φ = 1 := by
  refine RingEquiv.ext fun c => ?_
  rcases gf3_cases c with rfl | rfl | rfl
  · exact map_zero φ
  · exact map_one φ
  · rw [map_neg, map_one]
    rfl

theorem exists_pow_card_hom {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] :
    ∃ Fr : L →+* L, ∀ c, Fr c = c ^ Nat.card F := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  refine ⟨iterateFrobenius L p n, fun x => ?_⟩
  rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]

theorem rational_of_diag_baseChange {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    [IsAlgClosed L] {g : ModGL .E7 F} {b' : Fin (Tag.rank .E7) → Lˣ}
    (h : baseChangeGL (algebraMap F L) g = rootDiagUnit .E7 b') :
    ∃ b : Fin (Tag.rank .E7) → Fˣ, g = rootDiagUnit .E7 b := by
  obtain ⟨Fr, hFr⟩ := exists_pow_card_hom (F := F) (L := L)
  have hfix := units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g
  rw [h] at hfix
  have h0 : Units.map (entrywiseHom Fr) (rootDiagUnit .E7 b') =
      rootDiagUnit .E7 (fun i => Units.map Fr.toMonoidHom (b' i)) :=
    Units.ext (entrywise_rootDiag Fr b')
  have hb : ∀ i, Units.map Fr.toMonoidHom (b' i) = b' i :=
    congrFun (rootDiagUnit_injective (h0.symm.trans hfix))
  have hr : ∀ i, ∃ a : Fˣ, Units.map (algebraMap F L).toMonoidHom a = b' i := by
    intro i
    have hpow : ((b' i : Lˣ) : L) ^ Nat.card F = (b' i : L) := by
      rw [← hFr]
      exact congrArg Units.val (hb i)
    obtain ⟨c₀, hc₀⟩ := mem_range_algebraMap_of_pow_card_eq hpow
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc₀
      exact (b' i).ne_zero hc₀.symm
    exact ⟨Units.mk0 c₀ hc0, Units.ext hc₀⟩
  choose a ha using hr
  refine ⟨a, baseChangeGL_injective (algebraMap F L) ?_⟩
  rw [h, baseChangeGL_rootDiagUnit]
  congr 2
  funext i
  exact (ha i).symm

theorem thetaDiag_add' {k : Type} [Field k] (x y : Fin (Tag.rank .E7) → ℤ) (c : kˣ) :
    thetaDiag (x + y) c = thetaDiag x c * thetaDiag y c := by
  funext i
  simp only [thetaDiag, Pi.mul_apply, iform_add_left, zpow_add]

theorem thetaDiag_smul' {k : Type} [Field k] (n : ℤ) (x : Fin (Tag.rank .E7) → ℤ) (c : kˣ) :
    thetaDiag (n • x) c = thetaDiag x (c ^ n) := by
  funext i
  simp only [thetaDiag, iform_smul_left, zpow_mul]

theorem thetaDiag_zero' {k : Type} [Field k] (c : kˣ) :
    thetaDiag (0 : Fin (Tag.rank .E7) → ℤ) c = 1 := by
  funext i
  have h : iform (0 : Fin (Tag.rank .E7) → ℤ) (Pi.single i 1) = 0 := by
    simpa using iform_smul_left 0 (0 : Fin (Tag.rank .E7) → ℤ) (Pi.single i 1)
  simp [thetaDiag, h]

end Small

section Generic

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem eq_on_roots_of_simple (hS : TorusSetup D x n H) {M : Type*} [Group M] (φ₁ φ₂ : K →* M)
    (h₁ : ∀ i c, φ₁ (x (Pi.single i 1) c) = φ₂ (x (Pi.single i 1) c))
    (h₂ : ∀ i c, φ₁ (x (-Pi.single i 1) c) = φ₂ (x (-Pi.single i 1) c)) :
    ∀ γ ∈ D.roots, ∀ c, φ₁ (x γ c) = φ₂ (x γ c) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hroot : ∀ i, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hw1 : ∀ i, φ₁ (CFSG.LieType.Steinberg.weylElement x i 1) =
      φ₂ (CFSG.LieType.Steinberg.weylElement x i 1) := by
    intro i
    unfold CFSG.LieType.Steinberg.weylElement
    simp only [map_mul, h₁ i, h₂ i]
  have hstep : ∀ (i : Fin D.rank) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
      (∀ c, φ₁ (x δ c) = φ₂ (x δ c)) →
      ∀ c, φ₁ (x (reflection D.cartan i δ) c) = φ₂ (x (reflection D.cartan i δ) c) := by
    intro i δ hδ hR c
    obtain ⟨ε, hε, hεw⟩ := hE.weyl i δ hδ
    have hε2 : (ε : F) * ε = 1 := by rcases hε with rfl | rfl <;> simp
    have h1 : x (reflection D.cartan i δ) c =
        CFSG.LieType.Steinberg.weylElement x i 1 * x δ ((ε : F) * c) *
          (CFSG.LieType.Steinberg.weylElement x i 1)⁻¹ := by
      rw [hεw 1 ((ε : F) * c)]
      congr 1
      simp
      linear_combination (-c) * hε2
    rw [h1]
    simp only [map_mul, map_inv, hw1 i, hR]
  have key : ∀ (k : Fin D.rank) (ω : List (Fin D.rank)), ∀ c,
      φ₁ (x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) c) =
      φ₂ (x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) c) := by
    intro k ω
    induction ω with
    | nil => simpa using h₁ k
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple]
      exact hstep i _ (weylAction_mem_roots D.isFiniteType _ (hroot k)) ih
  intro γ hγ c
  have hγ0 : γ ∈ roots D.isFiniteType D.divisible := hγ
  rcases hγ0 with ⟨w, k, rfl⟩ | ⟨w, k, hk, rfl⟩
  · obtain ⟨ω, -, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
    exact key k ω c
  · rw [hS.div] at hk
    exact absurd hk (Set.notMem_empty _)

end Generic

section Lemmas

theorem eq_of_roots_E7 {M : Type*} [Group M] (φ₁ φ₂ : M₇ →* M)
    (h : ∀ γ ∈ (e7Datum (GaloisField 3 1)).roots, ∀ c,
      φ₁ (e7Data_valid.xm (GaloisField 3 1) γ c) = φ₂ (e7Data_valid.xm (GaloisField 3 1) γ c)) :
    φ₁ = φ₂ := by
  have hS := torusSetup_E7 (GaloisField 3 1)
  obtain ⟨C, O, hE⟩ := hS.chev
  have htop := (e7Datum_isCTGroupDatum (GaloisField 3 1)).iSup_eq_top
  have hle : (⨆ γ ∈ (e7Datum (GaloisField 3 1)).roots,
      (e7Datum (GaloisField 3 1)).rootGroup γ) ≤ MonoidHom.eqLocus φ₁ φ₂ := by
    refine iSup₂_le fun γ hγ g hg => ?_
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 g).1 hg
    exact h γ hγ c
  refine MonoidHom.ext fun y => ?_
  exact hle (htop ▸ Subgroup.mem_top y)

theorem fixed_of_central_error {K : Type*} [Group K] (α : K →* K) {R : Subgroup K} (hR : Pow3 R)
    (hcen : ∀ y ∈ R, y⁻¹ * α y ∈ Subgroup.center K)
    (hcop : ∀ z ∈ Subgroup.center K, ¬ 3 ∣ orderOf z) : ∀ y ∈ R, α y = y := by
  have hcomm : ∀ u ∈ R, ∀ v ∈ R, α ⁅u, v⁆ = ⁅u, v⁆ := by
    intro u hu v hv
    rw [map_commutatorElement]
    have e1 : α u = u * (u⁻¹ * α u) := by group
    have e2 : α v = v * (v⁻¹ * α v) := by group
    rw [e1, e2, commutatorElement_mul_central_left (hcen u hu),
      commutatorElement_mul_central_right (hcen v hv)]
  have hle : ⁅R, R⁆ ≤ MonoidHom.eqLocus α (MonoidHom.id K) :=
    Subgroup.commutator_le.2 fun u hu v hv => hcomm u hu v hv
  intro y hy
  set z := y⁻¹ * α y with hz
  have hzc : z ∈ Subgroup.center K := hcen y hy
  have hαy : α y = y * z := by rw [hz]; group
  have h3 : α (y ^ 3) = y ^ 3 := hle (hR y hy)
  have hcz : Commute y z := Subgroup.mem_center_iff.1 hzc y
  have hz3 : z ^ 3 = 1 := by
    rw [map_pow, hαy, hcz.mul_pow] at h3
    exact mul_eq_left.1 h3
  have hord : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have h1 : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact h
    · exact (hcop z hzc (dvd_of_eq h.symm)).elim
  rw [hαy, orderOf_eq_one_iff.1 h1, mul_one]

variable {F : Type} [Field F] [Finite F]

theorem εm_xm_single (i : Fin (Tag.rank .E7)) (c : F) :
    εm F (e7Data_valid.xm F (Pi.single i 1) c) = xUnit .E7 F i c := by
  change ((e7Isogeny F (e7Data_valid.xm F (Pi.single i 1) c) : ↥(adjointGroup .E7 F)) :
    ModGL .E7 F) = _
  rw [e7Isogeny_xm_single, eltElement_simpleRoot]
  rfl

theorem εm_xm_neg_single (i : Fin (Tag.rank .E7)) (c : F) :
    εm F (e7Data_valid.xm F (-Pi.single i 1) c) = yUnit .E7 F i c := by
  change ((e7Isogeny F (e7Data_valid.xm F (-Pi.single i 1) c) : ↥(adjointGroup .E7 F)) :
    ModGL .E7 F) = _
  rw [e7Isogeny_xm_neg_single]
  exact (rootOperatorFamily .E7).eltUnit_neg_simple i c

theorem xm_mem_stdRankOne {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ (e7Datum F).roots) (c : F) :
    e7Data_valid.xm F γ c ∈ stdRankOne (e7Datum F) γ ∧
      e7Data_valid.xm F (-γ) c ∈ stdRankOne (e7Datum F) γ := by
  obtain ⟨C, O, hE⟩ := (torusSetup_E7 F).chev
  have hneg : -γ ∈ (e7Datum F).roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (e7Datum F).isFiniteType hγ
  exact ⟨Subgroup.mem_sup_left (((hE.param γ hγ).1 _).2 ⟨c, rfl⟩),
    Subgroup.mem_sup_right (((hE.param (-γ) hneg).1 _).2 ⟨c, rfl⟩)⟩

theorem conj_xm_of_diag {g : M₇} {b : Fin (Tag.rank .E7) → (GaloisField 3 1)ˣ}
    (hg : εm (GaloisField 3 1) g = rootDiagUnit .E7 b) (i : Fin (Tag.rank .E7))
    (c : GaloisField 3 1) :
    g * e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c * g⁻¹ =
      e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) ((b i : GaloisField 3 1) * c) ∧
    g * e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c * g⁻¹ =
      e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1)
        ((((b i)⁻¹ : (GaloisField 3 1)ˣ) : GaloisField 3 1) * c) := by
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E7 (GaloisField 3 1) b
  have hγ : IsRoot .E7 (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) := isRoot_single .E7 i
  have hγr : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ (e7Datum (GaloisField 3 1)).roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ
  have hRf := std_mem_fund3 hγ
  have hnorm : conjSub g (stdRankOne D₇ (Pi.single i 1)) = stdRankOne D₇ (Pi.single i 1) :=
    conjSub_std_of_torus3 ⟨b, hg⟩ hγ
  have huniq : ∀ u ∈ stdRankOne D₇ (Pi.single i 1), ∀ u' ∈ stdRankOne D₇ (Pi.single i 1),
      εm (GaloisField 3 1) u = εm (GaloisField 3 1) u' → u = u' := by
    intro u hu u' hu' h
    have hker : u⁻¹ * u' ∈ (εm (GaloisField 3 1)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have := no_central_fund3 hRf (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hu')
      (εm_ker_le_center hker)
    exact inv_mul_eq_one.1 this
  have hcj : ∀ x ∈ stdRankOne D₇ (Pi.single i 1), g * x * g⁻¹ ∈ stdRankOne D₇ (Pi.single i 1) :=
    fun x hx => hnorm ▸ conj_mem_conjSub hx
  refine ⟨huniq _ (hcj _ (xm_mem_stdRankOne hγr c).1) _ (xm_mem_stdRankOne hγr _).1 ?_,
    huniq _ (hcj _ (xm_mem_stdRankOne hγr c).2) _ (xm_mem_stdRankOne hγr _).2 ?_⟩
  · rw [map_mul, map_mul, map_inv, hg, εm_xm_single, εm_xm_single]
    exact hx i c
  · rw [map_mul, map_mul, map_inv, hg, εm_xm_neg_single, εm_xm_neg_single]
    exact hy i c

end Lemmas

section Main

theorem exists_diag_of_fixes_roots3 (Γ : Set (Fin Tag.E7.rank → ℤ)) (l : Fin Tag.E7.rank → ℤ)
    (hΓ : ∀ γ ∈ Γ, γ ∈ (e7Datum (GaloisField 3 1)).roots) (hl : l ∈ Submodule.span ℤ Γ)
    (hreg : ∀ σ ∈ rootFinset .E7, iform l σ ≠ 0)
    {X : Type} [Group X] (θ : M₇ →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center M₇) (σ : X ≃* X)
    (hfix : ∀ γ ∈ Γ, ∀ y ∈ stdRankOne D₇ γ, σ (θ y) = θ y) :
    ∃ (α : M₇ ≃* M₇) (b : Fin Tag.E7.rank → (GaloisField 3 1)ˣ), (∀ y, θ (α y) = σ (θ y)) ∧
      ∀ γ ∈ (e7Datum (GaloisField 3 1)).roots, ∀ c,
        α (e7Data_valid.xm (GaloisField 3 1) γ c) =
          e7Data_valid.xm (GaloisField 3 1) γ ((diagChar b γ : GaloisField 3 1) * c) := by
  have hS := torusSetup_E7 (GaloisField 3 1)
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E7 (p := 3) (F := GaloisField 3 1) θ hθ hker σ
  have hφ : φ = 1 := ringEquiv_gf3_eq_one φ
  subst hφ
  have hN : ∀ i c, α (e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c) =
        g * e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) ((a i : GaloisField 3 1) * c) *
          g⁻¹ ∧
      α (e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c) =
        g * e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1)
          ((((a i)⁻¹ : (GaloisField 3 1)ˣ) : GaloisField 3 1) * c) * g⁻¹ := fun i c => h i c
  set ĝ : ModGL .E7 (GaloisField 3 1) :=
    εm (GaloisField 3 1) g * rootDiagUnit .E7 a with hĝ
  obtain ⟨hdx, hdy, -⟩ := root_diagonal_conjugation .E7 (GaloisField 3 1) a
  have hε₁ : ∀ i c, ((εm (GaloisField 3 1)).comp α.toMonoidHom)
      (e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c) =
      ((MulAut.conj ĝ).toMonoidHom.comp (εm (GaloisField 3 1)))
        (e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c) := by
    intro i c
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hN i c).1, map_mul, map_mul, map_inv, εm_xm_single, εm_xm_single, hĝ]
    calc _ = εm (GaloisField 3 1) g * (rootDiagUnit .E7 a * xUnit .E7 (GaloisField 3 1) i c *
          (rootDiagUnit .E7 a)⁻¹) * (εm (GaloisField 3 1) g)⁻¹ := by rw [hdx i c]
      _ = _ := by group
  have hε₂ : ∀ i c, ((εm (GaloisField 3 1)).comp α.toMonoidHom)
      (e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c) =
      ((MulAut.conj ĝ).toMonoidHom.comp (εm (GaloisField 3 1)))
        (e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c) := by
    intro i c
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hN i c).2, map_mul, map_mul, map_inv, εm_xm_neg_single, εm_xm_neg_single, hĝ]
    calc _ = εm (GaloisField 3 1) g * (rootDiagUnit .E7 a * yUnit .E7 (GaloisField 3 1) i c *
          (rootDiagUnit .E7 a)⁻¹) * (εm (GaloisField 3 1) g)⁻¹ := by rw [hdy i c]
      _ = _ := by group
  have hεα : ∀ y, εm (GaloisField 3 1) (α y) = ĝ * εm (GaloisField 3 1) y * ĝ⁻¹ := fun y => by
    have := congrArg (fun φ : M₇ →* ModGL .E7 (GaloisField 3 1) => φ y)
      (eq_of_roots_E7 ((εm (GaloisField 3 1)).comp α.toMonoidHom)
        ((MulAut.conj ĝ).toMonoidHom.comp (εm (GaloisField 3 1)))
        (eq_on_roots_of_simple hS _ _ hε₁ hε₂))
    simpa using this
  have hΓr : ∀ γ ∈ Γ, IsRoot .E7 γ := fun γ hγ =>
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).1 (hΓ γ hγ)
  have hαfix : ∀ γ ∈ Γ, ∀ y ∈ stdRankOne D₇ γ, α y = y := by
    intro γ hγ
    refine fixed_of_central_error α.toMonoidHom (pow3_fund3 (std_mem_fund3 (hΓr γ hγ)))
      (fun y hy => ?_) (fun z hz => yData3_E7'.cop z hz)
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (θ y)⁻¹ * θ (α y) = 1
    rw [hαθ, hfix γ hγ y hy, inv_mul_cancel]
  have hcommΓ : ∀ γ ∈ Γ, ∀ A : SL2 (GaloisField 3 1),
      ĝ * rootSL2 .E7 (GaloisField 3 1) γ A = rootSL2 .E7 (GaloisField 3 1) γ A * ĝ := by
    intro γ hγ A
    have hmem : rootSL2 .E7 (GaloisField 3 1) γ A ∈
        (stdRankOne D₇ γ).map (εm (GaloisField 3 1)) := by
      rw [map_stdRankOne_εm (hΓr γ hγ)]
      exact ⟨A, rfl⟩
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hmem
    have h1 := hεα y
    rw [hαfix γ hγ y hy, hye] at h1
    rw [eq_comm, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  set k := AlgebraicClosure (GaloisField 3 1) with hk
  set ι := algebraMap (GaloisField 3 1) k with hι
  have hpk : CharP k 3 := charP_of_injective_algebraMap ι.injective 3
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k 3]; norm_num
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hkF
  have hĝk : ∀ γ ∈ Γ, ∀ A : SL2 k, Commute (baseChangeGL ι ĝ) (rootSL2 .E7 k γ A) :=
    fun γ hγ => commute_rootSL2_baseChange (Or.inr (Or.inr (Or.inl rfl))) ι h2 γ
      (fun A => hcommΓ γ hγ A)
  have hdiagΓ : ∀ γ ∈ Γ, ∀ c : kˣ, baseChangeGL ι ĝ * rootDiagUnit .E7 (thetaDiag γ c) =
      rootDiagUnit .E7 (thetaDiag γ c) * baseChangeGL ι ĝ := by
    intro γ hγ c
    rw [← rootTorusSL2_eq_thetaDiag_gen (hΓr γ hγ)]
    exact (hĝk γ hγ (HSL c)).eq
  have hspan : ∀ v ∈ Submodule.span ℤ Γ, ∀ c : kˣ,
      baseChangeGL ι ĝ * rootDiagUnit .E7 (thetaDiag v c) =
        rootDiagUnit .E7 (thetaDiag v c) * baseChangeGL ι ĝ := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem γ hγ => exact hdiagΓ γ hγ
    | zero =>
      intro c
      rw [thetaDiag_zero', rootDiagUnit_one, mul_one, one_mul]
    | add v w _ _ hv hw =>
      intro c
      rw [thetaDiag_add', rootDiagUnit_mul]
      exact (Commute.mul_right (hv c : Commute _ _) (hw c : Commute _ _)).eq
    | smul n v _ hv =>
      intro c
      rw [thetaDiag_smul']
      exact hv _
  have hĝG : baseChangeGL ι ĝ ∈ adjointGroup .E7 k := by
    rw [hĝ, map_mul]
    refine mul_mem (baseChangeGL_mem_adjointGroup ι (εm_mem g)) ?_
    rw [baseChangeGL_rootDiagUnit]
    exact parabolicLevi_le_adjointGroup .E7 k (∅ : Set (Fin (Tag.rank .E7)))
      (torusGroup_le_parabolicLevi _ (rootDiagUnit_mem_torusGroup _))
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B := by
    refine ⟨(rootFinset .E7).sup fun σ => (iform l σ).natAbs, fun σ hσ => ?_⟩
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.le_sup (f := fun σ => (iform l σ).natAbs) hσ
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) (2 * B)
  have hmem : baseChangeGL ι ĝ ∈ toralCentralizer .E7 k (thetaDiag l c) := by
    rw [mem_toralCentralizer]
    refine ⟨hĝG, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hspan l hl c).symm
  have hLevi := toralCentralizer_thetaDiag_le_levi (J := ∅) hB
    (fun σ hσ h0 => absurd h0 (hreg σ hσ)) hc hmem
  have hLT : parabolicLevi .E7 k (∅ : Set (Fin (Tag.rank .E7))) = torusGroup .E7 k := by
    have hempty : {g : ModGL .E7 k | ∃ j ∈ (∅ : Set (Fin (Tag.rank .E7))), ∃ c : k,
        g = xUnit .E7 k j c ∨ g = yUnit .E7 k j c} = ∅ := by
      ext; simp
    unfold parabolicLevi
    rw [hempty, Subgroup.closure_empty, sup_bot_eq]
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hLT ▸ hLevi)
  obtain ⟨bĝ, hbĝ⟩ := rational_of_diag_baseChange hb'
  have hεg : εm (GaloisField 3 1) g = rootDiagUnit .E7 (bĝ * a⁻¹) := by
    have : εm (GaloisField 3 1) g = ĝ * (rootDiagUnit .E7 a)⁻¹ := by rw [hĝ]; group
    rw [this, hbĝ, rootDiagUnit_inv, rootDiagUnit_mul]
  have hsimple₁ : ∀ i c, α (e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c) =
      e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) ((bĝ i : GaloisField 3 1) * c) := by
    intro i c
    rw [(hN i c).1, (conj_xm_of_diag hεg i _).1]
    congr 1
    have := (a i).ne_zero
    simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hsimple₂ : ∀ i c, α (e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c) =
      e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1)
        ((((bĝ i)⁻¹ : (GaloisField 3 1)ˣ) : GaloisField 3 1) * c) := by
    intro i c
    rw [(hN i c).2, (conj_xm_of_diag hεg i _).2]
    congr 1
    have := (a i).ne_zero
    have := (bĝ i).ne_zero
    simp only [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, inv_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp
  have hNF : NormalForm (e7Data_valid.xm (GaloisField 3 1)) α.toMonoidHom (1 : M₇) bĝ
      (1 : GaloisField 3 1 ≃+* GaloisField 3 1)
      (1 : Equiv.Perm (Fin (e7Datum (GaloisField 3 1)).rank)) := by
    refine ⟨fun i c => ?_, fun i c => ?_⟩
    · change α (e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) c) =
        1 * e7Data_valid.xm (GaloisField 3 1) (Pi.single i 1) ((bĝ i : GaloisField 3 1) * c) *
          1⁻¹
      rw [hsimple₁ i c, one_mul, inv_one, mul_one]
    · change α (e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1) c) =
        1 * e7Data_valid.xm (GaloisField 3 1) (-Pi.single i 1)
          ((((bĝ i)⁻¹ : (GaloisField 3 1)ˣ) : GaloisField 3 1) * c) * 1⁻¹
      rw [hsimple₂ i c, one_mul, inv_one, mul_one]
  obtain ⟨b, hb⟩ := diag_of_normalForm_trivial hS hNF (one_mem _)
  exact ⟨α, b, hαθ, hb⟩

theorem toralStdE73 : ToralStdE73 := by
  intro Γ l hΓ hl hreg Y _ ψ hψ σ hσ2 hσr k₀ hfix
  have hS := torusSetup_E7 (GaloisField 3 1)
  set θ₁ : M₇ →* Y := ψ.comp (MulAut.conj k₀).toMonoidHom with hθ₁
  have hθ₁ap : ∀ k, θ₁ k = ψ (k₀ * k * k₀⁻¹) := fun k => rfl
  have hrange : ∀ k, ψ k ∈ θ₁.range := fun k => ⟨k₀⁻¹ * k * k₀, by
    rw [hθ₁ap]
    congr 1
    group⟩
  have hσR : ∀ r ∈ θ₁.range, σ r ∈ θ₁.range := by
    rintro r ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hσr (k₀ * k * k₀⁻¹)
    rw [hθ₁ap, ← hk']
    exact hrange k'
  let σR : θ₁.range ≃* θ₁.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : Y) (b : Y)) }
  have hkerθ : θ₁.rangeRestrict.ker ≤ Subgroup.center M₇ := by
    intro y hy
    have h1 : θ₁ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    have hz : k₀ * y * k₀⁻¹ ∈ Subgroup.center M₇ :=
      hψ (MonoidHom.mem_ker.2 (by rwa [hθ₁ap] at h1))
    have hy' : y = k₀ * y * k₀⁻¹ := by
      have := Subgroup.mem_center_iff.1 hz k₀⁻¹
      calc y = k₀⁻¹ * (k₀ * y * k₀⁻¹) * k₀ := by group
        _ = (k₀ * y * k₀⁻¹) * k₀⁻¹ * k₀ := by rw [this]
        _ = k₀ * y * k₀⁻¹ := by group
    rw [hy']
    exact hz
  obtain ⟨α, b, hαθ, hb⟩ := exists_diag_of_fixes_roots3 Γ l hΓ hl hreg θ₁.rangeRestrict
    θ₁.rangeRestrict_surjective hkerθ σR (fun γ hγ y hy => Subtype.ext (hfix γ hγ y hy))
  obtain ⟨v, hv⟩ := fixes_iff_charOf hS (by norm_num : (3 : ℕ) ≠ 2) θ₁.rangeRestrict hkerθ
    (hC_E7 (GaloisField 3 1) _ hkerθ) σR (fun r => Subtype.ext (hσ2 r)) α.toMonoidHom hαθ b hb
  refine ⟨v, fun γ hγ => ⟨?_, ?_⟩⟩
  · intro y hy
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hy
    exact ⟨_, ⟨α s, diag_preserves_rankOne hS (α := α.toMonoidHom) hb hγ s hs, rfl⟩,
      congrArg Subtype.val (hαθ s)⟩
  · unfold charOf
    rw [← hv γ hγ]
    constructor
    · intro h y hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact Subtype.ext (h _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
    · intro h y hy
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hy
      exact congrArg Subtype.val (h _ ⟨s, hs, rfl⟩)

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
