module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSL3Aux
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerStrict
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderParity
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderCommQuasi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15CountBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module Matrix
open scoped MatrixGroups

private theorem m1S_sub_toRepresentation_val {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {N : Subgroup G}
    (SU : Subrepresentation (ρ.comp N.subtype)) (g : ↥N) (x : ↥SU.toSubmodule) :
    ((SU.toRepresentation g x : ↥SU.toSubmodule) : V) = ρ (g : G) (x : V) := by
  have h : SU.toRepresentation g x =
      ⟨(ρ.comp N.subtype) g (x : V), SU.apply_mem_toSubmodule g x.2⟩ :=
    (Subrepresentation.toRepresentation_apply_mk).mpr rfl
  rw [h]
  rfl

private theorem m1B_factorRep_eq_one_iff {K : Type*} [Group K] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} (U U' : Subrepresentation ρ) (k : K) :
    factorRep U U' k = 1 ↔ ∀ x ∈ U'.toSubmodule, ρ k x - x ∈ U.toSubmodule := by
  constructor
  · intro h x hx
    have h1 := LinearMap.congr_fun h (Submodule.Quotient.mk (p := factorSub U U') ⟨x, hx⟩)
    rw [factorRep_mk, Module.End.one_apply, Submodule.Quotient.eq] at h1
    exact h1
  · intro h
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (factorSub U U') w
    rw [factorRep_mk, Module.End.one_apply, Submodule.Quotient.eq]
    exact h x x.2

private theorem m1B_paritySection {G : Type} [Group G] [Finite G]
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    {N L B A : Subgroup G} (hLN : L ≤ N) (hAN : A ≤ N)
    (hAnorm : A ≤ Subgroup.normalizer (L : Set G))
    [CFSG.IsElementaryAbelian 2 ↥A]
    (π₁ : ↥L × ↥B →* ↥N)
    (hπ₁L : ∀ l : ↥L, π₁ (l, 1) = ⟨(l : G), hLN l.2⟩)
    (ρQ : Representation (ZMod 2) ↥N Q)
    {M₀ M₁ : Submodule (ZMod 2) Q}
    (hM₀L : ∀ l : ↥L, ∀ y ∈ M₀, ρQ (π₁ (l, 1)) y ∈ M₀)
    (hM₁L : ∀ l : ↥L, ∀ y ∈ M₁, ρQ (π₁ (l, 1)) y ∈ M₁)
    (hM₀irr : ∀ W : Submodule (ZMod 2) Q, W ≤ M₀ →
      (∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W) → W = ⊥ ∨ W = M₀)
    (hM₁irr : ∀ W : Submodule (ZMod 2) Q, W ≤ M₁ →
      (∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W) → W = ⊥ ∨ W = M₁)
    (hcompl : IsCompl M₀ M₁) (θ : ↥M₀ →+ ↥M₁) (hθ : θ ≠ 0)
    (hθL : ∀ (l : ↥L) (y : ↥M₀),
      ((θ ⟨ρQ (π₁ (l, 1)) y, hM₀L l y y.2⟩ : ↥M₁) : Q) = ρQ (π₁ (l, 1)) (θ y)) :
    ∃ (W : Submodule (ZMod 2) Q) (hWL : ∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W),
      (∀ a (ha : a ∈ A), ∀ y ∈ W, ρQ ⟨a, hAN ha⟩ y ∈ W) ∧
      ∃ ψ : ↥W ≃+ ↥M₀, ∀ (l : ↥L) (y : ↥W),
        (ψ ⟨ρQ (π₁ (l, 1)) y, hWL l y y.2⟩ : Q) = ρQ (π₁ (l, 1)) (ψ y) := by
  have hAeaN : CFSG.IsElementaryAbelian 2 (A.subgroupOf N) :=
    CFSG.IsElementaryAbelian.subgroupOf (p := 2) hAN
  have hA2N : IsPGroup 2 (A.subgroupOf N) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hcoe : ∀ (h : ↥N) (hh : h ∈ L.subgroupOf N),
      h = π₁ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩, 1) := by
    intro h hh
    rw [hπ₁L]
  have hHnorm : A.subgroupOf N ≤ Subgroup.normalizer (L.subgroupOf N : Set ↥N) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAnorm (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  have hH₀ : ∀ h ∈ L.subgroupOf N, ∀ y ∈ M₀, ρQ h y ∈ M₀ := by
    intro h hh y hy
    have h1 := hM₀L ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ y hy
    rwa [← hcoe h hh] at h1
  have hH₁ : ∀ h ∈ L.subgroupOf N, ∀ y ∈ M₁, ρQ h y ∈ M₁ := by
    intro h hh y hy
    have h1 := hM₁L ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ y hy
    rwa [← hcoe h hh] at h1
  have hirr₀ : ∀ W : Submodule (ZMod 2) Q, W ≤ M₀ →
      (∀ h ∈ L.subgroupOf N, ∀ y ∈ W, ρQ h y ∈ W) → W = ⊥ ∨ W = M₀ := by
    intro W hW hWin
    refine hM₀irr W hW fun l y hy => ?_
    have hmem : (⟨(l : G), hLN l.2⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr l.2
    have h1 := hWin _ hmem y hy
    rwa [← hπ₁L l] at h1
  have hirr₁ : ∀ W : Submodule (ZMod 2) Q, W ≤ M₁ →
      (∀ h ∈ L.subgroupOf N, ∀ y ∈ W, ρQ h y ∈ W) → W = ⊥ ∨ W = M₁ := by
    intro W hW hWin
    refine hM₁irr W hW fun l y hy => ?_
    have hmem : (⟨(l : G), hLN l.2⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr l.2
    have h1 := hWin _ hmem y hy
    rwa [← hπ₁L l] at h1
  have hθH : ∀ (h : ↥N) (hh : h ∈ L.subgroupOf N) (y : ↥M₀),
      ((θ ⟨ρQ h y, hH₀ h hh y y.2⟩ : ↥M₁) : Q) = ρQ h (θ y) := by
    intro h hh y
    have h2v : ρQ h y = ρQ (π₁ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩, 1)) y :=
      congrArg (fun z : ↥N => ρQ z y) (hcoe h hh)
    have h2 : (⟨ρQ h y, hH₀ h hh y y.2⟩ : ↥M₀) =
        ⟨ρQ (π₁ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩, 1)) y, hM₀L _ y y.2⟩ :=
      Subtype.ext h2v
    have h1 := hθL ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ y
    rw [h2, h1]
    exact (congrArg (fun z : ↥N => ρQ z ↑(θ y)) (hcoe h hh)).symm
  obtain ⟨W, hWH, hWA, ψ, hψ⟩ := exists_invariant_equiv_of_isCompl ρQ (L.subgroupOf N) (A.subgroupOf N) hA2N
    hHnorm hH₀ hH₁ hirr₀ hirr₁ hcompl θ hθ hθH
  have hWLinv : ∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W := by
    intro l y hy
    have hmem : (⟨(l : G), hLN l.2⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr l.2
    have h1 := hWH _ hmem y hy
    rwa [← hπ₁L l] at h1
  refine ⟨W, hWLinv, ?_, ψ, ?_⟩
  · intro a ha y hy
    exact hWA ⟨a, hAN ha⟩ (Subgroup.mem_subgroupOf.mpr ha) y hy
  · intro l y
    have hmem : (⟨(l : G), hLN l.2⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr l.2
    have h2v : ρQ (π₁ (l, 1)) y = ρQ (⟨(l : G), hLN l.2⟩ : ↥N) y :=
      congrArg (fun z : ↥N => ρQ z y) (hπ₁L l)
    have h2 : (⟨ρQ (π₁ (l, 1)) y, hWLinv l y y.2⟩ : ↥W) =
        ⟨ρQ (⟨(l : G), hLN l.2⟩ : ↥N) y, hWH _ hmem y y.2⟩ := Subtype.ext h2v
    have h1 := hψ _ hmem y
    rw [h2, h1]
    exact (congrArg (fun z : ↥N => ρQ z ↑(ψ y)) (hπ₁L l)).symm

private theorem m1N_factorSub_eq_bot {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    (h0 : U.toSubmodule = ⊥) : factorSub U U' = ⊥ := by
  rw [factorSub, h0, Submodule.comap_bot, Submodule.ker_subtype]

private theorem m1N_toSubmodule_eq_bot {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U : Subrepresentation ρ}
    (h : U = ⊥) : U.toSubmodule = ⊥ := by
  rw [h]; rfl

private theorem m1N_toRepresentation_eq_self_of_factorRep_eq_self
    {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    (hfac : factorSub U U' = ⊥) {k : K}
    (h : ∀ x : U'.toSubmodule ⧸ factorSub U U', factorRep U U' k x = x)
    (y : U'.toSubmodule) : U'.toRepresentation k y = y := by
  have hq := congrArg ((factorSub U U').quotEquivOfEqBot hfac)
    (h (Submodule.Quotient.mk y))
  rw [factorRep_mk] at hq
  simpa [Submodule.quotEquivOfEqBot_apply_mk] using hq

private theorem m1N_submodule_eq_bot_or_eq_of_covBy
    {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) K V} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hVs : IsCompositionSeries r Vs) {i : Fin r} {W : Submodule (ZMod 2) V}
    (hWle : W ≤ (Vs i.succ).toSubmodule)
    (hWinv : ∀ k : K, ∀ y ∈ W, ρ k y ∈ W)
    (hbot : Vs i.castSucc = ⊥) :
    W = ⊥ ∨ W = (Vs i.succ).toSubmodule := by
  let X : Subrepresentation ρ := ⟨W, hWinv⟩
  have hXle : X ≤ Vs i.succ := by
    intro y hy
    exact hWle hy
  have hUX : Vs i.castSucc ≤ X := by
    rw [hbot]
    exact bot_le
  rcases eq_or_lt_of_le hUX with heq | hlt
  · left
    have hXbot : X = ⊥ := heq.symm.trans hbot
    have hsub := congrArg Subrepresentation.toSubmodule hXbot
    have hXW : X.toSubmodule = W := rfl
    have hbot' : ((⊥ : Subrepresentation ρ).toSubmodule) = (⊥ : Submodule (ZMod 2) V) := rfl
    rw [hXW, hbot'] at hsub
    exact hsub
  · right
    have hXeq : X = Vs i.succ := eq_of_le_of_not_lt hXle ((hVs.covBy i).2 hlt)
    have hsub := congrArg Subrepresentation.toSubmodule hXeq
    have hXW : X.toSubmodule = W := rfl
    rw [hXW] at hsub
    exact hsub

private theorem m1N_prod_invariant
    {L B V : Type*} [Group L] [Group B] [AddCommGroup V] [Module (ZMod 2) V]
    {σ : Representation (ZMod 2) (L × B) V} {W : Submodule (ZMod 2) V}
    {P : Subgroup (L × B)}
    (hP : ∀ b : B, ((1 : L), b) ∈ P)
    (hfix : ∀ p ∈ P, ∀ y ∈ W, σ p y = y)
    (hWL : ∀ l : L, ∀ y ∈ W, σ (l, 1) y ∈ W) :
    ∀ k : L × B, ∀ y ∈ W, σ k y ∈ W := by
  rintro ⟨l, b⟩ y hy
  have hk : ((l, b) : L × B) = (l, 1) * (1, b) := by ext <;> simp
  have hyb : σ ((1 : L), b) y = y := hfix ((1 : L), b) (hP b) y hy
  rw [hk, map_mul, Module.End.mul_apply, hyb]
  exact hWL l y hy


private theorem m1N_succ_ne_bot_of_covBy {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    (h : U ⋖ U') (h0 : U = ⊥) : U'.toSubmodule ≠ ⊥ := by
  intro hbot
  have hsub : U.toSubmodule = U'.toSubmodule := by
    rw [m1N_toSubmodule_eq_bot h0, hbot]
  exact h.1.ne (Subrepresentation.ext hsub)

private theorem m1N_subtype_eq_of_quot_mk_eq {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    (hfac : factorSub U U' = ⊥) {x y : U'.toSubmodule}
    (h : (Submodule.Quotient.mk x : U'.toSubmodule ⧸ factorSub U U') =
      Submodule.Quotient.mk y) : x = y := by
  have hq := congrArg ((factorSub U U').quotEquivOfEqBot hfac) h
  simpa [Submodule.quotEquivOfEqBot_apply_mk] using hq

private theorem m1N_exists_phi0 {K V F : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Field F] {ρ : Representation (ZMod 2) K V}
    {U U' : Subrepresentation ρ} {M : Submodule (ZMod 2) V}
    (hM : M = U'.toSubmodule) (hfac : factorSub U U' = ⊥)
    (φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (Fin 3 → F)) :
    ∃ φ₀ : ↥M ≃+ (Fin 3 → F), ∀ x : ↥M,
      φ₀ x = φ (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule)) := by
  let eM : ↥M ≃+ U'.toSubmodule :=
    { toFun := fun x => ⟨x.1, hM ▸ x.2⟩
      invFun := fun y => ⟨y.1, hM.symm ▸ y.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl
      map_add' := by intro x y; ext; rfl }
  refine ⟨eM.trans (((factorSub U U').quotEquivOfEqBot hfac).symm.toAddEquiv.trans φ), ?_⟩
  intro x
  change φ (((factorSub U U').quotEquivOfEqBot hfac).symm (eM x)) =
    φ (Submodule.Quotient.mk (eM x))
  rw [Submodule.quotEquivOfEqBot_symm_apply]

private theorem m1N_factorRep_mk_ofEq {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    {M : Submodule (ZMod 2) V} (hM : M = U'.toSubmodule) (k : K) (x : ↥M)
    (hx : ρ k x.1 ∈ M) :
    Submodule.Quotient.mk (⟨ρ k x.1, hM ▸ hx⟩ : U'.toSubmodule) =
      factorRep U U' k (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule)) := by
  rw [factorRep_mk]
  congr 1

private theorem m1N_factorRep_self_imp {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ}
    (hfac : factorSub U U' = ⊥) {k : K} {x : U'.toSubmodule}
    (h : factorRep U U' k (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) :
    U'.toRepresentation k x = x := by
  rw [factorRep_mk] at h
  exact m1N_subtype_eq_of_quot_mk_eq hfac h


private theorem m1N_mem_nontrivialFactors
    {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) K V} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hVs : IsCompositionSeries r Vs) {i : Fin r}
    (hfac : factorSub (Vs i.castSucc) (Vs i.succ) = ⊥)
    (hbot : Vs i.castSucc = ⊥) {L : Type*} [Group L] (π : L →* K)
    (hzero : ∀ q : V, (∀ l : L, ρ (π l) q = q) → q = 0) :
    i ∈ nontrivialFactors Vs := by
  rw [mem_nontrivialFactors]
  by_contra hall
  push Not at hall
  have hne : (Vs i.succ).toSubmodule ≠ ⊥ := m1N_succ_ne_bot_of_covBy (hVs.covBy i) hbot
  obtain ⟨y, hyM, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hyfix : ∀ l : L, ρ (π l) y = y := by
    intro l
    have hq : factorRep (Vs i.castSucc) (Vs i.succ) (π l)
        (Submodule.Quotient.mk (⟨y, hyM⟩ : ↥(Vs i.succ).toSubmodule)) =
        Submodule.Quotient.mk (⟨y, hyM⟩ : ↥(Vs i.succ).toSubmodule) := by
      have h1 := LinearMap.congr_fun (hall (π l))
        (Submodule.Quotient.mk (⟨y, hyM⟩ : ↥(Vs i.succ).toSubmodule))
      rwa [Module.End.one_apply] at h1
    exact congrArg Subtype.val (m1N_factorRep_self_imp hfac hq)
  exact hyne (hzero y hyfix)

private theorem m1N_phi0_equivariant
    {K V F : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V] [Field F]
    {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ} {M : Submodule (ZMod 2) V}
    (hM : M = U'.toSubmodule) (k : K) (f : K →* SL(3, F))
    (φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (Fin 3 → F))
    (hφ : ∀ x, φ (factorRep U U' k x) = (f k : Matrix (Fin 3) (Fin 3) F) *ᵥ φ x)
    (hinv : ∀ x ∈ M, ρ k x ∈ M) (φ₀ : ↥M ≃+ (Fin 3 → F))
    (hφ₀ : ∀ x, φ₀ x = φ (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule))) :
    ∀ x : ↥M, φ₀ ⟨ρ k x.1, hinv x.1 x.2⟩ =
      (f k : Matrix (Fin 3) (Fin 3) F) *ᵥ φ₀ x := by
  intro x
  rw [hφ₀, hφ₀]
  change φ (Submodule.Quotient.mk (⟨ρ k x.1, hM ▸ hinv x.1 x.2⟩ : U'.toSubmodule)) =
    (f k : Matrix (Fin 3) (Fin 3) F) *ᵥ
      φ (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule))
  rw [m1N_factorRep_mk_ofEq hM k x (hinv x.1 x.2)]
  exact hφ _


private theorem m1N_phi0_equivariant_dual
    {K V F : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V] [Field F]
    {ρ : Representation (ZMod 2) K V} {U U' : Subrepresentation ρ} {M : Submodule (ZMod 2) V}
    (hM : M = U'.toSubmodule) (k : K) (g : K →* SL(3, F))
    (φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (Fin 3 → F))
    (hφ : ∀ x, φ (factorRep U U' k x) = dualMat (g k) *ᵥ φ x)
    (hinv : ∀ x ∈ M, ρ k x ∈ M) (φ₀ : ↥M ≃+ (Fin 3 → F))
    (hφ₀ : ∀ x, φ₀ x = φ (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule))) :
    ∀ x : ↥M, φ₀ ⟨ρ k x.1, hinv x.1 x.2⟩ =
      dualMat (g k) *ᵥ φ₀ x := by
  intro x
  rw [hφ₀, hφ₀]
  change φ (Submodule.Quotient.mk (⟨ρ k x.1, hM ▸ hinv x.1 x.2⟩ : U'.toSubmodule)) =
    dualMat (g k) *ᵥ
      φ (Submodule.Quotient.mk (⟨x.1, hM ▸ x.2⟩ : U'.toSubmodule))
  rw [m1N_factorRep_mk_ofEq hM k x (hinv x.1 x.2)]
  exact hφ _



private theorem m1N_mem_map_comap_subtype {V Q : Type*} [AddCommGroup V] [AddCommGroup Q]
    [Module (ZMod 2) V] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q} {v : V} :
    v ∈ (W'.comap q).map (Submodule.subtype U) ↔
      ∃ u : ↥U, (u : V) = v ∧ q u ∈ W' := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl, hu⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u, hu, rfl⟩

private theorem m1N_le_map_comap_subtype {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q} :
    (W'.comap q).map U.subtype ≤ U := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

private theorem m1N_mem_comap_of_mem_map {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q}
    {v : ↥((W'.comap q).map U.subtype)} :
    q ⟨v.1, m1N_le_map_comap_subtype v.2⟩ ∈ W' := by
  obtain ⟨u, huv, hu⟩ := m1N_mem_map_comap_subtype.mp v.2
  have hsub : (⟨v.1, m1N_le_map_comap_subtype v.2⟩ : ↥U) = u := Subtype.ext huv.symm
  rw [hsub]
  exact hu

private noncomputable def m1N_liftMap {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] (U : Submodule (ZMod 2) V)
    (q : ↥U →ₗ[ZMod 2] Q) (W' : Submodule (ZMod 2) Q) :
    ↥((W'.comap q).map U.subtype) →+ ↥W' where
  toFun v := ⟨q ⟨v.1, m1N_le_map_comap_subtype v.2⟩, m1N_mem_comap_of_mem_map (v := v)⟩
  map_zero' := by
    apply Subtype.ext
    change q (0 : ↥U) = 0
    exact map_zero q
  map_add' := by
    intro v w
    apply Subtype.ext
    change q ((⟨v.1, m1N_le_map_comap_subtype v.2⟩ : ↥U) +
      ⟨w.1, m1N_le_map_comap_subtype w.2⟩) =
      q ⟨v.1, m1N_le_map_comap_subtype v.2⟩ +
        q ⟨w.1, m1N_le_map_comap_subtype w.2⟩
    exact map_add q _ _

private theorem m1N_liftMap_mk {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q} (u : ↥U) (hu : q u ∈ W') :
    m1N_liftMap U q W' ⟨(u : V), ⟨u, hu, rfl⟩⟩ = ⟨q u, hu⟩ := by
  unfold m1N_liftMap
  apply Subtype.ext
  change q (⟨(u : V), _⟩ : ↥U) = q u
  congr 1


private theorem m1N_lift_invariant {K V Q : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q]
    {U : Submodule (ZMod 2) V} {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q}
    {σ : Representation (ZMod 2) K V} {τ : Representation (ZMod 2) K Q}
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U)
    (hq : ∀ k (u : ↥U), q ⟨σ k u.1, hU k u.1 u.2⟩ = τ k (q u))
    (hW' : ∀ k, ∀ y ∈ W', τ k y ∈ W') :
    ∀ k, ∀ v ∈ (W'.comap q).map U.subtype, σ k v ∈ (W'.comap q).map U.subtype := by
  intro k v hv
  obtain ⟨u, huv, hu⟩ := (m1N_mem_map_comap_subtype (q := q) (W' := W')).mp hv
  refine (m1N_mem_map_comap_subtype (q := q) (W' := W')).mpr
    ⟨⟨σ k u.1, hU k u.1 u.2⟩, ?_, ?_⟩
  · exact congrArg (σ k) huv
  · rw [hq k u]
    exact hW' k _ hu

private theorem m1N_liftMap_natural {K V Q : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q]
    {U : Submodule (ZMod 2) V} {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q}
    {σ : Representation (ZMod 2) K V} {τ : Representation (ZMod 2) K Q}
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U)
    (hq : ∀ k (u : ↥U), q ⟨σ k u.1, hU k u.1 u.2⟩ = τ k (q u))
    (hW' : ∀ k, ∀ y ∈ W', τ k y ∈ W') (k : K)
    (v : ↥((W'.comap q).map U.subtype)) :
    m1N_liftMap U q W'
        ⟨σ k v.1, m1N_lift_invariant hU hq hW' k v.1 v.2⟩ =
      ⟨τ k (m1N_liftMap U q W' v),
        hW' k _ (m1N_liftMap U q W' v).2⟩ := by
  unfold m1N_liftMap
  apply Subtype.ext
  exact hq k ⟨v.1, m1N_le_map_comap_subtype v.2⟩

private theorem m1N_liftMap_val {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q}
    (v : ↥((W'.comap q).map U.subtype)) :
    (m1N_liftMap U q W' v : Q) = q ⟨v.1, m1N_le_map_comap_subtype v.2⟩ := by
  unfold m1N_liftMap
  rfl

private theorem m1N_liftMap_surjective_of_surjective {V Q : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup Q] [Module (ZMod 2) Q] {U : Submodule (ZMod 2) V}
    {q : ↥U →ₗ[ZMod 2] Q} {W' : Submodule (ZMod 2) Q} (hq : Function.Surjective q) :
    Function.Surjective (m1N_liftMap U q W') := by
  intro y
  obtain ⟨u, hu⟩ := hq (y : Q)
  have hmem : q u ∈ W' := by rw [hu]; exact y.2
  refine ⟨⟨(u : V), ⟨u, hmem, rfl⟩⟩, ?_⟩
  rw [m1N_liftMap_mk (U := U) (q := q) (W' := W') u hmem]
  exact Subtype.ext hu


private theorem m1N_lift_final {G V F : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Field F] (ρ : Representation (ZMod 2) G V) (N : Subgroup G)
    (SU : Subrepresentation (ρ.comp N.subtype))
    (SC : Subrepresentation SU.toRepresentation)
    (W' : Submodule (ZMod 2) (↥SU.toSubmodule ⧸ SC.toSubmodule))
    {L : Subgroup G} (iL : ↥L →* ↥N) (hiL : ∀ l : ↥L, (iL l : G) = l)
    {A : Subgroup G} (iA : ↥A →* ↥N) (hiA : ∀ a : ↥A, (iA a : G) = a)
    (hW'L : ∀ l : ↥L, ∀ y ∈ W', SC.quotient (iL l) y ∈ W')
    (hW'A : ∀ a : ↥A, ∀ y ∈ W', SC.quotient (iA a) y ∈ W')
    (M₀ : Submodule (ZMod 2) (↥SU.toSubmodule ⧸ SC.toSubmodule))
    (hM₀L : ∀ l : ↥L, ∀ y ∈ M₀, SC.quotient (iL l) y ∈ M₀)
    (Mat : ↥L →* GL (Fin 3) F) (φ₀ : ↥M₀ ≃+ (Fin 3 → F))
    (hφ₀ : ∀ (l : ↥L) (y : ↥M₀),
      φ₀ ⟨SC.quotient (iL l) y, hM₀L l y y.2⟩ =
        (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ φ₀ y)
    (ψ' : ↥W' ≃+ ↥M₀)
    (hψ' : ∀ (l : ↥L) (y : ↥W'),
      (ψ' ⟨SC.quotient (iL l) y, hW'L l y y.2⟩ :
        ↥SU.toSubmodule ⧸ SC.toSubmodule) = SC.quotient (iL l) (ψ' y))
    (hC : ∀ u : ↥SU.toSubmodule,
      u ∈ SC.toSubmodule ↔ ∀ l ∈ L, ρ l u.1 = u.1) :
    ∃ (W : Submodule (ZMod 2) V) (hWL : ∀ l ∈ L, ∀ v ∈ W, ρ l v ∈ W),
      (∀ a ∈ A, ∀ v ∈ W, ρ a v ∈ W) ∧
      ∃ p : ↥W →+ (Fin 3 → F), Function.Surjective p ∧
        (∀ (l : ↥L) (v : ↥W),
          p ⟨ρ l v, hWL l l.2 v v.2⟩ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ p v) ∧
        ∀ v : ↥W, p v = 0 ↔ ∀ l ∈ L, ρ l v = v := by
  let W : Submodule (ZMod 2) V := (W'.comap SC.toSubmodule.mkQ).map SU.toSubmodule.subtype
  have hWmem : ∀ v : V, v ∈ W ↔ ∃ u : ↥SU.toSubmodule, (u : V) = v ∧
      (Submodule.Quotient.mk u : ↥SU.toSubmodule ⧸ SC.toSubmodule) ∈ W' := by
    intro v
    exact m1N_mem_map_comap_subtype
  have hWsubU : W ≤ SU.toSubmodule := by
    intro v hv
    obtain ⟨u, rfl, -⟩ := (hWmem v).mp hv
    exact u.2
  have hmemW : ∀ v : ↥W,
      (Submodule.Quotient.mk (⟨v.1, hWsubU v.2⟩ : ↥SU.toSubmodule) :
        ↥SU.toSubmodule ⧸ SC.toSubmodule) ∈ W' := by
    intro v
    obtain ⟨u, huv, hu⟩ := (hWmem v.1).mp v.2
    have hclass : (Submodule.Quotient.mk (⟨v.1, hWsubU v.2⟩ : ↥SU.toSubmodule) :
        ↥SU.toSubmodule ⧸ SC.toSubmodule) = Submodule.Quotient.mk u := by
      congr 1
      exact Subtype.ext huv.symm
    rwa [hclass]
  have hWL : ∀ l ∈ L, ∀ v ∈ W, ρ l v ∈ W := by
    intro l hl v hv
    obtain ⟨u, rfl, hu⟩ := (hWmem v).mp hv
    refine (hWmem (ρ l u.1)).mpr
      ⟨⟨ρ (iL ⟨l, hl⟩) u.1, SU.apply_mem_toSubmodule (iL ⟨l, hl⟩) u.2⟩, ?_, ?_⟩
    · exact congrArg (fun g : G => ρ g u.1) (hiL ⟨l, hl⟩)
    · have h1 : (Submodule.Quotient.mk
          (⟨ρ (iL ⟨l, hl⟩) u.1,
            SU.apply_mem_toSubmodule (iL ⟨l, hl⟩) u.2⟩ : ↥SU.toSubmodule) :
          ↥SU.toSubmodule ⧸ SC.toSubmodule) =
          SC.quotient (iL ⟨l, hl⟩) (Submodule.Quotient.mk u) :=
        (Subrepresentation.quotient_apply_mk SC (iL ⟨l, hl⟩) u).symm
      rw [h1]
      exact hW'L ⟨l, hl⟩ _ hu
  have hWA : ∀ a ∈ A, ∀ v ∈ W, ρ a v ∈ W := by
    intro a ha v hv
    obtain ⟨u, rfl, hu⟩ := (hWmem v).mp hv
    refine (hWmem (ρ a u.1)).mpr
      ⟨⟨ρ (iA ⟨a, ha⟩) u.1, SU.apply_mem_toSubmodule (iA ⟨a, ha⟩) u.2⟩, ?_, ?_⟩
    · exact congrArg (fun g : G => ρ g u.1) (hiA ⟨a, ha⟩)
    · have h1 : (Submodule.Quotient.mk
          (⟨ρ (iA ⟨a, ha⟩) u.1,
            SU.apply_mem_toSubmodule (iA ⟨a, ha⟩) u.2⟩ : ↥SU.toSubmodule) :
          ↥SU.toSubmodule ⧸ SC.toSubmodule) =
          SC.quotient (iA ⟨a, ha⟩) (Submodule.Quotient.mk u) :=
        (Subrepresentation.quotient_apply_mk SC (iA ⟨a, ha⟩) u).symm
      rw [h1]
      exact hW'A ⟨a, ha⟩ _ hu
  let toW' : ↥W →+ ↥W' := m1N_liftMap SU.toSubmodule SC.toSubmodule.mkQ W'
  refine ⟨W, hWL, hWA, ?_⟩
  let p : ↥W →+ (Fin 3 → F) :=
    φ₀.toAddMonoidHom.comp (ψ'.toAddMonoidHom.comp toW')
  have hp : Function.Surjective p := by
    have hq : Function.Surjective (SC.toSubmodule.mkQ :
      ↥SU.toSubmodule →ₗ[ZMod 2] (↥SU.toSubmodule ⧸ SC.toSubmodule)) :=
      Submodule.mkQ_surjective SC.toSubmodule
    have hcomp : Function.Surjective (fun v : ↥W => φ₀ (ψ' (toW' v))) :=
      φ₀.surjective.comp (ψ'.surjective.comp
        (m1N_liftMap_surjective_of_surjective (U := SU.toSubmodule)
          (q := SC.toSubmodule.mkQ) (W' := W') hq))
    change Function.Surjective (fun v : ↥W => φ₀ (ψ' (toW' v)))
    exact hcomp
  have hpL : ∀ (l : ↥L) (v : ↥W),
      p ⟨ρ l v, hWL l l.2 v v.2⟩ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ p v := by
    intro l v
    have hqA : ∀ (k : ↥L) (u : ↥SU.toSubmodule),
        SC.toSubmodule.mkQ ⟨((ρ.comp N.subtype).comp iL) k u.1,
          SU.apply_mem_toSubmodule (iL k) u.2⟩ =
          (SC.quotient.comp iL) k (SC.toSubmodule.mkQ u) := by
      intro k u
      exact (Subrepresentation.quotient_apply_mk SC (iL k) u).symm
    have hstep := m1N_liftMap_natural
      (σ := (ρ.comp N.subtype).comp iL) (τ := SC.quotient.comp iL)
      (hU := fun k u hu => SU.apply_mem_toSubmodule (iL k) hu)
      (hq := hqA)
      (hW' := fun k y hy => hW'L k y hy) l v
    have hinv : ρ (iL l) v.1 ∈ W := by
      rw [hiL l]
      exact hWL l l.2 v v.2
    have hstep' : toW' ⟨ρ (iL l) v.1, hinv⟩ =
        ⟨SC.quotient (iL l) (toW' v), hW'L l (toW' v) (toW' v).2⟩ := by
      simpa using hstep
    have hElemL : (⟨ρ l v, hWL l l.2 v v.2⟩ : ↥W) =
        ⟨ρ (iL l) v.1, hinv⟩ := by
      apply Subtype.ext
      exact (congrArg (fun g : G => ρ g v.1) (hiL l)).symm
    rw [hElemL]
    have hψ'sub : ψ' ⟨SC.quotient (iL l) (toW' v), hW'L l (toW' v) (toW' v).2⟩ =
        ⟨SC.quotient (iL l) (ψ' (toW' v)),
          hM₀L l (ψ' (toW' v)) (ψ' (toW' v)).2⟩ := by
      apply Subtype.ext
      exact hψ' l (toW' v)
    calc p ⟨ρ (iL l) v.1, hinv⟩
        = φ₀ (ψ' (toW' ⟨ρ (iL l) v.1, hinv⟩)) := rfl
      _ = φ₀ (ψ' ⟨SC.quotient (iL l) (toW' v), hW'L l (toW' v) (toW' v).2⟩) := by
          rw [hstep']
      _ = φ₀ ⟨SC.quotient (iL l) (ψ' (toW' v)),
            hM₀L l (ψ' (toW' v)) (ψ' (toW' v)).2⟩ := by rw [hψ'sub]
      _ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ φ₀ (ψ' (toW' v)) :=
          hφ₀ l (ψ' (toW' v))
      _ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ p v := rfl
  have hpker : ∀ v : ↥W, p v = 0 ↔ ∀ l ∈ L, ρ l v = v := by
    intro v
    have htoW : toW' v = 0 ↔
        (⟨v.1, hWsubU v.2⟩ : ↥SU.toSubmodule) ∈ SC.toSubmodule := by
      have h1 : toW' v = 0 ↔
          (Submodule.Quotient.mk (⟨v.1, hWsubU v.2⟩ : ↥SU.toSubmodule) :
            ↥SU.toSubmodule ⧸ SC.toSubmodule) = 0 := by
        constructor
        · intro h
          have hv := congrArg Subtype.val h
          rw [m1N_liftMap_val] at hv
          exact hv
        · intro h
          apply Subtype.ext
          rw [m1N_liftMap_val]
          exact h
      rw [h1]
      exact Submodule.Quotient.mk_eq_zero _
    calc p v = 0
        ↔ ψ' (toW' v) = 0 := by simp [p]
      _ ↔ toW' v = 0 := AddEquiv.map_eq_zero_iff ψ'
      _ ↔ (⟨v.1, hWsubU v.2⟩ : ↥SU.toSubmodule) ∈ SC.toSubmodule := htoW
      _ ↔ ∀ l ∈ L, ρ l v.1 = v.1 := hC ⟨v.1, hWsubU v.2⟩
  exact ⟨p, hp, hpL, hpker⟩

section FactorTriv

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V}

private theorem m1T_exists_quotient_equiv {M₀ : Submodule (ZMod 2) V}
    {U₀ U₁ U₂ : Subrepresentation ρ} (h₀ : U₀.toSubmodule = ⊥) (h₂ : U₂.toSubmodule = ⊤)
    (h₁ : U₁.toSubmodule = M₀)
    (φ : (U₁.toSubmodule ⧸ factorSub U₀ U₁) ≃+ (U₂.toSubmodule ⧸ factorSub U₁ U₂))
    (hφ : ∀ k x, φ (factorRep U₀ U₁ k x) = factorRep U₁ U₂ k (φ x))
    (hM₀ : ∀ k, ∀ y ∈ M₀, ρ k y ∈ M₀) :
    ∃ Φ : ↥M₀ ≃+ (V ⧸ M₀),
      ∀ (k : K) (y : ↥M₀), Φ ⟨ρ k (y : V), hM₀ k y y.2⟩ =
        (Submodule.mapQ M₀ M₀ (ρ k) (fun y hy => hM₀ k y hy)) (Φ y) := by
  classical
  have hker : factorSub U₀ U₁ = ⊥ := by
    rw [factorSub, h₀, Submodule.comap_bot, Submodule.ker_subtype]
  let mk₀ : ↥M₀ →+ (U₁.toSubmodule ⧸ factorSub U₀ U₁) :=
    (Submodule.mkQ (factorSub U₀ U₁)).toAddMonoidHom.comp
      (Submodule.inclusion (show M₀ ≤ U₁.toSubmodule by rw [h₁])).toAddMonoidHom
  have mk₀_apply : ∀ y : ↥M₀, mk₀ y =
      Submodule.Quotient.mk (p := factorSub U₀ U₁)
        (Submodule.inclusion (show M₀ ≤ U₁.toSubmodule by rw [h₁]) y) := fun y => rfl
  have mk₀_inj : Function.Injective mk₀ := by
    intro x y hxy
    have h1 : Submodule.inclusion (show M₀ ≤ U₁.toSubmodule by rw [h₁]) x =
        Submodule.inclusion (show M₀ ≤ U₁.toSubmodule by rw [h₁]) y := by
      have h := (Submodule.Quotient.eq (factorSub U₀ U₁)).mp hxy
      rwa [hker, Submodule.mem_bot, sub_eq_zero] at h
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have mk₀_surj : Function.Surjective mk₀ := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (factorSub U₀ U₁) z
    refine ⟨⟨(x : V), by rw [← h₁]; exact x.2⟩, ?_⟩
    rw [mk₀_apply]
    congr 1
  let e₂ : (U₂.toSubmodule ⧸ factorSub U₁ U₂) →+ (V ⧸ M₀) :=
    (Submodule.mapQ (factorSub U₁ U₂) M₀ U₂.toSubmodule.subtype (by rw [factorSub, h₁])).toAddMonoidHom
  have e₂_apply : ∀ x : ↥U₂.toSubmodule, e₂ (Submodule.Quotient.mk (p := factorSub U₁ U₂) x) =
      Submodule.Quotient.mk (p := M₀) (x : V) := by
    intro x
    exact Submodule.mapQ_apply (p := factorSub U₁ U₂) (q := M₀) (f := U₂.toSubmodule.subtype)
      (h := by rw [factorSub, h₁]) x
  have e₂_inj : Function.Injective e₂ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (factorSub U₁ U₂) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (factorSub U₁ U₂) b
    rw [e₂_apply, e₂_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq, factorSub, h₁]
    show ((x - y : ↥U₂.toSubmodule) : V) ∈ M₀
    simpa using hab
  have e₂_surj : Function.Surjective e₂ := by
    intro z
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective M₀ z
    refine ⟨Submodule.Quotient.mk (p := factorSub U₁ U₂) ⟨v, ?_⟩, ?_⟩
    · rw [h₂]; exact Submodule.mem_top
    · rw [e₂_apply]
  let Φ₀ : ↥M₀ →+ (V ⧸ M₀) := e₂.comp (φ.toAddMonoidHom.comp mk₀)
  have Φ₀_apply : ∀ y : ↥M₀, Φ₀ y = e₂ (φ (mk₀ y)) := fun y => rfl
  have Φ₀_inj : Function.Injective Φ₀ := fun x y h => mk₀_inj (φ.injective (e₂_inj h))
  have Φ₀_surj : Function.Surjective Φ₀ := by
    intro z
    obtain ⟨a, rfl⟩ := e₂_surj z
    obtain ⟨b, rfl⟩ := φ.surjective a
    obtain ⟨y, rfl⟩ := mk₀_surj b
    exact ⟨y, rfl⟩
  let e : ↥M₀ ≃ (V ⧸ M₀) := Equiv.ofBijective Φ₀ ⟨Φ₀_inj, Φ₀_surj⟩
  have he : ∀ y : ↥M₀, e y = Φ₀ y := fun y => rfl
  refine ⟨⟨e, fun a b => Φ₀.map_add a b⟩, ?_⟩
  intro k y
  show Φ₀ ⟨ρ k (y : V), hM₀ k y y.2⟩ =
    (Submodule.mapQ M₀ M₀ (ρ k) (fun y hy => hM₀ k y hy)) (Φ₀ y)
  have hmk : mk₀ ⟨ρ k (y : V), hM₀ k y y.2⟩ = factorRep U₀ U₁ k (mk₀ y) := by
    have hy : mk₀ y = (Submodule.Quotient.mk (p := factorSub U₀ U₁)
        (Submodule.inclusion (show M₀ ≤ U₁.toSubmodule by rw [h₁]) y)) := mk₀_apply y
    rw [hy, factorRep_mk, mk₀_apply]
    congr 1
  have hstep : e₂ (factorRep U₁ U₂ k (φ (mk₀ y))) =
      (Submodule.mapQ M₀ M₀ (ρ k) (fun y hy => hM₀ k y hy)) (e₂ (φ (mk₀ y))) := by
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective (factorSub U₁ U₂) (φ (mk₀ y))
    rw [← hz, factorRep_mk, e₂_apply, e₂_apply, Submodule.mapQ_apply]
    rfl
  calc Φ₀ ⟨ρ k (y : V), hM₀ k y y.2⟩
      = e₂ (φ (mk₀ ⟨ρ k (y : V), hM₀ k y y.2⟩)) := rfl
    _ = e₂ (φ (factorRep U₀ U₁ k (mk₀ y))) := by rw [hmk]
    _ = e₂ (factorRep U₁ U₂ k (φ (mk₀ y))) := by rw [hφ]
    _ = (Submodule.mapQ M₀ M₀ (ρ k) (fun y hy => hM₀ k y hy)) (e₂ (φ (mk₀ y))) := hstep
    _ = (Submodule.mapQ M₀ M₀ (ρ k) (fun y hy => hM₀ k y hy)) (Φ₀ y) := rfl

private theorem m1T_factorSub_bot {U U' : Subrepresentation ρ} (h : U.toSubmodule = ⊥) :
    factorSub U U' = ⊥ := by
  rw [factorSub, h, Submodule.comap_bot, Submodule.ker_subtype]

private theorem m1T_toRepresentation_eq_one_of_factorRep_eq_one {U U' : Subrepresentation ρ}
    (hU : U.toSubmodule = ⊥) {k : K} (h : factorRep U U' k = 1) :
    U'.toRepresentation k = 1 := by
  have hker : factorSub U U' = ⊥ := m1T_factorSub_bot hU
  refine LinearMap.ext fun x => ?_
  have hx : (Submodule.Quotient.mk (p := factorSub U U') ((U'.toRepresentation k) x)) =
      (Submodule.Quotient.mk (p := factorSub U U') x) := by
    have h1 := LinearMap.congr_fun h (Submodule.Quotient.mk (p := factorSub U U') x)
    simpa [factorRep_mk] using h1
  have hx' : (U'.toRepresentation k) x - x ∈ factorSub U U' := (Submodule.Quotient.eq _).mp hx
  rw [hker, Submodule.mem_bot, sub_eq_zero] at hx'
  exact hx'

private theorem m1T_quotient_eq_of_factorRep_top_eq_one (U : Subrepresentation ρ) (k : K)
    (h : factorRep U ⊤ k = 1) (x : V) :
    (Submodule.Quotient.mk (p := U.toSubmodule) (ρ k x)) =
      (Submodule.Quotient.mk (p := U.toSubmodule) x) := by
  rw [Submodule.Quotient.eq]
  have hx := LinearMap.congr_fun h
    (Submodule.Quotient.mk (p := factorSub U ⊤) (⟨x, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) V)))
  rw [factorRep_mk, Module.End.one_apply] at hx
  have hx1 : (((⊤ : Subrepresentation ρ).toRepresentation k) ⟨x, Submodule.mem_top⟩ -
      (⟨x, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) V))) ∈ factorSub U ⊤ :=
    (Submodule.Quotient.eq _).mp hx
  have hx2 : ((↑(((⊤ : Subrepresentation ρ).toRepresentation k) ⟨x, Submodule.mem_top⟩) : V) - x) ∈
      U.toSubmodule := by
    have h := hx1
    rw [factorSub, Submodule.mem_comap] at h
    simpa using h
  exact hx2

end FactorTriv

section Theta

variable {K : Type*} [Group K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private theorem m1T_quotientEquivOfIsCompl_apply_mk (σ : Representation (ZMod 2) K E)
    {M₀ M₁ : Submodule (ZMod 2) E} (h : IsCompl M₀ M₁)
    (hM₀ : ∀ k, M₀ ≤ Submodule.comap (σ k) M₀) (hM₁ : ∀ k, ∀ y ∈ M₁, σ k y ∈ M₁)
    (k : K) (x : E) :
    (Submodule.quotientEquivOfIsCompl M₀ M₁ h) (Submodule.Quotient.mk (σ k x)) =
      ⟨σ k (((Submodule.quotientEquivOfIsCompl M₀ M₁ h)
          (Submodule.Quotient.mk x) : ↥M₁) : E),
        hM₁ k _ ((Submodule.quotientEquivOfIsCompl M₀ M₁ h)
          (Submodule.Quotient.mk x)).2⟩ := by
  let e := Submodule.quotientEquivOfIsCompl M₀ M₁ h
  have hkey : (Submodule.Quotient.mk (p := M₀) (σ k x)) =
      (Submodule.Quotient.mk (p := M₀) (σ k ((e (Submodule.Quotient.mk x) : ↥M₁) : E))) := by
    rw [Submodule.Quotient.eq, ← map_sub]
    refine hM₀ k ?_
    have h1 : ((e (Submodule.Quotient.mk x) : ↥M₁) : E) - x ∈ M₀ := by
      have h2 : (Submodule.Quotient.mk (p := M₀) ((e (Submodule.Quotient.mk x) : ↥M₁) : E)) =
          (Submodule.Quotient.mk (p := M₀) x) := by
        rw [← Submodule.quotientEquivOfIsCompl_symm_apply]
        exact e.symm_apply_apply _
      exact (Submodule.Quotient.eq M₀).mp h2
    simpa using neg_mem h1
  apply e.symm.injective
  rw [e.symm_apply_apply, Submodule.quotientEquivOfIsCompl_symm_apply]
  exact hkey

private theorem m1T_quotientEquivOfIsCompl_mapQ (σ : Representation (ZMod 2) K E)
    {M₀ M₁ : Submodule (ZMod 2) E} (h : IsCompl M₀ M₁)
    (hM₀ : ∀ k, M₀ ≤ Submodule.comap (σ k) M₀) (hM₁ : ∀ k, ∀ y ∈ M₁, σ k y ∈ M₁)
    (k : K) (q : E ⧸ M₀) :
    (Submodule.quotientEquivOfIsCompl M₀ M₁ h) ((Submodule.mapQ M₀ M₀ (σ k) (hM₀ k)) q) =
      ⟨σ k (((Submodule.quotientEquivOfIsCompl M₀ M₁ h) q : ↥M₁) : E),
        hM₁ k (((Submodule.quotientEquivOfIsCompl M₀ M₁ h) q : ↥M₁) : E)
          ((Submodule.quotientEquivOfIsCompl M₀ M₁ h) q).2⟩ := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M₀ q
  rw [Submodule.mapQ_apply]
  exact m1T_quotientEquivOfIsCompl_apply_mk σ h hM₀ hM₁ k x

private theorem m1T_theta_of_quotient_map (σ : Representation (ZMod 2) K E)
    {M₀ M₁ : Submodule (ZMod 2) E} (h : IsCompl M₀ M₁)
    (hM₀ : ∀ k, M₀ ≤ Submodule.comap (σ k) M₀) (hM₁ : ∀ k, ∀ y ∈ M₁, σ k y ∈ M₁)
    (ψ : ↥M₀ →+ (E ⧸ M₀))
    (hψ : ∀ (k : K) (y : ↥M₀), ψ ⟨σ k (y : E), hM₀ k y.2⟩ =
      (Submodule.mapQ M₀ M₀ (σ k) (hM₀ k)) (ψ y))
    (hne : M₀ ≠ ⊥) (hinj : Function.Injective ψ) :
    ∃ θ : ↥M₀ →+ ↥M₁, θ ≠ 0 ∧ ∀ (k : K) (y : ↥M₀),
      (θ ⟨σ k (y : E), hM₀ k y.2⟩ : E) = σ k (θ y) := by
  let e := Submodule.quotientEquivOfIsCompl M₀ M₁ h
  refine ⟨e.toLinearMap.toAddMonoidHom.comp ψ, ?_, ?_⟩
  · intro hzero
    obtain ⟨y, hy⟩ : ∃ y : ↥M₀, y ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (eq_bot_iff.mpr fun z hz => by
        have h5 := congrArg Subtype.val (hc ⟨z, hz⟩)
        simpa using h5)
    have h1 : ψ y = 0 := by
      have h2 : e (ψ y) = 0 := by
        have h3 := congrArg (fun f => f y) hzero
        simpa using h3
      exact e.injective (by simpa using h2)
    exact hy (hinj (by rw [h1, map_zero]))
  · intro k y
    show ((e (ψ ⟨σ k (y : E), hM₀ k y.2⟩) : ↥M₁) : E) = σ k ((e (ψ y) : ↥M₁) : E)
    have h1 : e (ψ ⟨σ k (y : E), hM₀ k y.2⟩) =
        e ((Submodule.mapQ M₀ M₀ (σ k) (hM₀ k)) (ψ y)) := by rw [hψ]
    rw [h1, m1T_quotientEquivOfIsCompl_mapQ σ h hM₀ hM₁ k (ψ y)]

end Theta

private theorem m1_qlevel {G : Type} [Group G] [Finite G] {L A B N : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hFc : Fintype.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) [CFSG.IsElementaryAbelian 2 ↥A]
    (hperf : commutator ↥L = ⊤) (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLN : L ≤ N)
    (hAN' : A ≤ N) (hBp : IsPGroup 2 ↥B) (hLp : CFSG.pCore 2 ↥L = ⊥) (lB : ↥B →* ↥L)
    [hAea : CFSG.IsElementaryAbelian 2 (graphSub lB)]
    (hnotle : ¬ graphSub lB ≤ CFSG.pCore 2 (↥L × ↥B))
    (e1 : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* ↥L)
    (he1 : ∀ x : ↥L × ↥B, e1 (QuotientGroup.mk x) = x.1)
    (π₁ : ↥L × ↥B →* ↥N) (hπ₁L : ∀ l : ↥L, π₁ (l, 1) = ⟨l, hLN l.2⟩)
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (ρQ : Representation (ZMod 2) ↥N Q)
    (hF1 : ∀ q : Q, (∀ l : ↥L, ρQ (π₁ (l, 1)) q = q) → q = 0)
    (hF2 : ∀ q : Q, q ∈ Submodule.span (ZMod 2)
      {w | ∃ l : ↥L, ∃ y, w = ρQ (π₁ (l, 1)) y - y})
    (hbud : ∀ (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation (ρQ.comp π₁)),
      IsCompositionSeries r Vs →
      ∑ i ∈ nontrivialFactors Vs, factorCodim Vs (graphSub lB) i ≤
        Nat.log 2 (Nat.card ((graphSub lB).map
          (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))))))
    (hQ : Nontrivial Q) :
    ∃ Mat : ↥L →* GL (Fin 3) F, Function.Injective Mat ∧
      Mat.range = (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range ∧
      ∃ (W' : Submodule (ZMod 2) Q) (hW'L : ∀ l : ↥L, ∀ y ∈ W', ρQ (π₁ (l, 1)) y ∈ W'),
        (∀ a (ha : a ∈ A), ∀ y ∈ W', ρQ ⟨a, hAN' ha⟩ y ∈ W') ∧
        ∃ φ : ↥W' ≃+ (Fin 3 → F), ∀ (l : ↥L) (y : ↥W'),
          φ ⟨ρQ (π₁ (l, 1)) y, hW'L l y y.2⟩ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ φ y := by
  classical
  let ψ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e1.trans e
  obtain ⟨r, Vs, hVs⟩ := exists_isCompositionSeries (ρQ.comp π₁)
  obtain ⟨hpc, hnat, hcard, -⟩ := chief_factors_of_FFClassification ψ (by omega) hFc
    (ffClassificationSL3_of_card hn hFc) hVs (graphSub lB) hnotle (hbud r Vs hVs)
  have hF3 : nontrivCount ((ρQ.comp π₁).comp (MonoidHom.inl ↥L ↥B)) ≤ 2 := by
    have hker : ∀ b : ↥B, ((1 : ↥L), b) ∈ CFSG.pCore 2 (↥L × ↥B) := fun b => by
      rw [pCore_prod_eq_ker_fst hBp hLp]
      exact MonoidHom.mem_ker.mpr rfl
    have hsurj : ∀ (i : Fin r) (k : ↥L × ↥B), ∃ l : ↥L,
        factorRep (Vs i.castSucc) (Vs i.succ) k =
          factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l) := by
      rintro i ⟨l, b⟩
      refine ⟨l, ?_⟩
      have hk : ((l, b) : ↥L × ↥B) = MonoidHom.inl ↥L ↥B l * ((1 : ↥L), b) := by simp
      calc factorRep (Vs i.castSucc) (Vs i.succ) (l, b)
          = factorRep (Vs i.castSucc) (Vs i.succ)
              (MonoidHom.inl ↥L ↥B l * ((1 : ↥L), b)) := congrArg _ hk
        _ = factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l) *
              factorRep (Vs i.castSucc) (Vs i.succ) ((1 : ↥L), b) := map_mul _ _ _
        _ = factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l) := by
            apply LinearMap.ext
            intro x
            change (factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l))
              ((factorRep (Vs i.castSucc) (Vs i.succ) ((1 : ↥L), b)) x) =
              (factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l)) x
            congr 1
            exact hpc i ((1 : ↥L), b) (hker b) x
    have hle : nontrivCount ((ρQ.comp π₁).comp (MonoidHom.inl ↥L ↥B)) ≤
        (nontrivialFactors Vs).card :=
      nontrivCount_comp_le_card (ρ := ρQ.comp π₁) (MonoidHom.inl ↥L ↥B) hVs hsurj
    exact hle.trans hcard
  have hr : 0 < r := by
    by_contra hpos
    have hr0 : r = 0 := by omega
    subst r
    have hbt : (⊥ : Subrepresentation (ρQ.comp π₁)) = ⊤ := by
      rw [← hVs.zero, ← hVs.last]
      congr 1
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    have hmem : q ∈ (⊤ : Subrepresentation (ρQ.comp π₁)).toSubmodule := Submodule.mem_top
    have h1 : (⊥ : Subrepresentation (ρQ.comp π₁)).toSubmodule = ⊥ := rfl
    rw [← hbt, h1] at hmem
    exact hq ((Submodule.mem_bot (ZMod 2)).mp hmem)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, i₀ = ⟨0, hr⟩ := ⟨_, rfl⟩
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Submodule (ZMod 2) Q,
      M₀ = (Vs i₀.succ).toSubmodule := ⟨_, rfl⟩
  have hM₀L : ∀ l : ↥L, ∀ y ∈ M₀, ρQ (π₁ (l, 1)) y ∈ M₀ := by
    intro l y hy
    exact hM₀.symm ▸ (Vs i₀.succ).apply_mem_toSubmodule (l, 1) (hM₀ ▸ hy)
  have hM₀irr : ∀ W : Submodule (ZMod 2) Q, W ≤ M₀ →
      (∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W) → W = ⊥ ∨ W = M₀ := by
    intro W hWM hWL
    have hcast0 : i₀.castSucc = (0 : Fin (r + 1)) := by rw [hi₀]; rfl
    have hbotcast : Vs i₀.castSucc = ⊥ := by rw [hcast0, hVs.zero]
    have hfac : factorSub (Vs i₀.castSucc) (Vs i₀.succ) = ⊥ :=
      m1N_factorSub_eq_bot (m1N_toSubmodule_eq_bot hbotcast)
    have hpcmem : ∀ b : ↥B, ((1 : ↥L), b) ∈ CFSG.pCore 2 (↥L × ↥B) := by
      intro b
      rw [pCore_prod_eq_ker_fst hBp hLp]
      exact MonoidHom.mem_ker.mpr rfl
    have hfixP : ∀ p ∈ CFSG.pCore 2 (↥L × ↥B), ∀ y ∈ M₀, ρQ (π₁ p) y = y := by
      intro p hp y hy
      exact congrArg Subtype.val
        (m1N_toRepresentation_eq_self_of_factorRep_eq_self hfac (hpc i₀ p hp)
          (⟨y, hM₀ ▸ hy⟩ : ↥(Vs i₀.succ).toSubmodule))
    have hWinv : ∀ k : ↥L × ↥B, ∀ y ∈ W, (ρQ.comp π₁) k y ∈ W :=
      m1N_prod_invariant (P := CFSG.pCore 2 (↥L × ↥B)) hpcmem
        (fun p hp y hy => hfixP p hp y (hWM hy)) hWL
    rcases m1N_submodule_eq_bot_or_eq_of_covBy (ρ := ρQ.comp π₁) hVs
      (i := i₀) (hM₀ ▸ hWM) hWinv hbotcast with h | h
    · left; exact h
    · right; exact h.trans hM₀.symm
  obtain ⟨Mat, hMat, hMatr, φ₀, hφ₀⟩ : ∃ Mat : ↥L →* GL (Fin 3) F, Function.Injective Mat ∧
      Mat.range = (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range ∧
      ∃ φ₀ : ↥M₀ ≃+ (Fin 3 → F), ∀ (l : ↥L) (y : ↥M₀),
        φ₀ ⟨ρQ (π₁ (l, 1)) y, hM₀L l y y.2⟩ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ φ₀ y := by
    have hcast0 : i₀.castSucc = (0 : Fin (r + 1)) := by rw [hi₀]; rfl
    have hbotcast : Vs i₀.castSucc = ⊥ := by rw [hcast0, hVs.zero]
    have hfac : factorSub (Vs i₀.castSucc) (Vs i₀.succ) = ⊥ :=
      m1N_factorSub_eq_bot (m1N_toSubmodule_eq_bot hbotcast)
    have hi₀mem : i₀ ∈ nontrivialFactors Vs :=
      m1N_mem_nontrivialFactors (ρ := ρQ.comp π₁) hVs (i := i₀) hfac hbotcast
        (MonoidHom.inl ↥L ↥B) (fun q hq => hF1 q (fun l => hq l))
    rcases (hnat i₀ hi₀mem).1 with hN | hD
    · obtain ⟨φ, hφ⟩ := hN
      let Mat : ↥L →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL.comp e.toMonoidHom
      have hMat : Function.Injective Mat :=
        Matrix.SpecialLinearGroup.toGL_injective.comp e.injective
      have hMatr : Mat.range =
          (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range := by
        ext M
        rw [MonoidHom.mem_range, MonoidHom.mem_range]
        constructor
        · rintro ⟨l, rfl⟩
          exact ⟨e l, rfl⟩
        · rintro ⟨s, rfl⟩
          exact ⟨e.symm s, by simp [Mat]⟩
      refine ⟨Mat, hMat, hMatr, ?_⟩
      obtain ⟨φ₀, hφ₀_apply⟩ := m1N_exists_phi0 hM₀ hfac φ
      refine ⟨φ₀, ?_⟩
      intro l y
      let f : (↥L × ↥B) →* SL(3, F) :=
        ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B)))
      have hfl : f ((l, 1) : ↥L × ↥B) = e l := by
        change ψ (((l, 1) : ↥L × ↥B) :
          (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B)) = e l
        change e (e1 (QuotientGroup.mk ((l, 1) : ↥L × ↥B))) = e l
        rw [he1]
      have hmat : (f ((l, 1) : ↥L × ↥B) : Matrix (Fin 3) (Fin 3) F) =
          (Mat l : Matrix (Fin 3) (Fin 3) F) := by
        rw [hfl]
        exact (Matrix.SpecialLinearGroup.coe_GL_coe_matrix (e l)).symm
      simpa [hmat] using
        (m1N_phi0_equivariant hM₀ ((l, 1) : ↥L × ↥B) f φ
          (fun x => hφ ((l, 1)) x) (hM₀L l) φ₀ hφ₀_apply y)
    · obtain ⟨φ, hφ⟩ := hD
      let D : SL(3, F) →* SL(3, F) :=
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F).toMonoidHom
      let Mat : ↥L →* GL (Fin 3) F :=
        Matrix.SpecialLinearGroup.toGL.comp (D.comp e.toMonoidHom)
      have hDinj : Function.Injective D :=
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F).injective
      have hMat : Function.Injective Mat :=
        Matrix.SpecialLinearGroup.toGL_injective.comp (hDinj.comp e.injective)
      have hMatr : Mat.range =
          (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range := by
        ext M
        rw [MonoidHom.mem_range, MonoidHom.mem_range]
        constructor
        · rintro ⟨l, rfl⟩
          exact ⟨D (e l), rfl⟩
        · rintro ⟨s, rfl⟩
          refine ⟨e.symm ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F).symm s), ?_⟩
          simp [Mat, D]
      refine ⟨Mat, hMat, hMatr, ?_⟩
      obtain ⟨φ₀, hφ₀_apply⟩ := m1N_exists_phi0 hM₀ hfac φ
      refine ⟨φ₀, ?_⟩
      intro l y
      let g : (↥L × ↥B) →* SL(3, F) :=
        ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B)))
      have hgl : g ((l, 1) : ↥L × ↥B) = e l := by
        change ψ (((l, 1) : ↥L × ↥B) :
          (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B)) = e l
        change e (e1 (QuotientGroup.mk ((l, 1) : ↥L × ↥B))) = e l
        rw [he1]
      have hmat : dualMat (g ((l, 1) : ↥L × ↥B)) =
          (Mat l : Matrix (Fin 3) (Fin 3) F) := by
        rw [hgl]
        exact (Matrix.SpecialLinearGroup.coe_GL_coe_matrix (D (e l))).symm
      simpa [hmat] using
        (m1N_phi0_equivariant_dual hM₀ ((l, 1) : ↥L × ↥B) g φ
          (fun x => hφ ((l, 1)) x) (hM₀L l) φ₀ hφ₀_apply y)
  obtain ⟨W', hW'L, hW'A, ψ', hψ'⟩ : ∃ (W' : Submodule (ZMod 2) Q)
      (hW'L : ∀ l : ↥L, ∀ y ∈ W', ρQ (π₁ (l, 1)) y ∈ W'),
      (∀ a (ha : a ∈ A), ∀ y ∈ W', ρQ ⟨a, hAN' ha⟩ y ∈ W') ∧
      ∃ ψ' : ↥W' ≃+ ↥M₀, ∀ (l : ↥L) (y : ↥W'),
        (ψ' ⟨ρQ (π₁ (l, 1)) y, hW'L l y y.2⟩ : _) = ρQ (π₁ (l, 1)) (ψ' y) := by
    by_cases hAM : ∀ a (ha : a ∈ A), ∀ y ∈ M₀, ρQ ⟨a, hAN' ha⟩ y ∈ M₀
    · exact ⟨M₀, hM₀L, hAM, AddEquiv.refl _, fun l y => rfl⟩
    · push Not at hAM
      obtain ⟨a, ha, y₀, hy₀, hy₀M⟩ := hAM
      obtain ⟨M₁, hM₁⟩ : ∃ M₁ : Submodule (ZMod 2) Q,
          M₁ = M₀.map (ρQ ⟨a, hAN' ha⟩) := ⟨_, rfl⟩
      have hainvL : ∀ l ∈ L, a⁻¹ * l * a ∈ L := fun l hl => by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAN ha)) l).mp hl
      have haL : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl =>
        (Subgroup.mem_normalizer_iff.mp (hAN ha) l).mp hl
      have hconj₁ : ∀ l : ↥L, (⟨a, hAN' ha⟩ : ↥N)⁻¹ * π₁ (l, 1) * ⟨a, hAN' ha⟩
          = π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1) := by
        intro l
        rw [hπ₁L, hπ₁L]
        exact Subtype.ext rfl
      have hconj₂ : ∀ l : ↥L, (⟨a, hAN' ha⟩ : ↥N) * π₁ (l, 1) * ⟨a, hAN' ha⟩⁻¹
          = π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1) := by
        intro l
        rw [hπ₁L, hπ₁L]
        exact Subtype.ext rfl
      have hmulρ : ∀ (g h : ↥N) (z : Q),
          ρQ (g * h) z = ρQ g (ρQ h z) := fun g h z => by
        rw [map_mul, Module.End.mul_apply]
      have hstep₁ : ∀ (l : ↥L) (x : Q),
          ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ x) = ρQ ⟨a, hAN' ha⟩
            (ρQ (π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1)) x) := by
        intro l x
        have hmul' : π₁ (l, 1) * (⟨a, hAN' ha⟩ : ↥N) = (⟨a, hAN' ha⟩ : ↥N) *
            π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1) := by
          calc π₁ (l, 1) * ⟨a, hAN' ha⟩ = ⟨a, hAN' ha⟩ *
              ((⟨a, hAN' ha⟩ : ↥N)⁻¹ * π₁ (l, 1) * ⟨a, hAN' ha⟩) := by group
            _ = ⟨a, hAN' ha⟩ * π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1) := by
                rw [hconj₁ l]
        calc ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ x)
            = ρQ (π₁ (l, 1) * ⟨a, hAN' ha⟩) x := (hmulρ _ _ _).symm
          _ = ρQ ((⟨a, hAN' ha⟩ : ↥N) *
                π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1)) x := by rw [hmul']
          _ = ρQ ⟨a, hAN' ha⟩
                (ρQ (π₁ (⟨a⁻¹ * (l : G) * a, hainvL (l : G) l.2⟩, 1)) x) := hmulρ _ _ _
      have hstep₂ : ∀ (l : ↥L) (w : Q),
          ρQ (π₁ (l, 1)) (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹ w) = ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹
            (ρQ (π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1)) w) := by
        intro l w
        have hmul' : π₁ (l, 1) * (⟨a, hAN' ha⟩ : ↥N)⁻¹ = (⟨a, hAN' ha⟩ : ↥N)⁻¹ *
            π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1) := by
          calc π₁ (l, 1) * ⟨a, hAN' ha⟩⁻¹ = ⟨a, hAN' ha⟩⁻¹ *
              ((⟨a, hAN' ha⟩ : ↥N) * π₁ (l, 1) * ⟨a, hAN' ha⟩⁻¹) := by group
            _ = ⟨a, hAN' ha⟩⁻¹ * π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1) := by
                rw [hconj₂ l]
        calc ρQ (π₁ (l, 1)) (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹ w)
            = ρQ (π₁ (l, 1) * (⟨a, hAN' ha⟩ : ↥N)⁻¹) w := (hmulρ _ _ _).symm
          _ = ρQ ((⟨a, hAN' ha⟩ : ↥N)⁻¹ *
                π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1)) w := by rw [hmul']
          _ = ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹
                (ρQ (π₁ (⟨a * (l : G) * a⁻¹, haL (l : G) l.2⟩, 1)) w) := hmulρ _ _ _
      have hinvcomp : ∀ z : Q,
          ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹ (ρQ ⟨a, hAN' ha⟩ z) = z := by
        intro z
        have h : ρQ ((⟨a, hAN' ha⟩ : ↥N)⁻¹ * ⟨a, hAN' ha⟩) z = z := by
          rw [inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hmulρ] at h
      have hcompinv : ∀ z : Q,
          ρQ ⟨a, hAN' ha⟩ (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹ z) = z := by
        intro z
        have h : ρQ ((⟨a, hAN' ha⟩ : ↥N) * ⟨a, hAN' ha⟩⁻¹) z = z := by
          rw [mul_inv_cancel, map_one, Module.End.one_apply]
        rwa [hmulρ] at h
      have hM₁L : ∀ l : ↥L, ∀ y ∈ M₁, ρQ (π₁ (l, 1)) y ∈ M₁ := by
        intro l y hy
        rw [hM₁] at hy ⊢
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
        rw [hstep₁ l x]
        exact Submodule.mem_map.mpr
          ⟨_, hM₀L _ x hx, rfl⟩
      have hM₁irr : ∀ W : Submodule (ZMod 2) Q, W ≤ M₁ →
          (∀ l : ↥L, ∀ y ∈ W, ρQ (π₁ (l, 1)) y ∈ W) → W = ⊥ ∨ W = M₁ := by
        intro W hW hWin
        have hW'le : W.map (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹) ≤ M₀ := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
          have hwM₁ : w ∈ M₁ := hW hw
          rw [hM₁] at hwM₁
          obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hwM₁
          rw [hinvcomp]
          exact hx
        have hW'L : ∀ l : ↥L, ∀ y ∈ W.map (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹),
            ρQ (π₁ (l, 1)) y ∈ W.map (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹) := by
          intro l y hy
          obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
          rw [hstep₂ l w]
          exact Submodule.mem_map.mpr
            ⟨_, hWin _ w hw, rfl⟩
        have hW'map : (W.map (ρQ (⟨a, hAN' ha⟩ : ↥N)⁻¹)).map (ρQ ⟨a, hAN' ha⟩) = W := by
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
            rw [hcompinv]
            exact hw
          · intro hz
            exact Submodule.mem_map.mpr
              ⟨_, Submodule.mem_map.mpr ⟨z, hz, rfl⟩, hcompinv z⟩
        rcases hM₀irr _ hW'le hW'L with h | h
        · left
          rw [← hW'map, h, Submodule.map_bot]
        · right
          rw [← hW'map, h]
          exact hM₁.symm
      have hcompl : IsCompl M₀ M₁ := by
        have hy₀ne : y₀ ≠ 0 := by
          intro h0
          apply hy₀M
          rw [h0, map_zero]
          exact M₀.zero_mem
        have hM₀ne : M₀ ≠ ⊥ := by
          intro h0
          have h1 : y₀ ∈ (⊥ : Submodule (ZMod 2) Q) := by
            rw [← h0]; exact hy₀
          exact hy₀ne (by simpa using h1)
        have hdisj : M₀ ⊓ M₁ = ⊥ := by
          have hinfL : ∀ l : ↥L, ∀ y ∈ M₀ ⊓ M₁, ρQ (π₁ (l, 1)) y ∈ M₀ ⊓ M₁ := fun l y hy =>
            Submodule.mem_inf.mpr ⟨hM₀L l y (Submodule.mem_inf.mp hy).1,
              hM₁L l y (Submodule.mem_inf.mp hy).2⟩
          rcases hM₀irr (M₀ ⊓ M₁) inf_le_left hinfL with h | h
          · exact h
          · exfalso
            have hle : M₀ ≤ M₁ := by rw [← h]; exact inf_le_right
            rcases hM₁irr M₀ hle hM₀L with h0 | h1
            · exact hM₀ne h0
            · refine hy₀M ?_
              rw [h1, hM₁]
              exact Submodule.mem_map.mpr ⟨y₀, hy₀, rfl⟩
        have hsup : M₀ ⊔ M₁ = ⊤ := by
          by_contra hne
          let ρL : Representation (ZMod 2) ↥L Q :=
            (ρQ.comp π₁).comp (MonoidHom.inl ↥L ↥B)
          have hsupL : ∀ l : ↥L, ∀ y ∈ M₀ ⊔ M₁, ρL l y ∈ M₀ ⊔ M₁ := by
            intro l y hy
            obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
            exact Submodule.mem_sup.mpr ⟨ρL l u, hM₀L l u hu,
              ρL l v, hM₁L l v hv, (map_add (ρL l) u v).symm⟩
          let S₀ : Subrepresentation ρL := ⊥
          let S₁ : Subrepresentation ρL := ⟨M₀, fun l => hM₀L l⟩
          let S₂ : Subrepresentation ρL := ⟨M₀ ⊔ M₁, hsupL⟩
          let S₃ : Subrepresentation ρL := ⊤
          have h01 : S₀ ≤ S₁ := bot_le
          have h12 : S₁ ≤ S₂ := fun x hx => Submodule.mem_sup_left hx
          have h23 : S₂ ≤ S₃ := fun x _ => trivial
          have n1 : ∃ l : ↥L, factorRep S₀ S₁ l ≠ 1 := by
            by_contra h
            push Not at h
            refine hy₀ne (hF1 y₀ fun l => ?_)
            have h1 : ρQ (π₁ (l, 1)) y₀ - y₀ ∈ S₀.toSubmodule :=
              (m1B_factorRep_eq_one_iff S₀ S₁ l).mp (h l) y₀ hy₀
            rw [show S₀.toSubmodule = (⊥ : Submodule (ZMod 2) Q)
              from rfl, Submodule.mem_bot, sub_eq_zero] at h1
            exact h1
          have n2 : ∃ l : ↥L, factorRep S₁ S₂ l ≠ 1 := by
            by_contra h
            push Not at h
            have hxM₁ : ρQ ⟨a, hAN' ha⟩ y₀ ∈ M₁ := by
              rw [hM₁]
              exact Submodule.mem_map.mpr ⟨y₀, hy₀, rfl⟩
            have hxS₂ : ρQ ⟨a, hAN' ha⟩ y₀ ∈ M₀ ⊔ M₁ := Submodule.mem_sup_right hxM₁
            have hfix : ∀ l : ↥L,
                ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ y₀) = ρQ ⟨a, hAN' ha⟩ y₀ := by
              intro l
              have h1 : ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ y₀) - ρQ ⟨a, hAN' ha⟩ y₀ ∈
                  S₁.toSubmodule := (m1B_factorRep_eq_one_iff S₁ S₂ l).mp (h l) _ hxS₂
              have h2 : ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ y₀) ∈ M₁ := hM₁L l _ hxM₁
              have h3 : ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ y₀) - ρQ ⟨a, hAN' ha⟩ y₀ ∈ M₁ :=
                M₁.sub_mem h2 hxM₁
              have h4 : ρQ (π₁ (l, 1)) (ρQ ⟨a, hAN' ha⟩ y₀) - ρQ ⟨a, hAN' ha⟩ y₀ ∈ M₀ ⊓ M₁ :=
                Submodule.mem_inf.mpr ⟨h1, h3⟩
              rw [hdisj, Submodule.mem_bot] at h4
              exact sub_eq_zero.mp h4
            have hzero : ρQ ⟨a, hAN' ha⟩ y₀ = 0 := hF1 _ hfix
            exact hy₀M (by rw [hzero]; exact M₀.zero_mem)
          have n3 : ∃ l : ↥L, factorRep S₂ S₃ l ≠ 1 := by
            by_contra h
            push Not at h
            have hspan : Submodule.span (ZMod 2) {w | ∃ l : ↥L, ∃ y,
                w = ρQ (π₁ (l, 1)) y - y} ≤ M₀ ⊔ M₁ := by
              rw [Submodule.span_le]
              rintro w ⟨l, y, rfl⟩
              exact (m1B_factorRep_eq_one_iff S₂ S₃ l).mp (h l) y Submodule.mem_top
            exact hne (eq_top_iff.mpr fun q _ => hspan (hF2 q))
          have h3 := three_le_nontrivCount (α := MonoidHom.id ↥L) (ρ := ρL) hperf h01 h12 h23
            n1 n2 n3
          rw [MonoidHom.comp_id] at h3
          have hF3' : nontrivCount ρL ≤ 2 := hF3
          exact (not_le_of_gt (Nat.lt_of_succ_le h3)) hF3'
        exact isCompl_iff.mpr ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
      obtain ⟨θ, hθ, hθL⟩ : ∃ θ : ↥M₀ →+ ↥M₁, θ ≠ 0 ∧ ∀ (l : ↥L) (y : ↥M₀),
          ((θ ⟨ρQ (π₁ (l, 1)) y, hM₀L l y y.2⟩ : ↥M₁) : Q) =
            ρQ (π₁ (l, 1)) (θ y) := by
        classical
        clear Mat hMat hMatr φ₀ hφ₀
        have hM₁ne : M₁ ≠ ⊥ := by
          intro hbot
          have hz : ρQ ⟨a, hAN' ha⟩ y₀ ∈ M₁ := by
            rw [hM₁]
            exact Submodule.mem_map.mpr ⟨y₀, hy₀, rfl⟩
          rw [hbot] at hz
          have hz0 : ρQ ⟨a, hAN' ha⟩ y₀ = 0 := by simpa using hz
          exact hy₀M (by rw [hz0]; exact M₀.zero_mem)
        let M₀s : Subrepresentation (ρQ.comp π₁) :=
          ⟨M₀, fun k y hy =>
            hM₀.symm ▸ (Vs i₀.succ).apply_mem_toSubmodule k (hM₀ ▸ hy)⟩
        have hM₀sU : M₀s = Vs i₀.succ := Subrepresentation.toSubmodule_injective hM₀
        have hcover0 : (⊥ : Subrepresentation (ρQ.comp π₁)) ⋖ M₀s := by
          have h01 : (⊥ : Subrepresentation (ρQ.comp π₁)) ⋖ Vs i₀.succ := by
            have hcast : Vs i₀.castSucc = (⊥ : Subrepresentation (ρQ.comp π₁)) := by
              rw [show i₀.castSucc = (0 : Fin (r + 1)) by ext; simp [hi₀], hVs.zero]
            exact hcast ▸ hVs.covBy i₀
          rwa [← hM₀sU] at h01
        have hM₀ne : M₀ ≠ ⊥ := by
          intro hbot
          have hne : M₀s ≠ (⊥ : Subrepresentation (ρQ.comp π₁)) := by
            intro h
            rw [h] at hcover0
            exact (lt_irrefl _) hcover0.1
          refine hne (Subrepresentation.toSubmodule_injective ?_)
          show M₀s.toSubmodule = (⊥ : Subrepresentation (ρQ.comp π₁)).toSubmodule
          rw [show (⊥ : Subrepresentation (ρQ.comp π₁)).toSubmodule = ⊥ from rfl]
          exact hbot
        have hlt : M₀s < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro htop
          apply hM₁ne
          have hMQ : M₀ = ⊤ := by
            have h1 := congrArg Subrepresentation.toSubmodule htop
            rw [show (⊤ : Subrepresentation (ρQ.comp π₁)).toSubmodule = ⊤ from rfl] at h1
            exact h1
          have hle : M₁ ≤ M₀ := by rw [hMQ]; exact le_top
          rw [← inf_eq_right.mpr hle, hcompl.inf_eq_bot]
        have hcover1 : M₀s ⋖ ⊤ := by
          refine covBy_of_eq_or_eq hlt (fun S h1 h2 => ?_)
          rcases eq_or_lt_of_le h1 with h | h
          · exact Or.inl h.symm
          · right
            have hSle : M₀ ≤ S.toSubmodule := h.le
            have hinv : ∀ l : ↥L, ∀ y ∈ S.toSubmodule ⊓ M₁,
                ρQ (π₁ (l, 1)) y ∈ S.toSubmodule ⊓ M₁ := by
              intro l y hy
              exact ⟨S.apply_mem_toSubmodule ((l, 1) : ↥L × ↥B) hy.1, hM₁L l y hy.2⟩
            have hS' : S.toSubmodule = M₀ ⊔ (S.toSubmodule ⊓ M₁) := by
              calc S.toSubmodule = S.toSubmodule ⊓ ⊤ := (inf_top_eq S.toSubmodule).symm
                _ = S.toSubmodule ⊓ (M₀ ⊔ M₁) := by rw [hcompl.sup_eq_top]
                _ = (S.toSubmodule ⊓ M₁) ⊔ M₀ := by
                    rw [sup_comm M₀ M₁]
                    exact (inf_sup_assoc_of_le (x := S.toSubmodule) (y := M₁) (z := M₀) hSle).symm
                _ = M₀ ⊔ (S.toSubmodule ⊓ M₁) := (sup_comm (S.toSubmodule ⊓ M₁) M₀)
            rcases hM₁irr (S.toSubmodule ⊓ M₁) inf_le_right hinv with hbot | htop
            · exfalso
              exact h.ne (Subrepresentation.toSubmodule_injective (by
                rw [hS', hbot, sup_bot_eq]))
            · apply Subrepresentation.toSubmodule_injective
              show S.toSubmodule = (⊤ : Subrepresentation (ρQ.comp π₁)).toSubmodule
              rw [show (⊤ : Subrepresentation (ρQ.comp π₁)).toSubmodule = ⊤ from rfl]
              rw [hS', htop, hcompl.sup_eq_top]
        let Vs' : Fin 3 → Subrepresentation (ρQ.comp π₁) :=
          Fin.cases ⊥ (Fin.cases M₀s (fun _ => ⊤))
        have hVs'0 : Vs' 0 = (⊥ : Subrepresentation (ρQ.comp π₁)) := rfl
        have hVs'1 : Vs' 1 = M₀s := rfl
        have hVs'2 : Vs' 2 = (⊤ : Subrepresentation (ρQ.comp π₁)) := rfl
        have hVs'1t : (Vs' 1).toSubmodule = M₀ := rfl
        have hVs'2t : (Vs' 2).toSubmodule = (⊤ : Submodule (ZMod 2) Q) := rfl
        have hVs' : IsCompositionSeries 2 Vs' := by
          refine ⟨hVs'0, ?_, ?_⟩
          · show Vs' (Fin.last 2) = ⊤
            rfl
          · intro i
            fin_cases i
            · exact hcover0
            · exact hVs'1.symm ▸ (hVs'2.symm ▸ hcover1)
        have hM₀inv : ∀ k : ↥L × ↥B, ∀ y ∈ M₀, (ρQ.comp π₁) k y ∈ M₀ :=
          fun k y hy => hM₀.symm ▸ (Vs i₀.succ).apply_mem_toSubmodule k (hM₀ ▸ hy)
        have hfac0 : (0 : Fin 2) ∈ nontrivialFactors Vs' := by
          rw [mem_nontrivialFactors]
          by_contra hcon
          push Not at hcon
          have hcon0 : ∀ k : ↥L × ↥B, factorRep (Vs' 0) (Vs' 1) k = 1 := fun k => hcon k
          have hV0 : (Vs' 0).toSubmodule = ⊥ := rfl
          have hrepr : ∀ k : ↥L × ↥B, (Vs' 1).toRepresentation k = 1 := fun k =>
            m1T_toRepresentation_eq_one_of_factorRep_eq_one hV0 (hcon0 k)
          have htriv : ∀ l : ↥L, ∀ y ∈ M₀, ρQ (π₁ (l, 1)) y = y := by
            intro l y hy
            have hy' : y ∈ (Vs' 1).toSubmodule := by rw [hVs'1t]; exact hy
            have h2 : (Vs' 1).toRepresentation ((l, 1) : ↥L × ↥B) ⟨y, hy'⟩ = ⟨y, hy'⟩ := by
              rw [hrepr]; rfl
            exact (Subrepresentation.toRepresentation_apply_coe).mp h2
          obtain ⟨y, hy⟩ : ∃ y : ↥M₀, y ≠ 0 := by
            by_contra hc
            push Not at hc
            exact hM₀ne (eq_bot_iff.mpr fun z hz => by
              have h5 := congrArg Subtype.val (hc ⟨z, hz⟩)
              simpa using h5)
          exact hy (Subtype.ext (hF1 (y : Q) fun l => htriv l y y.2))
        have hfac1 : (1 : Fin 2) ∈ nontrivialFactors Vs' := by
          rw [mem_nontrivialFactors]
          by_contra hcon
          push Not at hcon
          have hcon1 : ∀ k : ↥L × ↥B, factorRep (Vs' 1) (Vs' 2) k = 1 := fun k => hcon k
          have hcon1' : ∀ k : ↥L × ↥B, factorRep (Vs' 1) ⊤ k = 1 := fun k => hcon1 k
          have htriv : ∀ l : ↥L, ∀ y ∈ M₁, ρQ (π₁ (l, 1)) y = y := by
            intro l y hy
            have hq := m1T_quotient_eq_of_factorRep_top_eq_one (Vs' 1)
              ((l, 1) : ↥L × ↥B) (hcon1' (l, 1)) y
            rw [hVs'1t] at hq
            have hsub : (ρQ.comp π₁) ((l, 1) : ↥L × ↥B) y - y ∈ M₀ :=
              (Submodule.Quotient.eq M₀).mp hq
            have hsub₁ : (ρQ.comp π₁) ((l, 1) : ↥L × ↥B) y - y ∈ M₁ :=
              M₁.sub_mem (hM₁L l y hy) hy
            exact sub_eq_zero.mp (by
              have hmem : (ρQ.comp π₁) ((l, 1) : ↥L × ↥B) y - y ∈ M₀ ⊓ M₁ := ⟨hsub, hsub₁⟩
              rw [hcompl.inf_eq_bot] at hmem
              exact (Submodule.mem_bot (ZMod 2)).mp hmem)
          obtain ⟨y, hy⟩ : ∃ y : ↥M₁, y ≠ 0 := by
            by_contra hc
            push Not at hc
            exact hM₁ne (eq_bot_iff.mpr fun z hz => by
              have h5 := congrArg Subtype.val (hc ⟨z, hz⟩)
              simpa using h5)
          exact hy (Subtype.ext (hF1 (y : Q) fun l => htriv l y y.2))
        obtain ⟨-, hnat', hcard', hiso'⟩ :=
          chief_factors_of_FFClassification ψ (by omega) hFc (ffClassificationSL3_of_card hn hFc)
            hVs' (graphSub lB) hnotle (hbud 2 Vs' hVs')
        have hcard2 : (nontrivialFactors Vs').card = 2 := by
          have hsub : ({(0 : Fin 2), 1} : Finset (Fin 2)) ⊆ nontrivialFactors Vs' := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl
            exacts [hfac0, hfac1]
          have h2 : ({(0 : Fin 2), 1} : Finset (Fin 2)).card = 2 := Finset.card_pair (by decide)
          have hle : 2 ≤ (nontrivialFactors Vs').card := by
            calc 2 = ({(0 : Fin 2), 1} : Finset (Fin 2)).card := h2.symm
              _ ≤ (nontrivialFactors Vs').card := Finset.card_le_card hsub
          omega
        obtain ⟨i, j, hi, hj, hij, ⟨φ, hφ⟩, -, -⟩ := hiso' hcard2
        clear hbud hF3 hVs hpc hnat hcard hM₀irr
        have hi0 : i = 0 := by
          apply Fin.ext
          have := i.isLt
          have := j.isLt
          omega
        have hj1 : j = 1 := by
          apply Fin.ext
          have := i.isLt
          have := j.isLt
          omega
        subst hi0
        subst hj1
        obtain ⟨Φ, hΦ⟩ := m1T_exists_quotient_equiv (M₀ := M₀) (U₀ := Vs' 0) (U₁ := Vs' 1)
          (U₂ := Vs' 2) (by rw [hVs'0]; rfl) hVs'2t hVs'1t φ hφ (fun k y hy => hM₀inv k y hy)
        exact m1T_theta_of_quotient_map
          ((ρQ.comp π₁).comp (MonoidHom.inl ↥L ↥B)) hcompl
          (fun l y hy => hM₀inv (l, 1) y hy) (fun l y hy => hM₁L l y hy) Φ.toAddMonoidHom
          (fun l y => hΦ (l, 1) y) hM₀ne Φ.injective
      exact m1B_paritySection hLN hAN' hAN π₁ hπ₁L ρQ hM₀L hM₁L hM₀irr hM₁irr hcompl θ hθ hθL
  refine ⟨Mat, hMat, hMatr, W', hW'L, hW'A, ψ'.trans φ₀, fun l y => ?_⟩
  have h1 : ψ' ⟨ρQ (π₁ (l, 1)) y, hW'L l y y.2⟩ =
      ⟨ρQ (π₁ (l, 1)) (ψ' y), hM₀L l _ (ψ' y).2⟩ := Subtype.ext (hψ' l y)
  show φ₀ (ψ' ⟨ρQ (π₁ (l, 1)) y, hW'L l y y.2⟩) = _
  rw [h1, hφ₀]
  rfl

theorem exists_natural_section_sl3 {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) {L : Subgroup G} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) {A : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) (hbest : IsBestOffenderOn ρ A ⊤) :
    ∃ Mat : ↥L →* GL (Fin 3) F, Function.Injective Mat ∧
      Mat.range = (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range ∧
      ∃ (W : Submodule (ZMod 2) V) (hWL : ∀ l ∈ L, ∀ v ∈ W, ρ l v ∈ W),
        (∀ a ∈ A, ∀ v ∈ W, ρ a v ∈ W) ∧
        ∃ p : ↥W →+ (Fin 3 → F), Function.Surjective p ∧
          (∀ (l : ↥L) (v : ↥W),
            p ⟨ρ l v, hWL l l.2 v v.2⟩ = (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ p v) ∧
          ∀ v : ↥W, p v = 0 ↔ ∀ l ∈ L, ρ l v = v := by
  classical
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hquasi : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_mulEquiv_sl3 e
  have hperf : commutator ↥L = ⊤ := hquasi.1
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hquasi.2
  have hZ' : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := center_pow_three e
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    simpa using congrArg Subtype.val (hZ' _ hmem)
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hfaith
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (mem_cenOn.mp (h k.2)).2 v Submodule.mem_top
    obtain ⟨a, b, hab⟩ := hsimple.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [h1 x, h1 y])
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbestB, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hbest
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hA2.toIsMulCommutative.is_comm.comm ⟨b, hBA hb⟩ ⟨c, hBA hc⟩)
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN (hBA hb)) l).mp hl
  have hinner := strictMin_inner ρ L B hn hF e hquasi hBN hB2 hBc hUinv hLU hbestB hquad hmove
  obtain ⟨lB, hlB⟩ := exists_lift_hom hB2 hBc hZ hinner
  obtain ⟨π, hπ⟩ := exists_split_hom lB hlB
  have hLsub : ∀ l : ↥L, π (l, 1) = (l : G) := fun l => by rw [hπ]; simp
  have hgr : ∀ b : ↥B, π (lB b, b) = (b : G) := fun b => by rw [hπ]; simp
  have hπmem : ∀ k : ↥L × ↥B, π k ∈ L ⊔ B := by
    rintro ⟨l, b⟩
    rw [hπ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (lB b).2))) (Subgroup.mem_sup_right b.2)
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, by
    apply Subtype.ext
    show (b : G) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hB2 b b.2⟩
  have hLp : CFSG.pCore 2 ↥L = ⊥ := pCore_two_eq_bot_of_quasisimple hperf hsimple hZ'
  obtain ⟨e1, he1⟩ := exists_quotientEquiv_fst hBp hLp
  let ψ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* Matrix.SpecialLinearGroup (Fin 3) F := e1.trans e
  have hAea : CFSG.IsElementaryAbelian 2 (graphSub lB) := graphSub_isElementaryAbelian lB
    (fun b c => Subtype.ext (hBc b b.2 c c.2)) (fun b => Subtype.ext (hB2 b b.2))
  have hex : ∃ b : ↥B, lB b ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hBU fun b hb => mem_cenOn_of_lift_eq_one lB hlB hmove ⟨b, hb⟩ (hall ⟨b, hb⟩)
  have hnotle : ¬ graphSub lB ≤ CFSG.pCore 2 (↥L × ↥B) := not_graphSub_le_pCore hBp hLp lB hex
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = Subgroup.normalizer (L : Set G) := ⟨_, rfl⟩
  have hLN : L ≤ N := hN ▸ Subgroup.le_normalizer
  have hAN' : A ≤ N := hN ▸ hAN
  have hBN' : B ≤ N := hBA.trans hAN'
  have hπN : ∀ k : ↥L × ↥B, π k ∈ N := fun k =>
    (sup_le hLN hBN') (hπmem k)
  let π₁ : ↥L × ↥B →* ↥N := π.codRestrict N hπN
  let SU : Subrepresentation (ρ.comp N.subtype) :=
    ⟨commOn ρ L ⊤, fun g _ hw => isInvariant_commOn_top (ρ := ρ) (K := L) (H := N)
      (hN ▸ le_rfl) g g.2 _ hw⟩
  let SC : Subrepresentation SU.toRepresentation :=
    ⟨(fixSub ρ L).comap SU.toSubmodule.subtype, by
      intro g x hx
      have hxL : ∀ l ∈ L, ρ l (x : V) = x := by
        have h := hx
        rw [Submodule.mem_comap] at h
        intro l hl
        simpa using (mem_fixSub.mp h) l hl
      rw [Submodule.mem_comap]
      change ((SU.toRepresentation g x : ↥SU.toSubmodule) : V) ∈ fixSub ρ L
      rw [mem_fixSub]
      intro l hl
      have hgN : (g : G) ∈ Subgroup.normalizer (L : Set G) := hN ▸ g.2
      have hconj : (g : G)⁻¹ * l * (g : G) ∈ L := by
        have hg : (g : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hgN
        simpa using (Subgroup.mem_normalizer_iff.mp hg l).mp hl
      have hmul : ρ l (ρ (g : G) (x : V)) =
          ρ (g : G) (ρ ((g : G)⁻¹ * l * (g : G)) (x : V)) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 1
        group
      rw [m1S_sub_toRepresentation_val, hmul, hxL _ hconj]⟩
  let ρQ := SC.quotient
  have : Finite ↥SU.toSubmodule := inferInstanceAs (Finite ↥(commOn ρ L ⊤))
  have : Finite (↥SU.toSubmodule ⧸ SC.toSubmodule) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hπ₁L : ∀ l : ↥L, π₁ (l, 1) = ⟨l, hLN l.2⟩ := fun l => Subtype.ext (hLsub l)
  have hF1 : ∀ q : ↥SU.toSubmodule ⧸ SC.toSubmodule,
      (∀ l : ↥L, ρQ (π₁ (l, 1)) q = q) → q = 0 := by
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := SC.toSubmodule) q
    have hmem : ∀ l : ↥L,
        SU.toRepresentation (π₁ (l, 1)) x - x ∈ SC.toSubmodule := by
      intro l
      have h1 : SC.quotient (π₁ (l, 1)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := hq l
      have h2 : (Submodule.Quotient.mk (SU.toRepresentation (π₁ (l, 1)) x) :
          ↥SU.toSubmodule ⧸ SC.toSubmodule) = Submodule.Quotient.mk x := by
        calc Submodule.Quotient.mk (SU.toRepresentation (π₁ (l, 1)) x)
            = SC.quotient (π₁ (l, 1)) (Submodule.Quotient.mk x) :=
              (Subrepresentation.quotient_apply_mk SC (π₁ (l, 1)) x).symm
          _ = Submodule.Quotient.mk x := h1
      exact (Submodule.Quotient.eq _).mp h2
    have hvalx : ∀ m : ↥L,
        ((SU.toRepresentation (π₁ (m, 1)) x : ↥SU.toSubmodule) : V) = ρ (m : G) (x : V) := by
      intro m
      rw [m1S_sub_toRepresentation_val]
      simp [hπ₁L]
    have hval : ∀ m : ↥L,
        ((SU.toRepresentation (π₁ (m, 1)) x - x : ↥SU.toSubmodule) : V) =
          ρ (m : G) (x : V) - x := by
      intro m
      rw [Submodule.coe_sub, hvalx]
    have hfixvec : ∀ l m : ↥L,
        ρ (l : G) (ρ (m : G) (x : V) - x) = ρ (m : G) (x : V) - x := by
      intro l m
      have h1 := hmem m
      rw [Submodule.mem_comap] at h1
      have h2 := (mem_fixSub.mp h1) l l.2
      simpa [hval] using h2
    have hfix : ∀ l m : ↥L,
        SU.toRepresentation (π₁ (l, 1)) (SU.toRepresentation (π₁ (m, 1)) x - x) =
          SU.toRepresentation (π₁ (m, 1)) x - x := by
      intro l m
      apply Subtype.ext
      rw [m1S_sub_toRepresentation_val]
      simp only [Submodule.coe_sub, hvalx]
      simpa [hπ₁L] using hfixvec l m
    let φ : ↥L →* Multiplicative ↥SU.toSubmodule :=
      { toFun := fun l => Multiplicative.ofAdd (SU.toRepresentation (π₁ (l, 1)) x - x)
        map_one' := by
          show Multiplicative.ofAdd (SU.toRepresentation (π₁ (1, 1)) x - x) = 1
          rw [show π₁ (1, 1) = 1 from map_one π₁, map_one, Module.End.one_apply, sub_self]
          rfl
        map_mul' := fun l m => by
          show Multiplicative.ofAdd (SU.toRepresentation (π₁ (l * m, 1)) x - x) =
            Multiplicative.ofAdd (SU.toRepresentation (π₁ (l, 1)) x - x) *
              Multiplicative.ofAdd (SU.toRepresentation (π₁ (m, 1)) x - x)
          rw [← ofAdd_add]
          congr 1
          have hlm1 : π₁ (l * m, 1) = π₁ (l, 1) * π₁ (m, 1) := by
            simpa using map_mul π₁ (l, 1) (m, 1)
          have hlm : SU.toRepresentation (π₁ (l * m, 1)) x =
              SU.toRepresentation (π₁ (l, 1)) (SU.toRepresentation (π₁ (m, 1)) x) := by
            rw [hlm1, map_mul]
            rfl
          have hsplit : SU.toRepresentation (π₁ (l, 1))
                (SU.toRepresentation (π₁ (m, 1)) x) - x =
              SU.toRepresentation (π₁ (l, 1)) (SU.toRepresentation (π₁ (m, 1)) x - x) +
                (SU.toRepresentation (π₁ (l, 1)) x - x) := by
            rw [map_sub]
            abel
          rw [hlm, hsplit, hfix]
          abel }
    have hker := Abelianization.commutator_subset_ker φ
    rw [hperf] at hker
    have hzero : ∀ l : ↥L, SU.toRepresentation (π₁ (l, 1)) x - x = 0 := fun l =>
      ofAdd_eq_one.mp (hker (Subgroup.mem_top l))
    have hx : x ∈ SC.toSubmodule := by
      rw [Submodule.mem_comap]
      change ∀ l ∈ L, ρ l (x : V) = x
      intro l hl
      have h2 : SU.toRepresentation (π₁ (⟨l, hl⟩, 1)) x = x := sub_eq_zero.mp (hzero ⟨l, hl⟩)
      have h3 := congrArg (fun y : ↥SU.toSubmodule => (y : V)) h2
      rw [m1S_sub_toRepresentation_val] at h3
      simpa [hπ₁L] using h3
    exact (Submodule.Quotient.mk_eq_zero (p := SC.toSubmodule)).mpr hx
  have hF2 : ∀ q : ↥SU.toSubmodule ⧸ SC.toSubmodule, q ∈ Submodule.span (ZMod 2)
      {w | ∃ l : ↥L, ∃ y, w = ρQ (π₁ (l, 1)) y - y} := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := SC.toSubmodule) q
    let T : Submodule (ZMod 2) (↥SU.toSubmodule ⧸ SC.toSubmodule) :=
      Submodule.span (ZMod 2) {w | ∃ l : ↥L, ∃ y, w = ρQ (π₁ (l, 1)) y - y}
    let X : Submodule (ZMod 2) V := commOn ρ L (commOn ρ L ⊤)
    have hUU : X = commOn ρ L ⊤ :=
      commOn_commOn_eq (ρ := ρ) (A := A) (L := L) hA2 hAN hLA
    have hx : (x : V) ∈ X := by
      rw [hUU]
      exact x.2
    have hUL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) :=
      fun l hl => hUinv l (Subgroup.mem_sup_left hl)
    have hXU : X ≤ commOn ρ L ⊤ := CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Replacement.commOn_le hUL
    have key : ∀ v ∈ X, (∀ hv : v ∈ X,
        (Submodule.Quotient.mk (⟨v, hXU hv⟩ : ↥(commOn ρ L ⊤)) : _) ∈ T) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hvgen =>
        intro hvX
        obtain ⟨l, hl, u, hu, rfl⟩ := hvgen
        have hrep : ((SU.toRepresentation (π₁ (⟨l, hl⟩, 1))
            (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) : ↥SU.toSubmodule) : V) = ρ l u := by
          rw [m1S_sub_toRepresentation_val]
          simp [hπ₁L]
        have hsub : SU.toRepresentation (π₁ (⟨l, hl⟩, 1))
              (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) -
              (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) =
            (⟨ρ l u - u, hXU hvX⟩ : ↥(commOn ρ L ⊤)) := by
          apply Subtype.ext
          simp [hrep]
        refine Submodule.subset_span
          ⟨⟨l, hl⟩, (Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤))), ?_⟩
        have hq1 : (Submodule.Quotient.mk (SU.toRepresentation (π₁ (⟨l, hl⟩, 1))
              (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) : _) =
            SC.quotient (π₁ (⟨l, hl⟩, 1))
              (Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) :=
          (Subrepresentation.quotient_apply_mk SC (π₁ (⟨l, hl⟩, 1))
            (⟨u, hu⟩ : ↥(commOn ρ L ⊤))).symm
        calc Submodule.Quotient.mk (⟨ρ l u - u, hXU hvX⟩ : ↥(commOn ρ L ⊤))
            = Submodule.Quotient.mk (SU.toRepresentation (π₁ (⟨l, hl⟩, 1))
                (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) -
                (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) := by rw [hsub]
          _ = Submodule.Quotient.mk (SU.toRepresentation (π₁ (⟨l, hl⟩, 1))
                (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) -
              Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) := by
              rw [Submodule.Quotient.mk_sub]
          _ = SC.quotient (π₁ (⟨l, hl⟩, 1))
                (Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) -
              Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) := by rw [hq1]
          _ = ρQ (π₁ (⟨l, hl⟩, 1))
                (Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤))) -
              Submodule.Quotient.mk (⟨u, hu⟩ : ↥(commOn ρ L ⊤)) := rfl
      | zero =>
        intro hvX
        have h0 : (⟨(0 : V), hXU hvX⟩ : ↥(commOn ρ L ⊤)) = 0 := rfl
        rw [h0]
        exact T.zero_mem
      | add v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
        intro hvX
        have h1 := ih₁ hv₁
        have h2 := ih₂ hv₂
        have hsum : (⟨v₁ + v₂, hXU hvX⟩ : ↥(commOn ρ L ⊤)) =
            (⟨v₁, hXU hv₁⟩ : ↥(commOn ρ L ⊤)) +
              (⟨v₂, hXU hv₂⟩ : ↥(commOn ρ L ⊤)) := rfl
        rw [hsum, Submodule.Quotient.mk_add]
        exact T.add_mem h1 h2
      | smul c v hv ih =>
        intro hvX
        have h1 := ih hv
        have hsm : (⟨c • v, hXU hvX⟩ : ↥(commOn ρ L ⊤)) =
            c • (⟨v, hXU hv⟩ : ↥(commOn ρ L ⊤)) := rfl
        rw [hsm, Submodule.Quotient.mk_smul]
        exact T.smul_mem c h1
    have hkey := key (x : V) hx hx
    have hxeq : (⟨(x : V), hXU hx⟩ : ↥(commOn ρ L ⊤)) = x := Subtype.ext rfl
    rwa [hxeq] at hkey

  have hbud : ∀ (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation (ρQ.comp π₁)),
      IsCompositionSeries r Vs →
      ∑ i ∈ nontrivialFactors Vs, factorCodim Vs (graphSub lB) i ≤
        Nat.log 2 (Nat.card ((graphSub lB).map
          (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))))) := by
    intro r Vs hVs
    let φ : ↥B →* (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) :=
      (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))).comp (lB.prod (MonoidHom.id ↥B))
    have hrange : φ.range = (graphSub lB).map (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))) :=
      (MonoidHom.map_range _ _).symm
    have hφ : ∀ b : ↥B, φ b = 1 → (b : G) ∈ cenOn ρ B (commOn ρ L ⊤) := by
      intro b hb
      have h1 : (lB b, b) ∈ CFSG.pCore 2 (↥L × ↥B) := (QuotientGroup.eq_one_iff _).mp hb
      rw [pCore_prod_eq_ker_fst hBp hLp] at h1
      exact mem_cenOn_of_lift_eq_one lB hlB hmove b (MonoidHom.mem_ker.mp h1)
    have hlog := finrank_sub_le_log_card_range hbestB φ hφ
    rw [hrange] at hlog
    let C : Subrepresentation (SU.toRepresentation.comp π₁) :=
      ⟨SC.toSubmodule, fun k _ hx => SC.apply_mem_toSubmodule (π₁ k) hx⟩
    let SU' : Subrepresentation (ρ.comp π) :=
      ⟨commOn ρ L ⊤, fun g _ hw => hUinv (π g) (hπmem g) _ hw⟩
    have hfixeq : fixSub (SU.toRepresentation.comp π₁) (graphSub lB) =
        fixSub SU'.toRepresentation (graphSub lB) := rfl
    calc ∑ i ∈ nontrivialFactors Vs, factorCodim Vs (graphSub lB) i
        ≤ ∑ i, factorCodim Vs (graphSub lB) i :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ finrank (ZMod 2) (↥SU.toSubmodule ⧸ SC.toSubmodule) -
            finrank (ZMod 2) ↥(fixSub (ρQ.comp π₁) (graphSub lB)) :=
          sum_factorCodim_le Vs (fun i => (hVs.covBy i).le) hVs.zero hVs.last _
      _ ≤ finrank (ZMod 2) ↥SU.toSubmodule -
            finrank (ZMod 2) ↥(fixSub (SU.toRepresentation.comp π₁) (graphSub lB)) := by
          have hstep := finrank_quotient_sub_finrank_fixSub_le
            (K := ↥L × ↥B) (ρ := SU.toRepresentation.comp π₁) C (graphSub lB)
          have hCq : C.quotient = ρQ.comp π₁ := rfl
          rw [hCq] at hstep
          exact hstep
      _ = finrank (ZMod 2) ↥SU.toSubmodule -
            finrank (ZMod 2) ↥(fixOn ρ B (commOn ρ L ⊤)) := by
          rw [hfixeq, finrank_fixSub_graph lB π hgr SU']
      _ ≤ Nat.log 2 (Nat.card ((graphSub lB).map
            (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))))) := hlog
  have hQ : Nontrivial (↥SU.toSubmodule ⧸ SC.toSubmodule) := by
    by_contra hnt
    have hsubQ : Subsingleton (↥SU.toSubmodule ⧸ SC.toSubmodule) :=
      not_nontrivial_iff_subsingleton.mp hnt
    have hSC : SC.toSubmodule = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsubQ
    apply hLU
    intro l hl
    refine mem_cenOn.mpr ⟨hl, fun u hu => ?_⟩
    have hu' : (⟨u, hu⟩ : ↥SU.toSubmodule) ∈ SC.toSubmodule := by
      rw [hSC]
      exact Submodule.mem_top
    rw [Submodule.mem_comap] at hu'
    have h2 := (mem_fixSub.mp hu') l hl
    simpa using h2
  obtain ⟨Mat, hMat, hMatr, W', hW'L, hW'A, φ, hφ⟩ := m1_qlevel hn hFc e hperf hAN hLN hAN'
    hBp hLp lB hnotle e1 he1 π₁ hπ₁L ρQ hF1 hF2 hbud hQ
  refine ⟨Mat, hMat, hMatr, ?_⟩
  exact m1N_lift_final (ρ := ρ) (N := N) (SU := SU) (SC := SC) (W' := W')
    (L := L) (iL := π₁.comp (MonoidHom.inl ↥L ↥B))
    (hiL := fun l => by
      change ((π₁ (l, 1) : ↥N) : G) = l
      rw [hπ₁L l])
    (A := A) (iA := (Subgroup.subtype A).codRestrict N (fun a => hAN' a.2))
    (hiA := fun a => rfl)
    (hW'L := fun l y hy => hW'L l y hy)
    (hW'A := fun a y hy => hW'A a.1 a.2 y hy)
    (M₀ := W') (hM₀L := fun l y hy => hW'L l y hy)
    (Mat := Mat) (φ₀ := φ) (hφ₀ := fun l y => hφ l y)
    (ψ' := AddEquiv.refl _) (hψ' := fun l y => rfl)
    (hC := fun u => by
      rw [Submodule.mem_comap]
      exact mem_fixSub)

theorem exists_natQuot_sl3 {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) {L : Subgroup G} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hbest : IsBestOffenderOn ρ A ⊤)
    (hnot : ¬ A ≤ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ N : NatQuot ρ L F 3,
      N.Mat.range = (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range ∧
      (∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x}) ∧
      ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I := by
  have hfaith' : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := fun a _ h =>
    hfaith (by rw [map_one]; exact LinearMap.ext h)
  obtain ⟨hA2, -⟩ := (isBestOffender_iff_on ρ A hfaith').mpr hbest
  have hquasi : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_mulEquiv_sl3 e
  have hLA : ⁅L, A⁆ = L := commutator_eq_of_isQuasisimple_of_not_le hquasi hAN hnot
  obtain ⟨Mat, hMat, hMatr, W, hWL, hWA, p, hp, hpL, hker⟩ :=
    exists_natural_section_sl3 ρ hfaith hn hF e hA2 hAN hLA hbest
  have hnt : ∃ l : ↥L, Mat l ≠ 1 := exists_ne_one_of_mulEquiv_sl3 e Mat hMat
  obtain ⟨N, hNMat, hIcomm, hAI⟩ := NatQuot.exists_of_section hquasi.1 Mat hMat
    (addSubgroup_eq_bot_or_top_of_range Mat hMatr) hnt hWL p hp hpL hker hAN hWA
  exact ⟨N, hNMat ▸ hMatr, hIcomm, hAI⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
