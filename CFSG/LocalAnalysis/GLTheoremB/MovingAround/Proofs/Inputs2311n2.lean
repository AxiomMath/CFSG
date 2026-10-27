module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311n
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.E7SixProved
public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous
public import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.LieType.SeitzGeneration.HyperCoverE6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311j2
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311n

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LieType.Chevalley (hyperRSet)

section GenericTwo

theorem le_closure_of_map_le_n {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    {X : Subgroup G} {P : Subgroup H} {T : Set G} {W : Set H}
    (hXP : ∀ x ∈ X, φ x ∈ P) (hP : P ≤ Subgroup.closure W) (hW : W ⊆ φ '' T) :
    X ≤ Subgroup.closure T := by
  intro x hx
  have h1 : φ x ∈ (Subgroup.closure T).map φ := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hW (hP (hXP x hx))
  obtain ⟨x', hx', hxx'⟩ := h1
  rw [← hφ hxx']
  exact hx'

theorem exists_sl2_rElement_ne_one_n (K : Type) [Field K] :
    ∃ Y : Matrix.SpecialLinearGroup (Fin 2) K, Y ≠ 1 ∧ Y ^ ringChar K = 1 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K), fun h => ?_,
    Inputs2311c.transvection_pow_ringChar _ _⟩
  have h1 := (Matrix.SpecialLinearGroup.transvection_mem_center_iff (show (0 : Fin 2) ≠ 1 by decide)
    (1 : K)).1 (by rw [h]; exact Subgroup.one_mem _)
  exact one_ne_zero h1

theorem mem_closure_hyperRSet_of_split_layer_n {G H : Type} [Group G] [Finite G] [Group H] {p r : ℕ}
    [hp : Fact p.Prime] [hr : Fact r.Prime] (φ : G →* H) (hφ : Function.Injective φ)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) {y : G} (hy : y ∈ E) (hy1 : y ≠ 1)
    {e₀ e₁ : G} (he₀ : e₀ ∈ E) (he₀y : e₀ ∉ Subgroup.zpowers y) (he₁ : e₁ ∈ E)
    (he₁y : e₁ ∉ Subgroup.zpowers y) (P₀ : Subgroup H) [Finite P₀] (hP₀q : CFSG.IsQuasisimple P₀)
    (hP₀r : r ∣ Nat.card P₀) (hP₀φ : ∀ u ∈ P₀, ∃ g : G, g * y = y * g ∧ φ g = u)
    (hP₀e : ∀ g : G, φ g ∈ P₀ → g * e₀ = e₀ * g)
    {k k₀ : G} (hky : k * y = y * k) (hk₀y : k₀ * y = y * k₀) (hk₀P : φ k₀ ∈ P₀)
    (hk₁e : (k * k₀⁻¹) * e₁ = e₁ * (k * k₀⁻¹))
    (hkP : ∀ g : G, φ g ∈ P₀ → φ (k⁻¹ * g * k) ∈ P₀) (hkr : ∃ n : ℕ, k ^ r ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E r p) := by
  classical
  set N : Subgroup G := Subgroup.closure (hyperRSet ⊤ E r p) with hN
  set X₀ : Subgroup G := Subgroup.centralizer ({y} : Set G) ⊓ P₀.comap φ with hX₀
  have hmemX : ∀ g, g ∈ X₀ ↔ g * y = y * g ∧ φ g ∈ P₀ := by
    intro g
    rw [hX₀, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap]
  have hk₀X : k₀ ∈ X₀ := (hmemX k₀).2 ⟨hk₀y, hk₀P⟩
  have hky' : k⁻¹ * y = y * k⁻¹ := (Commute.inv_left (hky : Commute k y)).eq
  have hkX : ∀ z ∈ X₀, k⁻¹ * z * k ∈ X₀ := by
    intro z hz
    obtain ⟨hzy, hzP⟩ := (hmemX z).1 hz
    refine (hmemX _).2 ⟨?_, hkP z hzP⟩
    calc k⁻¹ * z * k * y = k⁻¹ * z * (k * y) := by group
      _ = k⁻¹ * z * (y * k) := by rw [hky]
      _ = k⁻¹ * (z * y) * k := by group
      _ = k⁻¹ * (y * z) * k := by rw [hzy]
      _ = (k⁻¹ * y) * z * k := by group
      _ = (y * k⁻¹) * z * k := by rw [hky']
      _ = y * (k⁻¹ * z * k) := by group
  obtain ⟨n₀, hn₀⟩ := hkr
  obtain ⟨u, v, huv, hu, hur, hvX⟩ := exists_rElement_mul_of_mul_n hr.out (orderOf_pos _).ne' hk₀X
    (show k = (k * k₀⁻¹) * k₀ by group) hkX hn₀
  have hk₀y' : k₀⁻¹ * y = y * k₀⁻¹ := (Commute.inv_left (hk₀y : Commute k₀ y)).eq
  have hk₁y : (k * k₀⁻¹) * y = y * (k * k₀⁻¹) := by
    calc k * k₀⁻¹ * y = k * (k₀⁻¹ * y) := by group
      _ = k * (y * k₀⁻¹) := by rw [hk₀y']
      _ = (k * y) * k₀⁻¹ := by group
      _ = (y * k) * k₀⁻¹ := by rw [hky]
      _ = y * (k * k₀⁻¹) := by group
  have huN : u ∈ N := mem_closure_hyperRSet_of_commute_pair_n hE hEc hy he₁ hy1 he₁y
    (commute_of_mem_zpowers_n hu hk₁y) (commute_of_mem_zpowers_n hu hk₁e) hur
  have hX₀N : X₀ ≤ N := by
    have hPgen := Inputs2311f.le_closure_pow_of_quasisimple (r := r) hP₀q hP₀r
    refine (le_closure_of_map_le_n φ hφ (X := X₀) (P := P₀)
      (T := {z | z ∈ X₀ ∧ ∃ n : ℕ, z ^ r ^ n = 1}) (fun x hx => ((hmemX x).1 hx).2) hPgen ?_).trans
      ((Subgroup.closure_le _).2 ?_)
    · rintro w ⟨hwP, n, hn⟩
      obtain ⟨g, hgy, rfl⟩ := hP₀φ w hwP
      refine ⟨g, ⟨(hmemX g).2 ⟨hgy, hwP⟩, n, ?_⟩, rfl⟩
      apply hφ
      rw [map_pow, hn, map_one]
    · rintro z ⟨hz, hzr⟩
      obtain ⟨hzy, hzP⟩ := (hmemX z).1 hz
      exact mem_closure_hyperRSet_of_commute_pair_n hE hEc hy he₀ hy1 he₀y hzy (hP₀e z hzP) hzr
  have hk : k = u * (v * k₀) := by
    have h1 : k = (k * k₀⁻¹) * k₀ := by group
    rw [h1, huv, mul_assoc]
  rw [hk]
  exact N.mul_mem huN (hX₀N (X₀.mul_mem hvX hk₀X))

theorem uniPlaneGen_of_sylowTorus_rgen_n {d : TauCeti.ValidLieTypeIndex} {p m : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : CFSG.LieType.SeitzGeneration.Cat d →* _))
    (hS : SylowTorus (CFSG.LieType.SeitzGeneration.Cat d) p m)
    {Ec : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)} (hEcel : IsElemAbelian p Ec)
    (hEcc : Nat.card Ec = p ^ m)
    (hgen : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ Ec d.1.characteristic p))
    {E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hin : InnerPlane d p E) : Inputs2311c.UniPlaneGen d.1.characteristic E := by
  classical
  obtain ⟨E', hE'el, hE'c, hE'map⟩ := CFSG.HardMathSupport.Lang.AnisoE6.exists_map_conj_eq hinj hin hE hEc
  obtain ⟨T, V0, -, hconj, hV0T, hV0tor, hV0el, hV0c⟩ := hS.exists_torus
  obtain ⟨g, hg⟩ := hconj E' (CFSG.Open.IsElemAbelian.isPGroup hE'el)
  set V : Subgroup (CFSG.LieType.SeitzGeneration.Cat d) := V0.map (MulAut.conj g).toMonoidHom with hVdef
  have hVel : IsElemAbelian p V :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hV0el _
  have hVc : Nat.card V = p ^ m := by
    rw [hVdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV0c]
  have hE'V : E' ≤ V := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hg hx
    have htp : t ^ p = 1 := by
      have h1 := hE'el.2 x hx
      rw [← hxt] at h1
      have : (MulAut.conj g) (t ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact (MulAut.conj g).injective (this.trans (map_one _).symm)
    exact ⟨t, hV0tor t ht htp, hxt⟩
  obtain ⟨x, hx⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.exists_conj_of_sylowTorus_cube hp hS hEcel hEcc hVel hVc
  have hVgen : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ V d.1.characteristic p) := by
    refine CFSG.LieType.SeitzGeneration.QuasiHigh.closure_hyperRSet_of_mulEquiv (MulAut.conj x)⁻¹ ?_
    have hVEc : V.map ((MulAut.conj x)⁻¹ : MulAut _).toMonoidHom = Ec := by
      rw [hx, Subgroup.map_map]
      convert Subgroup.map_id Ec
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [hVEc]
    exact hgen
  rw [Inputs2311c.UniPlaneGen, eq_top_iff]
  refine hVgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro s ⟨-, ⟨n, hn⟩, B, hBV, hBi, hsB⟩
  obtain ⟨y, hyEB, hy1⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.exists_ne_one_mem_plane_inf_hyperplane hp hE'V
    hE'c hBi (by rw [hVc]; exact (pow_pos hp.pos m).ne')
  refine Inputs2311c.mem_uniPlaneClosure (e := MulAut.conj y) ?_ ?_ ?_ hn
  · rw [← hE'map]
    exact Subgroup.mem_map_of_mem _ hyEB.1
  · intro h1
    exact hy1 (hinj (by rw [h1, map_one]))
  · rw [MulAut.conj_apply, Subgroup.mem_centralizer_iff.1 hsB y hyEB.2, mul_inv_cancel_right]

end GenericTwo

section RootSL2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ringChar_dvd_card_of_rootSL2_mem_n {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    {P : Subgroup (ModGL τ L)} (i : Fin τ.rank) (h₀ : ModGL τ L)
    (hroot : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
      h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) B) * h₀⁻¹ ∈ P) :
    ringChar K ∣ Nat.card P := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hr, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hr⟩
  obtain ⟨Y, hY1, hYr⟩ := exists_sl2_rElement_ne_one_n K
  have hzP := hroot Y
  have hzr : (h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹) ^
      ringChar K = 1 := by
    rw [conj_pow, ← map_pow, ← map_pow, hYr, map_one, map_one, mul_one, mul_inv_cancel]
  have hz1 : h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ≠ 1 := by
    intro h
    apply hY1
    have h1 : simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) = 1 := by
      have := congrArg (fun w => h₀⁻¹ * w * h₀) h
      simpa [mul_assoc] using this
    apply CFSG.GH74.Filter.Lie.sl2_map_injective (algebraMap K L)
    apply CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_field τ i
    rw [h1, map_one, map_one]
  have ho : orderOf (⟨_, hzP⟩ : P) = ringChar K := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hzr hz1
  rw [← ho]
  exact orderOf_dvd_natCard _

end RootSL2

section OrbitR

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open CFSG.LieType.Chevalley (hyperRSet)

open scoped Matrix

set_option linter.unusedSectionVars false

theorem mem_closure_hyperRSet_of_kernel_orbit_n (hLay : E7ThreeLayers)
    {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    {c : adjointGroup .E7 K} {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E7 K} (hy : y ∈ E) (hy1 : y ≠ 1) (σ : Fin Tag.E7.rank → ℤ)
    (hσ : ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 b = psiC F.g0 c y →
      ∀ α ∈ rootCharKernel b, ∃ j : ℕ, α = ((((-1 : ℤ) • e7T3W) ^ j) *ᵥ σ))
    {k : adjointGroup .E7 K} (hk : k * y = y * k) (hkr : ∃ n : ℕ, k ^ ℓ ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E ℓ p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_three_prelim F hp hyo c hhy
  obtain ⟨ι₀, P, ψ, -, hψinj, hψ, hψHQ, -⟩ := e7_three_perx hLay F hf hK hp hp3 hε hpf hstab hyo c
    hhy hb hap hb1 hbh
  have hbE : ∀ e : E, ∃ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b = (psiC F.g0 c).comp E.subtype e := by
    intro e
    have h := hT e e.2
    rw [F.hT] at h
    obtain ⟨b, -, hb⟩ := h
    exact ⟨b, hb⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom ((psiC F.g0 c).comp E.subtype) hbE σ
  obtain ⟨e, hey, hχe⟩ := CFSG.HardMathSupport.Lang.TwE6Step3.exists_mem_ker_not_mem_zpowers hE hEc χ hy
  have hee : (e : adjointGroup .E7 K) ∈ E := e.2
  have hTe := hT e e.2
  have hTe' := hTe
  rw [F.hT] at hTe'
  obtain ⟨be, hbeF, hbe⟩ := hTe'
  have hbe' : rootDiagUnit .E7 be = (psiC F.g0 c).comp E.subtype e := hbe
  have hσe : rootChar be σ = 1 := by
    rw [← hχ e be hbe']
    exact hχe
  have hsub : rootCharKernel b ⊆ rootCharKernel be := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    obtain ⟨j, rfl⟩ := hσ b (by rw [hbh, psiC_apply]) α hα
    rw [rootChar_pow_mulVec_of_mem_fixedCharTuples (hFr := hFr) hbeF j σ, hσe, one_pow]
  have hbeT : rootDiagUnit .E7 be ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hbe']; exact hTe
  have hcent : torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b) ≤
      Subgroup.centralizer {rootDiagUnit .E7 be} := by
    refine sup_le ?_ (rootSpan_le_centralizer be hsub)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact torusGroup_comm hx (mem_twistedTorusOf.1 hbeT).1
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiC F.g0 c k ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b) := by
    have h := hψHQ ⟨k, hkC⟩
    rw [hψ] at h
    simpa [psiC_apply] using h
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcent hψk)
  rw [hbe'] at hc
  have hke : k * e = e * k := by
    apply psiC_injective F.g0 c
    rw [map_mul, map_mul]
    exact hc
  exact mem_closure_hyperRSet_of_commute_pair_n hE hEc hy hee hy1 hey hk hke hkr

end OrbitR

section Kind01R

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open CFSG.LieType.Chevalley (hyperRSet)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

theorem e7T3_layer_A2_eq_root_n {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 0) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      P = rootSpan Tag.E7 L ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) ∧
      ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L (e7Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  have hg' : (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 support13 := by
    rw [hkind] at hg
    exact hg
  obtain ⟨P, hPeq, hfac, h₀, hh₀⟩ := e7_a2_factor hf hk hε hq2 ((coxeterSystem Tag.E7).wordProd w) n
    hnm ((coxeterSystem Tag.E7).wordProd cm.u) hg' (fun α hα => by
      have h1 := hact α (by rw [hkind]; exact hα)
      rw [h1, hkind]
      simp [e7T3Beta, permLattice_one])
  rw [hkind]
  exact ⟨P, hPeq, hfac, h₀, hh₀⟩

theorem mem_closure_hyperRSet_of_kind01_n (K : Type) [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    (c : adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (y : adjointGroup .E7 K) (hy : y ∈ E) (hy1 : y ≠ 1) (b : Fin Tag.E7.rank → Lˣ)
    (hb : rootDiagUnit .E7 b = psiC F.g0 c y) (cert : E7T3Cert) (hcert : cert ∈ e7T3Certs)
    (hker : rootCharKernel b = {α | ∃ l ∈ cert.rootList, α = toVec Tag.E7.rank l})
    (hkinds : cert.comps.map E7T3Comp.kind = [0, 1]) (hσ0 : sigma0 ∈ cert.rootList)
    (k : adjointGroup .E7 K) (hk : k * y = y * k) (hkr : ∃ n : ℕ, k ^ ℓ ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E ℓ p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b', hb', hap, hb1, hbh, huniq⟩ := e7_three_prelim F hp hyo c hhy
  have hbb : b = b' := huniq b (by rw [hb, psiC_apply])
  rw [← hbb] at hbh
  have hq2 : 2 < ℓ ^ f := by
    have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [← hK]
    exact e7T3_q_gt_two hp3 rfl hKq hpf rfl
  obtain ⟨hgood, hσB, hσspan, τ, hτA, hτspan⟩ := cert_cases01 cert hcert hkinds hσ0
  have hcomps := hgood.1
  rcases hcc : cert.comps with _ | ⟨cm₀, _ | ⟨cm₁, _ | ⟨cm₂, rest⟩⟩⟩
  · rw [hcc] at hkinds; simp at hkinds
  · rw [hcc] at hkinds; simp at hkinds
  · rw [hcc] at hkinds hcomps
    have hg₀ : cm₀.Good e7T3Word cert.w := hcomps cm₀ List.mem_cons_self
    have hg₁ : cm₁.Good e7T3Word cert.w :=
      hcomps cm₁ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hk₀ : cm₀.kind < 4 := hg₀.2.1
    have hk₁ : cm₁.kind < 4 := hg₁.2.1
    have hkk : cm₀.kind = 0 ∧ cm₁.kind = 1 := by simpa using hkinds
    have hset := e7T3_rootSet_two hcc hk₀ hk₁
    rw [hkk.1, hkk.2] at hset
    set v := (coxeterSystem Tag.E7).wordProd cert.w with hv
    have hKer : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1) := hker.trans hset
    obtain ⟨P₀, hP₀eq, hfac₀, hc₀, hhc₀⟩ := e7T3_layer_A2_eq_root_n (k := K) hf hK hε (fun _ => hq2) F.hnW hg₀
      hkk.1
    obtain ⟨P₁, hfac₁⟩ := e7T3_layer_A1 hf hε F.hnW hg₁ hkk.2
    rw [hkk.1] at hP₀eq hfac₀
    rw [hkk.2] at hfac₁
    have hS₀ := isRoot_image_parabolicRoots v (e7T3J 0)
    have hS₁ := isRoot_image_parabolicRoots v (e7T3J 1)
    have horth : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0),
        ∀ β ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1),
          iform (τ := Tag.E7) α β = 0 := by
      rintro _ ⟨α', hα', rfl⟩ _ ⟨β', hβ', rfl⟩
      rw [iform_smul]
      rw [parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hα'
      rw [parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hβ'
      obtain ⟨l, hl, rfl⟩ := hα'
      obtain ⟨l', hl', rfl⟩ := hβ'
      exact e7T3_orth_A2_A1 l hl l' hl'
    have horth' : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0),
        ∀ β ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1),
          α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := fun α hα β hβ => by
      rw [dotProduct_mulVec_eq_iform]
      exact horth α hα β hβ
    have hfam := sigmaFactor_union_E7 hS₀ hS₁ horth hfac₀ hfac₁
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψθ, hPψ⟩ := e7_perx_of_family F hK hp hyo c hstab hhy hbh
      (P := Sum.elim (fun _ : Unit => P₀) (fun _ : Unit => P₁)) (by rw [hKer]; exact hfam)
    have hψ' : ∀ z, ψ z = psiC F.g0 c (z : adjointGroup .E7 K) := fun z => by
      rw [hψ, psiC_apply]
    have hkC : k ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hk
    set k' : Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := ⟨k, hkC⟩ with hk'
    have hm : ψ k' ∈ torusGroup .E7 L ⊔ rootSpan .E7 L
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
          (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1)) := by
      have := hψHQ k'
      rwa [hKer] at this
    have hJ₀ := e7T3_stab_A2 hε F.hnW hg₀ hkk.1
    have hJ₁ := e7T3_stab_A1 hε F.hnW hg₁ hkk.2
    obtain ⟨t, htH, htθ, a₀, ha₀, ha₀θ, a₁, ha₁, ha₁θ, hmeq⟩ := e7_fixedSplit_A2_3A1
      iterateFrobenius_bijective Finite.one_lt_card hFr F.hnm v hJ₀ hJ₁ hm (hψθ k')
    have ha₀P : a₀ ∈ P₀ := by
      rw [hP₀eq]
      exact Subgroup.mem_inf.2 ⟨ha₀, ha₀θ⟩
    obtain ⟨k₀', hk₀'⟩ := hPψ (Sum.inl ()) ha₀P
    have hcomm : a₀ * a₁ = a₁ * a₀ :=
      rootSpan_commute_of_orth (τ := Tag.E7) (Or.inr (Or.inr (Or.inl rfl))) hS₀ hS₁ horth'
        a₀ ha₀ a₁ ha₁
    have hψk₁ : ψ (k' * k₀'⁻¹) = t * a₁ := by
      rw [map_mul, map_inv, hk₀', hmeq]
      calc t * a₀ * a₁ * a₀⁻¹ = t * (a₀ * a₁) * a₀⁻¹ := by group
        _ = t * (a₁ * a₀) * a₀⁻¹ := by rw [hcomm]
        _ = t * a₁ := by group
    obtain ⟨e₁, he₁E, he₁y, he₁k⟩ := exists_kill_elem F hK hE hEc hT hy hσspan
    have hS₁sub : ∀ be : Fin Tag.E7.rank → Lˣ,
        (∀ l ∈ e7CompB cert, rootChar be (toVec Tag.E7.rank l) = 1) →
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1) ⊆ rootCharKernel be := by
      intro be hbe α hα
      refine ⟨hS₁ α hα, ?_⟩
      obtain ⟨γ, hγ, rfl⟩ := hα
      rw [parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hγ
      obtain ⟨l, hl, rfl⟩ := hγ
      show rootChar be (v • toVec Tag.E7.rank l) = 1
      rw [hv, wordProd_smul_toVec7]
      exact hbe _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    have hS₀sub : ∀ be : Fin Tag.E7.rank → Lˣ,
        (∀ l ∈ e7CompA cert, rootChar be (toVec Tag.E7.rank l) = 1) →
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ⊆ rootCharKernel be := by
      intro be hbe α hα
      refine ⟨hS₀ α hα, ?_⟩
      obtain ⟨γ, hγ, rfl⟩ := hα
      rw [parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hγ
      obtain ⟨l, hl, rfl⟩ := hγ
      show rootChar be (v • toVec Tag.E7.rank l) = 1
      rw [hv, wordProd_smul_toVec7]
      exact hbe _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    have hψk₁' : psiC F.g0 c (((k' * k₀'⁻¹ : Subgroup.centralizer
        ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K)) = t * a₁ :=
      (hψ' _).symm.trans hψk₁
    have hcomm₁ : ((k' * k₀'⁻¹ : Subgroup.centralizer
        ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K) * e₁ =
        e₁ * ((k' * k₀'⁻¹ : Subgroup.centralizer
          ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K) := by
      apply psiC_injective F.g0 c
      have hTe := hT e₁ he₁E
      rw [F.hT] at hTe
      obtain ⟨be, -, hbe⟩ := hTe
      have hbe' : rootDiagUnit .E7 be = psiC F.g0 c e₁ := hbe
      have h := mul_commute_rootDiagUnit be (hS₁sub be (he₁k be hbe')) htH ha₁
      rw [map_mul, map_mul, hψk₁', ← hbe']
      exact h.symm
    obtain ⟨e₀, he₀E, he₀y, he₀k⟩ := exists_kill_elem F hK hE hEc hT hy hτspan
    have hψk₀ : psiC F.g0 c (k₀' : adjointGroup .E7 K) = a₀ := (hψ' k₀').symm.trans hk₀'
    have hTe₀ := hT e₀ he₀E
    rw [F.hT] at hTe₀
    obtain ⟨be₀, -, hbe₀⟩ := hTe₀
    have hbe₀' : rootDiagUnit .E7 be₀ = psiC F.g0 c e₀ := hbe₀
    have hP₀e : ∀ g : adjointGroup .E7 K, psiC F.g0 c g ∈ P₀ → g * e₀ = e₀ * g := by
      intro g hg
      apply psiC_injective F.g0 c
      have hgS : psiC F.g0 c g ∈
          rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0)) :=
        hfac₀.le_root () hg
      have h := mul_commute_rootDiagUnit be₀ (hS₀sub be₀ (he₀k be₀ hbe₀')) (one_mem _)
        (a := psiC F.g0 c g) hgS
      rw [map_mul, map_mul, ← hbe₀']
      simpa using h.symm
    have hP₀φ : ∀ u ∈ P₀, ∃ g : adjointGroup .E7 K, g * y = y * g ∧ psiC F.g0 c g = u := by
      intro u hu
      obtain ⟨z, hz⟩ := hPψ (Sum.inl ()) hu
      exact ⟨z, Subgroup.mem_centralizer_singleton_iff.1 z.2, (hψ' z).symm.trans hz⟩
    have hkP : ∀ g : adjointGroup .E7 K, psiC F.g0 c g ∈ P₀ →
        psiC F.g0 c (k⁻¹ * g * k) ∈ P₀ := by
      intro g hg
      have hmk : psiC F.g0 c k ∈ torusGroup .E7 L ⊔ rootSpan .E7 L
          ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
            (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1)) := by
        rw [← hψ' k']
        exact hm
      have hθk : psiC F.g0 c k ∈
          twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
        rw [← hψ' k']
        exact hψθ k'
      have h := hfam.2.2.2.2.2.1 (Sum.inl ()) _ (inv_mem hmk) (inv_mem hθk) _ hg
      rw [map_mul, map_mul, map_inv]
      simpa using h
    have hk₁e : (k * (k₀' : adjointGroup .E7 K)⁻¹) * e₁ = e₁ * (k * (k₀' : adjointGroup .E7 K)⁻¹) := by
      simpa [hk'] using hcomm₁
    have hdvd : ℓ ∣ Nat.card P₀ := by
      have h := ringChar_dvd_card_of_rootSL2_mem_n (K := K) (e7Index 0) hc₀ hhc₀
      rwa [ringChar.eq K ℓ] at h
    haveI : Finite P₀ := hfac₀.finite ()
    have hP₀q : CFSG.IsQuasisimple P₀ := hfac₀.quasi ()
    have hk₀P : psiC F.g0 c (k₀' : adjointGroup .E7 K) ∈ P₀ := by
      rw [hψk₀]
      exact ha₀P
    exact mem_closure_hyperRSet_of_split_layer_n (psiC F.g0 c) (psiC_injective F.g0 c) hE hEc hy hy1 he₀E he₀y
      he₁E he₁y P₀ hP₀q hdvd hP₀φ hP₀e hk (Subgroup.mem_centralizer_singleton_iff.1 k₀'.2) hk₀P hk₁e hkP hkr
  · rw [hcc] at hkinds; simp at hkinds

end Kind01R

section Kind3R

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open CFSG.LieType.Chevalley (hyperRSet)

open scoped Matrix

set_option linter.unusedSectionVars false

theorem mem_closure_hyperRSet_of_kind3_n (K : Type) [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    (c : adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (y : adjointGroup .E7 K) (hy : y ∈ E) (hy1 : y ≠ 1) (b : Fin Tag.E7.rank → Lˣ)
    (hb : rootDiagUnit .E7 b = psiC F.g0 c y) (cert : E7T3Cert) (hcert : cert ∈ e7T3Certs)
    (hker : rootCharKernel b = {α | ∃ l ∈ cert.rootList, α = toVec Tag.E7.rank l})
    (hkinds : cert.comps.map E7T3Comp.kind = [3])
    (k : adjointGroup .E7 K) (hk : k * y = y * k) (hkr : ∃ n : ℕ, k ^ ℓ ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E ℓ p) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hgood := cert_good3 cert hcert hkinds
  have hinj : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  rcases hcc : cert.comps with _ | ⟨cm₀, _ | ⟨cm₁, rest⟩⟩
  · rw [hcc] at hkinds
    simp at hkinds
  · rw [hcc] at hkinds
    have hkind : cm₀.kind = 3 := by simpa using hkinds
    have hg₀ : cm₀.Good e7T3Word cert.w := hgood.1 cm₀ (by rw [hcc]; exact List.mem_singleton_self _)
    have hk₀ : cm₀.kind < 4 := by rw [hkind]; norm_num
    have hset := e7T3_rootSet_single hcc hk₀
    rw [hkind] at hset
    obtain ⟨hg, hact⟩ := e7T3_comp_eps hε F.hnW hg₀
    have hg' : (coxeterSystem Tag.E7).wordProd cm₀.u ∈
        parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7) := by
      rw [hkind] at hg
      exact hg
    exact mem_closure_hyperRSet_of_a5_line_n F hf hK hp hp3 hpf hE hEc hT hy hy1
      ((coxeterSystem Tag.E7).wordProd cert.w)
      (fun b' hb' => by
        have hbb : b' = b := hinj (hb'.trans hb.symm)
        rw [hbb, hker]
        exact hset)
      ⟨(coxeterSystem Tag.E7).wordProd cm₀.u, hg', fun α hα => by
        have h1 := hact α (by rw [hkind]; exact hα)
        rw [h1, hkind, weyl_smul_zsmul_pm _ hε]
        simp [e7T3Beta, permLattice_one]⟩ hk hkr
  · rw [hcc] at hkinds
    simp at hkinds

end Kind3R

section AssemblyR

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open CFSG.LieType.Chevalley (hyperRSet)

open scoped Matrix

set_option linter.unusedSectionVars false

theorem exists_cube_top_le_closure_hyperRSet_E7Six_n (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (p : ℕ) (hp : p.Prime) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    ∃ E : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (⊤ : Subgroup (adjointGroup Tag.E7 K)) ≤ Subgroup.closure (hyperRSet ⊤ E r p) := by
  classical
  have hR : E7SixRSub := e7SixRSub
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := three_lt_of_orderOf_eq_six hp hord
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hrn, hcardn⟩ := FiniteField.card K r
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardn
  let L := AlgebraicClosure K
  have : CharP L r := charP_of_injective_algebraMap (algebraMap K L).injective r
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
    have h := (CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six
      hp hord).1
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
    have h' := Int.natCast_dvd_natCast.2 h
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at h'
    simpa [sub_eq_add_neg] using h'
  obtain ⟨F⟩ := exists_e7ThreeFrame K hf hK hp hp3 hε hpf L
  have hFr : ∀ x, iterateFrobenius L r (n : ℕ) x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def r (n : ℕ) x
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (((-1 : ℤ) : ℤ) : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using this
  have hLay : E7ThreeLayers :=
    e7ThreeLayers CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 CFSG.RankThree.PartOne.KA5L.a5Layer_E7
  obtain ⟨c, E, hE, hEc, hT0⟩ := exists_cube_in_frame F hp hord
  have hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L r (n : ℕ)))) := fun x hx => by
    rw [psiC_apply]; exact hT0 x hx
  have hbE : ∀ e : E, ∃ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b = (psiC F.g0 c).comp E.subtype e := by
    intro e
    have h := hT e e.2
    rw [F.hT] at h
    obtain ⟨b, -, hb⟩ := h
    exact ⟨b, hb⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom ((psiC F.g0 c).comp E.subtype) hbE
    (toVec Tag.E7.rank sigma0)
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero _ hp.ne_zero)
  have hpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hpg : IsPGroup p χ.ker := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hpE (x : E)⟩
  obtain ⟨K₁, hK₁⟩ := exists_subgroup_card_sq hpg (two_le_card_ker hE hEc χ)
  set E₁ : Subgroup (adjointGroup .E7 K) := (K₁.map χ.ker.subtype).map E.subtype with hE₁
  have hE₁E : E₁ ≤ E := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.card_map_of_injective χ.ker.subtype_injective, hK₁]
  have hE₁χ : ∀ y ∈ E₁, ∃ hyE : y ∈ E, χ ⟨y, hyE⟩ = 1 := by
    rintro _ ⟨z, ⟨w, -, hwz⟩, rfl⟩
    refine ⟨z.2, ?_⟩
    show χ z = 1
    rw [← hwz]
    exact w.2
  obtain ⟨R, hR1, hRp, hRc⟩ := hR K L F hK c
  have hE₁R : ∀ x ∈ E₁, ∀ u ∈ R, x * u = u * x := by
    intro x hx u hu
    obtain ⟨hxE, hχx⟩ := hE₁χ x hx
    obtain ⟨b, hb⟩ := hbE ⟨x, hxE⟩
    refine hRc x ⟨b, hb, ?_⟩ u hu
    rw [← hχ ⟨x, hxE⟩ b hb]
    exact hχx
  have hlines : ∀ y ∈ E₁, y ≠ 1 → ∀ k : adjointGroup .E7 K, k * y = y * k →
      (∃ m : ℕ, k ^ r ^ m = 1) → k ∈ Subgroup.closure (hyperRSet ⊤ E r p) := by
    intro y hyE₁ hy1 k hk' hkr
    obtain ⟨hyE, hχy⟩ := hE₁χ y hyE₁
    obtain ⟨b, hb⟩ := hbE ⟨y, hyE⟩
    have hbpsi : rootDiagUnit .E7 b = psiC F.g0 c y := hb
    have hσb : rootChar b (toVec Tag.E7.rank sigma0) = 1 := by
      rw [← hχ ⟨y, hyE⟩ b hb]; exact hχy
    have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hyE) hy1
    have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L r (n : ℕ)))) := by
      simpa [psiC_apply] using hT y hyE
    obtain ⟨b', hb', hap, hb1, hbh, huniq⟩ := e7_three_prelim F hp hyo c hhy
    have hbb' : b = b' := huniq b (by rw [hbpsi, psiC_apply])
    subst hbb'
    rcases e7T3_kernel_structure (iterateFrobenius L r (n : ℕ)) hFr hp hp3 hε hΦ hb' hap hb1 with
      hempty | ⟨cert, hcert, hker, hgood⟩
    · exfalso
      have : toVec Tag.E7.rank sigma0 ∈ rootCharKernel b := ⟨sigma0_isRoot, hσb⟩
      rw [hempty] at this
      exact this
    · have hσk : toVec Tag.E7.rank sigma0 ∈ rootCharKernel b := ⟨sigma0_isRoot, hσb⟩
      rw [hker] at hσk
      obtain ⟨l, hl, hlσ⟩ := hσk
      have hlr : l ∈ Tag.E7.artifactRoots := hgood.2.2.1 l hl
      have hmem : sigma0 ∈ cert.rootList := by
        rw [eq_sigma0_of_toVec_eq l hlr hlσ.symm] at hl
        exact hl
      rcases cert_cases cert hcert hmem with ⟨-, horb⟩ | hk3 | hk01
      · refine mem_closure_hyperRSet_of_kernel_orbit_n hLay F hf hK hp hp3 hpf hE hEc hT hyE hy1
          (toVec Tag.E7.rank sigma0) ?_ hk' hkr
        intro b'' hb'' α hα
        have : b'' = b := huniq b'' (by rw [hb'', psiC_apply])
        subst this
        rw [hker] at hα
        obtain ⟨l, hl, rfl⟩ := hα
        obtain ⟨j, -, rfl⟩ := horb l hl
        exact ⟨j, toVec_negWorbit j⟩
      · exact mem_closure_hyperRSet_of_kind3_n K L F hf hK hp hp3 hpf c E hE hEc hT y hyE hy1 b hbpsi cert
          hcert hker hk3 k hk' hkr
      · exact mem_closure_hyperRSet_of_kind01_n K L F hf hK hp hp3 hpf c E hE hEc hT y hyE hy1 b hbpsi cert
          hcert hker hk01 hmem k hk' hkr
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => hE.2 x (hE₁E hx)⟩
    apply Subtype.ext
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨a, hE₁E a.2⟩ ⟨b, hE₁E b.2⟩)
    exact h
  have hE₁ne : E₁ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hE₁c
    have := hp.one_lt
    nlinarith
  have hRn : ∀ x ∈ E₁, R.map (MulAut.conj x).toMonoidHom = R := by
    intro x hx
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := hE₁R x hx v hv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this, mul_inv_cancel_right]
      exact hv
    · intro hu
      refine ⟨u, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hE₁R x hx u hu, mul_inv_cancel_right]
  have hrp : r ≠ p := by
    intro hrp
    have h0 : ((Nat.card K : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, hK, ← hrp]
      exact dvd_pow_self r n.ne_zero
    rw [h0, orderOf_zero] at hord
    omega
  haveI : IsSimpleGroup ↥(adjointGroup Tag.E7 K) :=
    isSimpleGroup_adjointGroup_of_isQuasisimple (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K)
  have hgenR : RootInvariantHyperGenerationR (adjointGroup Tag.E7 K) r p := by
    intro A R' hAC hA hA1 hRC hRr hR' hAR
    haveI := hA
    exact ordinary_root_invariant_prime_subgroup_hyperplane_generation_r Tag.E7 K r p hrp A hAC hA1 R' hRC
      hRr hR' hAR
  have h1 := closure_hyperRSet_of_native (MulEquiv.refl _) hgenR hE₁el hE₁ne ⟨R, hR1, hRp, hRn⟩
  refine ⟨E, hE, hEc, h1.trans ((Subgroup.closure_le _).2 ?_)⟩
  rintro x ⟨-, hxr, B, hBE₁, hBi, hxB⟩
  have hBc := card_eq_of_relIndex_eq hp hBE₁ hE₁c hBi
  obtain ⟨y, hyB, hy1⟩ : ∃ y ∈ B, y ≠ 1 := by
    have hBne : B ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hBc
      exact hp.one_lt.ne hBc
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
    exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
  exact hlines y (hBE₁ hyB) hy1 x ((Subgroup.mem_centralizer_iff.1 hxB) y hyB).symm hxr

end AssemblyR

section CatR

open TauCeti

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_E7Six_inner_n :
    Inputs2311c.UniSeitzPlanes fun d p E => InnerPlane d p E ∧
      ∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, q, hq, hord⟩
  obtain rfl : d = .E7 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : (LieTypeIndex.E7 q).characteristic = q.p := LieTypeIndex.characteristic_E7 q
  have hpq : p ≠ q.p := fun h => hpd (by rw [hchar]; exact h)
  have h7 := CFSG.LieType.SeitzGeneration.ExcHigh.seven_le_of_orderOf_six hp hord
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hK]; exact hord
  obtain ⟨V, hVel, hVc, hgen⟩ := exists_cube_top_le_closure_hyperRSet_E7Six_n K q.p p hp hordK
  set Vc : Subgroup (Cat ⟨.E7 q, hv⟩) := V.map e.symm.toMonoidHom with hVcdef
  have hVcmap : Vc.map e.toMonoidHom = V := by
    rw [hVcdef, Subgroup.map_map]
    convert Subgroup.map_id V
    ext y
    simp
  have hVcgen : (⊤ : Subgroup (Cat ⟨.E7 q, hv⟩)) ≤
      Subgroup.closure (hyperRSet ⊤ Vc q.p p) := by
    refine CFSG.LieType.SeitzGeneration.QuasiHigh.closure_hyperRSet_of_mulEquiv e ?_
    rw [hVcmap]
    exact hgen
  have hVcel : IsElemAbelian p Vc :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hVel _
  have hVcc : Nat.card Vc = p ^ 3 := by
    rw [hVcdef, Subgroup.card_map_of_injective e.symm.injective, hVc]
  rw [← hchar] at hVcgen
  exact uniPlaneGen_of_sylowTorus_rgen_n hp (conj_injective_cat_E7 q hv)
    (CFSG.LieType.SeitzGeneration.ExcHigh.sylowTorus_cat_E7_six hv hp h7 hpq hord) hVcel hVcc hVcgen hE hc hin

end CatR

section Residual

open TauCeti

@[expose] def OddCpfInnerExc3 : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => Inputs2311c.OddCpfRest d p E ∧ InnerPlane d p E ∧ 5 ≤ p ∧
    (∃ q : PrimePower, d.1 = .E8 q ∧ 7 ≤ p ∧
      (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6))

@[expose] def Input23_11TwoRestExc3 : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
    InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
    (∃ q : PrimePower, d.1 = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 6))

set_option linter.unusedSectionVars false

theorem oddCpfInnerExc2_of_rest3 (h : OddCpfInnerExc3) : Inputs2311j.OddCpfInnerExc2 := by
  refine Inputs2311c.UniSeitzPlanes.of_cover (fun d p _ _ E hs => ?_) uniSeitzPlanes_E7Six_inner_n h
  obtain ⟨hR, hin, hp5, hcls⟩ := hs
  rcases hcls with hE7 | hE8
  · exact Or.inl ⟨hin, hE7⟩
  · exact Or.inr ⟨hR, hin, hp5, hE8⟩

theorem input23_11TwoRestExc2_of_rest3 (h : Input23_11TwoRestExc3) : Inputs2311j.Input23_11TwoRestExc2 := by
  refine Inputs2311c.UniSeitzPlanes.of_cover (fun d p _ _ E hs => ?_) uniSeitzPlanes_E7Six_inner_n h
  obtain ⟨hch, hp5, hcpf, hin, hn, hcls⟩ := hs
  rcases hcls with hE7 | hE8
  · exact Or.inl ⟨hin, hE7⟩
  · exact Or.inr ⟨hch, hp5, hcpf, hin, hn, hE8⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311n
