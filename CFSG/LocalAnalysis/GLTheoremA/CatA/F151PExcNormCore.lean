module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLangNormalizer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.GLTheoremA.S267.Gen
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (toralRootGroup_le_normalizer_rationalRoots)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (components_of_langSetup map_fixSubgroup_eq_of_conj)

namespace CFSG.LocalAnalysis.GLTheoremA.F151


theorem compNormal_of_langSetup_of_conn {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hConn : ∀ y ∈ toralCentralizer τ L a, S.D.step y = y →
      y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    CompNormal β := by
  intro K hK
  obtain ⟨i, -, hKR⟩ := components_of_langSetup S hp ι hι hrange β hβ hT hap h1 hTame hK
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hN : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤
      Subgroup.normalizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ L)) := by
    intro g hg
    obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
    have hgM : g ∈ S.D.model := Subgroup.commutator_le_self S.D.model hgΓ
    have hgR : g ∈ toralRootGroup τ L a :=
      hConn g (Subgroup.mem_inf.2 ⟨hgM.1, hgc⟩) hgM.2
    have h1' := toralRootGroup_le_normalizer_rationalRoots S hT i hgR
    have h2 : g ∈ Subgroup.normalizer (S.Γ : Set (ModGL τ L)) := Subgroup.le_normalizer hgΓ
    have h3 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h1', h2⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h3 ⊢
    change (⁅rationalSpan S.ρ S.Γ (rootCharHom a) i, rationalSpan S.ρ S.Γ (rootCharHom a) i⁆).map
      (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_commutator]
    change ⁅(rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).map _,
      (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).map _⁆ = _
    have h3' : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).map
        (MulAut.conj g).toMonoidHom = rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ :=
      h3
    rw [h3']
    rfl
  refine Subgroup.le_normalizer_iff.2 fun g hg k hk => ?_
  have hg' : ι g ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem ι hg
  have hk' : ι k ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hKR]
    exact Subgroup.mem_map_of_mem ι hk
  have h2 := (hN hg' (ι k)).1 hk'
  rw [← hKR, ← map_inv, ← map_mul, ← map_mul] at h2
  exact (Subgroup.mem_map_iff_mem hι).1 h2

open TauCeti CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremA.T171Sh in
theorem compNormal_E6_charTwo_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : ¬ 3 ∣ Nat.card K - 1) (x : ↥(adjointGroup Tag.E6 K)) (hx1 : x ≠ 1) (hxp : x ^ 3 = 1) :
    CompNormal (MulAut.conj x) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hcard⟩ := FiniteField.card' K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hKn]; intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hp₀K : ¬ 5 ∣ Nat.card K := by
    rw [hKn]; intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ := single_edge_perfect Tag.E6 K (by simp)
  have hp1 : (x : ModGL Tag.E6 K) ^ 3 = 1 := by simpa using congrArg Subtype.val hxp
  have hh1 : (x : ModGL Tag.E6 K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (Or.inr (Or.inr (Or.inl rfl))) Nat.prime_three hpK
      (p₀ := 5) Nat.prime_five hp₀K (Or.inl le_rfl) hmon hperf (MulAut.conj x) x.1
      (baseChange_mem_adjointGroup_of_mem_inndiag (adjointGroup_le_inndiagGroup x.2))
      (fun c => rfl) hp1 hh1
  have hTame := langSetup_hTame_of_prime S Nat.prime_three
    (natCast_ne_zero_algebraicClosure Nat.prime_three hpK) (fun h => by cases h) hT hap h1
  have hq : ¬ 3 ∣ S.D.q - 1 := by rw [hSq]; exact hK
  have hConn : ∀ y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a, S.D.step y = y →
      y ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
        rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a)) :=
    fun y hy hyF => e6CentralizerConnOdd_untw_holds (AlgebraicClosure K) 5 S
      ⟨Fr, fun c => by rw [hSq]; exact hFr c, hΦ⟩ hq a hT hap y hy hyF
  exact compNormal_of_langSetup_of_conn S Nat.prime_three ι hinj hrange _ hconj hT hap h1 hTame
    hConn

open TauCeti CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.T171Sh in
theorem compNormal_twE6_charTwo_three {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hKcard : Nat.card K = (q.p ^ q.exponent) ^ 2) (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (hq3 : ¬ 3 ∣ q.p ^ q.exponent + 1)
    (x : ↥(twistedE6RootGroup K σ)) (hx1 : x ≠ 1) (hxp : x ^ 3 = 1) :
    CompNormal (MulAut.conj x) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, hq2, ← pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_twE6_of_prime (ℓ := q.p) (f := q.exponent) q.prime_p
      q.exponent_pos hKcard σ hσ Nat.prime_three (by rw [hq2]; norm_num) (p₀ := 5) Nat.prime_five
      (by rw [hq2]; norm_num) (Or.inl le_rfl) hmon (MulAut.conj x) x.1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2) (fun c => rfl)
      (by simpa using congrArg Subtype.val hxp) (fun h => hx1 (Subtype.ext h))
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 3).1 h0)
    omega
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL (fun h => by cases h) hT hap h1
  have hq : ¬ 3 ∣ S.D.q + 1 := by rw [hSq]; exact hq3
  have hConn : ∀ y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a, S.D.step y = y →
      y ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
        rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a)) :=
    fun y hy hyF => twE6CentralizerConnOdd_holds (AlgebraicClosure K) 5 S
      ⟨Fr, fun c => by rw [hSq]; exact hFr c, hΦ⟩ hq a hT hap y hy hyF
  exact compNormal_of_langSetup_of_conn S Nat.prime_three ι hinj hrange _ hconj hT hap h1 hTame
    hConn

theorem mem_normalizer_glaPComponent_of_compNormal {R : Type} [Group R] [Finite R] {p : ℕ}
    {x y : R} (hxy : Commute x y)
    (hPL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (MulAut.conj x))
    (hCN : CompNormal (MulAut.conj x)) {J : Subgroup R}
    (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J) :
    y ∈ Subgroup.normalizer (J : Set R) := by
  have hfix := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.fixSubgroup_conj_eq x
  rw [← hfix] at hJ
  have hperf := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ
  have hle := hPL J hJ.1 hperf
  have hcomp :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hle).1
  have hy : y ∈ fixSubgroup (MulAut.conj x) := by
    rw [hfix, Subgroup.mem_centralizer_singleton_iff]
    exact hxy.symm.eq
  exact hCN J hcomp hy

end CFSG.LocalAnalysis.GLTheoremA.F151

end
