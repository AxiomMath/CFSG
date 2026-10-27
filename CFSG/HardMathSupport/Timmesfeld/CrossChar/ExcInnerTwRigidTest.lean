module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidE6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

section Criterion

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rigid_of_model_testSet (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
    [Algebra K L] {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f)
    (hq : Nat.card K = S.D.q) [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (Ycl : Set (ModGL τ L))
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (y : ModGL τ K) (σ : K ≃+* K),
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 ∈ Ycl ∧ ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (X : Set (ModGL τ L)) (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL τ L, ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (hI : ∀ z ∈ Ycl, (∀ x ∈ X, Commute z x) → ∀ x : S.Γ, Commute z (x : ModGL τ L))
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL τ L) ∈ X → δ x = x) : δ = 1 := by
  classical
  have : ExpChar L p₀ := ExpChar.prime hp₀
  obtain ⟨y, σ, hyY, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') S.D.g0 := ⟨_, rfl⟩
  have hδx : ∀ x : S.Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) =
        S.D.g0 * (e h : ModGL τ L) * S.D.g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  have hfix' : ∀ x ∈ X, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have h1 : δ ⟨x, hXΓ hx⟩ = ⟨x, hXΓ hx⟩ := hfix ⟨x, hXΓ hx⟩ hx
    have h2 := hδx ⟨x, hXΓ hx⟩
    rw [h1] at h2
    exact h2.symm
  have hj0 : j = 0 := by
    by_contra hj0
    exact hF p₀ f j hp₀ (hq.symm.trans hK) (Nat.pos_of_ne_zero hj0) hj
      z (by rw [hσ'] at hfix'; exact hfix')
  have hF1 : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzY : z ∈ Ycl := by
    have : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 := by rw [hz, hF1]
    rw [this]
    exact hyY
  have hcomm : ∀ x ∈ X, Commute z x := by
    intro x hx
    have h1 := hfix' x hx
    rw [hF1] at h1
    show z * x = x * z
    calc z * (x : ModGL τ L) = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have hzΓ := hI z hzY hcomm
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hF1]
  have := (hzΓ x).eq
  rw [MulAut.one_apply]
  calc z * (x : ModGL τ L) * z⁻¹ = x * z * z⁻¹ := by rw [this]
    _ = x := by group

end Criterion

section E6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rigid_E6_of_testSet (S : LangSetup .E6 L p) (hd : S.Descends) (X : Set (ModGL .E6 L))
    (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL .E6 L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (hI : ∀ z ∈ adjointGroup .E6 L, (∀ x ∈ X, Commute z x) →
      ∀ x : S.Γ, Commute z (x : ModGL .E6 L))
    (hIg : ∀ w ∈ adjointGroup .E6 L, ¬ ∀ x ∈ X, Commute (w * graphP L) x)
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL .E6 L) ∈ X → δ x = x) : δ = 1 := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  refine rigid_of_model_testSet S hp₀ hf hK hq e he
    {z | z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L}
    (fun α => ?_) X hXΓ hF (fun z hz hzc x => ?_) δ hfix
  · obtain ⟨g, a, σ, ε, hα⟩ :=
      (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
    refine ⟨(g : ModGL .E6 K) * rootDiagUnit .E6 a * exactQ .E6 K ε, σ, ?_, fun h => ?_⟩
    · have hga : baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) ∈
          adjointGroup .E6 L := by
        rw [map_mul, baseChangeGL_rootDiagUnit]
        exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
          (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
      have hg0 := S.D.g0_mem
      have hP : ∀ x ∈ adjointGroup .E6 L,
          graphP L * x * (graphP L)⁻¹ ∈ adjointGroup .E6 L :=
        fun x hx => E6GraphLevi.diagramMap_conj_mem_adjointGroup' hx
      fin_cases ε
      · left
        have hQ : exactQ .E6 K ((0 : Fin 2) : ℕ) = 1 := pow_zero (graphP K)
        simp only [Fin.val_zero] at hQ ⊢
        rw [hQ, mul_one]
        exact mul_mem (mul_mem (inv_mem hg0) hga) hg0
      · right
        refine ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) *
          (graphP L * S.D.g0 * (graphP L)⁻¹), ?_, ?_⟩
        · exact mul_mem (mul_mem (inv_mem hg0) hga) (hP _ hg0)
        · have hQ : exactQ .E6 K ((1 : Fin 2) : ℕ) = graphP K := pow_one (graphP K)
          have hbc : baseChangeGL (algebraMap K L) (graphP K) = graphP L :=
            baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6
          simp only [Fin.val_one] at hQ ⊢
          rw [hQ, map_mul, hbc]
          group
    · rw [hα h, mul_inv_rev, mul_inv_rev]
      group
  · rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hI z hz hzc x
    · exact absurd hzc (hIg w hw)

end E6

section TorusRoots

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem exists_component_of_torus (S : LangSetup τ L p) {D : Subgroup (ModGL τ L)} [Finite D]
    (hDT : D ≤ S.D.torus) (hpow : ∀ x ∈ D, x ^ p = 1) (hcard : p < Nat.card D)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D ∧ rootDiagUnit τ a ≠ 1 ∧
      ∃ i : KernelComponent (rootCharHom a), γ ∈ componentRoots (rootCharHom a) i := by
  have hDH : D ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (hDT hx)).1
  obtain ⟨a, haD, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite S.hp hDH hpow hcard γ
  have hk : γ ∈ kernelRoots (rootCharHom a) := ⟨hγ, hχ⟩
  exact ⟨a, haD, ha1, ⟦⟨γ, hk⟩⟧, hk, rfl⟩

end TorusRoots

section Torus

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem mem_bigAnyRoots_of_torus (hbig : ThreeBigComponents) (S : LangSetup τ L 3)
    (hq4 : 4 ≤ S.D.q) {D : Subgroup (ModGL τ L)} [Finite D] (hDT : D ≤ S.D.torus)
    (hpow : ∀ x ∈ D, x ^ 3 = 1) (hcard : 3 < Nat.card D) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    γ ∈ bigAnyRoots S D := by
  obtain ⟨a, haD, ha1, i, hγi⟩ := exists_component_of_torus S hDT hpow hcard hγ
  have hs0 := (outer_componentOrbitLength_spec S (hDT haD) i).1
  refine ⟨a, haD, ha1, i, hbig τ L S a (hDT haD) ha1 i, ?_, hγi⟩
  calc 4 ≤ S.D.q := hq4
    _ = S.D.q ^ 1 := (pow_one _).symm
    _ ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
      Nat.pow_le_pow_right (by omega) hs0

theorem commute_adjointGroup_of_torus (hAK : AnyKindCommuteT) (hbig : ThreeBigComponents)
    (S : LangSetup τ L 3) (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) {D : Subgroup (ModGL τ L)}
    [Finite D] (hDT : D ≤ S.D.torus) (hpow : ∀ x ∈ D, x ^ 3 = 1) (hcard : 3 < Nat.card D)
    {z : ModGL τ L} (hz : ∀ x ∈ bigComponentSet S D, Commute z x) :
    ∀ g ∈ adjointGroup τ L, Commute z g := by
  have hroot : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : L, Commute z (pinnedX τ L γ c) := by
    intro γ hγ c
    obtain ⟨a, haD, ha1, i, hbig', hQ, hγi⟩ :=
      mem_bigAnyRoots_of_torus hbig S hq4 hDT hpow hcard hγ
    exact hAK τ L 3 S hτ a (hDT haD) (hpow _ haD) i (by omega) hQ z
      (fun x hx => hz x ⟨a, haD, ha1, i, hbig', hx⟩) _ (pinnedX_mem_rootSpan hγi c)
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hgx : g = pinnedX τ L (Pi.single i 1) c := by
        rw [pinnedX_single]
        exact Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hgx]
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroot _ (isRoot_single τ i) c).symm.eq
    · have hgy : g = pinnedX τ L (-Pi.single i 1) c := by
        rw [pinnedX_neg_single]
        exact Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hgy]
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroot _ (isRoot_neg_single τ i) c).symm.eq
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem noFrobenius_testSet_of_torus (hbig : ThreeBigComponents) (S : LangSetup τ L 3)
    (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) (hq4' : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    {D : Subgroup (ModGL τ L)} [Finite D] (hDT : D ≤ S.D.torus) (hpow : ∀ x ∈ D, x ^ 3 = 1)
    (hcard : 3 < Nat.card D) (r f j : ℕ) [ExpChar L r] (hr : r.Prime) (hqf : S.D.q = r ^ f)
    (hj0 : 0 < j) (hjf : j < f) (z : ModGL τ L) :
    ¬ ∀ x ∈ bigComponentSet S D,
      z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x := by
  intro hz
  obtain ⟨a, haD, ha1, i, hbig', -, -⟩ :=
    mem_bigAnyRoots_of_torus hbig S hq4 hDT hpow hcard (isRoot_single τ 0)
  exact outer_false_of_component_fixed_by_twist S hτ (hDT haD) i hr hqf hq4' hj0 hjf z
    fun x hx => hz x ⟨a, haD, ha1, i, hbig', hx⟩

end Torus

end CFSG.HardMathSupport.Timmesfeld.CrossChar
