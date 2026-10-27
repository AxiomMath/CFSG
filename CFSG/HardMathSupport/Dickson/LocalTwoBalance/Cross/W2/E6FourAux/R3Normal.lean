module

public import CFSG.RankThree.PartOne.KE.E6FourCore

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet)
open CFSG.LieType.Chevalley.EvenExceptionalActorCoverage (exactQ_E6_one)
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6_four_normal_of_fixes (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    {η : MulAut (adjointGroup .E6 K)} (hηx : η x = x)
    (hηd : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)),
        η d = d)
    (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE .E6))
    (hexpr : ∀ y : adjointGroup .E6 K, (η y : ModGL .E6 K) = (g : ModGL .E6 K) *
      rootDiagUnit .E6 a * exactQ .E6 K ε * Units.map (entrywiseHom σ.toRingHom)
        (y : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹ * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹) :
    σ = 1 ∧ (ε : ℕ) = 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_four_perx K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0 hperf
    hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set ι : ModGL .E6 K →* ModGL .E6 L := baseChangeGL (algebraMap K L) with hιdef
  have hιadj : ∀ y : adjointGroup .E6 K, adjEmb .E6 K L y = ι (y : ModGL .E6 K) := fun y => rfl
  set h'' : ModGL .E6 L := (adjEmb .E6 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)),
        adjEmb .E6 K L y = h'' * simpleRootSL2 .E6 L (e6Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    rw [← h2] at hmem
    obtain ⟨y', hy', hy'ψ⟩ := hmem
    refine ⟨(y' : adjointGroup .E6 K), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hy', rfl⟩
    · have h3 := hψ y'
      rw [hy'ψ] at h3
      have h4 : adjEmb .E6 K L (c * (y' : adjointGroup .E6 K) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 .E6 L (e6Index 0)
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc adjEmb .E6 K L (y' : adjointGroup .E6 K)
          = (adjEmb .E6 K L c)⁻¹ * (adjEmb .E6 K L c * adjEmb .E6 K L (y' : adjointGroup .E6 K) *
              (adjEmb .E6 K L c)⁻¹) * adjEmb .E6 K L c := by group
        _ = _ := by rw [h4]; group
  have hσ : σ = 1 := by
    let Z : Subgroup (MulAut (adjointGroup .E6 K)) :=
      { carrier := {η | ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ :
            Subgroup (adjointGroup .E6 K)), η d = d}
        mul_mem' := fun {a b} ha hb d hd => by
          rw [MulAut.mul_apply, hb d hd, ha d hd]
        one_mem' := fun d _ => rfl
        inv_mem' := fun {a} ha d hd => by
          have := ha d hd
          calc a⁻¹ d = a⁻¹ (a d) := by rw [this]
            _ = d := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
    have hηZ : η ∈ Z := hηd
    have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup .E6 K) (Y : SL2 K),
        baseChangeGL (algebraMap K L) (u : ModGL .E6 K) =
          h'' * simpleRootSL2 .E6 L (e6Index 0) (conjGL (1 : GL (Fin 2) L)
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ → η' u = u := by
      intro η' hη'Z u Y hu
      refine hη'Z u ?_
      obtain ⟨y, hyD, hy⟩ := hKey Y
      rw [conjGL_one, ← hy] at hu
      have hu' : adjEmb .E6 K L u = adjEmb .E6 K L y := by rw [adjEmb_apply, hu]
      rw [adjEmb_injective hu']
      exact hyD
    have hU : ∀ Y : SL2 K, h'' * simpleRootSL2 .E6 L (e6Index 0) (conjGL (1 : GL (Fin 2) L)
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ ∈
          (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) := by
      intro Y
      obtain ⟨y, -, hy⟩ := hKey Y
      rw [conjGL_one, ← hy]
      exact ⟨(y : ModGL .E6 K), y.2, rfl⟩
    exact (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E6 (Or.inl rfl) K L
      (e6Index 0) 1 h'' hU Z hZ).1 η hηZ g a σ ε hexpr
  refine ⟨hσ, ?_⟩
  by_contra hε
  have hε1 : (ε : ℕ) = 1 := by
    have hlt : (ε : ℕ) < 2 := ε.2
    omega
  have hid : ∀ y : ModGL .E6 K, Units.map (entrywiseHom σ.toRingHom) y = y := by
    intro y
    rw [hσ]
    exact Units.ext (entrywise_id _)
  set mK : ModGL .E6 K := (g : ModGL .E6 K) * rootDiagUnit .E6 a * exactQ .E6 K 1 with hmK
  have hη' : ∀ y : adjointGroup .E6 K, (η y : ModGL .E6 K) = mK * (y : ModGL .E6 K) * mK⁻¹ := by
    intro y
    rw [hexpr y, hε1, hid, hmK]
    group
  have hmD : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)),
      mK * (d : ModGL .E6 K) * mK⁻¹ = (d : ModGL .E6 K) := fun d hd => by
    rw [← hη' d, hηd d hd]
  have hmx : mK * (x : ModGL .E6 K) * mK⁻¹ = (x : ModGL .E6 K) := by
    rw [← hη' x, hηx]
  set Q : ModGL .E6 L := diagE6 L with hQ
  have hιQ : ι (exactQ .E6 K 1) = Q := by
    rw [exactQ_E6_one]
    exact baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6
  set m' : ModGL .E6 L :=
    g0⁻¹ * adjEmb .E6 K L c * ι mK * (adjEmb .E6 K L c)⁻¹ * g0 with hm'
  set G₃ : ModGL .E6 L := g0⁻¹ * adjEmb .E6 K L c * adjEmb .E6 K L g *
    ι (rootDiagUnit .E6 a) * (Q * ((adjEmb .E6 K L c)⁻¹ * g0) * Q⁻¹) with hG₃def
  have hm'eq : m' = G₃ * Q := by
    rw [hm', hG₃def, hmK, map_mul, map_mul, hιQ, hιadj g]
    group
  have hQconj : ∀ y ∈ adjointGroup .E6 L, Q * y * Q⁻¹ ∈ adjointGroup .E6 L := fun y hy => by
    have := map_conj_exactQ (τ := .E6) (K := L) (H := adjointGroup .E6 L) (Or.inl rfl) 1
    rw [exactQ_E6_one] at this
    have hmem : (MulAut.conj (diagE6 L : ModGL .E6 L) : ModGL .E6 L ≃* ModGL .E6 L) y ∈
        (adjointGroup .E6 L).map (MulAut.conj (diagE6 L : ModGL .E6 L)).toMonoidHom :=
      ⟨y, hy, rfl⟩
    rw [this] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hG₃adj : G₃ ∈ adjointGroup .E6 L := by
    refine mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hg0C) (adjEmb_mem c)) (adjEmb_mem g)) ?_)
      (hQconj _ (mul_mem (inv_mem (adjEmb_mem c)) hg0C))
    rw [hιdef, baseChangeGL_rootDiagUnit]
    exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
  have hfixψ : ∀ d : adjointGroup .E6 K, mK * (d : ModGL .E6 K) * mK⁻¹ = (d : ModGL .E6 K) →
      m' * (g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0 := by
    intro d hd
    have hd' : ι mK * adjEmb .E6 K L d * (ι mK)⁻¹ = adjEmb .E6 K L d := by
      have := congrArg ι hd
      rw [map_mul, map_mul, map_inv] at this
      exact this
    have e : m' * (g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * adjEmb .E6 K L c * (ι mK * adjEmb .E6 K L d * (ι mK)⁻¹) *
          (adjEmb .E6 K L c)⁻¹ * g0 := by
      rw [hm']
      simp only [map_mul, map_inv]
      group
    rw [e, hd']
    simp only [map_mul, map_inv]
    group
  have hbfix : b ∈ fixedCharTuples e6FourM Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨a', ha', haa⟩ := hh'
    have : a' = b := hinj0 (haa.trans hb.symm)
    exact this ▸ ha'
  have hbp : orderOf (rootDiagUnit .E6 b) = p := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0) =
        orderOf (adjEmb .E6 K L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (adjEmb .E6 K L (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (adjEmb .E6 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  obtain ⟨z, hz0, hzr, hcol⟩ := exists_column_of_fixed e6FourM Fr hFr hp hbfix hbap hb1
  have hstabb := e6Four_stab_of_fixed Fr hFr hp hp3 hord hΦ hbfix hbap hb1
  have hCent : ∀ y ∈ adjointGroup .E6 L, y * rootDiagUnit .E6 b = rootDiagUnit .E6 b * y →
      y ∈ (torusGroup .E6 L : Set (ModGL .E6 L)) *
        (rootSpan .E6 L (sigmaSetE6A3 v) : Set (ModGL .E6 L)) := fun y hy hcomm =>
    mem_torus_mul_rootSpan_of_commute_of_stab hstabb (sigmaSetE6A3_isRoot v) (sigmaSetE6A3_neg v)
      (by rw [hSeq]) hy hcomm
  have hfixh : (G₃ * diagE6 L) * rootDiagUnit .E6 b * (G₃ * diagE6 L)⁻¹ = rootDiagUnit .E6 b := by
    rw [← hm'eq, hb]
    exact hfixψ x hmx
  have hP : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
      Matrix.SpecialLinearGroup.toGL Z =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
      (G₃ * diagE6 L) * rhoSigmaE6A3 L v Z * (G₃ * diagE6 L)⁻¹ = rhoSigmaE6A3 L v Z := by
    intro Z hZ
    have hmem := hH Z hZ
    rw [← h2] at hmem
    obtain ⟨d', hd', hd'ψ⟩ := hmem
    have hd'D : ((d' : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) :
        adjointGroup .E6 K) ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ :
            Subgroup (adjointGroup .E6 K)) := by
      rw [← h1]
      exact ⟨d', hd', rfl⟩
    rw [← hm'eq, ← hd'ψ, hψ d']
    exact hfixψ _ (hmD _ hd'D)
  have hp5 : p = 5 ∨ 7 < p := e6Four_p_cases hp hp3 hord
  exact e6_graph_contra (K := K) (L := L) hp5 hz0 hzr hΦ hcol hSeq hCent hG₃adj hfixh hP


end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
