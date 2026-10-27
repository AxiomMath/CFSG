module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isPGroup_of_perfect_le_map {G G' : Type*} [Group G] [Group G'] [Finite G]
    (ψ : G →* G') (hψ : Function.Injective ψ) {F : Subgroup G} {X : Subgroup G'}
    (hXF : X ≤ F.map ψ) (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  set Y := X.comap ψ with hY
  have hYX : Y.map ψ = X := Subgroup.map_comap_eq_self (hXF.trans (Subgroup.map_le_range ψ F))
  have hYF : Y ≤ F := by
    intro y hy
    have hy' : ψ y ∈ X := hy
    obtain ⟨c, hc, hcy⟩ := hXF hy'
    rw [hψ hcy] at hc
    exact hc
  have hYp : ⁅Y, Y⁆ = Y := by
    apply Subgroup.map_injective hψ
    rw [Subgroup.map_commutator, hYX, hX]
  have hY1 : Y ≠ ⊥ := by
    intro h
    apply hX1
    rw [← hYX, h, Subgroup.map_bot]
  exact not_isPGroup_of_perfect_ne_bot hYF hYp hY1

section Rational

open CFSG.LieType.Chevalley.E6SignedGraph

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_perfect_rational_graph_coset
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {ε : ℕ}
    (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)))
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    ∃ S : Subgroup (ModGL TwistTag.E6.tag k),
      S ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))⁆ ⊓
        Subgroup.centralizer {x * diagramMap TwistTag.E6 k} ∧ ⁅S, S⁆ = S ∧ S ≠ ⊥ := by
  classical
  obtain ⟨-, -, -, hrep⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  obtain ⟨⟨y, hyR, hyA'⟩, -⟩ := hrep x hx hx2
  obtain ⟨A, hAdef⟩ : ∃ A, y * (x * diagramMap TwistTag.E6 k) * y⁻¹ = A := ⟨_, rfl⟩
  obtain ⟨AK, hAK⟩ : ∃ AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)),
      (A = diagramMap TwistTag.E6 k ∧ AK = diagramMap TwistTag.E6 _) ∨
      (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k ∧
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) := by
    rw [hAdef] at hyA'
    rcases hyA' with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨-, -, hSJ, -, -, hSq, hP1, hD1⟩ :=
    E6_canonical_graph_centralizer_rational_fixed_components p hp he k A AK hAK
  set S := rationalRootGroup (iterateFrobeniusEquiv k p e) AK
  have hSp : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hSq.1
  have hS1 : S ≠ ⊥ := by
    have : Nontrivial S := CFSG.LocalCores.isQuasisimple_nontrivial hSq
    exact (Subgroup.nontrivial_iff_ne_bot S).mp this
  obtain ⟨v, hS₁⟩ : ∃ v : ModGL TwistTag.E6.tag k, S.map (MulAut.conj v).toMonoidHom ≤
      frobFixedCentralizer TwistTag.E6.tag p e A (diagramMap TwistTag.E6 k ^ ε) := by
    rcases hε with rfl | rfl
    · refine ⟨1, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      change 1 * s * 1⁻¹ ∈ _
      rw [one_mul, inv_one, mul_one]
      exact hSJ hs
    · rcases hAK with ⟨hA, -⟩ | ⟨hA, -⟩
      · refine ⟨1, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        change 1 * s * 1⁻¹ ∈ _
        rw [one_mul, inv_one, mul_one, hP1 hA]
        exact hSJ hs
      · obtain ⟨v, -, hv⟩ := hD1 hA
        refine ⟨v⁻¹, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        have hs' := hSJ hs
        rw [← hv] at hs'
        obtain ⟨j, hj, rfl⟩ := hs'
        change v⁻¹ * (v * j * v⁻¹) * v⁻¹⁻¹ ∈ _
        rwa [show v⁻¹ * (v * j * v⁻¹) * v⁻¹⁻¹ = j by group]
  set P := diagramMap TwistTag.E6 k
  set F := frobTwistGL TwistTag.E6.tag k p e (P ^ ε)
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F
  obtain ⟨hyG, hFy⟩ := Subgroup.mem_inf.1 hyR
  have hFy' : F y = y := hFy
  set S₂ := (S.map (MulAut.conj v).toMonoidHom).map (MulAut.conj y⁻¹).toMonoidHom with hS₂def
  have hS₂B : S₂ ≤ R ⊓ Subgroup.centralizer {x * P} := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwZ, hwF⟩ := Subgroup.mem_inf.1 (hS₁ hw)
    obtain ⟨hwG, hwc⟩ := Subgroup.mem_inf.1 hwZ
    have hwF' : F w = w := hwF
    rw [Subgroup.mem_centralizer_singleton_iff] at hwc
    change y⁻¹ * w * y⁻¹⁻¹ ∈ _
    rw [inv_inv]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem (inv_mem hyG) hwG) hyG, ?_⟩, ?_⟩
    · change F (y⁻¹ * w * y) = y⁻¹ * w * y
      rw [map_mul, map_mul, map_inv, hFy', hwF']
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hxP : x * P = y⁻¹ * A * y := by rw [← hAdef]; group
      rw [hxP]
      calc y⁻¹ * w * y * (y⁻¹ * A * y) = y⁻¹ * (w * A) * y := by group
        _ = y⁻¹ * (A * w) * y := by rw [hwc]
        _ = y⁻¹ * A * y * (y⁻¹ * w * y) := by group
  have hS₂p : ⁅S₂, S₂⁆ = S₂ := by
    rw [hS₂def, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hSp]
  have hS₂1 : S₂ ≠ ⊥ := by
    rw [hS₂def, Ne, Subgroup.map_eq_bot_iff_of_injective _
      (f := (MulAut.conj y⁻¹).toMonoidHom) (MulAut.conj y⁻¹).injective,
      Subgroup.map_eq_bot_iff_of_injective _ (f := (MulAut.conj v).toMonoidHom)
        (MulAut.conj v).injective]
    exact hS1
  have hS₂R : S₂ ≤ R := hS₂B.trans inf_le_left
  refine ⟨S₂, le_inf ?_ (hS₂B.trans inf_le_right), hS₂p, hS₂1⟩
  exact hS₂p.symm.le.trans (Subgroup.commutator_mono hS₂R hS₂R)

end Rational

theorem not_isPGroup_E6_pure_graph
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {g : adjointGroup TwistTag.E6.tag K} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius k p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have halg := ExcSelector.isAlgebraic_algebraicClosure (K := K) p
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness TwistTag.E6.tag K hK k ι
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hdb : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag a) = rootDiagUnit TwistTag.E6.tag b :=
    baseChangeGL_rootDiagUnit ι a
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : adjointGroup TwistTag.E6.tag K,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group TwistTag.E6.tag K hK k Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)) =
        adjointGroup TwistTag.E6.tag k ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p n (P ^ 0) y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  have hxR : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)) := by
    rw [hRF]
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.E6.tag K) => φ h) hα
    simpa [sq] using this
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hPG : ∀ y ∈ adjointGroup TwistTag.E6.tag k,
      P * y * P⁻¹ ∈ adjointGroup TwistTag.E6.tag k := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have hx2 : (x * P) ^ 2 = 1 := by
    have hsqG : (x * P) ^ 2 ∈ adjointGroup TwistTag.E6.tag k := by
      have e : (x * P) ^ 2 = x * (P * x * P⁻¹) * (P * P) := by
        rw [sq]
        group
      rw [e, hP2, mul_one]
      exact mul_mem hxG (hPG x hxG)
    refine hfaith _ hsqG fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  have hHder : ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p n (P ^ 0))⁆ =
      (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : adjointGroup TwistTag.E6.tag K →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (adjointGroup TwistTag.E6.tag K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p n (P ^ 0)), fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p n (P ^ 0))⁆ ⊓ Subgroup.centralizer {x * P} := by
    rw [hHder]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
        x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K)
      calc baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
          (x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P)⁻¹) * (x * P) := by
            rw [h1]
        _ = x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * P * baseChangeGL ι c * (x * P)⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨S, hS, hSp, hS1⟩ :=
    exists_perfect_rational_graph_coset p hp2 n.pos halg (Or.inl rfl) hxR hx2
  exact not_isPGroup_of_perfect_le_map φ hφ (hS.trans hmap.symm.le) hSp hS1

end CFSG.ComponentClassification.HarrisLit.L33.E1
