module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.LemmaR
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.YS04E6F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b renaming weylAct → wAct
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (canonicalRep_conj_rootDiagUnit)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b renaming weylAct_mul_left → wAct_mul_left
open CFSG.SignalizerFunctorTheorem.NonLocalExc (torus_conj_mem_rootSpan)
open scoped Pointwise


variable {τ : Tag} {K : Type} [Field K]

@[expose] def twU (T : K ≃+* K) (a : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun i => Units.map T.toRingHom.toMonoidHom (a i)

theorem entrywise_rootDiagUnit (T : K ≃+* K) (a : Fin τ.rank → Kˣ) :
    Units.map (entrywiseHom T.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ (twU T a) :=
  Units.ext (entrywise_rootDiag T.toRingHom a)

theorem twU_mul (T : K ≃+* K) (a b : Fin τ.rank → Kˣ) : twU T (a * b) = twU T a * twU T b :=
  funext fun i => map_mul _ _ _

theorem twU_weylAct (T : K ≃+* K) (w : WeylGroup τ) (a : Fin τ.rank → Kˣ) :
    twU T (wAct w a) = wAct w (twU T a) := by
  funext i
  simp only [twU, wAct, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct,
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, map_prod, map_zpow]

theorem mem_torusGroup_of_conj_mem_stabilizer (h : adjointGroup τ K)
    (hA : MulAut.conj h ∈ unipotentPairAut τ K) : (h : ModGL τ K) ∈ torusGroup τ K := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf posUnipotent_le_adjointGroup hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf negUnipotent_le_adjointGroup hV
  have hB : (h : ModGL τ K) ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  have hB' : (h : ModGL τ K) ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
  exact Subgroup.mem_inf.2 ⟨hB, hB'⟩

theorem rootDiagUnit_mem_torusGroup_of_mem (b : Fin τ.rank → Kˣ)
    (hb : rootDiagUnit τ b ∈ adjointGroup τ K) : rootDiagUnit τ b ∈ torusGroup τ K := by
  refine mem_torusGroup_of_conj_mem_stabilizer (⟨rootDiagUnit τ b, hb⟩ : adjointGroup τ K) ?_
  have : MulAut.conj (⟨rootDiagUnit τ b, hb⟩ : adjointGroup τ K) = rootDiagAut τ K b :=
    MulEquiv.ext fun g => Subtype.ext (by rw [coe_rootDiagAut]; rfl)
  rw [this, rootDiagAut_eq_exactNormalAut]
  exact exactNormalAut_mem b (RingEquiv.refl K) 0

theorem torusGroup_le_adjointGroup' : torusGroup τ K ≤ adjointGroup τ K :=
  ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1.trans' le_sup_left

theorem rootDiagUnit_mem_adjointGroup_of_twist (T : K ≃+* K)
    (hcube : ∀ k : Fin τ.rank → Kˣ, (∀ i, T (k i : K) = k i) →
      rootDiagUnit τ k ∈ adjointGroup τ K)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) (a : Fin τ.rank → Kˣ)
    (hga : Units.map (entrywiseHom T.toRingHom) g = g * rootDiagUnit τ (a * (twU T a)⁻¹)) :
    rootDiagUnit τ a ∈ adjointGroup τ K := by
  classical
  set b : Fin τ.rank → Kˣ := a * (twU T a)⁻¹ with hb
  set d : ModGL τ K := rootDiagUnit τ b with hd
  have hd_eq : d = g⁻¹ * Units.map (entrywiseHom T.toRingHom) g := by rw [hga]; group
  have hdC : d ∈ adjointGroup τ K := by
    rw [hd_eq]
    exact mul_mem (inv_mem hg) (entrywiseAdjointAut τ T ⟨g, hg⟩).2
  have hdT : d ∈ torusGroup τ K := rootDiagUnit_mem_torusGroup_of_mem b hdC
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  have hbij := (bruhat_cell_factorization τ K).1 w
  obtain ⟨⟨β, v⟩, ⟨hβ, hv⟩, hβv⟩ := hbij.2.2 hw
  simp only at hβv
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hnM : n ∈ monomialSubgroup τ K :=
    Subgroup.mem_sup_right (canonicalRep_mem_closure (coxeterSystem τ) K w)
  have hnC : n ∈ adjointGroup τ K := monomialSubgroup_le_adjointGroup' hnM
  have hd'' : n * d * n⁻¹ ∈ torusGroup τ K := by
    have hN := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.1
    have hdM : d ∈ monomialSubgroup τ K := Subgroup.mem_sup_left hdT
    have := hN.conj_mem ⟨d, hdM⟩ (by simpa [Subgroup.mem_subgroupOf] using hdT) ⟨n, hnM⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hv' : d⁻¹ * v * d ∈ rootSpan τ K (inversionSet w) := by
    have := torus_conj_mem_rootSpan (inv_mem hdT) (fun α hα => hα.1) hv
    simpa [mul_assoc] using this
  have hβ' : β * (n * d * n⁻¹) ∈ borelGroup τ K := mul_mem hβ (Subgroup.mem_sup_left hd'')
  have hTg : Units.map (entrywiseHom T.toRingHom) β * n * Units.map (entrywiseHom T.toRingHom) v =
      (β * (n * d * n⁻¹)) * n * (d⁻¹ * v * d) := by
    have h1 : Units.map (entrywiseHom T.toRingHom) β * n *
        Units.map (entrywiseHom T.toRingHom) v = Units.map (entrywiseHom T.toRingHom) g := by
      rw [← hβv, map_mul, map_mul, entrywise_canonicalRep]
    rw [h1, hga, ← hβv]
    group
  have hfix := hbij.2.1 (x₁ := (Units.map (entrywiseHom T.toRingHom) β,
      Units.map (entrywiseHom T.toRingHom) v)) (x₂ := (β * (n * d * n⁻¹), d⁻¹ * v * d))
    ⟨entrywise_mem_borelGroup hβ, entrywise_mem_rootSpan hv⟩ ⟨hβ', hv'⟩ hTg
  simp only [Prod.mk.injEq] at hfix
  obtain ⟨hTβ, -⟩ := hfix
  have hβ2 : β ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hβ
  obtain ⟨h, hh, u, hu, rfl⟩ := hβ2
  rw [map_mul] at hTβ
  have hTh : Units.map (entrywiseHom T.toRingHom) h ∈ torusGroup τ K := entrywise_mem_torusGroup hh
  have hTu : Units.map (entrywiseHom T.toRingHom) u ∈ posUnipotent τ K :=
    entrywise_mem_rootSpan hu
  have hcu : (n * d * n⁻¹)⁻¹ * u * (n * d * n⁻¹) ∈ posUnipotent τ K := by
    have := (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_posUnipotent (inv_mem hd''))) u
    simpa [mul_assoc] using this.1 hu
  have huniq := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.1
    (Units.map (entrywiseHom T.toRingHom) h) hTh (h * (n * d * n⁻¹)) (mul_mem hh hd'')
    (Units.map (entrywiseHom T.toRingHom) u) hTu ((n * d * n⁻¹)⁻¹ * u * (n * d * n⁻¹)) hcu
    (by rw [hTβ]; group)
  obtain ⟨hThh, -⟩ := huniq
  obtain ⟨m, hm⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  subst hm
  have hmul : ∀ x y : Fin τ.rank → Kˣ,
      rootDiagUnit τ (x * y) = rootDiagUnit τ x * rootDiagUnit τ y := fun x y =>
    map_mul (rootDiagUnitHom τ K) x y
  have hdconj : n * d * n⁻¹ = rootDiagUnit τ (wAct w b) := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w b
  have hTm : twU T m = m * wAct w b := by
    apply rootDiagUnit_injective
    rw [← entrywise_rootDiagUnit, hThh, hdconj, hmul]
  have hk : twU T (m * wAct w a) = m * wAct w a := by
    rw [twU_mul, hTm, twU_weylAct]
    have : wAct w b * wAct w (twU T a) = wAct w a := by
      rw [← wAct_mul_left, hb, inv_mul_cancel_right]
    rw [mul_assoc, this]
  have hkfix : ∀ i, T ((m * wAct w a) i : K) = (m * wAct w a) i := fun i => by
    simpa [twU] using congrArg Units.val (congrFun hk i)
  have hkC := hcube _ hkfix
  have hmC : rootDiagUnit τ m ∈ adjointGroup τ K := torusGroup_le_adjointGroup' hh
  have hwaC : rootDiagUnit τ (wAct w a) ∈ adjointGroup τ K := by
    have : rootDiagUnit τ (wAct w a) = (rootDiagUnit τ m)⁻¹ * rootDiagUnit τ (m * wAct w a) := by
      rw [hmul]; group
    rw [this]
    exact mul_mem (inv_mem hmC) hkC
  have hconj : n * rootDiagUnit τ a * n⁻¹ = rootDiagUnit τ (wAct w a) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w a
  have hfin : rootDiagUnit τ a = n⁻¹ * rootDiagUnit τ (wAct w a) * n := by
    rw [← hconj]; group
  rw [hfin]
  exact mul_mem (mul_mem (inv_mem hnC) hwaC) hnC


theorem hcube_E6 (T : K ≃+* K) (hT : ∀ c : Kˣ, T (c : K) = c → ∃ s : Kˣ, s ^ 3 = c) :
    ∀ k : Fin Tag.E6.rank → Kˣ, (∀ i, T (k i : K) = k i) →
      rootDiagUnit Tag.E6 k ∈ adjointGroup Tag.E6 K := by
  intro k hk
  choose s hs using fun i => hT (k i) (hk i)
  have : k = fun l => s l ^ 3 := funext fun i => (hs i).symm
  rw [this]
  exact torusGroup_le_adjointGroup'
    (CFSG.StandardType.TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 s)

theorem conj_eq_rootDiagAut (h : adjointGroup Tag.E6 K) (b : Fin Tag.E6.rank → Kˣ)
    (hh : MulAut.conj h = rootDiagAut Tag.E6 K b) : (h : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 b := by
  have hA : MulAut.conj h ∈ unipotentPairAut Tag.E6 K := by
    rw [hh, rootDiagAut_eq_exactNormalAut]
    exact exactNormalAut_mem b (RingEquiv.refl K) 0
  have hT : (h : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K :=
    mem_torusGroup_of_conj_mem_stabilizer h hA
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have h1 : MulAut.conj h = rootDiagAut Tag.E6 K b' :=
    MulEquiv.ext fun g => Subtype.ext (by rw [coe_rootDiagAut]; simp [hb'])
  rw [hh, rootDiagAut_eq_exactNormalAut, rootDiagAut_eq_exactNormalAut] at h1
  have := exactNormalAut_injective (Or.inl rfl)
    (a := b) (a' := b') (σ := RingEquiv.refl K) (σ' := RingEquiv.refl K)
    (ε := ⟨0, by decide⟩) (ε' := ⟨0, by decide⟩) h1
  have hbb : b = b' := (Prod.mk.inj this).1
  rw [hb', hbb]

end CFSG.LocalAnalysis.GLTheoremA.YS04E6F
