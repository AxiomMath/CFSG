module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcQLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three18
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three6

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec chainRoot)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Certs


variable {L : Type} [Field L]

private theorem finite_e8T3QLayer {k : Type} [Field k] [Finite k] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [Algebra k L] [IsAlgClosure k L] [IsAlgClosed L] [CharP L ℓ]
    (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x) :
    Finite ↥(e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨P, hP, hfac, -⟩ := layer_A2 (L := L) hf hk hε hq2
    ((coxeterSystem Tag.E8).wordProd e8QWord) n hnm
    (monomialSubgroup_le_adjointGroup' hnm) hnW
    (fun α hα => by
      rw [sigmaSetE8_e8QWord] at hα ⊢
      exact e8T3We_smul_mem_e8A2Roots hε α hα)
    (fun α hα => by
      rw [sigmaSetE8_e8QWord] at hα ⊢
      exact neg_mem_e8A2Roots hα)
  rw [e8T3QLayer, ← sigmaSetE8_e8QWord, ← hP]
  exact hfac.finite ()

private theorem perfect_e8T3QLayer {k : Type} [Field k] [Finite k] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [Algebra k L] [IsAlgClosure k L] [IsAlgClosed L] [CharP L ℓ]
    (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x) :
    ⁅e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))),
      e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))⁆ =
        e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
  CFSG.Quasithin.F6.InspRest.commutator_eq_self_of_isQuasisimple
    (isQuasisimple_e8T3QLayer (L := L) hf hk hε hq2 n hnm
      (monomialSubgroup_le_adjointGroup' hnm) hnW)

private theorem mem_normalizer_e8T3QLayer_of_commute {K : Type} [Field K] {L : Type} [Field L]
    {n : ModGL Tag.E8 L} {Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L}
    {x z : adjointGroup Tag.E8 K}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) →* ModGL Tag.E8 L}
    {y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))}
    (hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))
    {p : ℕ} [NeZero p] {ζ : Lˣ} {q : ZMod p}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    (hψadj : ψ y ∈ adjointGroup Tag.E8 L)
    (hψfix : ψ y ∈ twistedFixedPoints n Φ)
    (hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val))
    (hcomm : Commute (ψ y) (ψ ⟨z, hzC⟩)) :
    ψ y ∈ Subgroup.normalizer (e8T3QLayer n Φ : Set (ModGL Tag.E8 L)) := by
  have hfam : ψ y ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer Tag.E8 L
      (fun _ : Unit => fun i => ζ ^ (e8T3ZColumn ε q i).val) := by
    refine CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.2
      ⟨hψadj, fun _ => ?_⟩
    show rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val) * ψ y *
      (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val))⁻¹ = ψ y
    rw [← hψz, ← hcomm.eq]
    group
  have hNspan : ψ y ∈ Subgroup.normalizer
      (rootSpan Tag.E8 L e8A2Roots : Set (ModGL Tag.E8 L)) :=
    familyCentralizer_e8T3ZColumn_le_normalizer_rootSpan (L := L) hζ hp hp3 hε hq hfam
  rw [e8T3QLayer]
  exact mem_normalizer_inf_twistedFixedPoints hNspan hψfix


variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_e8T3_JQ_layers (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hq2 : ε = -1 → 2 < ℓ ^ f)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ y ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y = y) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {x z : adjointGroup Tag.E8 K} (c : adjointGroup Tag.E8 K)
    (hxz : Commute x z) (hx : orderOf x = p)
    (hxframe : adjEmb Tag.E8 K L (c * x * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹)
    (hzframe : adjEmb Tag.E8 K L (c * z * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹) :
    ∃ J Q : Subgroup (adjointGroup Tag.E8 K),
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal ∧
      CFSG.IsQuasisimple J ∧ p ∣ Nat.card J ∧
      Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 K)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 K)))).Normal ∧
      CFSG.IsQuasisimple Q ∧ p ∣ Nat.card Q := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L :=
    Units.map (entrywiseHom (iterateFrobenius L ℓ f))
  let Cx : Subgroup (adjointGroup Tag.E8 K) :=
    Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))
  let xb : Fin Tag.E8.rank → Lˣ :=
    fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val
  let zb : Fin Tag.E8.rank → Lˣ :=
    fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val
  let P6 : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (rootCharKernel xb) ⊓ twistedFixedPoints n Φ
  let QL : Subgroup (ModGL Tag.E8 L) := e8T3QLayer n Φ
  have hq : ((Nat.card K : ZMod p)) ^ 2 + (ε : ZMod p) * (Nat.card K : ZMod p) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  have hS : ∃ u : WeylGroup Tag.E8,
      (fun γ => u • γ) '' rootCharKernel xb =
        parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    obtain ⟨u, hu⟩ := exists_conj_rootKernel_e8T3XColumn_eq_e6Nodes hp hp3 hε hpf
    exact ⟨u, by
      rwa [CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ]⟩
  have hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n Φ := by
    rw [hxframe]
    have h : g0⁻¹ * (g0 * rootDiagUnit Tag.E8 xb * g0⁻¹) * g0 =
        rootDiagUnit Tag.E8 xb := by group
    rw [h]
    exact e8T3XColumn_mem_twistedTorus hζ
      (fun y => by rw [iterateFrobenius_def, hK]) hε hq
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f))
  have hb : rootDiagUnit Tag.E8 xb = g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 := by
    rw [hxframe]; group; rfl
  obtain ⟨ψ, J, hψinj, hψ, hψT, hψR, hψadj, hψNperx, hJdef, hJx, hJn, hJq, hpJ⟩ :=
    e8T3_perx_layers hE6 hε K hf hK hp hp3 hpf L n hnm hnW g0 hg0C hg0 hperf
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f)) hx c hh xb hb hS
  have hψeq : ψ = conjAdjEmbHom Tag.E8 K L g0 c x := by
    refine MonoidHom.ext fun y => ?_
    rw [hψ y]
    rfl
  have hxC : x ∈ Cx := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzC : z ∈ Cx := Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
  have hψx : ψ ⟨x, hxC⟩ = rootDiagUnit Tag.E8 xb := by
    rw [hψ ⟨x, hxC⟩, hxframe]
    group
    rfl
  have hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E8 zb := by
    rw [hψ ⟨z, hzC⟩, hzframe]
    group
    rfl
  have hsubX : e8A2Roots ⊆ rootCharKernel xb := fun α hα => by
    rw [show rootCharKernel xb = e8T3XKernel from
      (CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ _).trans
        (rootKernel_e8T3XColumn hp hp3 hε hq)]
    exact e8A2Roots_subset_e8T3XKernel hα
  have hsubZ : e8A2Roots ⊆ rootCharKernel zb := fun α hα => by
    rw [show rootCharKernel zb = e8T3ZKernel from
      (CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ _).trans
        (rootKernel_e8T3ZColumn hp hp3 hε hq)]
    exact e8A2Roots_subset_e8T3ZKernel hα
  have hQLqs : CFSG.IsQuasisimple ↥QL :=
    isQuasisimple_e8T3QLayer (L := L) hf hK hε hq2 n hnm
      (monomialSubgroup_le_adjointGroup' hnm) (fun x => by rw [hnW])
  have hpQL : p ∣ Nat.card ↥QL :=
    dvd_card_e8T3QLayer (L := L) hp hp3 hf hK hε hpf n hnm hnW
  have hQLfin : Finite ↥QL :=
    finite_e8T3QLayer (L := L) hf hK hε hq2 n hnm (fun x => by rw [hnW])
  have hQLperf : ⁅QL, QL⁆ = QL :=
    perfect_e8T3QLayer (L := L) hf hK hε hq2 n hnm (fun x => by rw [hnW])
  have hQLleP6 : QL ≤ P6 :=
    inf_le_inf_right _ (iSup₂_le fun α hα => le_iSup₂_of_le α (hsubX hα) le_rfl)
  have hQLadj : QL ≤ adjointGroup Tag.E8 L :=
    inf_le_left.trans (rootSpan_le_adjointGroup L e8A2Roots)
  have hQLfix : QL ≤ twistedFixedPoints n Φ := inf_le_right
  have hQLcentx : QL ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.E8 xb} : Set (ModGL Tag.E8 L)) :=
    inf_le_left.trans (rootSpan_le_centralizer (K := L) xb hsubX)
  have hQLrange' : QL ≤ (conjAdjEmbHom Tag.E8 K L g0 c x).range :=
    le_range_conjAdjEmbHom_of_twistedFixed (τ := Tag.E8) hg0C hg0 hQLfin hQLperf
      hQLadj hQLfix (fun q hq => by
        have h := hQLcentx hq
        rw [Subgroup.mem_centralizer_singleton_iff] at h
        rw [← hψ ⟨x, hxC⟩, hψx]
        exact h) hperf
  have hQLrange : QL ≤ ψ.range := by rwa [hψeq]
  have hQLz : QL ≤ Subgroup.centralizer ({ψ ⟨z, hzC⟩} : Set (ModGL Tag.E8 L)) := by
    rw [hψz]
    exact inf_le_left.trans (rootSpan_le_centralizer (K := L) zb hsubZ)
  have hN : ∀ y : ↥Cx, (y : adjointGroup Tag.E8 K) * z = z * (y : adjointGroup Tag.E8 K) →
      ψ y ∈ Subgroup.normalizer (QL : Set (ModGL Tag.E8 L)) := by
    intro y hyz
    exact mem_normalizer_e8T3QLayer_of_commute (x := x) (n := n) (Φ := Φ)
      hzC hζ hp hp3 hε hq (hψadj y)
      (by rw [mem_twistedFixedPoints]; exact hψR y) hψz
      (commute_psi_of_commute hzC hyz)
  obtain ⟨Q, hQJ, hQz, hQn, hQopen, hpQ⟩ :=
    exists_qLayer_of_quasisimple (x := x) (z := z) ψ hψinj
      (P := P6) (QL := QL) hQLleP6 hQLrange hzC hQLz hN
      ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥QL)).1 hQLqs) hpQL
  refine ⟨J, Q, hJx, hJn, hJq, hpJ, ?_, hQz, ?_, ?_, hpQ⟩
  · rw [hJdef]
    exact hQJ
  · rw [hJdef]
    exact hQn
  · exact (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥Q)).2 hQopen


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
