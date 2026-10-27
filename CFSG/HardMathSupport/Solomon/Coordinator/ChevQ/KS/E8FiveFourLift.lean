module

public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenCenter

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Foote.Coordinator

set_option linter.unusedSectionVars false


theorem exists_fixed_lift {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (v c : WeylGroup τ) (hvc : v * c = c * v) :
    ∃ m : ModGL τ L, m ∈ monomialSubgroup τ L ∧ MapsRootLines m c ∧
      canonicalRep (coxeterSystem τ) L v * Units.map (entrywiseHom Fr) m *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ = m := by
  classical
  set n := canonicalRep (coxeterSystem τ) L v with hn
  set m₀ := canonicalRep (coxeterSystem τ) L c with hm₀
  have hnm : n ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L v
  have hΦm₀ : Units.map (entrywiseHom Fr) m₀ = m₀ :=
    Units.ext (congrArg Units.val (baseChangeGL_canonicalRep (τ := τ) Fr c))
  obtain ⟨k₁, hk₁, e₁⟩ := canonicalRep_mul_mem (τ := τ) (R := L) v c
  obtain ⟨k₂, hk₂, e₂⟩ := canonicalRep_mul_mem (τ := τ) (R := L) c v
  rw [hvc] at e₁
  set h := k₁ * k₂⁻¹ with hh
  have hhT : h ∈ torusGroup τ L := mul_mem hk₁ (inv_mem hk₂)
  have e₃ : n * m₀ * n⁻¹ = h * m₀ := by
    have e₄ : canonicalRep (coxeterSystem τ) L (c * v) = k₂⁻¹ * (m₀ * n) := by
      rw [← hn, ← hm₀] at e₂
      rw [e₂]
      group
    calc n * m₀ * n⁻¹ = k₁ * canonicalRep (coxeterSystem τ) L (c * v) * n⁻¹ := by
          rw [e₁]
      _ = k₁ * (k₂⁻¹ * (m₀ * n)) * n⁻¹ := by rw [e₄]
      _ = h * m₀ := by rw [hh]; group
  have hnorm : m₀ ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer c
  have hs : m₀⁻¹ * h * m₀ ∈ torusGroup τ L := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnorm) h).1 hhT
    rwa [inv_inv] at this
  set s := m₀⁻¹ * h * m₀ with hsdef
  have hall : ∀ β ∈ parabolicRoots τ (Set.univ : Set (Fin τ.rank)),
      weylQuotientHom τ L ⟨n, hnm⟩ • β ∈ parabolicRoots τ (Set.univ : Set (Fin τ.rank)) :=
    fun β hβ => ⟨IsRoot.smul hβ.1 _, fun i hi => absurd (Set.mem_univ i) hi⟩
  obtain ⟨t, ht, hLang⟩ := exists_lang_supportedTorus_of_monomial hq hFr n hnm hall s⁻¹
    (torusGroup_le_supportedTorus_univ (inv_mem hs))
  have htT : t ∈ torusGroup τ L := supportedTorus_le_torusGroup _ ht
  refine ⟨m₀ * t, mul_mem (canonicalRep_mem_monomialSubgroup L c)
    (torusGroup_le_monomialSubgroup htT), ?_, ?_⟩
  · simpa using (mapsRootLines_canonicalRep c).mul (mapsRootLines_of_mem_torusGroup htT)
  · have e5 : n * Units.map (entrywiseHom Fr) t * n⁻¹ = t * s⁻¹ := by
      calc n * Units.map (entrywiseHom Fr) t * n⁻¹
          = t * (t⁻¹ * (n * Units.map (entrywiseHom Fr) t * n⁻¹)) := by group
        _ = t * s⁻¹ := by rw [hLang]
    have e6 : h * m₀ = m₀ * s := by rw [hsdef]; group
    calc n * Units.map (entrywiseHom Fr) (m₀ * t) * n⁻¹
        = (n * m₀ * n⁻¹) * (n * Units.map (entrywiseHom Fr) t * n⁻¹) := by
          rw [map_mul, hΦm₀]
          group
      _ = (m₀ * s) * (t * s⁻¹) := by rw [e₃, e5, e6]
      _ = m₀ * (s * t) * s⁻¹ := by group
      _ = m₀ * (t * s) * s⁻¹ := by rw [torusGroup_comm hs htT]
      _ = m₀ * t := by group

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
