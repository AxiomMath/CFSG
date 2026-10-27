module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OCount
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Reduce

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.ComponentClassification.UnbalancedLayer

theorem false_of_pPrimeCore_eq_bot (hF1 : F1Odd) (hF2b : F2bOdd) (hSpin : SpinFactsAllOdd)
    {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L))
    (hq : p ^ f = 3 ∨ 5 ≤ p ^ f) (hchar : (L.subgroupOf (centralizer {z})).Characteristic)
    (hconj : ∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔
      (x ∈ L ∧ orderOf x = 2))
    (hOH : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥) (S : Sylow 2 G)
    (hSL : (S : Subgroup G) ≤ L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ centralizer ({z} : Set G) := hL.1
  have hn : (L.subgroupOf (centralizer ({z} : Set G))).Normal := by
    have := hchar
    infer_instance
  have hOL : pPrimeCore 2 ↥L = ⊥ := by
    have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hn.isSubnormal
    rw [hOH, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    have h2 := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hLH)
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  have hcovL : IsCoverOf .POmegaOdd 3 p f 2 ↥L :=
    isCoverOf_congr ((QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot) hcov
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (↥L ≃* spinGroup (quadOdd 3 K)) := by
    rcases hq with h3 | h5
    · obtain ⟨K, i1, i2, hK, he⟩ := nonempty_mulEquiv_spinSeven_three h3 hcovL
      exact ⟨K, i1, i2, hK.trans h3.symm, he⟩
    · obtain ⟨K, i1, i2, hK, -, -, -, he⟩ := nonempty_mulEquiv_spinOdd h5 hcovL
      exact ⟨K, i1, i2, hK, he⟩
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLH g.2))
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hez : e ⟨z, hzL⟩ = spinZ K := by
    refine eq_spinZ_of_mem_center hp hp2 hK ((mem_center_mulEquiv_iff e _).mpr hzc) ?_
    intro h
    apply hz1
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    exact this
  let φ : spinGroup (quadOdd 3 K) →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := (subtype_injective L).comp e.symm.injective
  have hrange : φ.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hφz : φ (spinZ K) = z := by
    change ((e.symm (spinZ K) : ↥L) : G) = z
    rw [← hez, MulEquiv.symm_apply_apply]
  have hoddL : Odd (L.relIndex (centralizer ({z} : Set G))) := by
    have hdvd : L.relIndex (centralizer ({z} : Set G)) ∣ (S : Subgroup G).index := by
      rw [← Subgroup.relIndex_mul_index (hSL.trans hLH),
        ← Subgroup.relIndex_mul_relIndex _ _ _ hSL hLH]
      exact (dvd_mul_left _ _).mul_right _
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => S.not_dvd_index (h2.trans hdvd))
  let Su : SetupOdd G :=
    { K := K
      p := p
      f := f
      hp := hp
      hp2 := hp2
      hK := hK
      z := z
      L := L
      φ := φ
      hφ := hφ
      hrange := hrange
      hφz := hφz
      hLH := hLH
      hLn := fun h hh l hl => by
        have := hn.conj_mem ⟨l, hLH hl⟩ (mem_subgroupOf.mpr hl) ⟨h, hh⟩
        exact mem_subgroupOf.mp this
      hodd := hoddL
      hinv := fun x hx hx2 =>
        ((hconj x hx).mp (exists_conj_of_sylow_le hLH hconj S hSL hx2)).1
      oneClass := fun x hx2 => exists_conj_of_sylow_le hLH hconj S hSL hx2 }
  exact Su.false_of_spinFacts hF1 hF2b (hSpin K p f hp hp2 hK)

end CFSG.ComponentClassification.HarrisLit.T1.S74
