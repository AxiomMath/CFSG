module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GCount
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Reduce
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Solomon

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.ComponentClassification.UnbalancedLayer

theorem solomon74SpinSevenAsUsed_of (hL38 : Lemma38) (hF1 : F1) (hF2b : F2b)
    (hSpin : SpinFactsAll) : Solomon74SpinSevenAsUsed := by
  intro G _ _ hsimple hnonab hKP hcat z hz L hL hzL p f hp hp2 hcov h5 hchar hQ _ hconj S hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ centralizer ({z} : Set G) := hL.1
  have hn : (L.subgroupOf (centralizer ({z} : Set G))).Normal := by
    have := hchar
    infer_instance
  have hyp := hyp31i_of_le hnonab hKP hcat hz hL hzL hp hp2 hcov h5 hchar hQ hconj S hSL
  have hOH : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := hL38 G z p f hyp
  have hOL : pPrimeCore 2 ↥L = ⊥ := by
    have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hn.isSubnormal
    rw [hOH, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    have h2 := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hLH)
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  have hcovL : IsCoverOf .POmegaOdd 3 p f 2 ↥L :=
    isCoverOf_congr ((QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot) hcov
  obtain ⟨K, _, _, hK, -, -, -, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd h5 hcovL
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
  let Su : Setup G :=
    { K := K
      p := p
      f := f
      hp := hp
      hp2 := hp2
      hK := hK
      h5 := h5
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
  exact Su.false_of_spinFacts hF1 hF2b (hSpin K p f hp hp2 hK h5)

end CFSG.ComponentClassification.HarrisLit.T1.S74
