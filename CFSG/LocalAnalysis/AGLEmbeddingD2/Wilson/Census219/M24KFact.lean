module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24Tc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.SylowExp
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.ThreeCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec21 Subgroup Equiv

section YLevel


theorem m24TcQ_eq :
    m24TcQ = NativeSporadic.M24 ⊓ centralizer ({permOfArr 24 m24xA} : Set (Perm (Fin 24))) := by
  obtain ⟨-, -, hCeq, hcard⟩ := m24_threeSpec_rowA
  refine Subgroup.eq_of_le_of_card_ge (m24TcQ_le.trans hCeq.le) ?_
  rw [hcard, card_m24TcQ]

theorem m24xA_mem : permOfArr 24 m24xA ∈ NativeSporadic.M24 := m24_threeSpec_rowA.1

@[expose] noncomputable def m24y : NativeSporadic.M24 := ⟨permOfArr 24 m24xA, m24xA_mem⟩

theorem m24_centralizer_map :
    (centralizer ({m24y} : Set NativeSporadic.M24)).map NativeSporadic.M24.subtype = m24TcQ := by
  rw [m24TcQ_eq]
  exact map_subtype_centralizer m24y

theorem m24_layer :
    CFSG.inSubgroup CFSG.layer (centralizer ({m24y} : Set NativeSporadic.M24)) =
        centralizer ({m24y} : Set NativeSporadic.M24) ∧
      Nonempty (↥(centralizer ({m24y} : Set NativeSporadic.M24)) ≃* ↥m24TcQ) ∧
        CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥m24TcQ (alternatingGroup (Fin 6)) := by
  let e : ↥(centralizer ({m24y} : Set NativeSporadic.M24)) ≃* ↥m24TcQ :=
    ((centralizer ({m24y} : Set NativeSporadic.M24)).equivMapOfInjective
      NativeSporadic.M24.subtype NativeSporadic.M24.subtype_injective).trans
      (MulEquiv.subgroupCongr m24_centralizer_map)
  have hq : CFSG.IsQuasisimple ↥(centralizer ({m24y} : Set NativeSporadic.M24)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm m24Tc_spec.2.1
  exact ⟨Proving.inSubgroup_layer_eq_self hq, ⟨e⟩, m24Tc_spec.2.2⟩

end YLevel


section XLevel


theorem m24_pow_three {y : NativeSporadic.M24} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite NativeSporadic.M24 := inferInstance
  have hS := m24_sylow_le_card
  have hQ : Nat.card ((closure (permsA 24 m24sA)).subgroupOf NativeSporadic.M24) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hS.2]
    norm_num
  refine pow_eq_one_of_pPower_of_exp 3 3 _ hQ (by rw [m24_card]; norm_num) (fun q hq => ?_) hy
  apply Subtype.ext
  simpa using m24_sylow_exp (Subgroup.mem_subgroupOf.1 hq)

theorem ks219M24 : KS219M24 := by
  intro X _ _ ⟨e⟩ x hx1 hxc
  obtain ⟨S, hScard, hSC, k, hk⟩ := isCentral218_data hxc
  have hcardX : Nat.card X = 244823040 := by rw [Nat.card_congr e.toEquiv, m24_card]
  have hb3 : (e x) ^ 3 = 1 := m24_pow_three (k := k) (by rw [← map_pow, hk, map_one])
  have hb1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  have hord : orderOf ((e x : NativeSporadic.M24) : Perm (Fin 24)) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hb3 hb1
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover (e x).2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    let gP : NativeSporadic.M24 := ⟨g, hg⟩
    let φ : X ≃* NativeSporadic.M24 := e.trans (MulAut.conj gP⁻¹)
    have hφ : φ x = m24y := by
      apply Subtype.ext
      show g⁻¹ * ((e x : NativeSporadic.M24) : Perm (Fin 24)) * g = permOfArr 24 m24xA
      rw [hgr]
      show g⁻¹ * (g * permOfArr 24 m24xA * g⁻¹) * g = permOfArr 24 m24xA
      group
    obtain ⟨hlayer, ⟨e'⟩, hQ⟩ := m24_layer
    refine ks219_transport φ x (K := centralizer ({m24y} : Set NativeSporadic.M24))
      (by rw [hφ]; exact hlayer) ?_ e' hQ
    rw [hφ]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  ·
    exfalso
    have h27 : 27 ∣ Nat.card ↥(centralizer ({x} : Set X)) := by
      have := Subgroup.card_dvd_of_le hSC
      rwa [hScard, hcardX, ← m24_sylow] at this
    have hcard : Nat.card ↥(centralizer ({x} : Set X)) = 504 := by
      calc Nat.card ↥(centralizer ({x} : Set X))
          = Nat.card ↥((centralizer ({x} : Set X)).map e.toMonoidHom) :=
            (Subgroup.card_map_of_injective e.injective).symm
        _ = Nat.card ↥(centralizer ({e x} : Set NativeSporadic.M24)) := by
            rw [Proving.centralizer_map_mulEquiv_wilson e x]
        _ = Nat.card ↥((centralizer ({e x} : Set NativeSporadic.M24)).map
              NativeSporadic.M24.subtype) :=
            (Subgroup.card_map_of_injective NativeSporadic.M24.subtype_injective).symm
        _ = Nat.card ↥(NativeSporadic.M24 ⊓
              centralizer ({((e x : NativeSporadic.M24) : Perm (Fin 24))} : Set (Perm (Fin 24)))) := by
            rw [map_subtype_centralizer]
        _ = Nat.card ↥(centralizer ({((e x : NativeSporadic.M24) : Perm (Fin 24))} :
              Set (Perm (Fin 24))) ⊓ NativeSporadic.M24) := by rw [inf_comm]
        _ = Nat.card ↥(centralizer ({tp 24 m24Row3B.rep} : Set (Perm (Fin 24))) ⊓
              NativeSporadic.M24) := (card_centralizer_inf_conj NativeSporadic.M24 hg hgr.symm).symm
        _ = 504 := by rw [inf_comm]; exact m24_threeSpec_rowB
    rw [hcard] at h27
    exact absurd h27 (by norm_num)

end XLevel

end CFSG.AGLEmbeddingD2.Wilson.Census219
