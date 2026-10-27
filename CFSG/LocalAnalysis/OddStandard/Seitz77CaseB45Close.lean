module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Odd

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers

section Conj

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_cs {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (cs g P) (cs g K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨cs_mono g hle, hP.map (MulAut.conj g).toMonoidHom, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P K
  have h2 := Subgroup.relIndex_mul_card (cs g P) (cs g K)
  rw [inf_eq_left.mpr hle] at h1
  rw [inf_eq_left.mpr (cs_mono g hle), nat_card_cs, nat_card_cs] at h2
  have h3 : (cs g P).relIndex (cs g K) = P.relIndex K := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, h1]
  rw [h3]
  exact hdvd

omit [Finite G] in
theorem centralizer_conj_eq (t x : G) :
    centralizer ({x⁻¹ * t * x} : Set G) = cs x⁻¹ (centralizer ({t} : Set G)) := by
  ext z
  rw [mem_cs, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e1 : x⁻¹⁻¹ * z * x⁻¹ * t = x⁻¹⁻¹ * (z * (x⁻¹ * t * x)) * x⁻¹ := by group
    have e2 : t * (x⁻¹⁻¹ * z * x⁻¹) = x⁻¹⁻¹ * ((x⁻¹ * t * x) * z) * x⁻¹ := by group
    rw [e1, e2, h]
  · intro h
    have e1 : z * (x⁻¹ * t * x) = x⁻¹ * (x⁻¹⁻¹ * z * x⁻¹ * t) * x := by group
    have e2 : x⁻¹ * t * x * z = x⁻¹ * (t * (x⁻¹⁻¹ * z * x⁻¹)) * x := by group
    rw [e1, e2, h]

end Conj

end CFSG.OddStandard.Seitz77.CaseB45

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CaseB45

theorem caseBG0_false
    (hchk : Certificates.Seitz77CaseB45.fbSixCheck = true) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : Hyp G A) (d : Datum A) {G₁ G₂ S₀ W₁ W₂ : Subgroup G}
    (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.simple
  obtain ⟨Q, _, _, MD, ⟨E⟩⟩ := c.exists_emb hchk
  obtain ⟨T, hPT, hST, hTN⟩ := c.exists_sylow E
  have cd := c.compData
  have htT : d.t ∈ (T : Subgroup G) := hPT d.t_mem_P
  have hidx : ((T : Subgroup G) ⊓ normalizer (G₁ : Set G)).relIndex (T : Subgroup G) = 2 :=
    E.relIndex_two hTN htT
  have htM : d.t ∉ (T : Subgroup G) ⊓ normalizer (G₁ : Set G) := fun hm => cd.t_not_mem hm.2
  obtain ⟨x, hxM, hext⟩ :=
    CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup h.nonab
      T.isPGroup' T.not_dvd_index inf_le_left hidx htT htM (datum_t_sq d) (mul_one 1)
      (fun y _ => by simp)
  have ht'2 : (x⁻¹ * d.t * x) * (x⁻¹ * d.t * x) = 1 := by
    calc (x⁻¹ * d.t * x) * (x⁻¹ * d.t * x) = x⁻¹ * (d.t * d.t) * x := by group
      _ = 1 := by rw [datum_t_sq d]; group
  have ht'1 : x⁻¹ * d.t * x ≠ 1 := by
    intro h1
    have h2 : d.t = 1 :=
      calc d.t = x * (x⁻¹ * d.t * x) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by rw [h1]
        _ = 1 := by group
    have h3 := d.sector.t_order
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hS1 : IsSylowOf 2 ((T : Subgroup G) ⊓ centralizer ({x⁻¹ * d.t * x} : Set G))
      (centralizer ({x⁻¹ * d.t * x} : Set G)) := isSylowOf_iff.2 hext
  have hS2 : IsSylowOf 2 (cs x⁻¹ d.P) (centralizer ({x⁻¹ * d.t * x} : Set G)) := by
    rw [centralizer_conj_eq]
    exact isSylowOf_cs d.P_isSylow_centralizer x⁻¹
  obtain ⟨z, -, hzeq⟩ := exists_conj_of_isSylowOf hS1 hS2
  have hPeq : (T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.P := d.centralizer_T_eq T hPT
  have e : ↥((T : Subgroup G) ⊓ centralizer ({x⁻¹ * d.t * x} : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer ({d.t} : Set G)) :=
    (MulEquiv.subgroupCongr hzeq.symm).trans ((equivCs z (cs x⁻¹ d.P)).symm.trans
      ((equivCs x⁻¹ d.P).symm.trans (MulEquiv.subgroupCongr hPeq.symm)))
  exact E.not_equiv c.odd_centralizer T.isPGroup' hTN hST c.S₀_le c.card_S₀ htT cd.t_not_mem
    (datum_t_sq d) hxM.1 hxM.2 ht'2 ht'1 ⟨e⟩

end CFSG.OddStandard.Seitz77
