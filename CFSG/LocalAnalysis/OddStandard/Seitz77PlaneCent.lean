module

public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneReg

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv

namespace Facts

section Cent

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem isSylowOf_centralizer (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hα : d.Alpha) (hW : W = V₁ ∨ W = V₂)
    (hcent : ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) →
      x ∈ W ⊔ centralizer (A : Set G)) :
    IsSylowOf 2 (d.E W : Subgroup G) (centralizer ((d.E W : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWV, -, -⟩ := hR.property hW
  obtain ⟨hE2, hEC⟩ := F.E_pgroup d hR hW
  set C := centralizer ((d.E W : Subgroup G) : Set G) with hC
  have hE' : IsPGroup 2 ((d.E W : Subgroup G).subgroupOf C) := hE2.comap_subtype
  obtain ⟨D₀, hD₀⟩ := hE'.exists_le_sylow
  set D : Subgroup G := (D₀ : Subgroup ↥C).map C.subtype with hD
  have hDsyl : IsSylowOf 2 D C := ⟨D₀, rfl⟩
  have hED : (d.E W : Subgroup G) ≤ D := fun x hx =>
    ⟨⟨x, hEC hx⟩, hD₀ (mem_subgroupOf.mpr hx), rfl⟩
  have htE : d.t ∈ (d.E W : Subgroup G) := mem_sup_right (mem_zpowers _)
  have hDE : D ≤ (d.E W : Subgroup G) := by
    intro x hx
    have hxC : x ∈ C := hDsyl.le hx
    have hxt : x * d.t = d.t * x := (mem_centralizer_iff.mp hxC d.t htE).symm
    have hxN : x ∈ normalizer (A : Set G) :=
      (centralizer_t_facts d.sector).1 (mem_centralizer_singleton_iff.mpr hxt)
    have hxW : ∀ w ∈ W, x * w = w * x := fun w hw =>
      (mem_centralizer_iff.mp hxC w (mem_sup_left hw)).symm
    obtain ⟨w, hw, k, hk, rfl⟩ := mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a (hWV ha).2) (hcent x hxN hxW)
    have hkD : k ∈ D := by
      have := D.mul_mem (D.inv_mem (hED (mem_sup_left hw))) hx
      simpa using this
    have hsg := F.sg_eq_zpowers d hR hα
    have hDK : D ⊓ centralizer (A : Set G) = sg A d.R :=
      sg_maximal inf_le_right hDsyl.isPGroup.to_inf_left (by
        rw [hsg]
        exact (zpowers_le).mpr ⟨hED htE, d.t_mem_K⟩)
    have hkR : k ∈ sg A d.R := hDK ▸ ⟨hkD, hk⟩
    rw [hsg] at hkR
    exact mul_mem (mem_sup_left hw) ((zpowers_le.mpr htE) hkR)
  rw [show D = (d.E W : Subgroup G) from le_antisymm hDE hED] at hDsyl
  exact hDsyl

theorem exists_oddComplement (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hα : d.Alpha) (hW : W = V₁ ∨ W = V₂)
    (hcent : ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) →
      x ∈ W ⊔ centralizer (A : Set G)) :
    ∃ O : Subgroup G, O ≤ centralizer ((d.E W : Subgroup G) : Set G) ∧ Odd (Nat.card O) ∧
      (∀ n ∈ normalizer ((d.E W : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O) ∧
      O ⊔ (d.E W : Subgroup G) = centralizer ((d.E W : Subgroup G) : Set G) ∧
      O ⊓ (d.E W : Subgroup G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hE2, hEC⟩ := F.E_pgroup d hR hW
  set C := centralizer ((d.E W : Subgroup G) : Set G) with hC
  have hsyl := F.isSylowOf_centralizer d hR hα hW hcent
  obtain ⟨P, hP⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hcentral : ∀ n : ↥C, ∀ q ∈ (P : Subgroup ↥C), n * q = q * n := by
    intro n q hq
    have hqE : (q : G) ∈ (d.E W : Subgroup G) := mem_subgroupOf.mp (hP ▸ hq)
    exact Subtype.ext (mem_centralizer_iff.mp n.2 q hqE).symm
  have hP' : normalizer ((P : Subgroup ↥C) : Set ↥C) ≤ centralizer ((P : Subgroup ↥C) : Set ↥C) :=
    fun n _ => mem_centralizer_iff.mpr fun q hq => (hcentral n q hq).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP'
  have hKodd0 := MonoidHom.not_dvd_card_ker_transferSylow P hP'
  have hKnormal := MonoidHom.normal_ker (MonoidHom.transferSylow P hP')
  obtain ⟨K, hK⟩ : ∃ K : Subgroup ↥C, K = (MonoidHom.transferSylow P hP').ker := ⟨_, rfl⟩
  rw [← hK] at hcompl hKodd0 hKnormal
  have hPmap : (P : Subgroup ↥C).map C.subtype = (d.E W : Subgroup G) := by
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEC]
  have hOodd : Odd (Nat.card (K.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd0)
  have hOC : ∀ c ∈ C, ∀ o ∈ K.map C.subtype, c * o * c⁻¹ ∈ K.map C.subtype := by
    rintro c hc _ ⟨o, ho, rfl⟩
    exact ⟨⟨c, hc⟩ * o * ⟨c, hc⟩⁻¹, hKnormal.conj_mem o ho ⟨c, hc⟩, rfl⟩
  have hsup : K.map C.subtype ⊔ (d.E W : Subgroup G) = C := by
    rw [← hPmap, ← Subgroup.map_sup, hcompl.sup_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hinf : K.map C.subtype ⊓ (d.E W : Subgroup G) = ⊥ := by
    rw [← hPmap, ← Subgroup.map_inf_eq _ _ _ C.subtype_injective, hcompl.disjoint.eq_bot,
      Subgroup.map_bot]
  have hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ K.map C.subtype := by
    intro x hx hxo
    have hEN : (d.E W : Subgroup G) ≤ normalizer ((K.map C.subtype : Subgroup G) : Set G) :=
      fun e he => (mem_normalizer_iff.mpr fun o => ⟨fun ho => hOC e (hEC he) o ho, fun ho => by
        have := hOC e⁻¹ (inv_mem (hEC he)) _ ho
        simpa [mul_assoc] using this⟩)
    rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEN,
      Set.mem_mul] at hx
    obtain ⟨o, ho, e, he, rfl⟩ := hx
    have hoC : o ∈ C := map_subtype_le _ ho
    have hcomm : Commute o e := (mem_centralizer_iff.mp hoC e he).symm
    have hpow : (o * e) ^ orderOf (o * e) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at hpow
    have hem : e ^ orderOf (o * e) ∈ K.map C.subtype ⊓ (d.E W : Subgroup G) := by
      refine ⟨?_, pow_mem he _⟩
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact (K.map C.subtype).inv_mem ((K.map C.subtype).pow_mem ho _)
    rw [hinf, Subgroup.mem_bot] at hem
    have he1 : e = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hE2 ⟨e, he⟩
      rw [Subgroup.orderOf_mk] at hk
      have hdvd : orderOf e ∣ orderOf (o * e) := orderOf_dvd_of_pow_eq_one hem
      rcases k with _ | k
      · exact orderOf_eq_one_iff.mp (by simpa using hk)
      · exfalso
        have h2 : 2 ∣ orderOf (o * e) :=
          (show 2 ∣ orderOf e from ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩).trans hdvd
        exact (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr h2)
    rw [he1, mul_one]
    exact ho
  refine ⟨K.map C.subtype, map_subtype_le _, hOodd, fun n hn o ho => ?_, hsup, hinf⟩
  have hoC : o ∈ C := map_subtype_le _ ho
  refine hodd _ (conj_mem_centralizer_of_mem_normalizer hn hoC) ?_
  rw [← (SemiconjBy.conj_mk n o).orderOf_eq]
  exact hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)

theorem exists_regularNormal_sylow_oddComplement (F : Facts A)
    (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) (hW : W = V₁ ∨ W = V₂)
    (AS : ASide A d.V W)
    (hcent : ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) →
      x ∈ W ⊔ centralizer (A : Set G)) :
    ∃ X Q O : Subgroup G, IsRegularNormal (d.E W : Subgroup G) d.t X ∧ IsSylowOf 2 Q X ∧
      (d.E W : Subgroup G) < Q ∧ Odd (Nat.card O) ∧
      (∀ n ∈ normalizer ((d.E W : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O) ∧
      O ⊔ (d.E W : Subgroup G) = centralizer ((d.E W : Subgroup G) : Set G) ∧
      Q ⊔ O = X ∧ Q ⊓ O = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := F.exists_regularNormal d hR hα hW AS
  obtain ⟨hE2, hEC⟩ := F.E_pgroup d hR hW
  obtain ⟨Q, hQsyl, hEQ, hQC⟩ := hX.exists_sylow hE2 hEC
  obtain ⟨O, hOC, hOodd, hOn, hOsup, hOinf⟩ := F.exists_oddComplement d hR hα hW hcent
  refine ⟨X, Q, O, hX, hQsyl, hEQ, hOodd, hOn, hOsup, ?_, ?_⟩
  · refine le_antisymm (sup_le hQsyl.le (hOC.trans hX.centralizer_le)) ?_
    rw [← hQC]
    refine sup_le le_sup_left ?_
    rw [← hOsup]
    exact sup_le le_sup_right (hEQ.le.trans le_sup_left)
  · have hP2 : IsPGroup 2 ↥(Q ⊓ O) := hQsyl.isPGroup.to_inf_left
    rcases hP2.card_eq_or_dvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hodd' : Odd (Nat.card ↥(Q ⊓ O)) :=
        hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)

end Cent

end Facts

end CFSG.OddStandard.Seitz77
