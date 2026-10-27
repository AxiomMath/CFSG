module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27Classes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporStruct
public import CFSG.Sporadic.Bridge.J3Surj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Sporadic.Schreier

theorem j3_fixN_pow {c : Equiv.Perm (Fin 6156)} (hc : c ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2) :
    fixN (c ^ e) = fixN c := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · have h2 : c ^ 2 = c⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hc
    rw [h2, fixN_inv]

theorem cent_conj_transport {S : Type} [Group S] {c : S} (hc : c ^ 3 = 1) {k₁ k₂ : S}
    {e₁ e₂ : ℕ} (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2) {E : Subgroup S}
    (hE : E ≤ Subgroup.centralizer {k₁ * c ^ e₁ * k₁⁻¹}) :
    E.map (MulAut.conj (k₂ * k₁⁻¹)).toMonoidHom ≤ Subgroup.centralizer {k₂ * c ^ e₂ * k₂⁻¹} := by
  rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_conj_map',
    CFSG.RankThree.PartTwo.KFacts.K426Rest.centralizer_pow_eq hc he₁] at hE
  rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_conj_map',
    CFSG.RankThree.PartTwo.KFacts.K426Rest.centralizer_pow_eq hc he₂]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 (hE hu)
  refine Subgroup.mem_map.2 ⟨v, hv, ?_⟩
  show k₂ * v * k₂⁻¹ = k₂ * k₁⁻¹ * (k₁ * v * k₁⁻¹) * (k₂ * k₁⁻¹)⁻¹
  group

theorem exists_E27_transport {B₀ : Subgroup (Equiv.Perm (Fin 6156))} (hP : B₀ ≤ j3P)
    (hEl : CFSG.IsElementaryAbelian 3 ↥B₀) (h27 : Nat.card ↥B₀ = 27)
    (hcomm : ∀ x ∈ B₀, ∀ z ∈ B₀, x * z = z * x)
    {a y k₁ k₂ c : Equiv.Perm (Fin 6156)} {e₁ e₂ : ℕ} (ha : a ∈ B₀) (hc : c ^ 3 = 1)
    (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2)
    (ha_eq : a = k₁ * c ^ e₁ * k₁⁻¹) (hy_eq : y = k₂ * c ^ e₂ * k₂⁻¹)
    (hk₁ : k₁ ∈ j3P) (hk₂ : k₂ ∈ j3P) :
    ∃ E : Subgroup (Equiv.Perm (Fin 6156)), E ≤ j3P ∧ E ≤ Subgroup.centralizer {y} ∧
      CFSG.IsElementaryAbelian 3 ↥E ∧ Nat.card ↥E = 27 := by
  have hBa : B₀ ≤ Subgroup.centralizer {a} := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm a ha x hx
  have hBk : B₀ ≤ Subgroup.centralizer {k₁ * c ^ e₁ * k₁⁻¹} := by
    rw [← ha_eq]
    exact hBa
  refine ⟨B₀.map (MulAut.conj (k₂ * k₁⁻¹)).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    have hgk : k₂ * k₁⁻¹ ∈ j3P := j3P.mul_mem hk₂ (j3P.inv_mem hk₁)
    exact j3P.mul_mem (j3P.mul_mem hgk (hP hu)) (j3P.inv_mem hgk)
  · rw [hy_eq]
    exact cent_conj_transport hc he₁ he₂ hBk
  · exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ hEl
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj (k₂ * k₁⁻¹)).toMonoidHom)
      (MulAut.conj (k₂ * k₁⁻¹)).injective, h27]

section Certified


theorem j3P_exists_E27_centralizer {y : Equiv.Perm (Fin 6156)} (hy : y ∈ j3P)
    (hy3 : orderOf y = 3) :
    ∃ E : Subgroup (Equiv.Perm (Fin 6156)), E ≤ j3P ∧ E ≤ Subgroup.centralizer {y} ∧
      CFSG.IsElementaryAbelian 3 ↥E ∧ Nat.card ↥E = 27 := by
  obtain ⟨B₀, B₁, hB₀P, hB₀el, hB₀27, hB₁B₀, hB₁9, hB₁fix, hB₀fix⟩ := j3P_e27_split
  have hB₀' := CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hB₀el
  have hcomm : ∀ x ∈ B₀, ∀ z ∈ B₀, x * z = z * x := hB₀'.1
  obtain ⟨a, ha, haB₁⟩ : ∃ a ∈ B₀, a ∉ B₁ := by
    by_contra hcon
    push Not at hcon
    have hle : B₀ ≤ B₁ := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨b, hbB₁, hb1⟩ : ∃ b ∈ B₁, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B₁ = ⊥ := by
      ext x
      rw [Subgroup.mem_bot]
      exact ⟨fun hx => hcon x hx, fun hx => by rw [hx]; exact B₁.one_mem⟩
    rw [hbot, Subgroup.card_bot] at hB₁9
    norm_num at hB₁9
  have hb : b ∈ B₀ := hB₁B₀ hbB₁
  have ha1 : a ≠ 1 := fun h => haB₁ (by rw [h]; exact B₁.one_mem)
  have hoa : orderOf a = 3 := orderOf_eq_prime (hB₀'.2 a ha) ha1
  have hob : orderOf b = 3 := orderOf_eq_prime (hB₀'.2 b hb) hb1
  have hfa : fixN a = 36 := hB₀fix a ha haB₁
  have hfb : fixN b = 0 := hB₁fix b hbB₁ hb1
  have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
  have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
  obtain ⟨ka, hka, ca, hca, ea, hea, ha_eq⟩ := j3t_fusion (hB₀P ha) hoa
  obtain ⟨kb, hkb, cb, hcb, eb, heb, hb_eq⟩ := j3t_fusion (hB₀P hb) hob
  obtain ⟨ky, hky, cy, hcy, ey, hey, hy_eq⟩ := j3t_fusion hy hy3
  have hcaA : ca = j3tXA := by
    rcases hca with h | h
    · exact h
    · exfalso
      have hc3 : ca ^ 3 = 1 := by rw [h]; exact hB3
      have h0 : fixN a = 0 := by
        rw [ha_eq, fixN_conj, j3_fixN_pow hc3 hea, h, fixN_XB]
      omega
  have hcbB : cb = j3tXB := by
    rcases hcb with h | h
    · exfalso
      have hc3 : cb ^ 3 = 1 := by rw [h]; exact hA3
      have h36 : fixN b = 36 := by
        rw [hb_eq, fixN_conj, j3_fixN_pow hc3 heb, h, fixN_XA]
      omega
    · exact h
  rcases hcy with h | h
  · rw [hcaA] at ha_eq
    rw [h] at hy_eq
    exact exists_E27_transport hB₀P hB₀el hB₀27 hcomm ha hA3 hea hey ha_eq hy_eq hka hky
  · rw [hcbB] at hb_eq
    rw [h] at hy_eq
    exact exists_E27_transport hB₀P hB₀el hB₀27 hcomm hb hB3 heb hey hb_eq hy_eq hkb hky

theorem j3P_three_le_pRank_centralizer (y : ↥j3P) (hy : orderOf y = 3) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({y} : Set ↥j3P)) := by
  have hy' : orderOf (y : Equiv.Perm (Fin 6156)) = 3 := (Subgroup.orderOf_coe y).trans hy
  obtain ⟨E, hEj, hEc, hEel, hE27⟩ := j3P_exists_E27_centralizer y.2 hy'
  have hE'c : E.subgroupOf j3P ≤ Subgroup.centralizer ({y} : Set ↥j3P) := by
    intro z hz
    have hzE : (z : Equiv.Perm (Fin 6156)) ∈ E := hz
    have hc := Subgroup.mem_centralizer_iff.1 (hEc hzE) (y : Equiv.Perm (Fin 6156))
      (Set.mem_singleton _)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact Subtype.ext hc
  have hE0 := CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hEel
  have hE'el : CFSG.IsElementaryAbelian 3 ↥(E.subgroupOf j3P) := by
    refine CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.2 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact Subtype.ext (hE0.1 a.1 ha b.1 hb)
    · exact Subtype.ext (hE0.2 a.1 ha)
  have hE'27 : Nat.card ↥(E.subgroupOf j3P) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEj).toEquiv, hE27]
  have hk : Nat.card ↥(E.subgroupOf j3P) = 3 ^ 3 := by
    rw [hE'27]
    norm_num
  exact CFSG.SectionRank.le_pRank (by norm_num) hE'c
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 (E.subgroupOf j3P)).1 hE'el) hk

end Certified

section SporJ3T


theorem j3_three_le_pRank_centralizer
    (G : Type) [Group G] [Finite G]
    (e : G ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) (y : G)
    (hy : orderOf y = 3) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.J3 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group := b0
  let ψ : G ≃* ↥j3P :=
    e.trans (b.symm.trans (j3PermEquiv))
  have hψ : orderOf (ψ y) = 3 := (MulEquiv.orderOf_eq ψ y).trans hy
  have := j3P_three_le_pRank_centralizer (ψ y) hψ
  rwa [← pRank_centralizer_eq_of_mulEquiv ψ y] at this

end SporJ3T

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
