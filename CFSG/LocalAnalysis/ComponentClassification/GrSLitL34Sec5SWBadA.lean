module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFus

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem centralizer_le_normalizer_of_sec4
    (hMax : MaximalTwoComponentInput) {G : Type} [Group G] [Finite G] {a x : G}
    {J S : Subgroup G} (hset : L34Sec4Setting G a x J S) :
    centralizer ({a} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨hbase, hU3, hL34, hmax, -, -, -⟩ := hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  exact GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax ⟨hsimple, hnab, hK, hUo, hU3.1,
    hU3.2.2.2.1, hU3.2.2.2.2.1, hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34,
    Or.inl ⟨hL34, hbase⟩⟩

theorem exists_conj_of_le_centralizer {G : Type} [Group G] [Finite G] {a : G} {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPb : P ≤ centralizer ({g⁻¹ * a * g} : Set G)) :
    ∃ h : G, h⁻¹ * (g⁻¹ * a * g) * h = a ∧ ∀ p ∈ P, h⁻¹ * p * h ∈ S := by
  set b : G := g⁻¹ * a * g with hbdef
  have hVC : P.map (MulAut.conj g).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heb := mem_centralizer_singleton_iff.mp (hPb he)
    rw [mem_centralizer_singleton_iff]
    show g * e * g⁻¹ * a = a * (g * e * g⁻¹)
    have hga : a = g * b * g⁻¹ := by rw [hbdef]; group
    rw [hga, show g * e * g⁻¹ * (g * b * g⁻¹) = g * (e * b) * g⁻¹ by group, heb]
    group
  obtain ⟨c, hcC, hc⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn
    (isSylowTwoIn_centralizer hS2 hcent hSyl) hVC (hP2.map _)
  refine ⟨g⁻¹ * c, ?_, fun p hp => ?_⟩
  · have hca : c⁻¹ * a * c = a := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hcC, ← mul_assoc, inv_mul_cancel,
        one_mul]
    rw [hbdef, show (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * c) = c⁻¹ * a * c by group, hca]
  · have h1 := hc _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hp)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [show (g⁻¹ * c)⁻¹ * p * (g⁻¹ * c) = c⁻¹ * (g * p * g⁻¹) * c by group]
    exact h1

theorem exists_conj_of_conj {G : Type} [Group G] {a : G} {M : Subgroup G}
    (hCM : centralizer ({a} : Set G) ≤ M) {b h : G} (hbh : h⁻¹ * b * h = a)
    (hah : ∃ m ∈ M, h⁻¹ * a * h = m⁻¹ * a * m) : ∃ m ∈ M, b = m⁻¹ * a * m := by
  obtain ⟨m, hm, ham⟩ := hah
  have hc : h * m⁻¹ ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : a = m * (h⁻¹ * a * h) * m⁻¹ := by rw [ham]; group
    calc h * m⁻¹ * a = h * m⁻¹ * (m * (h⁻¹ * a * h) * m⁻¹) := by rw [← e]
      _ = a * (h * m⁻¹) := by group
  have hhM : h ∈ M := by
    have := mul_mem (hCM hc) hm
    rwa [inv_mul_cancel_right] at this
  refine ⟨h⁻¹, inv_mem hhM, ?_⟩
  rw [inv_inv, ← hbh]
  group

end CFSG.ComponentClassification.GrSLit.GrS5S
