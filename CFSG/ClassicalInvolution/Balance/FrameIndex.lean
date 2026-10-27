module

public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing
public import CFSG.ClassicalInvolution.Generic.Weyl

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

theorem not_commutes_of_pairingAdj (Fr : ToralFrame F Ω E S) {K L : Subgroup G} (hL : L ∈ S)
    (h : PairingAdj E K L) : ¬ Commutes K L := by
  obtain ⟨z, hz, hzn⟩ := h
  intro hc
  apply hzn
  exact mem_axisSub_iff.mpr ⟨Fr.mem_of_isUniqueInvolution hL hz, fun k hk => hc k hk z hz.mem⟩

theorem not_pairingAdj_self (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) :
    ¬ PairingAdj E K K := by
  have := Fr.finite
  rintro ⟨z, hz, hzn⟩
  exact hzn ((Fr.inSigma hK).unique_involution_mem_axis Fr.odd hz)

private theorem isLine_cases [Finite F] (Fr : ToralFrame F Ω E S) {K L : Subgroup G} (hK : K ∈ S)
    (hL : L ∈ S) (hne : K ≠ L) (hl : IsLine E K L) {zK zL : G} (hzK : IsUniqueInvolution K zK)
    (hzL : IsUniqueInvolution L zL) :
    (zL ∈ axisSub E K ∧ zK ∈ axisSub E L ∧ zL = zK ∧
        ∃ M ∈ S, M ≠ K ∧ M ≠ L ∧ IsUniqueInvolution M zL) ∨
      (zL ∉ axisSub E K ∧ zK ∉ axisSub E L) := by
  obtain ⟨wK, hwK, hwK', wL, hwL, hwL', hswap, -⟩ := hl.swap
  have hzKE : zK ∈ E := Fr.mem_of_isUniqueInvolution hK hzK
  have hzLE : zL ∈ E := Fr.mem_of_isUniqueInvolution hL hzL
  have hwKN : wK ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hwK).2
  have heq : wK * zL * wK⁻¹ = wL * zK * wL⁻¹ := by
    have a1 := hzL.conj wK
    have a2 := hzK.conj wL
    rw [hswap] at a1
    exact a1.eq a2
  by_cases h1 : zL ∈ axisSub E K <;> by_cases h2 : zK ∈ axisSub E L
  · left
    have e1 : wK * zL * wK⁻¹ = zL :=
      InSigma.conj_eq_of_mem_axis (E := E) (K := K) (normPart_le_left K E hwK) h1
    have e2 : wL * zK * wL⁻¹ = zK :=
      InSigma.conj_eq_of_mem_axis (E := E) (K := L) (normPart_le_left L E hwL) h2
    have hzz : zL = zK := by rw [← e1, ← e2, heq]
    refine ⟨h1, h2, hzz, conjSub wK L, Fr.conj_mem hwKN hL, ?_, ?_, ?_⟩
    · exact conjSub_ne_of_ne (normPart_le_left K E hwK) hne
    · intro h
      rw [hswap] at h
      exact conjSub_ne_of_ne (normPart_le_left L E hwL) hne.symm h
    · have := hzL.conj wK
      rwa [e1] at this
  · exfalso
    have e1 : wK * zL * wK⁻¹ = zL :=
      InSigma.conj_eq_of_mem_axis (E := E) (K := K) (normPart_le_left K E hwK) h1
    have e2 : wL * zK * wL⁻¹ = zK * zL :=
      (Fr.inSigma hL).conj_eq_mul_of_not_mem_axis Fr.odd hzL hwL hwL' hzKE h2
    rw [e1, e2] at heq
    apply hzK.ne_one
    have : zK * zL = 1 * zL := by rw [← heq, one_mul]
    exact mul_right_cancel this
  · exfalso
    have e1 : wK * zL * wK⁻¹ = zL * zK :=
      (Fr.inSigma hK).conj_eq_mul_of_not_mem_axis Fr.odd hzK hwK hwK' hzLE h1
    have e2 : wL * zK * wL⁻¹ = zK :=
      InSigma.conj_eq_of_mem_axis (E := E) (K := L) (normPart_le_left L E hwL) h2
    rw [e1, e2] at heq
    apply hzL.ne_one
    have : zL * zK = 1 * zK := by rw [heq, one_mul]
    exact mul_right_cancel this
  · right
    exact ⟨h1, h2⟩

theorem pairingSymmetric_of_a2Dichotomy (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) : PairingSymmetric E S := by
  have := Fr.finite
  intro K hK L hL h
  have hne : K ≠ L := by
    rintro rfl
    exact not_pairingAdj_self Fr hK h
  have hnc := not_commutes_of_pairingAdj Fr hL h
  have hl : IsLine E K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK⟩ := Fr.exists_isUniqueInvolution hK
  obtain ⟨zL, hzL⟩ := Fr.exists_isUniqueInvolution hL
  have h' : zL ∉ axisSub E K := (pairingAdj_iff hzL).mp h
  rcases isLine_cases Fr hK hL hne hl hzK hzL with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 h'
  · exact (pairingAdj_iff hzK).mpr h2

theorem pairingAdj_iff_not_commutes (Fr : ToralFrame F Ω E S) (hA2 : A2Dichotomy E S)
    (hfib : FibreLE2 S) {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L) :
    PairingAdj E K L ↔ ¬ Commutes K L := by
  have := Fr.finite
  refine ⟨not_commutes_of_pairingAdj Fr hL, fun hnc => ?_⟩
  have hl : IsLine E K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK⟩ := Fr.exists_isUniqueInvolution hK
  obtain ⟨zL, hzL⟩ := Fr.exists_isUniqueInvolution hL
  rw [pairingAdj_iff hzL]
  rcases isLine_cases Fr hK hL hne hl hzK hzL with ⟨-, -, hzz, M, hM, hMK, hML, hzM⟩ | ⟨h1, -⟩
  · exfalso
    have hzK' : IsUniqueInvolution K zL := by rwa [hzz]
    rcases hfib zL K hK L hL M hM hzK' hzL hzM with h | h | h
    · exact hne h
    · exact hMK h.symm
    · exact hML h.symm
  · exact h1

theorem pairingConnected_of_nonCommConnected (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) :
    PairingConnected E S := by
  intro K L
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected K L)
  refine Relation.ReflTransGen.mono (fun K' L' hadj => ?_) K L h
  obtain ⟨hne, hnc⟩ := nonCommGraph_adj.mp hadj
  exact (pairingAdj_iff_not_commutes Fr hA2 hfib K'.2 L'.2 (fun h => hne (Subtype.ext h))).mpr hnc

theorem mem_or_mem_or_mul_mem_zClosure_of_a2Dichotomy (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) {a x y : G}
    (ha : a ∈ E) (hx : x ∈ E) (hy : y ∈ E) :
    x ∈ zClosure E S a ∨ y ∈ zClosure E S a ∨ x * y ∈ zClosure E S a :=
  mem_or_mem_or_mul_mem_zClosure Fr (pairingSymmetric_of_a2Dichotomy Fr hA2)
    (pairingConnected_of_nonCommConnected Fr hA2 hfib hconn) ha hx hy

theorem relIndex_zClosure_le_two_of_a2Dichotomy (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) {a : G} (ha : a ∈ E) :
    (zClosure E S a).relIndex E ≤ 2 :=
  relIndex_zClosure_le_two Fr (pairingSymmetric_of_a2Dichotomy Fr hA2)
    (pairingConnected_of_nonCommConnected Fr hA2 hfib hconn) ha

end CFSG.ClassicalInvolution.Balance
