module

public import CFSG.ClassicalInvolution.Balance.WeakFrame.Pairing
public import CFSG.ClassicalInvolution.Generic.Weyl

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

@[expose] def WeakFibreLE2 (S : Set (Subgroup G)) : Prop :=
  ∀ (z : G), ∀ K ∈ S, ∀ L ∈ S, ∀ M ∈ S, IsCentralInvolution K z → IsCentralInvolution L z →
    IsCentralInvolution M z → K = L ∨ K = M ∨ L = M

theorem not_commutes_of_weakPairingAdj [Finite G] (Fr : WeakPreFrame F Ω E S) {K L : Subgroup G}
    (hL : L ∈ S) (h : WeakPairingAdj E K L) : ¬ Commutes K L := by
  obtain ⟨z, hz, hzn⟩ := h
  intro hc
  apply hzn
  exact mem_axisSub_iff.mpr ⟨Fr.mem_of_central hL hz, fun k hk => hc k hk z hz.mem⟩

theorem not_weakPairingAdj_self [Finite G] (Fr : WeakPreFrame F Ω E S) {K : Subgroup G}
    (hK : K ∈ S) : ¬ WeakPairingAdj E K K := by
  rintro ⟨z, hz, hzn⟩
  exact hzn (Fr.mem_axisSub_of_central hK hz)

private theorem weak_isLine_cases [Finite G] (Fr : WeakPreFrame F Ω E S) {K L : Subgroup G}
    (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L) (hl : IsLine E K L) {zK zL : G}
    (hzK : IsCentralInvolution K zK) (hzL : IsCentralInvolution L zL) :
    (zL ∈ axisSub E K ∧ zK ∈ axisSub E L ∧ zL = zK ∧
        ∃ M ∈ S, M ≠ K ∧ M ≠ L ∧ IsCentralInvolution M zL) ∨
      (zL ∉ axisSub E K ∧ zK ∉ axisSub E L) := by
  obtain ⟨wK, hwK, hwK', wL, hwL, hwL', hswap, -⟩ := hl.swap
  have hzKE : zK ∈ E := Fr.mem_of_central hK hzK
  have hzLE : zL ∈ E := Fr.mem_of_central hL hzL
  have hwKN : wK ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hwK).2
  have hwLN : wL ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hwL).2
  have hKs := Fr.weakInSigma hK
  have hLs := Fr.weakInSigma hL
  have heq : wK * zL * wK⁻¹ = wL * zK * wL⁻¹ := by
    have a1 := hzL.conj wK
    have a2 := hzK.conj wL
    rw [hswap] at a1
    exact Fr.eq_of_central (Fr.conj_mem hwLN hK) a1 a2
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
      hLs.conj_eq_mul_of_not_mem_axis Fr.elem Fr.odd hzL hwL hwL' hzKE h2
    rw [e1, e2] at heq
    apply hzK.ne_one
    have : zK * zL = 1 * zL := by rw [← heq, one_mul]
    exact mul_right_cancel this
  · exfalso
    have e1 : wK * zL * wK⁻¹ = zL * zK :=
      hKs.conj_eq_mul_of_not_mem_axis Fr.elem Fr.odd hzK hwK hwK' hzLE h1
    have e2 : wL * zK * wL⁻¹ = zK :=
      InSigma.conj_eq_of_mem_axis (E := E) (K := L) (normPart_le_left L E hwL) h2
    rw [e1, e2] at heq
    apply hzL.ne_one
    have : zL * zK = 1 * zK := by rw [heq, one_mul]
    exact mul_right_cancel this
  · right
    exact ⟨h1, h2⟩

theorem weakPairingSymmetric_of_a2Dichotomy [Finite G] (Fr : WeakPreFrame F Ω E S)
    (hA2 : A2Dichotomy E S) : WeakPairingSymmetric E S := by
  intro K hK L hL h
  have hne : K ≠ L := by
    rintro rfl
    exact not_weakPairingAdj_self Fr hK h
  have hnc := not_commutes_of_weakPairingAdj Fr hL h
  have hl : IsLine E K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK, -⟩ := Fr.exists_central hK
  obtain ⟨zL, hzL, -⟩ := Fr.exists_central hL
  have h' : zL ∉ axisSub E K := (weakPairingAdj_iff Fr hL hzL).mp h
  rcases weak_isLine_cases Fr hK hL hne hl hzK hzL with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 h'
  · exact (weakPairingAdj_iff Fr hK hzK).mpr h2


theorem weakPairingAdj_iff_not_commutes [Finite G] (Fr : WeakPreFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : WeakFibreLE2 S) {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S)
    (hne : K ≠ L) : WeakPairingAdj E K L ↔ ¬ Commutes K L := by
  refine ⟨not_commutes_of_weakPairingAdj Fr hL, fun hnc => ?_⟩
  have hl : IsLine E K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK, -⟩ := Fr.exists_central hK
  obtain ⟨zL, hzL, -⟩ := Fr.exists_central hL
  rw [weakPairingAdj_iff Fr hL hzL]
  rcases weak_isLine_cases Fr hK hL hne hl hzK hzL with
    ⟨-, -, hzz, M, hM, hMK, hML, hzM⟩ | ⟨h1, -⟩
  · exfalso
    have hzK' : IsCentralInvolution K zL := by rwa [hzz]
    rcases hfib zL K hK L hL M hM hzK' hzL hzM with h | h | h
    · exact hne h
    · exact hMK h.symm
    · exact hML h.symm
  · exact h1

theorem weakPairingConnected_of_nonCommConnected [Finite G] (Fr : WeakPreFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : WeakFibreLE2 S) (hconn : NonCommConnected S) :
    WeakPairingConnected E S := by
  intro K L
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected K L)
  refine Relation.ReflTransGen.mono (fun K' L' hadj => ?_) K L h
  obtain ⟨hne, hnc⟩ := nonCommGraph_adj.mp hadj
  exact (weakPairingAdj_iff_not_commutes Fr hA2 hfib K'.2 L'.2
    (fun h => hne (Subtype.ext h))).mpr hnc

theorem WeakPreFrame.toFrame [Finite G] (Fr : WeakPreFrame F Ω E S) (hA2 : A2Dichotomy E S)
    (hfib : WeakFibreLE2 S) (hconn : NonCommConnected S) : WeakToralFrame F Ω E S :=
  { Fr with
    sym := weakPairingSymmetric_of_a2Dichotomy Fr hA2
    conn := weakPairingConnected_of_nonCommConnected Fr hA2 hfib hconn }

end CFSG.ClassicalInvolution.Balance
