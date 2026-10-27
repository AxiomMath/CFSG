module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Kernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Bad
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0BasicFacts

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

namespace A0Config

theorem eq_of_typeOne (hc : A0Config Q B z u N)
    (hI : ∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹) {x : J}
    (hxx : x * x = centralElt J) (hzxK : z * x ∈ a0Kernel Q B N) :
    x = u * z ∨ x = centralElt J * (u * z) := by
  have h := hc.setting
  have hz := hc.fourGen
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.mul_self
  set k := z * x with hkdef
  have hx : x = z * k := by rw [hkdef, ← mul_assoc, hz.mul_self, one_mul]
  have hzk := hI k hzxK
  rcases hc.conj_self_eq_of_mem_a0Kernel hzxK with h1 | h1
  ·
    have hkz : z * k = k * z := by
      calc z * k = z * k * z⁻¹ * z := by group
        _ = k * z := by rw [hzk, h1]
    have hkk : k * k = centralElt J := by
      rw [← hxx, hx, show z * k * (z * k) = (z * z) * (k * k) by
        rw [mul_assoc, ← mul_assoc k z k, ← hkz]; group, hz.mul_self, one_mul]
    have hku : u * k = k * u := by
      calc u * k = u * k * u⁻¹ * u := by group
        _ = k * u := by rw [h1]
    by_cases hk1 : k = u
    · left
      rw [hx, hk1, ← hc.comm]
    by_cases hk2 : k = centralElt J * u
    · right
      rw [hx, hk2, ← mul_assoc, (h.commute_centralElt z).eq, mul_assoc, ← hc.comm]
    exfalso
    have h2 := hc.mul_eq_central_mul_of_mem_a0Kernel hzxK hkk hk1 hk2
    rw [hku] at h2
    exact h.centralElt_ne_one (mul_eq_right.mp h2.symm)
  ·
    exfalso
    have hzk' : z * k * z⁻¹ = centralElt J * k := by rw [hzk, h1]
    have hkk : k * k = 1 := by
      have h3 : x * x = centralElt J * (k * k) := by
        rw [hx]
        calc z * k * (z * k) = (z * k * z⁻¹) * k := by rw [hzinv]; group
          _ = centralElt J * (k * k) := by rw [hzk', mul_assoc]
      rw [hxx] at h3
      have h4 : centralElt J * 1 = centralElt J * (k * k) := by rw [mul_one]; exact h3
      exact (mul_left_cancel h4).symm
    by_cases hk1 : k = 1
    · rw [hk1, mul_one, mul_inv_cancel] at h1
      exact h.centralElt_ne_one (by simpa using h1.symm)
    · have hke := hc.eq_centralElt_of_mem_a0Kernel hzxK
        (orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1)
      rw [hke, Setting.conj_eq_of_mem_center h.centralElt_mem_center,
        h.centralElt_mul_self] at h1
      exact h.centralElt_ne_one h1

theorem exists_mem_conj_of_typeOne (hc : A0Config Q B z u N)
    (hI : ∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹) {x : J}
    (hxQ : x ∈ (Q : Subgroup J)) (hxx : x * x = centralElt J) (hxc : x ≠ u * z)
    (hxc' : x ≠ centralElt J * (u * z)) : ∃ o ∈ N, o ∉ B ∧ o * x * o⁻¹ ∈ B := by
  have h := hc.setting
  obtain ⟨o, hoN, hoB⟩ := Set.not_subset.mp hc.not_le
  by_cases hxK : x ∈ a0Kernel Q B N
  · exact ⟨o, hoN, hoB, hxK.2 o hoN⟩
  by_cases hzxK : z * x ∈ a0Kernel Q B N
  · rcases hc.eq_of_typeOne hI hxx hzxK with h1 | h1
    · exact absurd h1 hxc
    · exact absurd h1 hxc'
  have hxZ : x ∉ Subgroup.center J := fun h1 => h.centralElt_ne_one (by
    rw [← hxx]
    exact h.mul_self_of_mem_center h1)
  have hzxZ : z * x ∉ Subgroup.center J := fun h1 => hzxK (by
    rcases h.mem_center_iff.mp h1 with h2 | h2 <;> rw [h2]
    · exact (a0Kernel Q B N).one_mem
    · exact hc.centralElt_mem_a0Kernel)
  obtain ⟨o', ho'N, ho'B, ho'x⟩ := hc.exists_mem_not_mem_commute_of_mul_not_mem hxQ
    (hxx ▸ h.centralElt_mem_center) hxZ hzxZ hzxK
  exact ⟨o', ho'N, ho'B, by rw [ho'x, mul_inv_cancel_right]; exact h.sylow_le hxQ⟩

theorem not_escapingLift
    (hc : A0Config Q B z u N) (IH : CanonicalBelow (Nat.card J)) :
    ¬ EscapingLift B z (u * z) := by
  intro hesc
  have h := hc.setting
  have hz := hc.fourGen
  obtain ⟨k, hkQ, hkne⟩ := h.exists_conj_mem_ne hz.mem
    (by rw [hz.mul_self]; exact (Subgroup.center J).one_mem) hz.not_mem_center
    hz.comm_mem_center
  set t := k⁻¹ * z * k with htdef
  have ht : t * t = 1 := by
    rw [htdef, show k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k by group, hz.mul_self]
    group
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.mul_self
  have htV : t ∉ fourGroup z := by
    intro hV
    apply hkne
    have hzk : z = k * t * k⁻¹ := by rw [htdef]; group
    rcases (hz.mem_fourGroup_iff h).mp hV with h1 | h1 | h1 | h1 <;> rw [h1]
    · exfalso
      apply hz.not_mem_center
      rw [hzk, h1, mul_one, mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    · exfalso
      apply hz.not_mem_center
      rw [hzk, h1, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
      exact h.centralElt_mem_center
    · rw [mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    · rw [hzinv, mul_assoc, hz.mul_self, mul_one]
      exact h.centralElt_mem_center
  have htc : t * (u * z) = u * z * t := by
    calc t * (u * z) = t * (u * z) * t⁻¹ * t := by group
      _ = u * z * t := by rw [hc.conj_mul_eq_of_not_mem hkQ ht htV]
  have hzL := distinguished_mem_localInvolutionPointHull hesc.commute
  have htL : ((t : J) : J ⧸ Subgroup.center J) ∈
      localInvolutionPointHull (z : J ⧸ Subgroup.center J)
        ((u * z : J) : J ⧸ Subgroup.center J) := by
    refine mem_localInvolutionPointHull ⟨(k : J ⧸ Subgroup.center J), ?_⟩ ?_
    · simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem, htdef,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    · rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, htc]
  have hyL : ((z * t : J) : J ⧸ Subgroup.center J) ∈
      localInvolutionPointHull (z : J ⧸ Subgroup.center J)
        ((u * z : J) : J ⧸ Subgroup.center J) := by
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ hzL htL
  have hbad := hesc.badLift_of_mem_hull h hz hyL (hc.mul_mul_self_of_not_mem hkQ ht htV)
  exact hbad.false_of_twoRank_eq_two h hz IH hc.twoRank_eq_two (hc.quasiImage_ne_top hesc)

theorem false_of_typeOne
    (hc : A0Config Q B z u N) (IH : CanonicalBelow (Nat.card J))
    (hI : ∀ k ∈ a0Kernel Q B N, z * k * z⁻¹ = u * k * u⁻¹) : False := by
  have h := hc.setting
  have hz := hc.fourGen
  have hcc := hc.mul_mul_self
  have hcB : u * z ∈ B := B.mul_mem hc.mem_core (hz.mem_of_setting h)
  have hcQ : u * z ∈ (Q : Subgroup J) := (Q : Subgroup J).mul_mem hc.mem hz.mem
  have hczz : (u * z) * z = z * (u * z) := by rw [← mul_assoc z u z, ← hc.comm]
  have hcz : Commute ((u * z : J) : J ⧸ Subgroup.center J) (z : J ⧸ Subgroup.center J) := by
    rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hczz]
  have hC : ∀ x : J, Commute (x : J ⧸ Subgroup.center J) ((u * z : J) : J ⧸ Subgroup.center J) →
      x ∈ B := by
    intro x hx
    by_contra hxB
    refine hc.not_escapingLift IH ⟨hcB, hcc, hcz, fun hle => hxB ?_⟩
    rw [← h.mk_mem_map_iff]
    exact hle (Subgroup.mem_centralizer_singleton_iff.mpr hx)
  have hcZ : u * z ∉ Subgroup.center J := fun h1 => h.centralElt_ne_one (by
    rw [← hcc]
    exact h.mul_self_of_mem_center h1)
  have hcomm : ∀ q ∈ (Q : Subgroup J), q * (u * z) * q⁻¹ * (u * z)⁻¹ ∈ Subgroup.center J := by
    intro q hq
    have h1 := (h.mem_normalizer_zpowers_iff hc.sq).mp (hc.mem_quasiNormalizer hq)
    have h2 := hz.comm_mem_center q hq
    rw [show q * (u * z) * q⁻¹ * (u * z)⁻¹ =
      (q * u * q⁻¹ * u⁻¹) * (u * (q * z * q⁻¹ * z⁻¹) * u⁻¹) by group]
    exact (Subgroup.center J).mul_mem h1
      ((inferInstance : (Subgroup.center J).Normal).conj_mem _ h2 u)
  obtain ⟨k, hkQ, hkne⟩ := h.exists_conj_mem_ne hcQ (hcc ▸ h.centralElt_mem_center) hcZ hcomm
  set x := k⁻¹ * (u * z) * k with hxdef
  have hxx : x * x = centralElt J := by
    have := h.conj_mul_self hcc k
    simpa [hxdef] using this
  have hx1 : x ≠ u * z := fun h1 => hkne (by
    rw [h1, mul_inv_cancel]
    exact (Subgroup.center J).one_mem)
  have hx2 : x ≠ centralElt J * (u * z) := fun h1 => hkne (by
    rw [h1, mul_inv_cancel_right]
    exact h.centralElt_mem_center)
  obtain ⟨o, -, hoB, hox⟩ := hc.exists_mem_conj_of_typeOne hI hkQ hxx hx1 hx2
  have hk1 : k⁻¹ ∈ B := h.mem_of_conj_mem_of_centralizer_le hz hcc hC (g := k⁻¹)
    (by simpa [hxdef] using h.sylow_le hkQ)
  have hk2 : o * k⁻¹ ∈ B := h.mem_of_conj_mem_of_centralizer_le hz hcc hC (g := o * k⁻¹) (by
    rw [show o * k⁻¹ * (u * z) * (o * k⁻¹)⁻¹ = o * x * o⁻¹ by rw [hxdef]; group]
    exact hox)
  exact hoB (by simpa using B.mul_mem hk2 (B.inv_mem hk1))

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
