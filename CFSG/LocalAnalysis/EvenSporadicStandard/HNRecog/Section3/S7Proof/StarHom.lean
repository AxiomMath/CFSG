module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem starHom_isConj_conj {G : Type} [Group G] {u v : G} (h : IsConj u v) (c : G) :
    IsConj u (c⁻¹ * v * c) :=
  h.trans (isConj_iff.mpr ⟨c⁻¹, by simp⟩)

private theorem starHom_orderOf_conj {G : Type} [Group G] (k x : G) :
    orderOf (k * x * k⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj k) x)

theorem s7_pair_of_hom {G : Type} [Group G] {a : G} (ρ : Sym 8 →* G)
    (hρ : Function.Injective ρ) (hT : ∀ τ : Sym 8, τ.IsSwap → IsConj a (ρ τ))
    (hP : ∀ s : Sym 8, s.cycleType = {2, 2} → IsConj a (ρ s)) :
    ∃ a' x' d' t' : G, IsConj a a' ∧ IsConj a x' ∧ IsConj a d' ∧ IsConj a t' ∧
      IsConj a (a' * d') ∧ IsConj a (a' * t') ∧ IsConj a (x' * d') ∧ IsConj a (x' * t') ∧
      orderOf (a' * x') = 3 ∧ d' ≠ t' ∧ d' * t' = t' * d' := by
  have hsw : ∀ x y : Fin 8, x ≠ y → IsConj a (ρ (Equiv.swap x y)) :=
    fun x y hxy => hT _ (Equiv.Perm.swap_isSwap_iff.mpr hxy)
  have hct : ∀ x y z t : Fin 8, [x, y, z, t].Nodup →
      (Equiv.swap x y * Equiv.swap z t).cycleType = {2, 2} :=
    fun x y z t h => Equiv.Perm.cycleType_swap_mul_swap_of_nodup h
  refine ⟨ρ (Equiv.swap (0 : Fin 8) 1), ρ (Equiv.swap 1 2), ρ (Equiv.swap 3 4),
    ρ (Equiv.swap 5 6), hsw 0 1 (by decide), hsw 1 2 (by decide), hsw 3 4 (by decide),
    hsw 5 6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using hP _ (hct 0 1 3 4 (by decide))
  · simpa only [map_mul] using hP _ (hct 0 1 5 6 (by decide))
  · simpa only [map_mul] using hP _ (hct 1 2 3 4 (by decide))
  · simpa only [map_mul] using hP _ (hct 1 2 5 6 (by decide))
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [← map_mul, orderOf_injective ρ hρ]
    exact orderOf_eq_prime (by decide) (by decide)
  · intro hh
    exact (by decide : Equiv.swap (3 : Fin 8) 4 ≠ Equiv.swap 5 6) (hρ hh)
  · simp only [← map_mul]
    exact congrArg ρ (by decide)

theorem s7_pair_conj {G : Type} [Group G] {a a' x' d' t' : G} (h : IsConj a a')
    (hx : IsConj a x') (hd : IsConj a d') (ht : IsConj a t') (had : IsConj a (a' * d'))
    (hat : IsConj a (a' * t')) (hxd : IsConj a (x' * d')) (hxt : IsConj a (x' * t'))
    (ho : orderOf (a' * x') = 3) (hdt : d' ≠ t') (hcomm : d' * t' = t' * d') :
    ∃ x d t : G, x ∈ orb3A a a ∧ d ∈ orb2A a a ∩ orb2A a x ∧ t ∈ orb2A a a ∩ orb2A a x ∧
      d ≠ t ∧ d * t = t * d := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have ha : a = c⁻¹ * a' * c := by rw [← hc]; group
  have hdmem : c⁻¹ * d' * c ∈ orb2A a a ∩ orb2A a (c⁻¹ * x' * c) := by
    simp only [Set.mem_inter_iff, orb2A, Set.mem_setOf_eq]
    refine ⟨⟨starHom_isConj_conj hd c, ?_⟩, starHom_isConj_conj hd c, ?_⟩
    · rw [show a * (c⁻¹ * d' * c) = c⁻¹ * (a' * d') * c by rw [ha]; group]
      exact starHom_isConj_conj had c
    · rw [show (c⁻¹ * x' * c) * (c⁻¹ * d' * c) = c⁻¹ * (x' * d') * c by group]
      exact starHom_isConj_conj hxd c
  have hxmem : c⁻¹ * x' * c ∈ orb3A a a := by
    simp only [orb3A, Set.mem_setOf_eq]
    refine ⟨starHom_isConj_conj hx c, ?_, ?_⟩
    · rw [show a * (c⁻¹ * x' * c) = c⁻¹ * (a' * x') * c by rw [ha]; group]
      rw [show orderOf (c⁻¹ * (a' * x') * c) = orderOf (a' * x') by
            simpa using starHom_orderOf_conj c⁻¹ (a' * x')]
      exact ho
    · exact ⟨c⁻¹ * d' * c, hdmem⟩
  have htmem : c⁻¹ * t' * c ∈ orb2A a a ∩ orb2A a (c⁻¹ * x' * c) := by
    simp only [Set.mem_inter_iff, orb2A, Set.mem_setOf_eq]
    refine ⟨⟨starHom_isConj_conj ht c, ?_⟩, starHom_isConj_conj ht c, ?_⟩
    · rw [show a * (c⁻¹ * t' * c) = c⁻¹ * (a' * t') * c by rw [ha]; group]
      exact starHom_isConj_conj hat c
    · rw [show (c⁻¹ * x' * c) * (c⁻¹ * t' * c) = c⁻¹ * (x' * t') * c by group]
      exact starHom_isConj_conj hxt c
  have hdteq : c⁻¹ * d' * c ≠ c⁻¹ * t' * c := by
    intro hh
    apply hdt
    have hh' : c * (c⁻¹ * d' * c) * c⁻¹ = c * (c⁻¹ * t' * c) * c⁻¹ :=
      congrArg (fun u => c * u * c⁻¹) hh
    group at hh'
    exact hh'
  have hcomm' : (c⁻¹ * d' * c) * (c⁻¹ * t' * c) =
      (c⁻¹ * t' * c) * (c⁻¹ * d' * c) := by
    calc (c⁻¹ * d' * c) * (c⁻¹ * t' * c) = c⁻¹ * (d' * t') * c := by group
      _ = c⁻¹ * (t' * d') * c := by rw [hcomm]
      _ = (c⁻¹ * t' * c) * (c⁻¹ * d' * c) := by group
  exact ⟨c⁻¹ * x' * c, c⁻¹ * d' * c, c⁻¹ * t' * c, hxmem, hdmem, htmem, hdteq, hcomm'⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
