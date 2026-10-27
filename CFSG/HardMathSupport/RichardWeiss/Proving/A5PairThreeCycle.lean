module

public import CFSG.HardMathSupport.RichardWeiss.Proving.A5PairFromHom
public import CFSG.HardMathSupport.RichardWeiss.Proving.CarmichaelLift

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.PushingUpLit.CGT6

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
theorem altFive_conj_u : ∀ σ : Perm (Fin 5), σ.support.card = 3 →
    ∃ π : Perm (Fin 5), Perm.sign π = 1 ∧ π * σ * π⁻¹ = altFiveUPerm := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
theorem altFive_conj_v : ∀ σ : Perm (Fin 5), σ.support.card = 3 →
    ∃ π : Perm (Fin 5), Perm.sign π = 1 ∧ π * σ * π⁻¹ = altFiveVPerm := by
  decide +kernel

theorem injective_of_ne_one_alt5 {K : Type} [Group K] (f : alternatingGroup (Fin 5) →* K)
    (x : alternatingGroup (Fin 5)) (hx : f x ≠ 1) : Function.Injective f := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker f) with h | h
  · exact h
  · exfalso
    have hx' : x ∈ MonoidHom.ker f := by
      rw [h]
      exact Subgroup.mem_top x
    exact hx (MonoidHom.mem_ker.mp hx')

theorem conj_apply_hom {S : Type} [Group S] (φ : alternatingGroup (Fin 5) →* S)
    (p x : alternatingGroup (Fin 5)) :
    (MulAut.conj (φ p)).toMonoidHom (φ x) = φ (p * x * p⁻¹) := by
  simp [map_mul, map_inv, MulAut.conj_apply]

theorem hasA5Pair_of_injective_hom_zpowers {S : Type} [Group S] {Y : Subgroup S}
    (φ : alternatingGroup (Fin 5) →* S) (hφ : Function.Injective φ)
    {c : alternatingGroup (Fin 5)} (hc : (c : Perm (Fin 5)).IsThreeCycle)
    (hY : Y = Subgroup.zpowers (φ c)) :
    ∃ g h : S, Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨π, hπ, hπu⟩ := altFive_conj_u (c : Perm (Fin 5)) (card_support_eq_three_iff.mpr hc)
  obtain ⟨π', hπ', hπv⟩ := altFive_conj_v (c : Perm (Fin 5)) (card_support_eq_three_iff.mpr hc)
  have hpu : (⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ : alternatingGroup (Fin 5)) * c *
      (⟨π, Perm.mem_alternatingGroup.mpr hπ⟩)⁻¹ = altFiveU :=
    Subtype.ext (by rw [altFiveU_val]; exact hπu)
  have hpv : (⟨π', Perm.mem_alternatingGroup.mpr hπ'⟩ : alternatingGroup (Fin 5)) * c *
      (⟨π', Perm.mem_alternatingGroup.mpr hπ'⟩)⁻¹ = altFiveV :=
    Subtype.ext (by rw [altFiveV_val]; exact hπv)
  have hYa : Y.map (MulAut.conj (φ ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩)).toMonoidHom =
      Subgroup.zpowers (φ altFiveU) := by
    rw [hY, MonoidHom.map_zpowers, conj_apply_hom, hpu]
  have hYb : Y.map (MulAut.conj (φ ⟨π', Perm.mem_alternatingGroup.mpr hπ'⟩)).toMonoidHom =
      Subgroup.zpowers (φ altFiveV) := by
    rw [hY, MonoidHom.map_zpowers, conj_apply_hom, hpv]
  exact ⟨_, _, exists_pair_A5_of_injective_hom φ hφ hYa hYb⟩

theorem hasA5Pair_zpowers_of_carmichael {S : Type} [Group S] (a : Fin 3 → S)
    (h3 : ∀ i, a i ^ 3 = 1) (h2 : ∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) (ha0 : a 0 ≠ 1) :
    ∃ g h : S, Nonempty (↥(pairGen (Subgroup.zpowers (a 0)) g h) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_altThreeCycle_eq 3 a h3 h2
  have hinj : Function.Injective ψ :=
    injective_of_ne_one_alt5 ψ (altThreeCycle 0) (by rw [hψ 0]; exact ha0)
  exact hasA5Pair_of_injective_hom_zpowers ψ hinj (c := altThreeCycle 0)
    (isThreeCycle_altThreeCyclePerm 0) (by rw [hψ 0])

end CFSG.HardMathSupport.RichardWeiss.Proving

end
