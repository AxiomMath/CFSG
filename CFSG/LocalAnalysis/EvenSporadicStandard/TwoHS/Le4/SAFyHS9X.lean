module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHInspect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHDec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHS9

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SignInsp

open Equiv Equiv.Perm Subgroup SignS9
open scoped Finset

theorem card_support_of_even_involution {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β = 5) {u : Perm β} (h1 : u ≠ 1) (h2 : u * u = 1) (h3 : sign u = 1) :
    #u.support = 4 := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := u) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : u.cycleType.sum ≤ Fintype.card β := sum_cycleType_le u
  rw [hn, Multiset.sum_replicate, hβ] at hsum
  have h01 : n = 0 ∨ n = 1 := by simp at hsum; omega
  rw [← sum_cycleType, hn]
  rcases h01 with rfl | rfl
  · exfalso
    rw [sign_of_cycleType, hn] at h3
    revert h3
    decide
  · simp

variable {α : Type*} [Fintype α] [DecidableEq α] {τ : Perm α} {D S : Subgroup (Perm α)}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}

theorem s9_inspect (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) {d s : Perm α}
    (hd : d ∈ D) (hd1 : d ≠ 1) (hdτ : d ≠ τ) (hs : s ∈ S) (hs1 : s ≠ 1) (hss : s * s = 1)
    (hsign : sign s = 1) : ¬ ∃ g : Perm α, d * s = g * τ * g⁻¹ := by
  have hP := card_fixedPoints_tau h hα
  have hcomm : ∀ (u : Perm (Function.fixedPoints τ)) (g : centralizer ({τ} : Set (Perm α))),
      fixRestrict τ g = 1 → ofSubtype u * (g : Perm α) = (g : Perm α) * ofSubtype u := by
    intro u g hg
    have hfix := (mem_ker_fixRestrict_iff τ g).1 hg
    refine Disjoint.commute fun x => ?_
    by_cases hx : τ x = x
    · exact Or.inr (hfix x hx)
    · exact Or.inl (ofSubtype_apply_of_not_mem u hx)
  obtain ⟨d', hd', hd'1, hds⟩ := retraction_mul_decomp h hP (fixRestrict τ) ofSubtype
    (ofSubtype_mem_centralizer τ) (fixRestrict_ofSubtype τ) hcomm hd hdτ hd1 hs
  have hu1 := retraction_ne_one h hP (fixRestrict τ) ofSubtype (ofSubtype_mem_centralizer τ)
    (fixRestrict_ofSubtype τ) hs hs1
  have hsC := right_le_centralizer h hs
  have huu : fixRestrict τ ⟨s, hsC⟩ * fixRestrict τ ⟨s, hsC⟩ = 1 := by
    have : (⟨s, hsC⟩ : centralizer ({τ} : Set (Perm α))) * ⟨s, hsC⟩ = 1 := Subtype.ext hss
    rw [← map_mul, this, map_one]
  have hu : sign (fixRestrict τ ⟨s, hsC⟩) = 1 := by
    rw [← sign_eq_sign_fixRestrict h hα hs]
    exact hsign
  have hcard4 := card_support_of_even_involution hP hu1 huu hu
  rintro ⟨g, hg⟩
  have hdisj : Disjoint d' (ofSubtype (fixRestrict τ ⟨s, hsC⟩)) := fun x => by
    by_cases hx : τ x = x
    · exact Or.inl (fix_of_mem_left h hα hd' hx)
    · exact Or.inr (ofSubtype_apply_of_not_mem _ hx)
  have h1 : #(d * s).support =
      #d'.support + #(ofSubtype (fixRestrict τ ⟨s, hsC⟩)).support := by
    rw [hds]
    exact hdisj.card_support_mul
  have h2 : #(ofSubtype (fixRestrict τ ⟨s, hsC⟩)).support = 4 := by
    rw [support_ofSubtype, Finset.card_map, hcard4]
  have h3 : 2 ≤ #d'.support := two_le_card_support_of_ne_one hd'1
  have h4 : #(d * s).support = 4 := by
    rw [hg, card_support_conj, card_support_of_cycleType_eq_two_two (cycleType_tau h hα)]
  omega

end SignInsp

theorem signDataS9X : SignDataS9X := by
  intro X _ _ φ τ D S eD eS h
  have h' := SignS9.localPair_map h φ
  have hA := SignWr.conclusion_of_map D S eS φ Equiv.Perm.sign
    ⟨fun d hd h4 => SignS9.sign_eq_neg_one_of_mem_left h' (Fintype.card_fin 9) hd h4,
     fun s hs => SignS9.sign_eq_neg_one_of_mem_right h' (Fintype.card_fin 9) s hs⟩
  refine ⟨Equiv.Perm.sign.comp φ.toMonoidHom, ?_, ?_, ?_⟩
  · intro d hd h4
    exact hA.1 d hd h4
  · intro s hs
    exact hA.2 s hs
  · refine SignInsp.inspect_of_map D S φ Equiv.Perm.sign rfl ?_
    intro d hd hd1 hdτ _ _ s hs hs1 hss hχs
    exact SignInsp.s9_inspect h' (Fintype.card_fin 9) hd hd1 hdτ hs hs1 hss hχs

end CFSG.EvenSporadicStandard.TwoHS
