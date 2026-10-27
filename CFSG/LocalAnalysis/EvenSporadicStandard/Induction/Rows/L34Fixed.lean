module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34LamLike
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.CoverFix
  CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification.PSL3Four Subgroup

theorem center_S_eq_bot : center ↥S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : Equiv.Perm (Fin 42)) ∈ Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R :=
    ⟨Subgroup.mem_centralizer_iff.2 fun s hs => by
      have := mem_center_iff.1 hx ⟨s, hs⟩
      exact congrArg Subtype.val this, S_le_R x.2⟩
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

theorem nonempty_equiv_S_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) : Nonempty (X ≃* ↥S) :=
  nonempty_equiv_of_stated X
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel h (by decide))

theorem center_eq_bot_of_equiv {X : Type} [Group X] (ψ : X ≃* ↥S) : center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : ψ x ∈ center ↥S := by
    rw [mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := ψ.surjective h
    rw [← map_mul, ← map_mul, mem_center_iff.1 hx g]
  rw [center_S_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (ψ.injective (by rw [this, map_one]))

theorem ker_eq_center {K : Type} [Group K] {π : K →* ↥S} (hπ : Function.Surjective π)
    (hle : π.ker ≤ center K) : π.ker = center K := by
  refine le_antisymm hle fun x hx => ?_
  rw [MonoidHom.mem_ker]
  have : π x ∈ center ↥S := by
    rw [mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := hπ h
    rw [← map_mul, ← map_mul, mem_center_iff.1 hx g]
  rw [center_S_eq_bot, Subgroup.mem_bot] at this
  exact this

theorem exists_cover_map {K G : Type} [Group K] [Group G] (e : (K ⧸ center K) ≃* G)
    (ψ : G ≃* ↥S) : ∃ π : K →* ↥S, Function.Surjective π ∧ π.ker = center K := by
  refine ⟨ψ.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K))),
    ψ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)), ?_⟩
  ext x
  simp

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem no_involution_of_odd {π : K →* ↥S} (hodd : Odd (Nat.card π.ker)) {α : MulAut K} :
    ∀ u ∈ fixed α, u ∈ π.ker → u * u = 1 → u = 1 := by
  intro u _ huk hu2
  by_contra hu1
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
  have h2 : 2 ∣ Nat.card π.ker := hord ▸ Subgroup.orderOf_dvd_natCard π.ker huk
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem involutionFixesNotLam_eight_of_odd (hperf : Group.IsPerfect K) (π : K →* ↥S)
    (hπ : Function.Surjective π) (hker : π.ker = center K) (hodd : Odd (Nat.card π.ker)) :
    InvolutionFixesNotLam K 8 := by
  intro α h1 h2
  rcases cover_profile hperf π hπ hker h1 h2 with hns | ⟨-, hnab, -, hout⟩ | hnab
  · have h := not_lamLike_of_nonsolvable (α := α) hns 8
    exact ⟨h.2.1, fun _ => h.1⟩
  · have h := not_lamLike_of_nonabelian (hnab (no_involution_of_odd hodd)) 8
    exact ⟨h.2.1, fun ⟨k, hk⟩ => absurd hk (hout k)⟩
  · have h := not_lamLike_of_nonabelian hnab 8
    exact ⟨h.2.1, fun _ => h.1⟩

theorem involutionFixesNotLam2_eight (hperf : Group.IsPerfect K) (π : K →* ↥S)
    (hπ : Function.Surjective π) (hker : π.ker = center K) : InvolutionFixesNotLam2 K 8 := by
  intro α h1 h2
  rcases cover_profile hperf π hπ hker h1 h2 with hns | ⟨h8, -, -, hout⟩ | hnab
  · have h := not_lamLike_of_nonsolvable (α := α) hns 8
    exact ⟨h.2.2.2, fun _ => h.2.2.1⟩
  · exact ⟨not_lamLike2_eight_of_orderEight h8, fun ⟨k, hk⟩ => absurd hk (hout k)⟩
  · have h := not_lamLike_of_nonabelian hnab 8
    exact ⟨h.2.2.2, fun _ => h.2.2.1⟩

theorem involutionFixesNotLam_four (hperf : Group.IsPerfect K) (π : K →* ↥S)
    (hπ : Function.Surjective π) (hker : π.ker = center K) : InvolutionFixesNotLam K 4 := by
  intro α h1 h2
  rcases cover_profile hperf π hπ hker h1 h2 with hns | ⟨-, hnab, helem, hout⟩ | hnab
  · have h := not_lamLike_of_nonsolvable (α := α) hns 4
    exact ⟨h.2.1, fun _ => h.1⟩
  · refine ⟨?_, fun ⟨k, hk⟩ => absurd hk (hout k)⟩
    by_cases hinv : ∃ u ∈ fixed α, u ∈ π.ker ∧ u * u = 1 ∧ u ≠ 1
    · exact not_lamLike_four_of_elemFour (helem hinv)
    · have hno : ∀ u ∈ fixed α, u ∈ π.ker → u * u = 1 → u = 1 := by
        intro u hu huk hu2
        by_contra hu1
        exact hinv ⟨u, hu, huk, hu2, hu1⟩
      exact (not_lamLike_of_nonabelian (hnab hno) 4).2.1
  · have h := not_lamLike_of_nonabelian hnab 4
    exact ⟨h.2.1, fun _ => h.1⟩

end CFSG.EvenSporadicStandard.L34Q8
