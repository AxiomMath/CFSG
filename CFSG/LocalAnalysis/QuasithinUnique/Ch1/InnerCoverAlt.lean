module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial Equiv Equiv.Perm

@[expose] def permY1 : Perm (Fin 8) := swap 0 2 * swap 1 3

@[expose] def permSigma : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def permY2 : Perm (Fin 8) := permY1 * (permSigma * permY1 * permSigma⁻¹)

theorem cycleType_eq_replicate_of_sq_eq_one {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (hσ : σ ^ 2 = 1) : σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := cycleType_of_pow_prime_eq_one (p := 2) hσ
  have hsum := σ.sum_cycleType
  rw [h, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [h]
  congr 1
  omega

theorem involution_classes_perm : ∀ y : Perm (Fin 8), y * y = 1 → y ≠ 1 → Perm.sign y = 1 →
    ∃ g : Perm (Fin 8), (g * y * g⁻¹ = permY1 ∨ g * y * g⁻¹ = permY2) ∧ Perm.sign g = 1 := by
  intro y hy2 hy1 hsign
  have hy : y ^ 2 = 1 := by rw [pow_two]; exact hy2
  have hct := cycleType_eq_replicate_of_sq_eq_one hy
  have hs8 : y.support.card ≤ 8 := by
    have := Finset.card_le_univ y.support
    simpa using this
  have hs0 : y.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]
    exact hy1
  have h2 : 2 ∣ y.support.card := Equiv.Perm.two_dvd_card_support hy
  have hsgn : sign y = (-1) ^ (3 * (y.support.card / 2)) := by
    rw [sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
    congr 1
    ring
  have hn : y.support.card = 4 ∨ y.support.card = 8 := by
    obtain ⟨m, hm⟩ := h2
    have hm1 : 1 ≤ m := by omega
    have hm4 : m ≤ 4 := by omega
    have hmm : y.support.card / 2 = m := by omega
    rw [hmm] at hsgn
    interval_cases m
    · exfalso
      rw [hsgn] at hsign
      revert hsign
      decide
    · left
      omega
    · exfalso
      rw [hsgn] at hsign
      revert hsign
      decide
    · right
      omega
  have hY1 : permY1 ^ 2 = 1 := by decide
  have hY2 : permY2 ^ 2 = 1 := by decide
  have hc1 : permY1.support.card = 4 := by decide
  have hc2 : permY2.support.card = 8 := by decide
  have hconj : ∃ c : Perm (Fin 8), c * y * c⁻¹ = permY1 ∨ c * y * c⁻¹ = permY2 := by
    rcases hn with hn | hn
    · have hc : IsConj y permY1 := by
        rw [isConj_iff_cycleType_eq, hct, cycleType_eq_replicate_of_sq_eq_one hY1, hn, hc1]
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      exact ⟨c, Or.inl hc⟩
    · have hc : IsConj y permY2 := by
        rw [isConj_iff_cycleType_eq, hct, cycleType_eq_replicate_of_sq_eq_one hY2, hn, hc2]
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      exact ⟨c, Or.inr hc⟩
  obtain ⟨c, hc⟩ := hconj
  by_cases hcs : sign c = 1
  · exact ⟨c, hc, hcs⟩
  · obtain ⟨a, ha⟩ : ∃ a, y a ≠ a := by
      by_contra h
      push Not at h
      exact hy1 (Equiv.ext h)
    have hya : y (y a) = a := by
      have := congrArg (fun f : Perm (Fin 8) => f a) hy2
      simpa using this
    have hcomm : y * swap a (y a) = swap a (y a) * y := by
      rw [mul_swap_eq_swap_mul, hya, swap_comm]
    have hsw : swap a (y a) * y * (swap a (y a))⁻¹ = y := by
      rw [← hcomm, mul_inv_cancel_right]
    refine ⟨c * swap a (y a), ?_, ?_⟩
    · have h1 : (c * swap a (y a)) * y * (c * swap a (y a))⁻¹ = c * y * c⁻¹ := by
        rw [mul_inv_rev]
        calc c * swap a (y a) * y * ((swap a (y a))⁻¹ * c⁻¹)
            = c * (swap a (y a) * y * (swap a (y a))⁻¹) * c⁻¹ := by group
          _ = c * y * c⁻¹ := by rw [hsw]
      rw [h1]
      exact hc
    · have hs : sign c = -1 := by
        rcases Int.units_eq_one_or (sign c) with h | h
        · exact absurd h hcs
        · exact h
      rw [map_mul, hs, sign_swap (Ne.symm ha)]
      decide

abbrev Alt8 : Type := alternatingGroup (Fin 8)

@[expose] def alt8Sigma : Alt8 :=
  ⟨permSigma, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt8C0 : Alt8 := altThreeCycle (n := 6) 0

@[expose] def alt8C1 : Alt8 := altThreeCycle (n := 6) 1

@[expose] def alt8Y1 : Alt8 := alt8C0 * alt8C1

@[expose] def alt8Y2 : Alt8 := alt8Y1 * (alt8Sigma * alt8Y1 * alt8Sigma⁻¹)

@[expose] def alt8P1 : Alt8 := alt8C0 * alt8C1⁻¹ * alt8C0

theorem coe_alt8Y1 : (alt8Y1 : Perm (Fin 8)) = permY1 := by
  decide

theorem coe_alt8Y2 : (alt8Y2 : Perm (Fin 8)) = permY2 := by
  decide

theorem alt8P1_comm_Y1 : alt8P1 * alt8Y1 = alt8Y1 * alt8P1 := by decide

theorem alt8P1_comm_Y1' : alt8P1 * (alt8Sigma * alt8Y1 * alt8Sigma⁻¹) =
    (alt8Sigma * alt8Y1 * alt8Sigma⁻¹) * alt8P1 := by decide

theorem alt8_comm00 : alt8C0 * (alt8Sigma * alt8C0 * alt8Sigma⁻¹) =
    (alt8Sigma * alt8C0 * alt8Sigma⁻¹) * alt8C0 := by decide

theorem alt8_comm01 : alt8C0 * (alt8Sigma * alt8C1 * alt8Sigma⁻¹) =
    (alt8Sigma * alt8C1 * alt8Sigma⁻¹) * alt8C0 := by decide

theorem alt8_comm10 : alt8C1 * (alt8Sigma * alt8C0 * alt8Sigma⁻¹) =
    (alt8Sigma * alt8C0 * alt8Sigma⁻¹) * alt8C1 := by decide

theorem alt8_comm11 : alt8C1 * (alt8Sigma * alt8C1 * alt8Sigma⁻¹) =
    (alt8Sigma * alt8C1 * alt8Sigma⁻¹) * alt8C1 := by decide

theorem involution_classes (y : Alt8) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : Alt8, g * y * g⁻¹ = alt8Y1 ∨ g * y * g⁻¹ = alt8Y2 := by
  obtain ⟨g, hg, hs⟩ := involution_classes_perm (y : Perm (Fin 8))
    (by simpa using congrArg Subtype.val hy2) (fun h => hy1 (Subtype.ext h))
    (Equiv.Perm.mem_alternatingGroup.mp y.2)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, ?_⟩
  rcases hg with hg | hg
  · exact Or.inl (Subtype.ext (by rw [coe_alt8Y1]; exact hg))
  · exact Or.inr (Subtype.ext (by rw [coe_alt8Y2]; exact hg))

section Helpers

variable {L : Type*} [Group L]

theorem commute_of_three_lifts {Q : Type*} [Group Q] (η : L →* Q)
    (hK : η.ker ≤ Subgroup.center L) (hK2 : IsPGroup 2 η.ker) {a b : L} (hb3 : b ^ 3 = 1)
    (hab : η a * η b = η b * η a) : a * b = b * a := by
  have h1 : (a * b * a⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3, mul_one, mul_inv_cancel]
  have h2 : η (a * b * a⁻¹) = η b := by
    rw [map_mul, map_mul, map_inv, hab, mul_inv_cancel_right]
  have h3 := eq_of_pow_three_eq_one_of_map_eq hK hK2 h1 hb3 h2
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem not_commute_mul_central_of_anticomm {u p z c : L} (hz1 : z ≠ 1)
    (hc : ∀ g, g * c = c * g) (h : u * p = z * (p * u)) : p * (u * c) ≠ u * c * p := by
  intro hcomm
  apply hz1
  have h1 : u * c * p = z * (p * u * c) := by
    calc u * c * p = u * (c * p) := by rw [mul_assoc]
      _ = u * (p * c) := by rw [← hc p]
      _ = (u * p) * c := by rw [mul_assoc]
      _ = z * (p * u) * c := by rw [h]
      _ = z * (p * u * c) := by rw [mul_assoc]
  have h2 : p * u * c = z * (p * u * c) := by
    calc p * u * c = p * (u * c) := by rw [mul_assoc]
      _ = u * c * p := hcomm
      _ = z * (p * u * c) := h1
  exact mul_eq_right.mp h2.symm

end Helpers

section Lifts

variable {L : Type} [Group L] [Finite L] [Group.IsPerfect L]

theorem alt_eight_key (η : L →* Alt8) (hsurj : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center L) (hK2 : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥) (l : L)
    (hl : η l = alt8Y1 ∨ η l = alt8Y2) : ∃ d : L, η d * η l = η l * η d ∧ d * l ≠ l * d := by
  obtain ⟨x, z, hxη, hx3, hzc, hz1, hz2, hzij⟩ :=
    alt_cover_structure (m := 6) (by norm_num) η hsurj hK hK2 hne
  have hzc' : ∀ g, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzc g
  have hts : (x 0 * x 1) ^ 2 = z := hzij 0 1 (by decide)
  have hst : (x 1 * x 0) ^ 2 = z := hzij 1 0 (by decide)
  have hηt : η (x 0) = alt8C0 := hxη 0
  have hηs : η (x 1) = alt8C1 := hxη 1
  obtain ⟨σ, hσ⟩ := hsurj alt8Sigma
  have ht'3 : (σ * x 0 * σ⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hs'3 : (σ * x 1 * σ⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hηt' : η (σ * x 0 * σ⁻¹) = alt8Sigma * alt8C0 * alt8Sigma⁻¹ := by
    rw [map_mul, map_mul, map_inv, hσ, hηt]
  have hηs' : η (σ * x 1 * σ⁻¹) = alt8Sigma * alt8C1 * alt8Sigma⁻¹ := by
    rw [map_mul, map_mul, map_inv, hσ, hηs]
  have c00 : x 0 * (σ * x 0 * σ⁻¹) = (σ * x 0 * σ⁻¹) * x 0 :=
    commute_of_three_lifts η hK hK2 ht'3 (by rw [hηt, hηt']; exact alt8_comm00)
  have c01 : x 0 * (σ * x 1 * σ⁻¹) = (σ * x 1 * σ⁻¹) * x 0 :=
    commute_of_three_lifts η hK hK2 hs'3 (by rw [hηt, hηs']; exact alt8_comm01)
  have c10 : x 1 * (σ * x 0 * σ⁻¹) = (σ * x 0 * σ⁻¹) * x 1 :=
    commute_of_three_lifts η hK hK2 ht'3 (by rw [hηs, hηt']; exact alt8_comm10)
  have c11 : x 1 * (σ * x 1 * σ⁻¹) = (σ * x 1 * σ⁻¹) * x 1 :=
    commute_of_three_lifts η hK hK2 hs'3 (by rw [hηs, hηs']; exact alt8_comm11)
  obtain ⟨d, hd⟩ : ∃ d : L, d = x 0 * (x 1)⁻¹ * x 0 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : L, u = x 0 * x 1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : L, v = (σ * x 0 * σ⁻¹) * (σ * x 1 * σ⁻¹) := ⟨_, rfl⟩
  have hηd : η d = alt8P1 := by
    rw [hd, map_mul, map_mul, map_inv, hηt, hηs, alt8P1]
  have hηu : η u = alt8Y1 := by rw [hu, map_mul, hηt, hηs, alt8Y1]
  have hηv : η v = alt8Sigma * alt8Y1 * alt8Sigma⁻¹ := by
    rw [hv, map_mul, hηt', hηs', alt8Y1]
    group
  have hanti : u * d = z * (d * u) := by
    rw [hu, hd]
    exact block_comm hzc' hz2 (hx3 0) (hx3 1) hts hst
  have hdv : d * v = v * d := by
    have h0 : Commute (x 0) v := by
      rw [hv]
      exact (show Commute (x 0) (σ * x 0 * σ⁻¹) from c00).mul_right
        (show Commute (x 0) (σ * x 1 * σ⁻¹) from c01)
    have h1 : Commute (x 1) v := by
      rw [hv]
      exact (show Commute (x 1) (σ * x 0 * σ⁻¹) from c10).mul_right
        (show Commute (x 1) (σ * x 1 * σ⁻¹) from c11)
    rw [hd]
    exact (((h0.mul_left h1.inv_left).mul_left h0)).eq
  rcases hl with hl | hl
  ·
    have hc : u⁻¹ * l ∈ Subgroup.center L := hK (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hηu, hl, inv_mul_cancel])
    have hlc : l = u * (u⁻¹ * l) := by rw [mul_inv_cancel_left]
    refine ⟨d, ?_, ?_⟩
    · rw [hηd, hl]
      exact alt8P1_comm_Y1
    · rw [hlc]
      exact not_commute_mul_central_of_anticomm hz1
        (fun g => Subgroup.mem_center_iff.mp hc g) hanti
  ·
    have hηuv : η (u * v) = alt8Y2 := by rw [map_mul, hηu, hηv, alt8Y2]
    have hc : (u * v)⁻¹ * l ∈ Subgroup.center L := hK (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hηuv, hl, inv_mul_cancel])
    have hlc : l = (u * v) * ((u * v)⁻¹ * l) := by rw [mul_inv_cancel_left]
    refine ⟨d, ?_, ?_⟩
    · rw [hηd, hl, alt8Y2]
      exact ((show Commute alt8P1 alt8Y1 from alt8P1_comm_Y1).mul_right
        (show Commute alt8P1 (alt8Sigma * alt8Y1 * alt8Sigma⁻¹) from alt8P1_comm_Y1')).eq
    · rw [hlc]
      refine not_commute_mul_central_of_anticomm hz1
        (fun g => Subgroup.mem_center_iff.mp hc g) ?_
      calc u * v * d = u * (v * d) := by rw [mul_assoc]
        _ = u * (d * v) := by rw [hdv]
        _ = (u * d) * v := by rw [mul_assoc]
        _ = z * (d * u) * v := by rw [hanti]
        _ = z * (d * (u * v)) := by rw [mul_assoc, mul_assoc]

end Lifts

theorem sylowCentralizerCentral_of_alt_eight {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 8))) : SylowCentralizerCentral X := by
  obtain ⟨e₈⟩ := h
  intro L _ _ hperf hZ hne ⟨e⟩ P x _ hx2 hx
  have := hperf
  by_contra hxn
  let η : L →* Alt8 := (e.trans e₈).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : η.ker = Subgroup.center L := RankOneRecog.ker_comp_centerQuotient (e.trans e₈)
  have hsurj : Function.Surjective η :=
    (e.trans e₈).surjective.comp (QuotientGroup.mk'_surjective _)
  have hK : η.ker ≤ Subgroup.center L := hker.le
  have hK2 : IsPGroup 2 η.ker := by rw [hker]; exact hZ
  have hne' : η.ker ≠ ⊥ := by rw [hker]; exact hne
  have hηx2 : η x * η x = 1 := by
    have : x * x ∈ η.ker := by rw [hker]; exact hx2
    rw [← map_mul]
    exact MonoidHom.mem_ker.mp this
  have hηx1 : η x ≠ 1 := fun h1 => hxn (by rw [← hker]; exact MonoidHom.mem_ker.mpr h1)
  obtain ⟨g, hg⟩ := involution_classes (η x) hηx2 hηx1
  obtain ⟨g', hg'⟩ := hsurj g
  have hηl' : η (g' * x * g'⁻¹) = g * η x * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg']
  have hηl : η (g' * x * g'⁻¹) = alt8Y1 ∨ η (g' * x * g'⁻¹) = alt8Y2 := by
    rw [hηl']
    exact hg
  obtain ⟨d, hd1, hd2⟩ := alt_eight_key η hsurj hK hK2 hne' (g' * x * g'⁻¹) hηl
  rw [hηl'] at hd1
  obtain ⟨d', hd'⟩ : ∃ d' : L, d' = g'⁻¹ * d * g' := ⟨_, rfl⟩
  have hcommη : η d' * η x = η x * η d' := by
    have e1 : η d' = g⁻¹ * η d * g := by rw [hd', map_mul, map_mul, map_inv, hg']
    rw [e1]
    calc g⁻¹ * η d * g * η x = g⁻¹ * (η d * (g * η x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * η x * g⁻¹) * η d) * g := by rw [hd1]
      _ = η x * (g⁻¹ * η d * g) := by group
  have hcomm_mem : d' * x * d'⁻¹ * x⁻¹ ∈ Subgroup.center L := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcommη]
    group
  have hdx : d' * x = x * d' := commute_of_commutator_mem_center hZ P hx hcomm_mem
  apply hd2
  calc d * (g' * x * g'⁻¹) = g' * (d' * x) * g'⁻¹ := by rw [hd']; group
    _ = g' * (x * d') * g'⁻¹ := by rw [hdx]
    _ = (g' * x * g'⁻¹) * d := by rw [hd']; group

end CFSG.QuasithinUnique.Ch1
