module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGL
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerQuasi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.RankThree.PartOne.KCUnitary

section Tiny

theorem le_center_of_normal_of_natCard_eq_two {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (hK : Nat.card K = 2) : K ≤ Subgroup.center G := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hx1 : x = 1
  · subst hx1
    simp
  · obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).1 hK
    have hxK : (⟨x, hx⟩ : ↥K) = y := hyuniq _ (fun h => hx1 (congrArg Subtype.val h))
    have hconj : g * x * g⁻¹ ∈ K := (‹K.Normal›).conj_mem x hx g
    have hconj1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h]
      group
    have h2 : (⟨g * x * g⁻¹, hconj⟩ : ↥K) = y :=
      hyuniq _ (fun h => hconj1 (congrArg Subtype.val h))
    have h3 : g * x * g⁻¹ = x := congrArg Subtype.val (h2.trans hxK.symm)
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h3]

end Tiny

variable {E : Type*} [Field E] [Finite E] [CharP E 2] {W : Type*} [AddCommGroup W] [Module E W]
  [FiniteDimensional E W]

theorem oddPCoreInClosure_generalLinearGroup_two_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : Nat.card E = 2) (hm : Module.finrank E W = 2) :
    OddPCoreInClosure p (LinearMap.GeneralLinearGroup E W) := by
  haveI : Finite (LinearMap.GeneralLinearGroup E W) := finite_generalLinearGroup'
  have h6 := natCard_generalLinearGroup_two_two (W := W) hE hm
  by_cases hp6 : p ∣ 6
  ·
    have hp3 : p = 3 := by
      have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hp6
      interval_cases p <;> first | rfl | (exfalso; revert hp hp2 hp6; decide)
    subst hp3
    refine OddPCoreInClosure.of_odd_core fun K hK hKcop => ?_
    have hKdvd : Nat.card K ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card K
    have hKd2 : Nat.card K ∣ 2 := by
      have : Nat.Coprime (Nat.card K) 3 := hKcop.symm
      exact this.dvd_of_dvd_mul_left (by simpa using hKdvd)
    rcases (Nat.dvd_prime Nat.prime_two).1 hKd2 with h1 | h2
    · rw [h1]; exact odd_one
    ·
      exfalso
      have hcen := le_center_of_normal_of_natCard_eq_two K h2
      have hbot : K = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hx2 : x ^ 2 = 1 := by
          have := pow_card_eq_one' (G := ↥K) (x := (⟨x, hx⟩ : ↥K))
          rw [h2] at this
          simpa using congrArg Subtype.val this
        refine eq_one_of_commute_special_of_sq_eq_one (by omega) x hx2 fun δ _ => ?_
        exact (Subgroup.mem_center_iff.1 (hcen hx)) δ
      rw [hbot, Subgroup.card_bot] at h2
      omega
  · exact OddPCoreInClosure.of_not_dvd hp (by rw [h6]; exact hp6)

theorem oddPCoreInClosure_generalLinearGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p (LinearMap.GeneralLinearGroup E W) := by
  haveI : Finite (LinearMap.GeneralLinearGroup E W) := finite_generalLinearGroup'
  by_cases hm : 2 ≤ Module.finrank E W
  · by_cases hexc : Module.finrank E W = 2 ∧ Nat.card E = 2
    · exact oddPCoreInClosure_generalLinearGroup_two_two hp hp2 hexc.2 hexc.1
    ·
      have h4 : 3 ≤ Module.finrank E W ∨ ∃ s : Finset E, s.card = 4 := by
        by_cases h3 : 3 ≤ Module.finrank E W
        · exact Or.inl h3
        · right
          have hE2 : Nat.card E ≠ 2 := fun h => hexc ⟨by omega, h⟩
          haveI : Fintype E := Fintype.ofFinite E
          obtain ⟨n, -, hn⟩ := FiniteField.card E 2
          have hcard : Fintype.card E = 2 ^ (n : ℕ) := hn
          have hn2 : 2 ≤ (n : ℕ) := by
            by_contra hlt
            have : (n : ℕ) = 1 := by have := n.pos; omega
            rw [this] at hcard
            exact hE2 (by rw [Nat.card_eq_fintype_card, hcard]; norm_num)
          have h4le : 4 ≤ Fintype.card E := by
            rw [hcard]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
          obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E))
            (by simpa using h4le)
          exact ⟨t, ht⟩
      set Q := (Units.map (LinearMap.det : Module.End E W →* E)).ker with hQ
      refine oddPCoreInClosure_of_quasisimple_normal hp Q (isQuasisimple_ker_det hm h4) ?_ ?_
      ·
        refine odd_natCard_of_forall_sq fun x hx2 => ?_
        have hxc : ∀ δ ∈ Q, δ * (x : LinearMap.GeneralLinearGroup E W) = x * δ :=
          Subgroup.mem_centralizer_iff.1 x.2
        have := eq_one_of_commute_special_of_sq_eq_one hm (x : LinearMap.GeneralLinearGroup E W)
          (by simpa using congrArg Subtype.val hx2) fun δ hδ =>
            hxc δ (MonoidHom.mem_ker.2 (Units.ext (by simpa using hδ)))
        exact Subtype.ext this
      ·
        intro hpG
        haveI : Fact p.Prime := ⟨hp⟩
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := LinearMap.GeneralLinearGroup E W) p
          hpG
        by_cases hdet : Units.map (LinearMap.det : Module.End E W →* E) g = 1
        · have hgQ : g ∈ Q := hdet
          have := Subgroup.orderOf_dvd_natCard Q hgQ
          rw [hg] at this
          exact this
        · have h1 : orderOf (Units.map (LinearMap.det : Module.End E W →* E) g) ∣ p :=
            hg ▸ orderOf_map_dvd _ g
          have h2 : orderOf (Units.map (LinearMap.det : Module.End E W →* E) g) = p :=
            ((Nat.dvd_prime hp).1 h1).resolve_left (fun h => hdet (orderOf_eq_one_iff.1 h))
          have h3 : p ∣ Nat.card E - 1 := by
            have := orderOf_dvd_natCard (Units.map (LinearMap.det : Module.End E W →* E) g)
            rw [h2, Nat.card_units] at this
            exact this
          exact h3.trans (natCard_sub_one_dvd_card_ker_det hm)
  · refine OddPCoreInClosure.of_odd_core fun K _ _ => odd_natCard_of_forall_sq fun x hx2 => ?_
    have := eq_one_of_sq_eq_one_of_finrank_le_one (by omega) (x : LinearMap.GeneralLinearGroup E W)
      (by simpa using congrArg Subtype.val hx2)
    exact Subtype.ext this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
