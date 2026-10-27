module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.FibreProduct

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


namespace CFSG.LocalAnalysis.GLTheoremA

theorem sporadicMultiplierOrder_dvd_twelve (s : TauCeti.SporadicName) :
    sporadicMultiplierOrder s ∣ 12 := by
  cases s <;> decide

theorem sporadic_prime_cases (s : TauCeti.SporadicName) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ sporadicMultiplierOrder s) :
    p = 3 ∧ (k2HatIndex 3 (TauCeti.CFSGIndex.sporadic s) ∨
      k3HatIndex 3 (TauCeti.CFSGIndex.sporadic s)) := by
  have h12 : p ∣ 12 := hd.trans (sporadicMultiplierOrder_dvd_twelve s)
  have hp3 : p = 3 := by
    have h2 : p ∣ 2 ^ 2 * 3 := by norm_num; exact h12
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h') hp2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h') hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  subst hp3
  refine ⟨rfl, ?_⟩
  cases s <;> simp [sporadicMultiplierOrder, k2HatIndex, k3HatIndex] at hd ⊢

theorem odd_dvd_three_of_sporadic (s : TauCeti.SporadicName) {d : ℕ}
    (hd : d ∣ sporadicMultiplierOrder s) (hodd : Odd d) : d ∣ 3 := by
  have h12 : d ∣ 4 * 3 := by
    have := hd.trans (sporadicMultiplierOrder_dvd_twelve s)
    norm_num
    exact this
  have hcop : Nat.Coprime d 4 := by
    have h2 : Nat.Coprime d 2 := Odd.coprime_two_right hodd
    have := Nat.Coprime.pow_right 2 h2
    norm_num at this
    exact this
  exact hcop.dvd_of_dvd_mul_left h12


section SporadicCertificates


theorem hat_level_ne_four (s : TauCeti.SporadicName) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hZ3 : Nat.card (Subgroup.center K) = 3)
    (hhat : k2HatIndex 3 (TauCeti.CFSGIndex.sporadic s) ∨
      k3HatIndex 3 (TauCeti.CFSGIndex.sporadic s)) :
    fullCoverLevel 3 K ≠ 4 := by
  set π : K →* (TauCeti.CFSGIndex.sporadic s).Group :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hbound : ∀ (D : Type) [Group D] [Finite D], CFSG.Open.IsQuasisimple D →
      ∀ ρ : D →* (TauCeti.CFSGIndex.sporadic s).Group, Function.Surjective ρ →
        ρ.ker = Subgroup.center D → Odd (Nat.card (Subgroup.center D)) →
          Nat.card (Subgroup.center D) ∣ 3 := by
    intro D _ _ hD ρ hρ hρk hodd
    have hd := (sporadicMultiplierTable_holds : SporadicMultiplierTable) s D hD ρ hρ hρk
    exact odd_dvd_three_of_sporadic s hd hodd
  have hMOC : MaximalOddCover K (TauCeti.CFSGIndex.sporadic s) :=
    maximalOddCover_of_oddBound (TauCeti.CFSGIndex.sporadic s) hq π hπ hker hZ3 hbound
  intro hlev
  rcases hhat with hk2 | hk3
  · exact KD264Z.fullCoverLevel_ne_four (Or.inr (Or.inl ⟨hq, Or.inr (Or.inr (Or.inr
      ⟨_, hk2, hMOC, hZ3⟩))⟩)) hlev
  · exact KD264Z.fullCoverLevel_ne_four (Or.inr (Or.inr ⟨hq, Or.inr (Or.inr
      ⟨_, hk3, hMOC, hZ3⟩)⟩)) hlev

theorem kd264KSpor_of_S (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h : KD264SporS p) :
    KD264KSpor p := by
  intro Y _ _ K B hKn hq _ hc hcore hlev hB _hKB hcard hmax hC
  obtain ⟨i, hi, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic q hq' =>
    exact (false_of_quasisimple_comm_quotient (G := Multiplicative (ZMod q)) hq eK).elim
  | alternating n h' => exact hi.elim
  | lie d => exact hi.elim
  | sporadic s =>
    haveI : Fact p.Prime := ⟨hp⟩
    set π : K →* (TauCeti.CFSGIndex.sporadic s).Group :=
      eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
    have hπ : Function.Surjective π := eK.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center K := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hdvd := (sporadicMultiplierTable_holds : SporadicMultiplierTable) s K hq π hπ hker
    by_cases hZ : Subgroup.center K = ⊥
    ·
      let e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eK
      exact Or.inl (h s Y K B hKn ⟨e⟩ hcore hlev hB hcard hmax hC)
    ·
      exfalso
      obtain ⟨a, ha⟩ := (KD264Z.isPGroup_center_of_pPrimeCore hp hcore).exists_card_eq
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hZ
        exact Subgroup.eq_bot_of_card_eq _ (by rw [ha, pow_zero])
      have hpZ : p ∣ Nat.card (Subgroup.center K) := by
        rw [ha]
        exact dvd_pow_self p ha0
      obtain ⟨h3, hhat⟩ := sporadic_prime_cases s hp hp2 (hpZ.trans hdvd)
      subst h3
      have hZ3 : Nat.card (Subgroup.center K) = 3 := by
        have h9 : ¬ 9 ∣ Nat.card (Subgroup.center K) := by
          intro h9
          have h12 := h9.trans (hdvd.trans (sporadicMultiplierOrder_dvd_twelve s))
          norm_num at h12
        rw [ha] at h9 ⊢
        rcases a with _ | _ | a
        · exact absurd rfl ha0
        · simp
        · exfalso
          apply h9
          exact ⟨3 ^ a, by ring⟩
      exact hat_level_ne_four s hq eK hZ3 hhat hlev


end SporadicCertificates

end CFSG.LocalAnalysis.GLTheoremA
