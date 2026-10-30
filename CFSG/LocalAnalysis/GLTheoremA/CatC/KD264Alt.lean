module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace CFSG.LocalAnalysis.GLTheoremA

theorem kd264KAlt_holds (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264KAlt p := by
  intro Y _ _ K B hKn hq _ hc hcore hlev hB hKB hcard hmax hC
  obtain ⟨i, hi, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn5 =>
    have hp3le : 3 ≤ p := by
      have := hp.two_le
      omega
    have hK6 : ¬ (n = 6 ∧ p = 3) := by
      rintro ⟨rfl, rfl⟩
      refine KD264Z.fullCoverLevel_ne_four (p := 3) (Q := ↥K) (Or.inl ⟨hq, Or.inr ⟨.alternating 6 (by norm_num),
        by simp [ambiguousChev], ⟨eK⟩⟩⟩) hlev
    rcases KD264Z.center_eq_bot_or_three hp hp2 hq hcore hn5 eK with hZ | ⟨hZ3, h67⟩
    ·
      let e : K ≃* alternatingGroup (Fin n) :=
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eK
      have hlev7 : ¬ (p = 3 ∧ (n = 7 ∨ n = 9 ∨ n = 10)) := by
        rintro ⟨h3, hn'⟩
        subst h3
        rcases hn' with rfl | rfl | rfl
        · refine KD264Z.fullCoverLevel_ne_four (p := 3) (Q := ↥K) (Or.inr (Or.inr ⟨hq, Or.inl
            (FullCover.simpleCoverList_of_center_eq_bot hZ ⟨.alternating 7 (by norm_num), ⟨rfl, Or.inl rfl⟩,
              ⟨eK⟩⟩)⟩)) hlev
        · refine KD264Z.fullCoverLevel_ne_four (p := 3) (Q := ↥K) (Or.inr (Or.inl ⟨hq, Or.inl
            (FullCover.simpleCoverList_of_center_eq_bot hZ ⟨.alternating 9 (by norm_num), Or.inl ⟨rfl, Or.inr rfl⟩,
              ⟨eK⟩⟩)⟩)) hlev
        · refine KD264Z.fullCoverLevel_ne_four (p := 3) (Q := ↥K) (Or.inr (Or.inr ⟨hq, Or.inl
            (FullCover.simpleCoverList_of_center_eq_bot hZ ⟨.alternating 10 (by norm_num), ⟨rfl, Or.inr rfl⟩,
              ⟨eK⟩⟩)⟩)) hlev
      have hp3 : p = 3 → n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 9 ∧ n ≠ 10 := by
        intro h3
        refine ⟨fun h => hK6 ⟨h, h3⟩, fun h => hlev7 ⟨h3, Or.inl h⟩, fun h => hlev7 ⟨h3, Or.inr (Or.inl h)⟩,
          fun h => hlev7 ⟨h3, Or.inr (Or.inr h)⟩⟩
      have hpn : p ≤ n := by
        by_contra hlt
        push Not at hlt
        haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
        have hcardK : Nat.card K = n.factorial / 2 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
            Fintype.card_fin]
        have hndvd : ¬ p ∣ Nat.card K := by
          rw [hcardK]
          intro hd
          have h2 : n.factorial / 2 ∣ n.factorial := Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega))
          have hpf : p ∣ n.factorial := hd.trans h2
          exact absurd ((Nat.Prime.dvd_factorial hp).1 hpf) (by omega)
        haveI := isQuasisimple_nontrivial hq
        have htop : (⊤ : Subgroup K) ≤ GLAPPrimeCore p K :=
          le_sSup ⟨inferInstance, by
            rw [Subgroup.card_top]
            exact (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd⟩
        rw [hcore] at htop
        obtain ⟨x, hx⟩ := exists_ne (1 : K)
        exact hx (Subgroup.mem_bot.1 (htop (Subgroup.mem_top x)))
      obtain ⟨E, hEB, hEel, hEcard, hEl⟩ :=
        KD264Core.alt_core hp hp2 hn5 hpn K B hKn e hZ hB hcard hmax hC hp3
      exact Or.inl ⟨E, hEB, hEel, hEcard, hEl⟩
    ·
      have h3 : p = 3 := by
        haveI : Fact p.Prime := ⟨hp⟩
        obtain ⟨a, ha⟩ := (KD264Z.isPGroup_center_of_pPrimeCore hp hcore).exists_card_eq
        rw [hZ3] at ha
        have hpdvd : p ∣ 3 := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · rw [h0, pow_zero] at ha
            omega
          · rw [ha]
            exact dvd_pow_self p h0.ne'
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpdvd
      subst h3
      have hn7 : n = 7 := by omega
      subst hn7
      set π : K →* alternatingGroup (Fin 7) :=
        eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
      have hπ : Function.Surjective π := eK.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : π.ker = Subgroup.center K := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hbound : ∀ (D : Type) [Group D] [Finite D], CFSG.Open.IsQuasisimple D →
          ∀ ρ : D →* alternatingGroup (Fin 7), Function.Surjective ρ → ρ.ker = Subgroup.center D →
            Odd (Nat.card (Subgroup.center D)) → Nat.card (Subgroup.center D) ∣ 3 := by
        intro D _ _ hD ρ hρ hρk hodd
        haveI : Group.IsPerfect D := Group.isPerfect_def.2 hD.1
        have hsmall := CFSG.SectionRank.alternating_small_odd_cover_bound (n := 7) (by norm_num)
          (by norm_num) ρ hρ hρk.le (by rw [hρk]; exact hodd)
        rw [hρk] at hsmall
        rcases hsmall.2 (Or.inr rfl) with h1 | h1 <;> simp [h1]
      have hK3 : K3Cover 3 ↥K := by
        refine ⟨hq, Or.inr (Or.inr ⟨.alternating 7 (by norm_num), ⟨rfl, rfl⟩, ?_, hZ3⟩)⟩
        have h57 : 5 ≤ 7 := by norm_num
        exact maximalOddCover_of_oddBound (TauCeti.CFSGIndex.alternating 7 h57) hq
          (π : K →* (TauCeti.CFSGIndex.alternating 7 h57).Group) hπ hker hZ3 hbound
      exact absurd hlev (KD264Z.fullCoverLevel_ne_four (p := 3) (Q := ↥K) (Or.inr (Or.inr hK3)))

end CFSG.LocalAnalysis.GLTheoremA

end
