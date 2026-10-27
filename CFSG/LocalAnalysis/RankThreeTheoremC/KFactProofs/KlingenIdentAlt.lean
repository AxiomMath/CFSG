module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdent
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentCore
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LargeExtraspecial.OutSixBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

namespace KlingenIdentAltAux

theorem commute_of_isPGroup_perm {α : Type*} [Finite α] {p : ℕ} [hpF : Fact p.Prime]
    (hα : Nat.card α < p ^ 2) {E : Subgroup (Equiv.Perm α)} (hE : IsPGroup p E)
    {x y : Equiv.Perm α} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  classical
  have hp : p.Prime := hpF.out
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  ext a
  set O : Set α := MulAction.orbit E a with hOdef
  have hOle : Nat.card O ≤ Nat.card α := Finite.card_subtype_le _
  have hOdvd : Nat.card O ∣ p ^ n := by
    rw [← hn, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk, hOk⟩ := (Nat.dvd_prime_pow hp).mp hOdvd
  have hk1 : k ≤ 1 := by
    by_contra h
    have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hOp : Nat.card O ≤ p := by
    rw [hOk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  set ρ : E →* Equiv.Perm O := MulAction.toPermHom E O
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective hE ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨m, hm⟩ := hRp.exists_card_eq
  have hRdvd : p ^ m ∣ p.factorial := by
    rw [← hm]
    refine (Subgroup.card_subgroup_dvd_card ρ.range).trans ?_
    rw [Nat.card_perm]
    exact Nat.factorial_dvd_factorial hOp
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : p ^ 2 ∣ p.factorial := (pow_dvd_pow p (by omega)).trans hRdvd
    have hfac : p.factorial = p * (p - 1).factorial := by
      conv_lhs => rw [show p = (p - 1) + 1 by have := hp.two_le; omega]
      rw [Nat.factorial_succ]
      congr 1
      have := hp.two_le
      omega
    rw [hfac, pow_two] at h2
    have h3 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.pos h2
    have h4 := (Nat.Prime.dvd_factorial hp).mp h3
    have := hp.two_le
    omega
  have hcyc : IsCyclic ρ.range := by
    rcases Nat.lt_or_ge m 1 with h0 | h1
    · have hm0 : m = 0 := by omega
      rw [hm0, pow_zero] at hm
      haveI : Subsingleton ρ.range := (Nat.card_eq_one_iff_unique.mp hm).1
      exact isCyclic_of_subsingleton
    · have hm1' : m = 1 := by omega
      rw [hm1', pow_one] at hm
      exact isCyclic_of_prime_card hm
  have hcomm : ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ = ρ ⟨y, hy⟩ * ρ ⟨x, hx⟩ := by
    have := (IsCyclic.commGroup (α := ρ.range)).mul_comm ⟨ρ ⟨x, hx⟩, ⟨_, rfl⟩⟩
      ⟨ρ ⟨y, hy⟩, ⟨_, rfl⟩⟩
    exact congrArg Subtype.val this
  have h := congrArg (fun σ : Equiv.Perm O => (σ ⟨a, MulAction.mem_orbit_self a⟩ : α)) hcomm
  simp only [ρ, MulAction.toPermHom_apply, Equiv.Perm.coe_mul, Function.comp_apply,
    MulAction.toPerm_apply, MulAction.orbit.coe_smul, Subgroup.mk_smul, Equiv.Perm.smul_def] at h
  exact h

theorem exists_ne_comm_of_card_center {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Y} (hEcard : Nat.card E = p ^ 3) (hEZ : Nat.card (Subgroup.center E) = p) :
    ∃ a b : E, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have htop : Subgroup.center E = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Subgroup.mem_center_iff.mpr fun g => hall g z
  rw [htop, Subgroup.card_top, hEcard] at hEZ
  have h1 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h1
  omega

end KlingenIdentAltAux

open KlingenIdentAltAux

@[expose] def KlingenIdentAltAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    Open.pRank p (Rb : Subgroup Y) = 3 →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rb Y₀ →
        ¬ Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p)))

theorem klingenIdentAltAt_of_five_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    KlingenIdentAltAt p := by
  intro Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl ⟨eA⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hred.ne_two
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZp : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hred.core_eq_bot hK
  have hZ : Subgroup.center K = ⊥ := by
    obtain ⟨m, hm⟩ : ∃ m, 3 * p = m + 2 := ⟨3 * p - 2, by omega⟩
    set eA' : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (m + 2)) :=
      eA.trans (Equiv.altCongrHom (finCongr hm))
    set η : K →* alternatingGroup (Fin (m + 2)) :=
      eA'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hη : Function.Surjective η := eA'.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : η.ker = Subgroup.center K := by
      ext x
      rw [MonoidHom.mem_ker]
      change eA' (QuotientGroup.mk' (Subgroup.center K) x) = 1 ↔ _
      rw [map_eq_one_iff _ eA'.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hodd : Odd (Nat.card η.ker) := by
      rw [hker]
      obtain ⟨k, hk⟩ := hZp.exists_card_eq
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m) η hη
      (hker ▸ le_rfl) hodd
    rw [hker] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K := fun c hc hcp =>
    mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hC : Subgroup.centralizer (K : Set Y) = ⊥ :=
    centralizer_eq_bot_of_forall_mem hp hp2 hred.core_eq_bot hKn hmem hZ
  set eK : K ≃* alternatingGroup (Fin (3 * p)) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eA
  obtain ⟨E, D, L, hER, hEcard, hEexp, hEZ, -, -, -, -, -, -, -, ek, hSL⟩ := hkl
  have hidx : ¬ p ^ 2 ∣ (K ⊔ Subgroup.centralizer (K : Set Y)).index := by
    rw [hC, sup_bot_eq]
    intro h
    have hdvd := CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv K
      (by rw [hC]; exact bot_le) eK
    exact not_dvd_card_outer_alternatingGroup (3 * p) (by omega) p hp hp2
      ((dvd_pow_self p two_ne_zero).trans (h.trans hdvd))
  have hCcyc : IsCyclic (Subgroup.centralizer (K : Set Y)) := by
    rw [hC]
    exact isCyclic_of_subsingleton
  have hEK : E ≤ K := le_of_klingen hCcyc hidx hEcard hEexp hEZ ek hSL
  set f : E →* Equiv.Perm (Fin (3 * p)) :=
    (alternatingGroup (Fin (3 * p))).subtype.comp (eK.toMonoidHom.comp (Subgroup.inclusion hEK))
  have hf : Function.Injective f :=
    (alternatingGroup (Fin (3 * p))).subtype_injective.comp
      (eK.injective.comp (Subgroup.inclusion_injective hEK))
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hFp : IsPGroup p f.range :=
    IsPGroup.of_surjective hEp f.rangeRestrict f.rangeRestrict_surjective
  have hα : Nat.card (Fin (3 * p)) < p ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, pow_two]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  obtain ⟨a, b, hab⟩ := exists_ne_comm_of_card_center hp hEcard hEZ
  apply hab
  apply hf
  rw [map_mul, map_mul]
  exact commute_of_isPGroup_perm hα hFp ⟨a, rfl⟩ ⟨b, rfl⟩

theorem klingenIdentAlt_of_three (h3 : @KlingenIdentAltAt 3 ⟨Nat.prime_three⟩) :
    KlingenIdentAlt := by
  intro p _ Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl
  have hp : p.Prime := Fact.out
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 Y Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl
  · have hp2 : p ≠ 2 := hred.ne_two
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have := hp.two_le
    exact klingenIdentAltAt_of_five_le p (by omega) Y Rb Y₀ hred hcat hrank K hK huniq hnc hcent
      hkl

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
