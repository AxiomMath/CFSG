module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalEmbed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding KlingenIdentAltAux

namespace KlingenIdentA9Aux

theorem commute_of_isPGroup_of_orbit {α : Type*} [Finite α] {p : ℕ} [hpF : Fact p.Prime]
    {E : Subgroup (Equiv.Perm α)} (hE : IsPGroup p E)
    (horb : ∀ a : α, Nat.card (MulAction.orbit E a) < p ^ 2)
    {x y : Equiv.Perm α} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  classical
  have hp : p.Prime := hpF.out
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  ext a
  set O : Set α := MulAction.orbit E a with hOdef
  have hlt : Nat.card O < p ^ 2 := horb a
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

end KlingenIdentA9Aux

open KlingenIdentA9Aux

theorem klingenIdentAltAt_three : @KlingenIdentAltAt 3 ⟨Nat.prime_three⟩ := by
  intro Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl ⟨eA⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZp : IsPGroup 3 (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hred.core_eq_bot hK
  have hZ : Subgroup.center K = ⊥ := by
    set eA' : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (7 + 2)) :=
      eA.trans (Equiv.altCongrHom (finCongr (by norm_num)))
    set η : K →* alternatingGroup (Fin (7 + 2)) :=
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
    have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by norm_num : 6 ≤ 7) η hη
      (hker ▸ le_rfl) hodd
    rw [hker] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = 3 → c ∈ K := fun c hc hcp =>
    mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hC : Subgroup.centralizer (K : Set Y) = ⊥ :=
    centralizer_eq_bot_of_forall_mem hp hp2 hred.core_eq_bot hKn hmem hZ
  set eK : K ≃* alternatingGroup (Fin 9) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eA
  haveI := hKn
  obtain ⟨φ, hφ, -⟩ :=
    CFSG.AGLEmbedding.exists_embedding_alternating K eK hC
  obtain ⟨E, D, L, hER, hEcard, hEexp, hEZ, -, -, -, -, -, hLC, -, ek, hSL⟩ := hkl
  obtain ⟨z, hz1⟩ : ∃ z : Subgroup.center E, z ≠ 1 := by
    haveI : Finite (Subgroup.center E) :=
      Nat.finite_of_card_ne_zero (by rw [hEZ]; norm_num)
    have : Nontrivial (Subgroup.center E) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hEZ]
      norm_num
    exact exists_ne 1
  set zY : Y := ((z : E) : Y) with hzYdef
  have hzE : zY ∈ E := (z : E).2
  have hzY1 : zY ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzord : orderOf zY = 3 := orderOf_eq_prime (hEexp zY hzE) hzY1
  set σ : Equiv.Perm (Fin 9) := φ zY with hσdef
  have hσord : orderOf σ = 3 := by rw [hσdef, orderOf_injective φ hφ]; exact hzord
  have hzZE : zY ∈ (Subgroup.center E).map E.subtype := ⟨z, z.2, rfl⟩
  have hLz : L ≤ Subgroup.centralizer ({zY} : Set Y) :=
    hLC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZE))
  have hEz : E ≤ Subgroup.centralizer ({zY} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hmapC : (Subgroup.centralizer ({zY} : Set Y)).map φ ≤
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * zY = zY * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, hσdef, ← map_mul, ← map_mul, hx']
  have hdvdC : Nat.card (Subgroup.centralizer ({zY} : Set Y)) ∣
      Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9)))) := by
    rw [← Subgroup.card_map_of_injective hφ]
    exact Subgroup.card_dvd_of_le hmapC
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hσord]; exact hp)
  rw [hσord] at hn
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  rcases (show n = 2 ∨ n ≤ 1 by omega) with rfl | hn1
  ·
    have h24 : 24 ∣ Nat.card (Subgroup.centralizer ({zY} : Set Y)) := by
      have hcardSL : Nat.card (StatedSL 2 (ZMod 3)) = 24 := by
        rw [CFSG.Open.StatedAPI.card_statedSL_two, Nat.card_zmod]
        norm_num
      rw [← hcardSL]
      have h1 := Subgroup.card_dvd_of_le hSL
      have h2 := Subgroup.card_map_dvd (H := L.subgroupOf (Subgroup.normalizer (E : Set Y)))
        (centerQuotientAction E ek)
      have h3 : Nat.card (L.subgroupOf (Subgroup.normalizer (E : Set Y))) ∣ Nat.card L := by
        rw [← Subgroup.card_map_of_injective (Subgroup.normalizer (E : Set Y)).subtype_injective,
          Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact h1.trans (h2.trans (h3.trans (Subgroup.card_dvd_of_le hLz)))
    have hc := Equiv.Perm.nat_card_centralizer σ
    rw [hn] at hc
    have h162 : Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9)))) = 162 := by
      rw [hc]
      decide
    have := h24.trans (hdvdC.trans (dvd_of_eq h162))
    norm_num at this
  ·
    set Q : Subgroup (Equiv.Perm (Fin 9)) := E.map φ with hQdef
    have hQp : IsPGroup 3 Q := (IsPGroup.of_card hEcard).map φ
    have hQC : ∀ q ∈ Q, q * σ = σ * q := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hσdef, ← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp (hEz hx))]
    have hsupp : σ.support.card = 3 * (n + 1) := by
      rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
    have horb : ∀ a : Fin 9, Nat.card (MulAction.orbit Q a) < 3 ^ 2 := by
      intro a
      by_cases ha : a ∈ σ.support
      · have hsub : MulAction.orbit Q a ⊆ (σ.support : Set (Fin 9)) := by
          rintro _ ⟨⟨q, hq⟩, rfl⟩
          simp only [Subgroup.mk_smul, Equiv.Perm.smul_def, Finset.mem_coe,
            Equiv.Perm.mem_support] at ha ⊢
          intro h
          apply ha
          apply q.injective
          rw [← Equiv.Perm.mul_apply, hQC q hq, Equiv.Perm.mul_apply, h]
        have := Nat.card_mono (Set.toFinite _) hsub
        have h2 : Nat.card ((σ.support : Finset (Fin 9)) : Set (Fin 9)) = σ.support.card := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
        rw [h2, hsupp] at this
        omega
      · have hsub : MulAction.orbit Q a ⊆ ((σ.supportᶜ : Finset (Fin 9)) : Set (Fin 9)) := by
          rintro _ ⟨⟨q, hq⟩, rfl⟩
          simp only [Subgroup.mk_smul, Equiv.Perm.smul_def, Finset.coe_compl, Set.mem_compl_iff,
            Finset.mem_coe, Equiv.Perm.mem_support, not_not] at ha ⊢
          rw [← Equiv.Perm.mul_apply, ← hQC q hq, Equiv.Perm.mul_apply, ha]
        have := Nat.card_mono (Set.toFinite _) hsub
        have h2 : Nat.card ((σ.supportᶜ : Finset (Fin 9)) : Set (Fin 9)) =
            (σ.supportᶜ).card := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
        rw [h2, Finset.card_compl, Fintype.card_fin, hsupp] at this
        omega
    obtain ⟨a, b, hab⟩ := exists_ne_comm_of_card_center hp hEcard hEZ
    apply hab
    apply Subtype.ext
    apply hφ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact commute_of_isPGroup_of_orbit hQp horb ⟨a, a.2, rfl⟩ ⟨b, b.2, rfl⟩

theorem klingenIdentAlt_holds : KlingenIdentAlt :=
  klingenIdentAlt_of_three klingenIdentAltAt_three

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
