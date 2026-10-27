module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256c2
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot)
open scoped commutatorElement

section Defs

variable {S : Type} [Group S]

@[expose] def IsChevSub (q : ℕ) (β : MulAut S) (J : Subgroup S) : Prop :=
  IsSubnormal J (fixSubgroup β) ∧ CFSG.Open.IsQuasisimple J ∧ IsChevSimple q (J ⧸ Subgroup.center J)

@[expose] def QGen (q : ℕ) (β : MulAut S) : Prop :=
  ∀ s : S, β s = s → (∃ n : ℕ, s ^ q ^ n = 1) → s ∈ ⨆ (J : Subgroup S) (_ : IsChevSub q β J), J

end Defs

section Generic

variable {G : Type*} [Group G]

theorem commutator_self_of_isQuasisimple {J : Subgroup G} (hJ : CFSG.Open.IsQuasisimple J) :
    ⁅J, J⁆ = J := by
  rw [← Subgroup.map_subtype_commutator, hJ.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_eq_top_of_self {J : Subgroup G} (hJ : ⁅J, J⁆ = J) : commutator J = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_of_mul_central {M Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) [Finite Z] {q : ℕ}
    (hcop : Nat.Coprime (Nat.card Z) q) {k w : G} (hw : w ∈ M) (hz : w⁻¹ * k ∈ Z)
    {n : ℕ} (hk : k ^ q ^ n = 1) : k ∈ M := by
  set N := Nat.card Z with hN
  have hzN : (w⁻¹ * k) ^ N = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨w⁻¹ * k, hz⟩)
    exact congrArg Subtype.val h
  have hcomm : Commute w (w⁻¹ * k) := Subgroup.mem_center_iff.1 (hZ hz) w
  have hkN : k ^ N = w ^ N := by
    have e : k = w * (w⁻¹ * k) := by group
    rw [e, hcomm.mul_pow, hzN, mul_one]
  have hcopk : N.Coprime (orderOf k) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk) (Nat.Coprime.pow_right n hcop)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopk
  rw [← hm, hkN]
  exact M.pow_mem (M.pow_mem hw N) m

theorem exists_pow_lift {T : Type*} [Group T] (π : G →* T) (hπ : Function.Surjective π) [Finite π.ker]
    {q : ℕ} (hcop : Nat.Coprime (Nat.card π.ker) q) {s : T} {n : ℕ} (hs : s ^ q ^ n = 1) :
    ∃ x : G, π x = s ∧ x ^ q ^ n = 1 := by
  obtain ⟨x₀, rfl⟩ := hπ s
  set N := Nat.card π.ker with hN
  have hcops : N.Coprime (orderOf (π x₀)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hs) (Nat.Coprime.pow_right n hcop)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcops
  refine ⟨(x₀ ^ N) ^ m, by rw [map_pow, map_pow, hm], ?_⟩
  have hker : x₀ ^ q ^ n ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hs]
  have h1 : (x₀ ^ q ^ n) ^ N = 1 := by
    have h := pow_card_eq_one' (G := π.ker) (x := ⟨x₀ ^ q ^ n, hker⟩)
    exact congrArg Subtype.val h
  calc ((x₀ ^ N) ^ m) ^ q ^ n = ((x₀ ^ q ^ n) ^ N) ^ m := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = 1 := by rw [h1, one_pow]

theorem eq_one_of_mem_of_coprime {Z : Subgroup G} [Finite Z] {q : ℕ}
    (hcop : Nat.Coprime (Nat.card Z) q) {z : G} (hz : z ∈ Z) {n : ℕ} (hzn : z ^ q ^ n = 1) : z = 1 := by
  have hzN : z ^ Nat.card Z = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val h
  have h1 : orderOf z ∣ Nat.gcd (Nat.card Z) (q ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzN) (orderOf_dvd_of_pow_eq_one hzn)
  rw [Nat.Coprime.pow_right n hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem coprime_card_of_perfect {Q : Type*} [Group Q] [Finite Q] (hQ : commutator Q = ⊤) {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card (Q ⧸ Subgroup.center Q)) : Nat.Coprime p (Nat.card Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : x ^ (Subgroup.center Q).index = 1 := by
    have hker : x ∈ (MonoidHom.transferCenterPow Q).ker :=
      Abelianization.commutator_subset_ker _ (hQ ▸ Subgroup.mem_top x)
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hker)
    rwa [MonoidHom.transferCenterPow_apply] at h1
  have h2 := orderOf_dvd_of_pow_eq_one hpow
  rw [hx, Subgroup.index_eq_card] at h2
  exact h h2

end Generic

section CentralImage

variable {X T : Type} [Group X] [Group T]

theorem commutator_le_self (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

theorem centralImage_equiv (π : X →* T) (hker : π.ker ≤ Subgroup.center X) {F : Subgroup X}
    (hF : commutator F = ⊤) :
    Nonempty ((F ⧸ Subgroup.center F) ≃* (F.map π ⧸ Subgroup.center (F.map π))) := by
  set ψ : F →* F.map π := π.subgroupMap F with hψ
  have hψs : Function.Surjective ψ := π.subgroupMap_surjective F
  have hψk : ψ.ker ≤ Subgroup.center F := by
    intro x hx
    have h1 : π (x : X) = 1 := congrArg Subtype.val hx
    have h2 : (x : X) ∈ Subgroup.center X := hker h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (y : X))
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hF ψ hψs hψk

theorem centralImage_facts (π : X →* T) (hker : π.ker ≤ Subgroup.center X) {F : Subgroup X}
    (hF : CFSG.Open.IsQuasisimple F) :
    CFSG.Open.IsQuasisimple (F.map π) ∧
      Nonempty ((F ⧸ Subgroup.center F) ≃* (F.map π ⧸ Subgroup.center (F.map π))) := by
  obtain ⟨e⟩ := centralImage_equiv π hker hF.1
  have hperf : commutator (F.map π) = ⊤ := by
    have : Group.IsPerfect F := ⟨hF.1⟩
    exact (Group.IsPerfect.ofSurjective (f := π.subgroupMap F) (π.subgroupMap_surjective F)).commutator_eq_top
  have hsimple : IsSimpleGroup (F.map π ⧸ Subgroup.center (F.map π)) := by
    haveI : IsSimpleGroup (F ⧸ Subgroup.center F) := hF.2
    exact e.symm.isSimpleGroup
  exact ⟨⟨hperf, hsimple⟩, ⟨e⟩⟩

theorem nonempty_pSimple_equiv {J : Subgroup X} [Finite X] {p : ℕ} (hp : p.Prime)
    (hJ : CFSG.Open.IsQuasisimple J) (hpJ : p ∣ Nat.card (J ⧸ Subgroup.center J)) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* PSimple p J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p J)) :=
    CFSG.pPrimeCore_coprime_card (p := p) (G := J)
  have hne : GLAPPrimeCore p J ≠ ⊤ := by
    intro h
    have h1 : p ∣ Nat.card J := hpJ.trans (Subgroup.card_quotient_dvd_card _)
    rw [h, Subgroup.card_top] at hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h1)
  have hle : GLAPPrimeCore p J ≤ Subgroup.center J :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJ (GLAPPrimeCore.normal p J) hne
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hJ.1
    (QuotientGroup.mk' (GLAPPrimeCore p J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hle)

end CentralImage

section ChevOrder

open CFSG.Open (orderA orderTwistedA orderBC orderD orderTwistedD orderE6 orderE7 orderE8 orderF4 orderG2
  orderTwistedE6 orderTrialityD4)

variable {Q r : ℕ}

theorem two_dvd_sq_sub_one (hQ : Odd Q) : 2 ∣ Q ^ 2 - 1 :=
  even_iff_two_dvd.1 (Nat.Odd.sub_odd (hQ.pow) odd_one)

theorem mul_gcd_two_dvd (hr : r.Prime) (hr2 : r ≠ 2) (hQ : Odd Q) (hrQ : r ∣ Q ^ 2 - 1) (a : ℕ) :
    Nat.gcd 2 a * r ∣ Q ^ 2 - 1 := by
  have h2r : 2 * r ∣ Q ^ 2 - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
      (two_dvd_sq_sub_one hQ) hrQ
  exact (mul_dvd_mul_right (Nat.gcd_dvd_left 2 a) r).trans h2r

theorem pair_subset_Icc {n : ℕ} (hn : 2 ≤ n) : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rw [Finset.mem_Icc]
  omega

theorem add_one_dvd_pow_three_add_one : Q + 1 ∣ Q ^ 3 + 1 := by
  simpa using (by decide : Odd 3).nat_add_dvd_pow_add_pow Q 1

theorem add_one_dvd_pow_five_add_one : Q + 1 ∣ Q ^ 5 + 1 := by
  simpa using (by decide : Odd 5).nat_add_dvd_pow_add_pow Q 1

theorem prime_dvd_orderA {n : ℕ} (hn : 1 ≤ n) (hQ : Odd Q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderA n Q := by
  unfold orderA
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ?_ _
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    show Nat.gcd 2 (Q - 1) * r ∣ ∏ i ∈ Finset.Icc 2 2, (Q ^ i - 1)
    rw [Finset.Icc_self, Finset.prod_singleton]
    exact mul_gcd_two_dvd hr hr2 hQ hrQ _
  · have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun i => Q ^ i - 1) (pair_subset_Icc h)
    rw [Finset.prod_pair (by norm_num)] at hprod
    refine (?_ : Nat.gcd (n + 1) (Q - 1) * r ∣ (Q ^ 2 - 1) * (Q ^ 3 - 1)).trans hprod
    rw [mul_comm (Q ^ 2 - 1)]
    exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one Q 3)) hrQ

theorem prime_dvd_orderTwistedA {n : ℕ} (hn : 2 ≤ n) (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderTwistedA n Q := by
  unfold orderTwistedA
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ?_ _
  have hprod := Finset.prod_dvd_prod_of_subset _ _
    (fun i => if Even i then Q ^ i - 1 else Q ^ i + 1) (pair_subset_Icc hn)
  rw [Finset.prod_pair (by norm_num), if_pos (by decide), if_neg (by decide)] at hprod
  refine (?_ : Nat.gcd (n + 1) (Q + 1) * r ∣ (Q ^ 2 - 1) * (Q ^ 3 + 1)).trans hprod
  rw [mul_comm (Q ^ 2 - 1)]
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans add_one_dvd_pow_three_add_one) hrQ

theorem prime_dvd_orderBC {n : ℕ} (hn : 1 ≤ n) (hQ : Odd Q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderBC n Q := by
  unfold orderBC
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ?_ _
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
  have hprod := Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) h1
  simp only [mul_one] at hprod
  exact (mul_gcd_two_dvd hr hr2 hQ hrQ _).trans hprod

theorem prime_dvd_orderD {n : ℕ} (hn : 2 ≤ n) (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderD n Q := by
  unfold orderD
  apply Nat.dvd_div_of_mul_dvd
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hprod := Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) h1
  simp only [mul_one] at hprod
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) (hrQ.trans hprod)

theorem prime_dvd_orderTwistedD {n : ℕ} (hn : 2 ≤ n) (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderTwistedD n Q := by
  unfold orderTwistedD
  apply Nat.dvd_div_of_mul_dvd
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hprod := Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) h1
  simp only [mul_one] at hprod
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) (hrQ.trans hprod)

theorem prime_dvd_orderE6 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderE6 Q := by
  unfold orderE6
  apply Nat.dvd_div_of_mul_dvd
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one Q 5).trans
    (dvd_mul_left _ _))) hrQ

theorem prime_dvd_orderTwistedE6 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderTwistedE6 Q := by
  unfold orderTwistedE6
  apply Nat.dvd_div_of_mul_dvd
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (add_one_dvd_pow_five_add_one.trans
    (dvd_mul_left _ _))) hrQ

theorem prime_dvd_orderE7 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderE7 Q := by
  unfold orderE7
  apply Nat.dvd_div_of_mul_dvd
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one Q 6).trans
    (dvd_mul_left _ _))) hrQ

theorem prime_dvd_orderE8 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderE8 Q := by
  unfold orderE8
  exact hrQ.mul_left _

theorem prime_dvd_orderF4 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderF4 Q := by
  unfold orderF4
  exact hrQ.mul_left _

theorem prime_dvd_orderG2 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderG2 Q := by
  unfold orderG2
  exact hrQ.mul_left _

theorem prime_dvd_orderTrialityD4 (hrQ : r ∣ Q ^ 2 - 1) : r ∣ orderTrialityD4 Q := by
  unfold orderTrialityD4
  exact hrQ.mul_left _

theorem dvd_pow_sq_sub_one {q : ℕ} (hr : r ∣ q ^ 2 - 1) (f : ℕ) : r ∣ (q ^ f) ^ 2 - 1 := by
  have e : (q ^ f) ^ 2 = (q ^ 2) ^ f := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e]
  exact hr.trans (Nat.sub_one_dvd_pow_sub_one (q ^ 2) f)


theorem prime_dvd_card_of_isChevSimple {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Type} [Group X] [Finite X]
    (hX : IsChevSimple q X) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ q ^ 2 - 1) : r ∣ Nat.card X := by
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h8 : q = 3 → False := fun h3 => by
    subst h3
    have h8' : r ∣ 2 ^ 3 := by simpa using hrq
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h8'))
  rcases hX with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d X ⟨e⟩]
      obtain ⟨d, hv⟩ := d
      have hs := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
      rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
      have hQ : ∀ Q : TauCeti.PrimePower, Q.p = q → Odd Q.card ∧ r ∣ Q.card ^ 2 - 1 := fun Q hQq => by
        rw [TauCeti.PrimePower.card_def, hQq]
        exact ⟨hqodd.pow, dvd_pow_sq_sub_one hrq _⟩
      cases d with
      | A n Q =>
        obtain ⟨hQo, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderA hs.1 hQo hr hr2 hQr
      | twistedA n Q =>
        obtain ⟨-, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderTwistedA hs.1 hQr
      | B n Q =>
        obtain ⟨hQo, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderBC (by omega) hQo hr hr2 hQr
      | C n Q =>
        obtain ⟨hQo, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderBC (by omega) hQo hr hr2 hQr
      | D n Q =>
        obtain ⟨-, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderD (by omega) hQr
      | twistedD n Q =>
        obtain ⟨-, hQr⟩ := hQ Q (by simpa using hdq)
        exact prime_dvd_orderTwistedD (by omega) hQr
      | E6 Q => exact prime_dvd_orderE6 (hQ Q (by simpa using hdq)).2
      | E7 Q => exact prime_dvd_orderE7 (hQ Q (by simpa using hdq)).2
      | E8 Q => exact prime_dvd_orderE8 (hQ Q (by simpa using hdq)).2
      | F4 Q => exact prime_dvd_orderF4 (hQ Q (by simpa using hdq)).2
      | G2 Q => exact prime_dvd_orderG2 (hQ Q (by simpa using hdq)).2
      | twistedE6 Q => exact prime_dvd_orderTwistedE6 (hQ Q (by simpa using hdq)).2
      | trialityD4 Q => exact prime_dvd_orderTrialityD4 (hQ Q (by simpa using hdq)).2
      | suzuki m => exact absurd (show q = 2 by simpa using hdq.symm) hq2
      | reeG2 m => exact (h8 (by simpa using hdq.symm)).elim
      | reeF4 m => exact absurd (show q = 2 by simpa using hdq.symm) hq2
      | tits => exact absurd (show q = 2 by simpa using hdq.symm) hq2
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n hn =>
      rcases hi with ⟨rfl, h | rfl⟩ | ⟨rfl, h | h⟩ | ⟨-, h⟩
      · exact absurd h hq2
      · have h24 : r ∣ 2 ^ 3 * 3 := by simpa using hrq
        have hr3 : r = 3 := by
          rcases (Nat.Prime.dvd_mul hr).1 h24 with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
          · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h
        rw [hr3, Nat.card_congr e.toEquiv]
        show 3 ∣ Nat.card (alternatingGroup (Fin 5))
        rw [Inputs256b.card_alt5]
        norm_num
      · exact absurd h hq2
      · exact (h8 h).elim
      · exact absurd h hq2
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k Q =>
        rcases k with _ | _ | k
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · have hi' : (Q.card = 7 ∧ q = 2) ∨ (Q.card = 8 ∧ q = 3) := by
            simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          rcases hi' with ⟨-, h⟩ | ⟨-, h⟩
          · exact absurd h hq2
          · exact (h8 h).elim
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | twistedA k Q =>
        rcases k with _ | _ | _ | _ | k
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · have hi' : Q.card = 3 ∧ q = 2 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          exact absurd hi'.2 hq2
        · have hi' : Q.card = 2 ∧ q = 3 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          exact (h8 hi'.2).elim
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

end ChevOrder

section Lift

variable {K S : Type} [Group K] [Finite K] [Group S]

theorem exists_quasisimple_lift (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (a : MulAut K) (β : MulAut S) (hπβ : ∀ x, π (a x) = β (π x))
    {J : Subgroup S} (hJsn : IsSubnormal J (fixSubgroup β)) (hJq : CFSG.Open.IsQuasisimple J) :
    ∃ JK : Subgroup K, IsSubnormal JK (fixSubgroup a) ∧ CFSG.Open.IsQuasisimple JK ∧ JK.map π = J ∧
      Nonempty ((JK ⧸ Subgroup.center JK) ≃* (J ⧸ Subgroup.center J)) := by
  set C : Subgroup K := fixSubgroup a with hCdef
  have hJD : J ≤ fixSubgroup β := hJsn.le
  have hJperf : ⁅J, J⁆ = J := commutator_self_of_isQuasisimple hJq
  have hCD : C.map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker a β hπβ
  have hJC : J ≤ C.map π :=
    CFSG.HardMathSupport.Solomon.Coordinator.le_map_fixSubgroup_of_perfect π hker a β hπβ hπ hJD hJperf
  set Jh : Subgroup K := J.comap π ⊓ C with hJh
  set JK : Subgroup K := ⁅Jh, Jh⁆ with hJK
  have hJhmap : Jh.map π = J := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro t ht
      obtain ⟨c, hc, rfl⟩ := hJC ht
      exact ⟨c, ⟨ht, hc⟩, rfl⟩
  have hJKmap : JK.map π = J := by
    rw [hJK, Subgroup.map_commutator, hJhmap, hJperf]
  have hJKJh : JK ≤ Jh := commutator_le_self Jh
  have hdecomp : ∀ x ∈ Jh, ∃ y ∈ JK, y⁻¹ * x ∈ Subgroup.center K := by
    intro x hx
    have hx' : π x ∈ JK.map π := by rw [hJKmap]; exact hx.1
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨y, hy, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hJKperf : ⁅JK, JK⁆ = JK := by
    refine le_antisymm (commutator_le_self JK) ?_
    show ⁅Jh, Jh⁆ ≤ ⁅JK, JK⁆
    rw [Subgroup.commutator_le]
    intro x₁ h₁ x₂ h₂
    obtain ⟨y₁, hy₁, hz₁⟩ := hdecomp x₁ h₁
    obtain ⟨y₂, hy₂, hz₂⟩ := hdecomp x₂ h₂
    have e₁ : x₁ = y₁ * (y₁⁻¹ * x₁) := (mul_inv_cancel_left y₁ x₁).symm
    have e₂ : x₂ = y₂ * (y₂⁻¹ * x₂) := (mul_inv_cancel_left y₂ x₂).symm
    rw [e₁, e₂, commutatorElement_def, commutator_mul_central hz₁ hz₂, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hy₁ hy₂
  have hJKsn : IsSubnormal JK C := by
    have h1 : IsSubnormal J (C.map π) := isSubnormal_of_le_of_le hJsn hJC hCD
    have h2 : IsSubnormal (J.comap π ⊓ C) ((C.map π).comap π ⊓ C) := (h1.comap π).inf C
    rw [inf_eq_right.2 (Subgroup.le_comap_map π C)] at h2
    refine IsSubnormal.step hJKJh ?_ h2
    rw [Subgroup.normal_subgroupOf_iff hJKJh]
    intro h k hh hk
    have e : k * h * k⁻¹ = ⁅k, h⁆ * h := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact JK.mul_mem (Subgroup.commutator_mem_commutator hk (hJKJh hh)) hh
  obtain ⟨e⟩ := centralImage_equiv π hker (commutator_eq_top_of_self hJKperf)
  have hJq' : CFSG.Open.IsQuasisimple (JK.map π) := by rw [hJKmap]; exact hJq
  have hJKq : CFSG.Open.IsQuasisimple JK := by
    refine ⟨commutator_eq_top_of_self hJKperf, ?_⟩
    haveI : IsSimpleGroup (JK.map π ⧸ Subgroup.center (JK.map π)) := hJq'.2
    exact e.isSimpleGroup
  refine ⟨JK, hJKsn, hJKq, hJKmap, ?_⟩
  rw [← hJKmap]
  exact ⟨e⟩

end Lift

section Transfer

variable {K S : Type} [Group K] [Finite K] [Group S]


theorem exists_chev5Comp_map (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (a : MulAut K) (β : MulAut S) (hπβ : ∀ x, π (a x) = β (π x))
    {J : Subgroup S} (hJ : IsChevSub 5 β J) :
    ∃ JK ∈ Inputs256b.chev5Comps a, JK.map π = J := by
  obtain ⟨hJsn, hJq, hJchev⟩ := hJ
  obtain ⟨JK, hsn, hq, hmap, ⟨e⟩⟩ := exists_quasisimple_lift π hπ hker a β hπβ hJsn hJq
  have hJK3 : 3 ∣ Nat.card (JK ⧸ Subgroup.center JK) := by
    haveI : Finite (J ⧸ Subgroup.center J) := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr e.toEquiv]
    exact prime_dvd_card_of_isChevSimple Nat.prime_five (by norm_num) hJchev Nat.prime_three (by norm_num)
      (by norm_num)
  obtain ⟨e'⟩ := nonempty_pSimple_equiv Nat.prime_three hq hJK3
  refine ⟨JK, ⟨?_, ?_⟩, hmap⟩
  · rw [Inputs256b.fixedSub_eq]
    exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three hsn hq hJK3
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e.symm.trans e') hJchev

theorem mem_iSup_chev5Comps_of_qGen (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (hcop : Nat.Coprime (Nat.card π.ker) 5) (a : MulAut K)
    (β : MulAut S) (hπβ : ∀ x, π (a x) = β (π x)) (hβ : QGen 5 β) {k : K} (hak : a k = k)
    (hk : ∃ n : ℕ, k ^ 5 ^ n = 1) :
    k ∈ ⨆ (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps a), J := by
  obtain ⟨n, hn⟩ := hk
  set M : Subgroup K := ⨆ (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps a), J with hM
  have hs : π k ∈ ⨆ (J : Subgroup S) (_ : IsChevSub 5 β J), J :=
    hβ (π k) (by rw [← hπβ, hak]) ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hle : (⨆ (J : Subgroup S) (_ : IsChevSub 5 β J), J) ≤ M.map π := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨JK, hJK, rfl⟩ := exists_chev5Comp_map π hπ hker a β hπβ hJ
    exact Subgroup.map_mono (le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps a) => J)
      JK hJK le_rfl)
  obtain ⟨w, hw, hwk⟩ := hle hs
  have hz : w⁻¹ * k ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwk, inv_mul_cancel]
  exact mem_of_mul_central hker hcop hw hz hn

end Transfer

section QGenTransport

variable {S T : Type} [Group S] [Group T]

theorem fixSubgroup_congr (e : S ≃* T) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* T) := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

theorem isChevSub_map {q : ℕ} (e : S ≃* T) (β : MulAut S) {J : Subgroup S} (hJ : IsChevSub q β J) :
    IsChevSub q (MulAut.congr e β) (J.map (e : S →* T)) := by
  obtain ⟨hsn, hq, hchev⟩ := hJ
  set e₁ : J ≃* J.map (e : S →* T) := Subgroup.equivMapOfInjective J (e : S →* T) e.injective
  have e₂ : (J ⧸ Subgroup.center J) ≃* (J.map (e : S →* T) ⧸ Subgroup.center (J.map (e : S →* T))) :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  refine ⟨?_, hq.of_mulEquiv e₁.symm, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e₂
    hchev⟩
  rw [fixSubgroup_congr]
  exact hsn.map (e : S →* T)

theorem qGen_congr {q : ℕ} (e : S ≃* T) (β : MulAut S) (h : QGen q β) : QGen q (MulAut.congr e β) := by
  intro t ht ⟨n, hn⟩
  have hs : β (e.symm t) = e.symm t := by
    have h1 : e (β (e.symm t)) = t := ht
    exact (e.eq_symm_apply).2 h1
  have hmem := h (e.symm t) hs ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hle : (⨆ (J : Subgroup S) (_ : IsChevSub q β J), J).map (e : S →* T) ≤
      ⨆ (J : Subgroup T) (_ : IsChevSub q (MulAut.congr e β) J), J := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hJ => le_iSup₂_of_le (f := fun (J : Subgroup T)
      (_ : IsChevSub q (MulAut.congr e β) J) => J) _ (isChevSub_map e β hJ) le_rfl
  have := hle (Subgroup.mem_map_of_mem (e : S →* T) hmem)
  simpa using this

theorem qGen_of_congr {q : ℕ} (e : S ≃* T) (β : MulAut S) (h : QGen q (MulAut.congr e β)) : QGen q β := by
  have h1 := qGen_congr e.symm _ h
  have h2 : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext x
    simp [MulAut.congr]
  rwa [h2] at h1

theorem qGen_conj {q : ℕ} (γ β : MulAut S) (h : QGen q β) : QGen q (γ * β * γ⁻¹) := by
  have hc : MulAut.congr (γ⁻¹ : S ≃* S) (γ * β * γ⁻¹) = β := by
    ext x
    show γ.symm (γ (β (γ.symm (γ x)))) = β x
    simp
  refine qGen_of_congr (γ⁻¹ : S ≃* S) (γ * β * γ⁻¹) ?_
  rw [hc]
  exact h

end QGenTransport

section QGenCentral

variable {X T : Type} [Group X] [Finite X] [Group T]

theorem normal_map_subgroupOf_map (π : X →* T) {A L : Subgroup X}
    (hL : ∀ c ∈ A, ∀ g ∈ L, c * g * c⁻¹ ∈ L) :
    ((L.map π).subgroupOf (A.map π)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨c, hc, hcg⟩ := g.2
  refine ⟨c * f * c⁻¹, hL c hc f hf, ?_⟩
  simp only [map_mul, map_inv, hcg, hfx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem qGen_of_centralQuotient {q : ℕ} (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (hcop : Nat.Coprime (Nat.card π.ker) q) (α : MulAut X)
    (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.Open.IsQuasisimple (F i))
    (hFchev : ∀ i, IsChevSimple q (F i ⧸ Subgroup.center (F i)))
    (hgen : ∀ x ∈ fixSubgroup α, (∃ n : ℕ, x ^ q ^ n = 1) → x ∈ ⨆ i, F i) : QGen q β := by
  intro s hs ⟨n, hn⟩
  obtain ⟨x, hx, hxn⟩ := exists_pow_lift π hπ hcop hn
  have hzk : x⁻¹ * α x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hx, hs, inv_mul_cancel]
  have hcomm : Commute x (α x) := by
    have hz : Commute x (x⁻¹ * α x) := Subgroup.mem_center_iff.1 (hker hzk) x
    have e : α x = x * (x⁻¹ * α x) := by group
    rw [e]
    exact (Commute.refl x).mul_right hz
  have hzq : (x⁻¹ * α x) ^ q ^ n = 1 := by
    rw [(hcomm.inv_left).mul_pow, inv_pow, hxn, ← map_pow, hxn, map_one, inv_one, one_mul]
  have hαx : α x = x := by
    have h1 := eq_one_of_mem_of_coprime hcop hzk hzq
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hxF : x ∈ ⨆ i, F i := hgen x hαx ⟨n, hxn⟩
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  have hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπ
  have hFS : ∀ i, IsChevSub q β ((F i).map π) := by
    intro i
    obtain ⟨hq, ⟨e⟩⟩ := centralImage_facts π hker (hFq i)
    refine ⟨?_, hq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e (hFchev i)⟩
    exact IsSubnormal.step (Subgroup.map_mono (hFα i)) (normal_map_subgroupOf_map π (hFn i))
      (IsSubnormal.step hNC hNn (IsSubnormal.refl _))
  have hle : (⨆ i, F i).map π ≤ ⨆ (J : Subgroup T) (_ : IsChevSub q β J), J := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun i => le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : IsChevSub q β J) => J) _
      (hFS i) le_rfl
  rw [← hx]
  exact hle (Subgroup.mem_map_of_mem π hxF)

theorem coprime_card_of_pow_eq_one {G : Type*} [Group G] [Finite G] {H : Subgroup G} {N q : ℕ} (hq : q.Prime)
    (hN : Nat.Coprime N q) (hH : ∀ z ∈ H, z ^ N = 1) : Nat.Coprime (Nat.card H) q := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have h1 : orderOf (z : G) = q := by rw [Subgroup.orderOf_coe]; exact hz
  have h2 : q ∣ N := h1 ▸ orderOf_dvd_of_pow_eq_one (hH z z.2)
  exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.1 hN) h2)

end QGenCentral

section Linear

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem eq_one_of_coprime_card {G : Type*} [Group G] [Finite G] {q : ℕ}
    (hcop : Nat.Coprime (Nat.card G) q) {g : G} {n : ℕ} (hg : g ^ q ^ n = 1) : g = 1 := by
  have h1 : orderOf g ∣ Nat.gcd (Nat.card G) (q ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_natCard g) (orderOf_dvd_of_pow_eq_one hg)
  rw [Nat.Coprime.pow_right n hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem coprime_pow_sub_one {q j : ℕ} (hq : q.Prime) (hj : 1 ≤ j) : Nat.Coprime (q ^ j - 1) q := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
  intro h
  have h1 : q ∣ q ^ j := dvd_pow_self q (by omega)
  have h2 := Nat.dvd_sub h1 h
  have h3 : q ^ j - (q ^ j - 1) = 1 := by
    have : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq.pos
    omega
  rw [h3] at h2
  exact hq.one_lt.ne' (Nat.dvd_one.1 h2)

theorem exists_card_eq_pow {q : ℕ} (hq : q.Prime) {E : Type*} [Field E] [Finite E] (hE : ringChar E = q) :
    ∃ j : ℕ, 1 ≤ j ∧ Nat.card E = q ^ j := by
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP E q := hE ▸ ringChar.charP E
  obtain ⟨j, -, hj⟩ := FiniteField.card E q
  exact ⟨j, j.pos, by rw [Nat.card_eq_fintype_card, hj]⟩

theorem coprime_card_units {q : ℕ} (hq : q.Prime) {E : Type*} [Field E] [Finite E] (hE : ringChar E = q) :
    Nat.Coprime (Nat.card Eˣ) q := by
  obtain ⟨j, hj1, hj⟩ := exists_card_eq_pow hq hE
  rw [Nat.card_units, hj]
  exact coprime_pow_sub_one hq hj1

theorem four_le_card {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {E : Type*} [Field E] [Finite E]
    (hE : ringChar E = q) : 4 ≤ Nat.card E := by
  obtain ⟨j, hj, hc⟩ := exists_card_eq_pow hq hE
  rw [hc]
  calc 4 ≤ q ^ 1 := by rw [pow_one]; omega
    _ ≤ q ^ j := Nat.pow_le_pow_right hq.pos hj

theorem coprime_card_gl_of_finrank_le_one {q : ℕ} (hq : q.Prime) {E W : Type*} [Field E] [Finite E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] (hE : ringChar E = q)
    (h : Module.finrank E W ≤ 1) :
    Nat.Coprime (Nat.card (LinearMap.GeneralLinearGroup E W)) q := by
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank E W = m := ⟨_, rfl⟩
  let b : Module.Basis (Fin m) E W := Module.finBasisOfFinrankEq E W hm
  have e : LinearMap.GeneralLinearGroup E W ≃* Matrix.GeneralLinearGroup (Fin m) E :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      Matrix.GeneralLinearGroup.toLin.symm
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  obtain ⟨j, hj1, hj⟩ := exists_card_eq_pow hq hE
  rw [← Nat.card_eq_fintype_card, hj]
  rw [hm] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
  · simp
  · simpa using coprime_pow_sub_one hq hj1

theorem sl_type {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {E : Type} [Field E] [Finite E] (hE : ringChar E = q)
    {m : ℕ} (hm : 2 ≤ m) {F : Type} [Group F] (e : Matrix.SpecialLinearGroup (Fin m) E ≃* F) :
    IsChevSimple q (F ⧸ Subgroup.center F) := by
  haveI : Fintype E := Fintype.ofFinite E
  have h4 : m = 2 → 4 ≤ Fintype.card E := fun _ => by
    rw [← Nat.card_eq_fintype_card]; exact four_le_card hq h5 hE
  have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds E m hm h4
  have e₂ : (Matrix.SpecialLinearGroup (Fin m) E ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) ≃*
      (F ⧸ Subgroup.center F) := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hchev := hX.chev
  rw [hE] at hchev
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e₂ hchev

variable {k : Type} [Field k] [Finite k]

theorem proj_ker_facts {q : ℕ} (hq : q.Prime) (hk : ringChar k = q) (n : ℕ) :
    (LinearFlag.proj n k).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) ∧
      Nat.Coprime (Nat.card (LinearFlag.proj n k).ker) q := by
  refine ⟨by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n k,
    coprime_card_of_pow_eq_one hq (coprime_card_units hq hk) fun z hz => ?_⟩
  rw [LinearFlag.ker_proj] at hz
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]

theorem mem_iSup_specialFactor_of_char {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {n : ℕ}
    {A : GL (Fin n) k} (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) {j : ℕ} (hg : g ^ q ^ j = 1) :
    (g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      ⨆ h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h},
        specialFactor A h.1.1 := by
  refine mem_iSup_specialFactor_of_blockDetHom_eq_one hsq g ?_
  have hu : blockDetHom hsq g ^ q ^ j = 1 := by rw [← map_pow, hg, map_one]
  refine Prod.ext (funext fun b => ?_) (funext fun b => ?_)
  · have : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    have : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
    have hchar : ringChar (AdjoinRoot (b : k[X])) = q := by
      rw [← Algebra.ringChar_eq k (AdjoinRoot (b : k[X])), hk]
    refine eq_one_of_coprime_card (coprime_card_units hq hchar) (n := j) ?_
    have := congrArg (fun u => u.1 b) hu
    simp only [Prod.pow_fst, Pi.pow_apply, Prod.fst_one, Pi.one_apply] at this
    exact this
  · have : Fact (Irreducible (b.1 : k[X])) := ⟨irreducible_of_mem_primaryFactors b.1.2⟩
    have : Finite (AdjoinRoot (b.1 : k[X])) := Module.finite_of_finite k
    have hchar : ringChar (AdjoinRoot (b.1 : k[X])) = q := by
      rw [← Algebra.ringChar_eq k (AdjoinRoot (b.1 : k[X])), hk]
    have hle : primaryMultiplicity (glA A : Module.End k (Fin n → k)) (b.1 : k[X]) ≤ 1 := by
      have h4 := four_le_card hq h5 hchar
      have hb := b.2
      unfold IsGoodFactor at hb
      omega
    haveI : Finite (blockGL (glA A : Module.End k (Fin n → k)) (b.1 : k[X])) :=
      Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h0 => by
        have := coprime_card_gl_of_finrank_le_one (W := primaryComponent (glA A :
          Module.End k (Fin n → k)) (b.1 : k[X])) hq hchar hle
        rw [blockGL] at h0
        rw [h0] at this
        exact hq.one_lt.ne' (Nat.coprime_zero_left _ |>.1 this))).ne'
    refine eq_one_of_coprime_card (coprime_card_gl_of_finrank_le_one hq hchar hle) (n := j) ?_
    have := congrArg (fun u => u.2 b) hu
    simp only [Prod.pow_snd, Pi.pow_apply, Prod.snd_one, Pi.one_apply] at this
    exact this

theorem qGen_conjAut {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {n p : ℕ}
    (hpk : ((p : ℕ) : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) : QGen q (LinearFlag.conjAut n k A) := by
  have hsq := squarefree_minpoly_glA hpk hA
  obtain ⟨hker, hcop⟩ := proj_ker_facts hq hk n
  refine qGen_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) hker hcop
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => open_isQuasisimple (isQuasisimple_specialFactor hsq h.1.2 h.2)) (fun h => ?_)
    (fun x hx ⟨j, hj⟩ => mem_iSup_specialFactor_of_char hq h5 hk hsq ⟨x, hx⟩ (j := j) (Subtype.ext hj))
  have : Fact (Irreducible (h.1.1 : k[X])) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  have : Finite (AdjoinRoot (h.1.1 : k[X])) := Module.finite_of_finite k
  have hchar : ringChar (AdjoinRoot (h.1.1 : k[X])) = q := by
    rw [← Algebra.ringChar_eq k (AdjoinRoot (h.1.1 : k[X])), hk]
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq h.1.2
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) (h.1.1 : k[X]) := by
    rcases h.2 with h3 | ⟨h2, -⟩ <;> omega
  exact sl_type hq h5 hchar hm e

theorem injective_map_subtype_sl {n : ℕ} (k₀ : Subfield k) :
    Function.Injective (Matrix.SpecialLinearGroup.map k₀.subtype :
      Matrix.SpecialLinearGroup (Fin n) k₀ →* Matrix.SpecialLinearGroup (Fin n) k) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun a b => Subtype.val_injective ?_)
  have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) k =>
    (x : Matrix (Fin n) (Fin n) k) a b) hgg'
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h1

theorem fixSubgroup_slFieldAut_eq_range {n : ℕ} {k₀ : Subfield k} {σ : k ≃+* k}
    (hk : ∀ x, x ∈ k₀ ↔ σ x = x) :
    fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ) =
      (Matrix.SpecialLinearGroup.map k₀.subtype :
        Matrix.SpecialLinearGroup (Fin n) k₀ →* Matrix.SpecialLinearGroup (Fin n) k).range := by
  ext g
  rw [mem_fixSubgroup]
  constructor
  · intro hg
    have hent : ∀ a b, σ ((g : Matrix (Fin n) (Fin n) k) a b) =
        (g : Matrix (Fin n) (Fin n) k) a b := fun a b =>
      congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k) a b) hg
    let g₀ : Matrix (Fin n) (Fin n) k₀ := Matrix.of fun a b => ⟨_, (hk _).2 (hent a b)⟩
    have hg₀ : g₀.map k₀.subtype = g := Matrix.ext fun _ _ => rfl
    have hdet : g₀.det = 1 := Subtype.val_injective (by
      change k₀.subtype g₀.det = k₀.subtype 1
      rw [RingHom.map_det, map_one]
      change (g₀.map k₀.subtype).det = 1
      rw [hg₀]
      exact g.2)
    exact ⟨⟨g₀, hdet⟩, Subtype.ext hg₀⟩
  · rintro ⟨g₀, rfl⟩
    refine Subtype.ext (Matrix.ext fun a b => ?_)
    exact (hk _).1 ((g₀ : Matrix (Fin n) (Fin n) k₀) a b).2

theorem qGen_fieldAut {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {n : ℕ} (hn : 2 ≤ n)
    (σ : k ≃+* k) : QGen q (LinearFlag.fieldAut n k σ) := by
  set k₀ : Subfield k := (σ : k →+* k).eqLocusField (RingHom.id k) with hk₀def
  have hk₀ : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => Iff.rfl
  set α := CatalogueBHigherLinearField.slFieldAut (Fin n) k σ with hα
  have hC := fixSubgroup_slFieldAut_eq_range (n := n) hk₀
  let e : Matrix.SpecialLinearGroup (Fin n) k₀ ≃* ↥(fixSubgroup α) :=
    (MonoidHom.ofInjective (injective_map_subtype_sl k₀)).trans (MulEquiv.subgroupCongr hC.symm)
  have hαβ : ∀ x, LinearFlag.proj n k (α x) = LinearFlag.fieldAut n k σ (LinearFlag.proj n k x) :=
    fun x => (LinearFlag.descendAut_proj n k α x).symm
  have hchar : ringChar k₀ = q := by rw [Algebra.ringChar_eq k₀ k, hk]
  have hqs : CFSG.Open.IsQuasisimple ↥(fixSubgroup α) :=
    open_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hn (four_le_card hq h5 hchar)))
  obtain ⟨hker, hcop⟩ := proj_ker_facts hq hk n
  have hchev := sl_type hq h5 hchar hn e
  refine qGen_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) hker hcop α
    (LinearFlag.fieldAut n k σ) hαβ (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
    (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg)
      ((fixSubgroup α).inv_mem hc))
    (fun _ => hqs) (fun _ => hchev) (fun x hx _ => Subgroup.mem_iSup_of_mem () hx)

theorem natCast_ne_zero_of_ne {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) (hk : ringChar k = q) :
    ((p : ℕ) : k) ≠ 0 := by
  intro h0
  rw [CharP.cast_eq_zero_iff k (ringChar k), hk] at h0
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h0).symm

theorem qGen_projectiveSL_three_le {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) {n : ℕ} (hn : 3 ≤ n)
    (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ p = 1) : QGen q β := by
  haveI : CharP k q := hk ▸ ringChar.charP k
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow hq hk
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hq hf hn hK
  have hpk := natCast_ne_zero_of_ne hq hp hpq hk
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n k
  · have hrange : LinearFlag.linearAutGroup n k = (LinearFlag.conjAut n k).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n k).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact qGen_conjAut hq h5 hk hpk hc.symm
  · obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ ∈ LinearFlag.semilinearAutGroup n k :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup (LinearFlag.conjAut_mem_linearAutGroup A))
        (Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩))
    have hne : LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ ≠ 1 := fun h => hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ) = p := orderOf_eq_prime hβ hne
    obtain ⟨-, τ, -, ⟨h, -, hβτ⟩, -⟩ := hdesc.2.2.2.2.2.2.2 p hp hpq _ hmem hlin hord
    rw [hβτ]
    exact qGen_conj h _ (qGen_fieldAut hq h5 hk (by omega) τ)

theorem qGen_projectiveSL_two {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q) (β : MulAut (LinearFlag.projectiveSL 2 k)) (hβ : β ^ p = 1) : QGen q β := by
  have : Fact p.Prime := ⟨hp⟩
  have hpk := natCast_ne_zero_of_ne hq hp hpq hk
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (CFSG.GorensteinWalter.PSL2 k), MulAut.congr (psl2Equiv k) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv k)).symm β, (MulAut.congr (psl2Equiv k)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (psl2Equiv k)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  have hcongr : ∀ A : GL (Fin 2) k, MulAut.congr (psl2Equiv k)
      (CatalogueSchreierLinearTwo.pglAction k (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 k A :=
    fun A => congr_pglAction_mk A
  by_cases hD : β₀ ∈ (CatalogueSchreierLinearTwo.pglAction k).range
  · obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 k A := by
      rw [← hββ₀, ← hg]
      exact hcongr A
    have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) k) := by
      have h1 : CatalogueSchreierLinearTwo.pglAction k (Matrix.ProjGenLinGroup.mk (A ^ p)) =
          CatalogueSchreierLinearTwo.pglAction k 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CatalogueSchreierLinearTwo.pglAction_injective k h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    rw [hβA]
    exact qGen_conjAut hq h5 hk hpk hc.symm
  · have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, -, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβ' : β = LinearFlag.conjAut 2 k A * LinearFlag.fieldAut 2 k σ *
        (LinearFlag.conjAut 2 k A)⁻¹ := by
      rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]
    rw [hβ']
    exact qGen_conj _ _ (qGen_fieldAut hq h5 hk le_rfl σ)

theorem qGen_projectiveSL {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : ringChar k = q) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) {n : ℕ} (hn : 2 ≤ n) (β : MulAut (LinearFlag.projectiveSL n k))
    (hβ : β ^ p = 1) : QGen q β := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact qGen_projectiveSL_two hq h5 hk hp hpq β hβ
  · exact qGen_projectiveSL_three_le hq h5 hk hp hp2 hpq h β hβ

end Linear

section Unitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (open_isQuasisimple)

section UnitaryAbstract

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

private theorem mem_iSup_specialBlock_of_blocks (H : UnitaryPrimaryData hK.bar B x)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hdet : ∀ b : primaryFactors (x : Module.End K V),
      blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1)
    (hbad : ∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
      blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) :
    y ∈ ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
      specialBlock B x (a.1 : K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
    specialBlock B x (a.1 : K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ (y : LinearMap.GeneralLinearGroup K V)
      (hy : y ∈ unitaryCentralizer B x),
      (∀ b : primaryFactors (x : Module.End K V), blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
        blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (y : Module.End K V) v = v) → y ∈ M by
    exact key (primaryFactors (x : Module.End K V)) y hy hdet hbad fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro y hy _ _ h
    have : y = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]
    exact M.one_mem
  | insert b F hbF ih =>
    intro y hy hdet hbad h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set O : Set K[X] := {b, dualPoly hK.bar b} with hOdef
      have hbO : b ∈ O := Or.inl rfl
      have hO : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O → dualPoly hK.bar c ∈ O := by
        intro c hc hcO
        rcases hcO with rfl | hcO
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hcO
          subst hcO
          exact Or.inl (dualPoly_dualPoly_of_mem H hbΦ)
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO hy
      have hgOc : gO ∈ gl_centralizer x := hgO.1.2
      have hres : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∈ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = blockRestrict x (c : K[X]) ⟨y, hy.2⟩ :=
        fun c hc => blockGL_ext fun v hv => hgOeq c c.2 hc v hv
      have hres1 : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∉ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 :=
        fun c hc => blockGL_ext fun v hv => hgO.2 c c.2 hc v hv
      have hdetO : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c
        by_cases hc : (c : K[X]) ∈ O
        · have : blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = blockDetHom x (c : K[X]) ⟨y, hy.2⟩ := by
            simp only [blockDetHom, MonoidHom.comp_apply]
            rw [hres c hc]
          rw [this]
          exact hdet c
        · simp only [blockDetHom, MonoidHom.comp_apply]
          rw [hres1 c hc, map_one]
      have hbadO : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c hcb
        by_cases hc : (c : K[X]) ∈ O
        · rw [hres c hc]
          exact hbad c hcb
        · exact hres1 c hc
      have hgOM : gO ∈ M := by
        by_cases hgood : IsGoodBlock hK x ⟨b, hbΦ⟩
        · refine Subgroup.mem_iSup_of_mem
            (⟨⟨b, hbΦ⟩, hgood⟩ : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a})
            (mem_specialBlock.mpr ⟨hgO, hgOc, hdetO ⟨b, hbΦ⟩⟩)
        · have h1 : gO = 1 := by
            refine eq_one_of_paired H hbΦ hgO fun v hv => ?_
            have := congrArg (fun γ : blockGL (x : Module.End K V) b => blockApply γ v hv)
              (hbadO ⟨b, hbΦ⟩ hgood)
            exact this
          rw [h1]
          exact M.one_mem
      have hy' : gO⁻¹ * y ∈ unitaryCentralizer B x := mul_mem (inv_mem hgO.1) hy
      have hdet' : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hdetO c, hdet c, inv_one, mul_one]
      have hbad' : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c hcb
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hbadO c hcb, hbad c hcb, inv_one, mul_one]
      have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((gO : Module.End K V) u) = u := fun u => by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * y : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv, ← hgo, hinv, hgo]
      have hrest := ih _ hy' hdet' hbad' h'
      have hg_eq : y = gO * (gO⁻¹ * y) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM hrest
    · refine ih y hy hdet hbad fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩


end UnitaryAbstract

section UnitaryConcrete

variable {ℓ f : ℕ} {K : Type} [Field K]

private theorem squarefree_minpoly_toLin_of_pow_scalar {n p : ℕ} (hpK : (p : K) ≠ 0)
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((Matrix.GeneralLinearGroup.toLin a :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C (c : K))
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree ?_
  have h1 : ((Matrix.GeneralLinearGroup.toLin a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
    hap]
  ext v i
  by_cases hi : i = v <;> simp [hi]

private theorem primaryData_toLin' {n : ℕ} (h : UnitaryFieldData ℓ f K) {P : GL (Fin n) K}
    (hP : P ∈ primeFormUnitary h (idGram K n)) {c : Kˣ} {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hap : P ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P) := by
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hsq := squarefree_minpoly_toLin_of_pow_scalar hpK hap
  have hX : ((Matrix.GeneralLinearGroup.toLin P : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  refine ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n,
    (toLin_mem_sesqUnitaryGroup_iff P).mpr hP, ?_⟩
  rw [hX]
  exact hsq

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

private noncomputable def toLinSU :
    ↥(gramSU h (idGram K n)) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
    ).toMonoidHom.comp (gramSU h (idGram K n)).subtype

variable {h n}

private theorem toLinSU_injective : Function.Injective (toLinSU h n) := fun _ _ e =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

private theorem toLinSU_mem_sesqSpecialUnitaryGroup (g : ↥(gramSU h (idGram K n))) :
    toLinSU h n g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)).mpr g.2

private theorem mem_range_toLinSU {g' : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (idForm h n)) : g' ∈ (toLinSU h n).range := by
  have hmem : Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU h (idGram K n) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n), MulEquiv.apply_symm_apply]
    exact hg'
  exact ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g', hmem⟩, by
    show Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g') = g'
    exact MulEquiv.apply_symm_apply _ _⟩

private theorem mem_fixSubgroup_primeFormConjSU_iff (A : primeFormUnitary h (idGram K n))
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (g : ↥(gramSU h (idGram K n))) :
    g ∈ fixSubgroup (primeFormConjSU h (idGram K n) A) ↔ toLinSU h n g ∈ gl_centralizer x := by
  subst hx
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  have e : toLinSU h n g * Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) * toLinSU h n g ↔
      (g : GL (Fin n) K) * (A : GL (Fin n) K) = (A : GL (Fin n) K) * (g : GL (Fin n) K) := by
    change Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) *
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) *
          Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ↔ _
    rw [← map_mul, ← map_mul]
    exact Matrix.GeneralLinearGroup.toLin.injective.eq_iff
  rw [e]
  constructor
  · intro hα
    have h1 : (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g := congrArg Subtype.val hα
    calc (g : GL (Fin n) K) * (A : GL (Fin n) K)
        = ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K) := by rw [h1]
      _ = (A : GL (Fin n) K) * g := by group
  · intro hc
    apply Subtype.ext
    change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.symm

private theorem toLinSU_mem_unitaryCentralizer (A : primeFormUnitary h (idGram K n))
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    {g : ↥(gramSU h (idGram K n))} (hg : g ∈ fixSubgroup (primeFormConjSU h (idGram K n) A)) :
    toLinSU h n g ∈ unitaryCentralizer (idForm h n) x :=
  Subgroup.mem_inf.mpr ⟨sesqSpecialUnitaryGroup_le _ (toLinSU_mem_sesqSpecialUnitaryGroup g),
    (mem_fixSubgroup_primeFormConjSU_iff A hx g).mp hg⟩

private theorem coprime_card_normOneScalars {n : ℕ} (h : UnitaryFieldData ℓ f K) :
    Nat.Coprime (Nat.card ↥(normOneScalars h (gramSU h (idGram K n)) n)) ℓ := by
  haveI := h.finite
  have hℓ : ℓ.Prime := h.prime
  haveI : CharP K ℓ := h.charP
  refine coprime_card_of_pow_eq_one hℓ (coprime_card_units hℓ (ringChar.eq K ℓ)) fun z hz => ?_
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hz
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, hc, ← map_pow, pow_card_eq_one', map_one, OneMemClass.coe_one]

private theorem primaryMultiplicity_le_one_of_not_good {n : ℕ} (h : UnitaryFieldData ℓ f K) (h5 : 5 ≤ ℓ)
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (b : primaryFactors (x : Module.End K (Fin n → K)))
    (hb : ¬ IsGoodBlock h x b) : primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]) ≤ 1 := by
  have hd : 1 ≤ (b : K[X]).natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors b.2)
  by_contra hm
  apply hb
  refine ⟨by omega, fun _ hmem => ?_⟩
  have h5' : 5 ≤ ℓ ^ (f * (b : K[X]).natDegree) :=
    h5.trans (Nat.le_self_pow (Nat.mul_pos h.one_le hd).ne' ℓ)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  omega

theorem qGen_primeFormConjHom {n : ℕ} (h : UnitaryFieldData ℓ f K) (h5 : 5 ≤ ℓ) {p : ℕ} (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    QGen ℓ (primeFormConjHom h (idGram K n) A) := by
  classical
  haveI := h.finite
  have hℓ : ℓ.Prime := h.prime
  haveI : CharP K ℓ := h.charP
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) hℓ.one_lt
    omega
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)
    with hx
  have H : UnitaryPrimaryData h.bar (idForm h n) x := primaryData_toLin' h A.2 hp hpℓ hA
  set α : MulAut ↥(gramSU h (idGram K n)) := primeFormConjSU h (idGram K n) A with hα
  set β : MulAut (primeFormP h (idGram K n)) := primeFormConjHom h (idGram K n) A with hβ
  set π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hcop : Nat.Coprime (Nat.card π.ker) ℓ := by
    rw [hπ, QuotientGroup.ker_mk']
    exact coprime_card_normOneScalars h
  have hαβ : ∀ g, π (α g) = β (π g) := fun g => (primeFormConjHom_mk h (idGram K n) A g).symm
  have hSBle : ∀ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
      specialBlock (idForm h n) x (a.1 : K[X]) ≤ (toLinSU h n).range := fun a g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let F : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a} →
      Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) x (a.1 : K[X])).comap (toLinSU h n)
  have hFmap : ∀ a, (F a).map (toLinSU h n) = specialBlock (idForm h n) x (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  have hFα : ∀ a, F a ≤ fixSubgroup α := fun a g hg =>
    (mem_fixSubgroup_primeFormConjSU_iff A hx g).mpr
      (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2
  have hFn : ∀ a, ∀ c' ∈ fixSubgroup α, ∀ g ∈ F a, c' * g * c'⁻¹ ∈ F a := by
    intro a c' hc g hg
    have hcU := toLinSU_mem_unitaryCentralizer A hx hc
    have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact this
  have hFq : ∀ a, CFSG.Open.IsQuasisimple (F a) := by
    intro a
    have e : ↥(F a) ≃* ↥(specialBlock (idForm h n) x (a.1 : K[X])) :=
      (Subgroup.equivMapOfInjective (F a) (toLinSU h n) toLinSU_injective).trans
        (MulEquiv.subgroupCongr (hFmap a))
    exact open_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((specialBlockFacts_of_good H hq a.1 a.2).quasisimple a.2.1))
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  have hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπs
  have hFchev : ∀ a, IsChevSimple ℓ (F a ⧸ Subgroup.center (F a)) := by
    intro a
    obtain ⟨hqa, ⟨e2⟩⟩ := centralImage_facts π hker (hFq a)
    have hcomp : CFSG.Open.IsComponentOf ((F a).map π) (fixSubgroup β) :=
      ⟨(Subgroup.map_mono (hFα a)).trans hNC,
        IsSubnormal.step (Subgroup.map_mono (hFα a)) (normal_map_subgroupOf_map π (hFn a))
          (IsSubnormal.step hNC hNn (IsSubnormal.refl _)), hqa⟩
    obtain ⟨Y, _, _, hY, -, g, hg, hgk⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_primeFormConjHom
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds hp hpℓ A hA _ hcomp
    obtain ⟨e1⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hY.perfect g hg hgk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e1.trans e2.symm) hY.chev
  have hgen : ∀ g ∈ fixSubgroup α, (∃ j : ℕ, g ^ ℓ ^ j = 1) → g ∈ ⨆ a, F a := by
    rintro g hg ⟨j, hj⟩
    have hy := toLinSU_mem_unitaryCentralizer A hx hg
    have hyj : (⟨toLinSU h n g, hy.2⟩ : gl_centralizer x) ^ ℓ ^ j = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← map_pow, hj, map_one, OneMemClass.coe_one]
    have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        blockDetHom x (b : K[X]) ⟨toLinSU h n g, hy.2⟩ = 1 := by
      intro b
      have : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      have : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
      have hchar : ringChar (AdjoinRoot (b : K[X])) = ℓ :=
        (Algebra.ringChar_eq K (AdjoinRoot (b : K[X]))).symm.trans (ringChar.eq K ℓ)
      refine eq_one_of_coprime_card (coprime_card_units hℓ hchar) (n := j) ?_
      rw [← map_pow, hyj, map_one]
    have hbad : ∀ b : primaryFactors (x : Module.End K (Fin n → K)), ¬ IsGoodBlock h x b →
        blockRestrict x (b : K[X]) ⟨toLinSU h n g, hy.2⟩ = 1 := by
      intro b hb
      have : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      have : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
      have hchar : ringChar (AdjoinRoot (b : K[X])) = ℓ :=
        (Algebra.ringChar_eq K (AdjoinRoot (b : K[X]))).symm.trans (ringChar.eq K ℓ)
      have hle := primaryMultiplicity_le_one_of_not_good h h5 b hb
      haveI : Finite (blockGL (x : Module.End K (Fin n → K)) (b : K[X])) :=
        Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h0 => by
          have := coprime_card_gl_of_finrank_le_one (W := primaryComponent (x :
            Module.End K (Fin n → K)) (b : K[X])) hℓ hchar hle
          rw [blockGL] at h0
          rw [h0] at this
          exact hℓ.one_lt.ne' (Nat.coprime_zero_left _ |>.1 this))).ne'
      refine eq_one_of_coprime_card (coprime_card_gl_of_finrank_le_one hℓ hchar hle) (n := j) ?_
      rw [← map_pow, hyj, map_one]
    have hmem := mem_iSup_specialBlock_of_blocks H hy hdet hbad
    have hmapsup : (⨆ a, F a).map (toLinSU h n) =
        ⨆ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
          specialBlock (idForm h n) x (a.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hFmap
    have hk : toLinSU h n g ∈ (⨆ a, F a).map (toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨s, hs, hs'⟩ := hk
    have : s = g := toLinSU_injective hs'
    rw [← this]
    exact hs
  exact qGen_of_centralQuotient π hπs hker hcop α β hαβ F hFα hFn hFq hFchev hgen

end UnitaryConcrete

section UnitaryField

open CFSG.RankThree.Classical (subfieldSU exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL
  subfieldSU_injective fixSubfield_unitaryFieldData fixSubfield_unitaryFieldData_bar)
open CFSG.LieType.Chevalley (fixSubfield)

variable {ℓ f n : ℕ} {K : Type} [Field K]

private theorem fixSubgroup_primeFormFieldSU_eq_range (h : UnitaryFieldData ℓ f K)
    {e : ℕ} {σ : K ≃+* K} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    fixSubgroup (primeFormFieldSU h hC σ) = (subfieldSU h h₀ hbar n).range := by
  ext x
  rw [mem_fixSubgroup]
  constructor
  · intro hx
    have hx' : glAut σ (x : GL (Fin n) K) = x := congrArg Subtype.val hx
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hx'
    have hg₀S := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ x.2)
    exact ⟨⟨g₀, hg₀S⟩, Subtype.ext hg₀⟩
  · rintro ⟨y, rfl⟩
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change σ ((((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j :
      fixSubfield σ) : K) = (((y : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ)) i j : K)
    exact (((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

private theorem nonempty_statedSU_mulEquiv_fixSubgroup (h : UnitaryFieldData ℓ f K)
    {e : ℕ} {σ : K ≃+* K} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    Nonempty (↥(CFSG.Open.StatedSU n (ℓ ^ e) (fixSubfield σ)) ≃*
      ↥(fixSubgroup (primeFormFieldSU h hC σ))) :=
  ⟨((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ n)).trans
    (MonoidHom.ofInjective (subfieldSU_injective h h₀ hbar n))).trans
    (MulEquiv.subgroupCongr (fixSubgroup_primeFormFieldSU_eq_range h h₀ hbar hC).symm)⟩

theorem qGen_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (h5 : 5 ≤ ℓ) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p) : QGen ℓ (primeFormFieldHom h hC σ) := by
  haveI := h.finite
  have hℓ : ℓ.Prime := h.prime
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_fixSubgroup h h₀ hbar hC
  set α : MulAut ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := primeFormFieldSU h hC σ
    with hα
  let π : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hcop : Nat.Coprime (Nat.card π.ker) ℓ := by
    rw [QuotientGroup.ker_mk']
    exact coprime_card_normOneScalars h
  have hαβ : ∀ x, π (α x) = primeFormFieldHom h hC σ (π x) := fun x =>
    (primeFormFieldAut_mk h hC σ x).symm
  have hne : ¬ (n = 3 ∧ ℓ ^ (f / p) = 2) := fun ⟨_, h2⟩ => by
    have : ℓ ≤ ℓ ^ (f / p) := Nat.le_self_pow (by have := h₀.one_le; omega) ℓ
    omega
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard : Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  have hqs : CFSG.IsQuasisimple ↥(fixSubgroup α) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
        (fun heq => hne ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1
  have hLF := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_fixSubfield_lieFactorData
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds h hn hp hp2 hσ hne
  have e₂ : (↥(CFSG.Open.StatedSU n (ℓ ^ (f / p)) (fixSubfield σ)) ⧸
      Subgroup.center ↥(CFSG.Open.StatedSU n (ℓ ^ (f / p)) (fixSubfield σ))) ≃*
      (↥(fixSubgroup α) ⧸ Subgroup.center ↥(fixSubgroup α)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hchev : IsChevSimple ℓ (↥(fixSubgroup α) ⧸ Subgroup.center ↥(fixSubgroup α)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e₂ hLF.chev
  exact qGen_of_centralQuotient π hπ hker hcop α _ hαβ (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
    (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg) ((fixSubgroup α).inv_mem hc))
    (fun _ => open_isQuasisimple hqs) (fun _ => hchev) (fun x hx _ => Subgroup.mem_iSup_of_mem () hx)

end UnitaryField

end Unitary

section Reduction

open CFSG.LieType.SeitzGeneration (Cat IsLinearIndex IsUnitaryIndex')

@[expose] def QGenOn (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, P d → 5 ≤ d.1.characteristic → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ≠ d.1.characteristic → ∀ β : MulAut (Cat d), orderOf β = p → QGen d.1.characteristic β

theorem qGenOn_of_families (hL : QGenOn fun d => IsLinearIndex d.1)
    (hU : QGenOn fun d => IsUnitaryIndex' d.1)
    (hSO : QGenOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .symplecticOrthogonal)
    (hE : QGenOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional) :
    QGenOn fun _ => True := by
  rintro ⟨d, hv⟩ - hd5 p hp hp2 hpd β hβ
  cases d with
  | A m q => exact hL ⟨_, hv⟩ ⟨m, q, rfl⟩ hd5 p hp hp2 hpd β hβ
  | twistedA m q => exact hU ⟨_, hv⟩ ⟨m, q, rfl⟩ hd5 p hp hp2 hpd β hβ
  | B m q => exact hSO ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | C m q => exact hSO ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | D m q => exact hSO ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | twistedD m q => exact hSO ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | E6 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | E7 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | E8 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | F4 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | G2 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | twistedE6 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | trialityD4 q => exact hE ⟨_, hv⟩ rfl hd5 p hp hp2 hpd β hβ
  | suzuki m => exact absurd hd5 (by simp)
  | reeG2 m => exact absurd hd5 (by simp)
  | reeF4 m => exact absurd hd5 (by simp)
  | tits => exact absurd hd5 (by simp)

theorem qGenOn_linear : QGenOn fun d => IsLinearIndex d.1 := by
  rintro ⟨d, hv⟩ ⟨m, Q, rfl⟩ hd5 p hp hp2 hpd β hβ
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hQc : (TauCeti.LieTypeIndex.A m Q).characteristic = Q.p := by simp
  change 5 ≤ (TauCeti.LieTypeIndex.A m Q).characteristic at hd5
  change p ≠ (TauCeti.LieTypeIndex.A m Q).characteristic at hpd
  change QGen (TauCeti.LieTypeIndex.A m Q).characteristic β
  rw [hQc] at hd5 hpd ⊢
  let e : Cat ⟨.A m Q, hv⟩ ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (m + 1)
      (GaloisField Q.p Q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hchar : ringChar (GaloisField Q.p Q.exponent) = Q.p := ringChar.eq _ Q.p
  have hβp : MulAut.congr e β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  exact qGen_of_congr e β (qGen_projectiveSL Q.prime_p hd5 hchar hp hp2 hpd (by omega) _ hβp)

theorem qGenOn_unitary : QGenOn fun d => IsUnitaryIndex' d.1 := by
  rintro ⟨d, hv⟩ ⟨r, Q, rfl⟩ hd5 p hp hp2 hpd β hβ
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hQc : (TauCeti.LieTypeIndex.twistedA r Q).characteristic = Q.p := by simp
  change 5 ≤ (TauCeti.LieTypeIndex.twistedA r Q).characteristic at hd5
  change p ≠ (TauCeti.LieTypeIndex.twistedA r Q).characteristic at hpd
  change QGen (TauCeti.LieTypeIndex.twistedA r Q).characteristic β
  rw [hQc] at hd5 hpd ⊢
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv (MulEquiv.refl _)
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData Q.p Q.exponent K :=
    ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv h
    (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : Cat ⟨.twistedA r Q, hv⟩ ≃*
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1)) :=
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram (1 : GL (Fin (r + 1)) K) :=
    CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  refine qGen_of_congr e' β ?_
  by_cases hσ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq'
      (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormPsi_apply, map_pow, hA, hβ', map_one,
        one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA]
    exact qGen_primeFormConjHom h hd5 hp hpd A hAp
  ·
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hne
    have hσp : orderOf (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq'
        (MulAut.congr e' β)) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp hp2
        (MulAut.congr e' β) hord _ rfl hσp
    have h1 := qGen_primeFormFieldHom h hd5 hn3 hC hp hp2 hσp
    rw [← hM] at h1
    have h2 := qGen_conj (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1)) M) _ h1
    have hsimp : ∀ γ δ : MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1))), γ * (γ⁻¹ * δ * γ) * γ⁻¹ = δ :=
      fun γ δ => by group
    rwa [hsimp] at h2

@[expose] def QGenSympOrth : Prop :=
  QGenOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .symplecticOrthogonal

@[expose] def QGenExc : Prop :=
  QGenOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional

theorem qGenOn_of_residuals (hSO : QGenSympOrth) (hE : QGenExc) : QGenOn fun _ => True :=
  qGenOn_of_families qGenOn_linear qGenOn_unitary hSO hE


theorem input14_2Five_of_qGenOn (h : QGenOn fun _ => True) : Inputs256c.Input14_2Five := by
  intro K _ _ hK hcore h5 a ha k hak hk
  obtain ⟨d, ⟨θ⟩, hd5⟩ := h5
  set π : K →* Cat d := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp [π]
  set ψ : MulAut K →* MulAut (Cat d) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K) with hψ
  have hπβ : ∀ x, π (a x) = ψ a (π x) := by
    intro x
    simp [π, ψ, MulAut.congr, quotientCenterAut']
  have hψi : Function.Injective ψ :=
    (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hK.1.1)
  have hβ : orderOf (ψ a) = 3 := by rw [orderOf_injective ψ hψi, ha]
  have hcop : Nat.Coprime (Nat.card π.ker) 5 := by
    rw [hkerπ]
    exact Inputs2311c.coprime_card_center Nat.prime_three Nat.prime_five (by norm_num) hcore
  have hQ := h d trivial (by rw [hd5]) 3 Nat.prime_three (by norm_num) (by rw [hd5]; norm_num) _ hβ
  rw [hd5] at hQ
  exact mem_iSup_chev5Comps_of_qGen π hπ hkerπ.le hcop a (ψ a) hπβ hQ hak hk

theorem input14_2Five_of_residuals (hSO : QGenSympOrth) (hE : QGenExc) : Inputs256c.Input14_2Five :=
  input14_2Five_of_qGenOn (qGenOn_of_residuals hSO hE)

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e

end
