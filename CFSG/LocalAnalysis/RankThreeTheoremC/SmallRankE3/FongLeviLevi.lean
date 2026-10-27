module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviPrime
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

theorem isPerfect_subgroupOf' {G : Type*} [Group G] {J Q : Subgroup G} (hJQ : J ≤ Q)
    (hJ : ⁅J, J⁆ = J) : Group.IsPerfect (J.subgroupOf Q) := by
  rw [Subgroup.isPerfect_iff]
  apply Subgroup.map_injective Q.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJQ, hJ]

theorem eq_one_of_pow_eq_one_of_pow_two_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : G} (hgp : g ^ p = 1) {k : ℕ} (hgk : g ^ (2 ^ k) = 1) : g = 1 := by
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · exfalso
    have h4 : p ∣ 2 ^ k := h3 ▸ orderOf_dvd_of_pow_eq_one hgk
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))

theorem eq_one_of_mem_ker_of_pow_eq_one {P M : Type*} [Group P] [Group M] (β : P →* M)
    (hβ : IsPGroup 2 β.ker) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : P} (hy : y ∈ β.ker)
    (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hβ ⟨y, hy⟩
  exact eq_one_of_pow_eq_one_of_pow_two_pow hp hp2 hyp (congrArg Subtype.val hk)

theorem normal_subgroupOf_of_commutators {M : Type*} [Group M] {R N : Subgroup M} (hNr : N ≤ R)
    (hab : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N) : (N.subgroupOf R).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h2 := hab (g : M) g.2 (n : M) (hNr hn)
  have h3 : (g : M) * n * (g : M)⁻¹ = ((g : M) * (n : M) * (g : M)⁻¹ * (n : M)⁻¹) * n := by
    group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h3]
  exact N.mul_mem h2 hn

theorem isSolvable_quotient_of_commutators {M : Type*} [Group M] {R N : Subgroup M} (hNr : N ≤ R)
    (hab : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N) :
    haveI := normal_subgroupOf_of_commutators hNr hab
    Group.IsSolvable (↥R ⧸ N.subgroupOf R) := by
  haveI := normal_subgroupOf_of_commutators hNr hab
  refine Group.isSolvable_of_comm ?_
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h2 := hab ((b⁻¹ : ↥R) : M) (b⁻¹).2 ((a⁻¹ : ↥R) : M) (a⁻¹).2
  convert h2 using 1
  simp [mul_assoc]

theorem map_perfectResidual_eq_of_levi {P M : Type*} [Group P] [Finite P] [Group M] [Finite M]
    (β : P →* M) (N : Subgroup M) (hNr : N ≤ β.range) (hNperf : ⁅N, N⁆ = N)
    [hNn : (N.subgroupOf β.range).Normal]
    (hsolv : Group.IsSolvable (↥β.range ⧸ N.subgroupOf β.range)) :
    (CFSG.perfectResidual P).map β = N := by
  obtain ⟨h1, -, -⟩ := CFSG.perfect_residual_transport β
  rw [h1]
  obtain ⟨-, -, -, -, hiff, -⟩ := CFSG.perfect_residual_characterization (G := ↥β.range)
  have hle : CFSG.perfectResidual ↥β.range ≤ N.subgroupOf β.range := (hiff _).mp hsolv
  have hge : N.subgroupOf β.range ≤ CFSG.perfectResidual ↥β.range :=
    (CFSG.perfect_residual_transport (MonoidHom.id ↥β.range)).2.2 _
      (isPerfect_subgroupOf' hNr hNperf)
  have heq : CFSG.perfectResidual ↥β.range = N.subgroupOf β.range := le_antisymm hle hge
  rw [heq, Subgroup.map_subgroupOf_eq_of_le hNr]

theorem mem_perfectResidual_of_levi {P M : Type*} [Group P] [Finite P] [Group M] [Finite M]
    (β : P →* M) (hβ : IsPGroup 2 β.ker) (N : Subgroup M)
    (hDN : (CFSG.perfectResidual P).map β = N) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpN : ∀ x ∈ β.range, x ^ p = 1 → x ∈ N) {x : P}
    (hx : orderOf x = p) : x ∈ CFSG.perfectResidual P := by
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hβxp : (β x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hmem : β x ∈ N := hpN (β x) (MonoidHom.mem_range.mpr ⟨x, rfl⟩) hβxp
  rw [← hDN] at hmem
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hmem
  have hk : x * d⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, mul_inv_cancel]
  obtain ⟨j, hj⟩ := hβ ⟨x * d⁻¹, hk⟩
  have hj' : (x * d⁻¹) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
  haveI : (CFSG.perfectResidual P).Characteristic :=
    (CFSG.perfect_residual_characterization (G := P)).2.1
  haveI : (CFSG.perfectResidual P).Normal := inferInstance
  have hq : (QuotientGroup.mk x : P ⧸ CFSG.perfectResidual P) = 1 := by
    have h1 : (QuotientGroup.mk x : P ⧸ CFSG.perfectResidual P) =
        QuotientGroup.mk (x * d⁻¹) := by
      rw [QuotientGroup.eq]
      simpa using (CFSG.perfectResidual P).inv_mem hd
    apply eq_one_of_pow_eq_one_of_pow_two_pow hp hp2 (k := j)
    · rw [← QuotientGroup.mk_pow, hxp]
      rfl
    · rw [h1, ← QuotientGroup.mk_pow, hj']
      rfl
  exact (QuotientGroup.eq_one_iff x).mp hq

theorem exists_surj_coprime_ker_of_levi {P M L : Type*} [Group P] [Finite P] [Group M] [Finite M]
    [Group L] (β : P →* M) (hβ : IsPGroup 2 β.ker) (N : Subgroup M)
    (hDN : (CFSG.perfectResidual P).map β = N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (π : ↥N →* L) (hπ : Function.Surjective π) (hπk : ¬ p ∣ Nat.card π.ker) :
    ∃ φ : ↥(CFSG.perfectResidual P) →* L, Function.Surjective φ ∧ ¬ p ∣ Nat.card φ.ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hD : ∀ d : ↥(CFSG.perfectResidual P), β d ∈ N := fun d =>
    hDN ▸ Subgroup.mem_map_of_mem β d.2
  let βD : ↥(CFSG.perfectResidual P) →* ↥N :=
    (β.comp (CFSG.perfectResidual P).subtype).codRestrict N hD
  have hβD : Function.Surjective βD := by
    intro n
    have : (n : M) ∈ (CFSG.perfectResidual P).map β := hDN ▸ n.2
    obtain ⟨d, hd, hdn⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, Subtype.ext hdn⟩
  refine ⟨π.comp βD, hπ.comp hβD, fun hdvd => ?_⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(π.comp βD).ker) p hdvd
  set d : ↥(CFSG.perfectResidual P) := (y : ↥(CFSG.perfectResidual P)) with hdd
  have hdp : d ^ p = 1 := by
    have h1 : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
    exact congrArg Subtype.val h1
  have hd1 : π (βD d) = 1 := y.2
  have hdord : orderOf d = p := by
    rw [hdd, Subgroup.orderOf_coe, hy]
  have hβDd : βD d = 1 := by
    let e' : ↥π.ker := ⟨βD d, hd1⟩
    have he'p : e' ^ p = 1 := Subtype.ext (by
      show (βD d) ^ p = 1
      rw [← map_pow, hdp, map_one])
    have he'1 : e' = 1 := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one he'p) with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ orderOf_dvd_natCard e') hπk
    exact congrArg Subtype.val he'1
  have hdker : (d : P) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val hβDd
    exact this
  have hdp' : (d : P) ^ p = 1 := congrArg Subtype.val hdp
  have hd0 : (d : P) = 1 :=
    eq_one_of_mem_ker_of_pow_eq_one β hβ hp hp2 hdker hdp'
  have : d = 1 := Subtype.ext hd0
  rw [this, orderOf_one] at hdord
  exact hp.one_lt.ne hdord

theorem leviSurj_of_levi {X : Type} [Group X] [Finite X] {P : Subgroup X} {z : X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzP : z ∈ P) (hz : orderOf z = p)
    {M : Type} [Group M] [Finite M] (β : ↥P →* M) (hβ : IsPGroup 2 β.ker)
    (N : Subgroup M) (hNr : N ≤ β.range) [hNn : (N.subgroupOf β.range).Normal]
    (hNperf : ⁅N, N⁆ = N) (hsolv : Group.IsSolvable (↥β.range ⧸ N.subgroupOf β.range))
    (hpN : ∀ x ∈ β.range, x ^ p = 1 → x ∈ N) {L : Type} [Group L] (π : ↥N →* L)
    (hπ : Function.Surjective π) (hπk : ¬ p ∣ Nat.card π.ker) (hL : IsSimpleGroup L)
    (hLn : ∃ a b : L, a * b ≠ b * a) (hpL : p ∣ Nat.card L) : LeviSurj p P z L := by
  have hDN : (CFSG.perfectResidual ↥P).map β = N :=
    map_perfectResidual_eq_of_levi β N hNr hNperf hsolv
  obtain ⟨φ₀, hφ₀s, hφ₀k⟩ := exists_surj_coprime_ker_of_levi β hβ N hDN hp hp2 π hπ hπk
  have hY : leviY P = (CFSG.perfectResidual ↥P).map P.subtype := leviY_eq_map_perfectResidual P
  let eD : ↥(CFSG.perfectResidual ↥P) ≃* ↥(leviY P) :=
    (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hY.symm)
  have hx : orderOf (⟨z, hzP⟩ : ↥P) = p := by rw [Subgroup.orderOf_mk, hz]
  have hzD : (⟨z, hzP⟩ : ↥P) ∈ CFSG.perfectResidual ↥P :=
    mem_perfectResidual_of_levi β hβ N hDN hp hp2 hpN hx
  refine ⟨?_, φ₀.comp eD.symm.toMonoidHom, hφ₀s.comp eD.symm.surjective, ?_, hL, hLn, hpL⟩
  · rw [hY]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, hzD, rfl⟩
  · have hker : (φ₀.comp eD.symm.toMonoidHom).ker = φ₀.ker.map eD.toMonoidHom := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_map_equiv, MonoidHom.comp_apply]
      rfl
    rw [hker, Subgroup.card_map_of_injective eD.injective]
    exact hφ₀k

theorem leviSurj_of_levi_comm {X : Type} [Group X] [Finite X] {P : Subgroup X} {z : X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzP : z ∈ P) (hz : orderOf z = p)
    {M : Type} [Group M] [Finite M] (β : ↥P →* M) (hβ : IsPGroup 2 β.ker)
    (N : Subgroup M) (hNr : N ≤ β.range) (hNperf : ⁅N, N⁆ = N)
    (hab : ∀ x ∈ β.range, ∀ y ∈ β.range, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hpN : ∀ x ∈ β.range, x ^ p = 1 → x ∈ N) {L : Type} [Group L] (π : ↥N →* L)
    (hπ : Function.Surjective π) (hπk : ¬ p ∣ Nat.card π.ker) (hL : IsSimpleGroup L)
    (hLn : ∃ a b : L, a * b ≠ b * a) (hpL : p ∣ Nat.card L) : LeviSurj p P z L := by
  haveI := normal_subgroupOf_of_commutators hNr hab
  exact leviSurj_of_levi hp hp2 hzP hz β hβ N hNr hNperf
    (isSolvable_quotient_of_commutators hNr hab) hpN π hπ hπk hL hLn hpL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
