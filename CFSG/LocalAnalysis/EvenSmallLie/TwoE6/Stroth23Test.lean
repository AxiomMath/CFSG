module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23Field
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23Unitary
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23Levi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.GSide

attribute [local irreducible] nuU

noncomputable abbrev CX
    : Subgroup Eam := centralizer ({xhatEam} : Set Eam)

theorem coe_mem_P1
    {y : Eam} (hy : y ∈ CX) : (y : Dfull) ∈ P1 := by
  have hJ : (y : Dfull) ∈ Jhat := by
    rw [← centralizer_xhat, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
  exact ⟨hJ, Eam_le_centralizer y.2⟩

theorem mem_CX_of_mem_P1
    {d : Dfull} (hd : d ∈ P1) : (⟨d, Pc_le_Eam 0 hd⟩ : Eam) ∈ CX := by
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (xhat_comm_of_mem_Jhat (P1_le_Jhat hd))

@[expose] noncomputable def toP1 :
    CX →* P1 where
  toFun y := ⟨((y : Eam) : Dfull), coe_mem_P1 y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toP1_bijective :
    Function.Bijective toP1 :=
  ⟨fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun p : P1 => (p : Dfull)) h)),
    fun d => ⟨⟨⟨d, Pc_le_Eam 0 d.2⟩, mem_CX_of_mem_P1 d.2⟩, rfl⟩⟩

theorem natCard_CX
    : Nat.card CX = 77148607752437760 := by
  rw [Nat.card_congr (Equiv.ofBijective _ toP1_bijective), natCard_P1]

instance finite_CX :
    Finite CX := Nat.finite_of_card_ne_zero (by rw [natCard_CX]; norm_num)

@[expose] noncomputable def piX
    : CX →* Unitary.Usig := p1Proj.comp toP1

theorem piX_eq_one_iff
    (y : CX) : piX y = 1 ↔ ((y : Eam) : Dfull) ∈ N1 := by
  change toP1 y ∈ p1Proj.ker ↔ _
  rw [ker_p1Proj, mem_subgroupOf]
  rfl

theorem pow_eq_one_of_piX
    {t : CX} (ht : piX t = 1) : t ^ 2 ^ 22 = 1 := by
  have hN := (piX_eq_one_iff t).1 ht
  have h := pow_card_eq_one' (G := N1) (x := ⟨_, hN⟩)
  rw [natCard_N1] at h
  apply Subtype.ext
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  rw [SubmonoidClass.coe_pow] at h'
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  exact h'

set_option maxHeartbeats 8000000 in
theorem exists_nu1
    : ∃ ν : CX, orderOf ν = 11 ∧ nuU ∈ zpowers (piX ν) := by
  obtain ⟨g, hg⟩ := p1Proj_surjective nuU
  obtain ⟨ν₂, hν₂⟩ := toP1_bijective.2 g
  have hπ : piX ν₂ = nuU := by rw [piX, MonoidHom.comp_apply, hν₂, hg]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨ν₂ ^ 2 ^ 22, orderOf_eq_prime ?_ fun h => ?_, ?_⟩
  · have h11 : piX (ν₂ ^ 11) = 1 := by rw [map_pow, hπ, nuU_pow]
    rw [← pow_mul, mul_comm, pow_mul, pow_eq_one_of_piX h11]
  · have h1 := congrArg piX h
    rw [map_pow, hπ, map_one] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_nuU] at h2
    norm_num at h2
  · rw [map_pow, hπ]
    have e : nuU = (nuU ^ 2 ^ 22) ^ 3 := by
      rw [← pow_mul, ← pow_mod_orderOf, orderOf_nuU]
      norm_num
    exact mem_zpowers_iff.2 ⟨(3 : ℕ), by rw [zpow_natCast]; exact e.symm⟩

theorem mem_sigmaPerp_of_mem_N1
    {d : Dfull} (hd : d ∈ N1) (hE : d ∈ Ehat) :
    psiW ⟨d, hE⟩ ∈ Unitary.sigmaPerp := by
  rw [N1_eq_EU] at hd
  obtain ⟨h, hx⟩ := mem_EU.1 hd
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
  exact hx _ sigmaW_mem_sigLine

theorem eq_four_of_ker
    {ν n : CX} (hu : nuU ∈ zpowers (piX ν)) (hn : piX n = 1)
    (hc : n * ν = ν * n) :
    (n : Eam) = 1 ∨ (n : Eam) = cE' ∨ (n : Eam) = cE' * xhatEam ∨ (n : Eam) = xhatEam := by
  have hN : ((n : Eam) : Dfull) ∈ N1 := (piX_eq_one_iff n).1 hn
  have hE : ((n : Eam) : Dfull) ∈ Ehat := N1_le_Ehat hN
  have hJ : ((ν : Eam) : Dfull) ∈ Jhat := P1_le_Jhat (coe_mem_P1 ν.2)
  have hconj := psiW_conj hJ hE
  have hc' : ((n : Eam) : Dfull) * ((ν : Eam) : Dfull) =
      ((ν : Eam) : Dfull) * ((n : Eam) : Dfull) :=
    congrArg (fun z : CX => ((z : Eam) : Dfull)) hc
  have e1 : (⟨((ν : Eam) : Dfull)⁻¹ * ((n : Eam) : Dfull) * ((ν : Eam) : Dfull),
      conj_mem_Ehat hJ hE⟩ : Ehat) = ⟨_, hE⟩ := by
    apply Subtype.ext
    change ((ν : Eam) : Dfull)⁻¹ * ((n : Eam) : Dfull) * ((ν : Eam) : Dfull) = ((n : Eam) : Dfull)
    rw [mul_assoc, hc', ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e1] at hconj
  have hfix : wAct v0 ((piX ν : Unitary.Usig) : Kstab v0) (psiW ⟨_, hE⟩) = psiW ⟨_, hE⟩ :=
    hconj.symm
  have hσ : psiW ⟨_, hE⟩ ∈ sigLine := by
    rw [mem_sigLine]
    exact eq_zero_or_eq_sigmaW_of_fixed' hu (mem_sigmaPerp_of_mem_N1 hN hE) hfix
  have hmem : ((n : Eam) : Dfull) ∈ Subgroup.closure {xhat, cQ} := by
    rw [← EU_sigLine]
    exact mem_EU.2 ⟨hE, hσ⟩
  rcases mem_closure_xhat_cQ hmem with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem xhatEam_mul_self :
    xhatEam * xhatEam = 1 := by
  rw [← sq, ← orderOf_xhatEam, pow_orderOf_eq_one]

theorem four_props
    {n : CX}
    (h : (n : Eam) = 1 ∨ (n : Eam) = cE' ∨ (n : Eam) = cE' * xhatEam ∨ (n : Eam) = xhatEam) :
    n * n = 1 ∧ (∀ z : CX, n * z = z * n) ∧ (n : Eam) ∈ commutator Eam := by
  have hc : ∀ z : Eam, z * cE' = cE' * z := fun z => mem_center_iff.1 cE'_mem_center z
  have hx : ∀ z : CX, (z : Eam) * xhatEam = xhatEam * z := fun z =>
    mem_centralizer_singleton_iff.1 z.2
  refine ⟨Subtype.ext ?_, fun z => Subtype.ext ?_, ?_⟩
  · rcases h with h | h | h | h <;> rw [Subgroup.coe_mul, h, Subgroup.coe_one]
    · exact one_mul 1
    · exact cE'_mul_self
    · calc cE' * xhatEam * (cE' * xhatEam) = cE' * (xhatEam * cE') * xhatEam := by
            simp only [mul_assoc]
        _ = cE' * (cE' * xhatEam) * xhatEam := by rw [hc xhatEam]
        _ = cE' * cE' * (xhatEam * xhatEam) := by simp only [mul_assoc]
        _ = 1 := by rw [cE'_mul_self, xhatEam_mul_self, one_mul]
    · exact xhatEam_mul_self
  · rcases h with h | h | h | h <;> rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
    · rw [one_mul, mul_one]
    · exact (hc z).symm
    · calc cE' * xhatEam * (z : Eam) = cE' * (xhatEam * z) := mul_assoc _ _ _
        _ = cE' * (z * xhatEam) := by rw [← hx z]
        _ = cE' * z * xhatEam := (mul_assoc _ _ _).symm
        _ = z * cE' * xhatEam := by rw [← hc (z : Eam)]
        _ = z * (cE' * xhatEam) := mul_assoc _ _ _
    · exact (hx z).symm
  · rcases h with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact cE'_mem_commutator
    · exact mul_mem cE'_mem_commutator xhatEam_mem_commutator
    · exact xhatEam_mem_commutator

theorem commute_of_ker
    {ν n : CX} (hν : ν ^ 11 = 1) (hn : piX n = 1)
    (hN : n ∈ normalizer (zpowers ν : Set CX)) : n * ν = ν * n := by
  have h1 : n * ν * n⁻¹ ∈ zpowers ν := (mem_normalizer_iff.1 hN ν).1 (mem_zpowers ν)
  have h2 : n * ν * n⁻¹ * ν⁻¹ ∈ zpowers ν := mul_mem h1 (inv_mem (mem_zpowers ν))
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  have h11 : (n * ν * n⁻¹ * ν⁻¹) ^ 11 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hν, one_zpow]
  have hker : piX (n * ν * n⁻¹ * ν⁻¹) = 1 := by
    simp only [map_mul, map_inv, hn, one_mul, inv_one, mul_one, mul_inv_cancel]
  have h22 := pow_eq_one_of_piX hker
  have h1' : n * ν * n⁻¹ * ν⁻¹ = 1 := orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h11)
      (by norm_num : Nat.Coprime 11 (2 ^ 22))) (orderOf_dvd_of_pow_eq_one h22))
  have h2' : n * ν * n⁻¹ = ν := mul_inv_eq_one.1 h1'
  rw [mul_inv_eq_iff_eq_mul] at h2'
  exact h2'

section Identities

variable {G : Type*} [Group G]

theorem commute_mul_self_of_conj_inv {Y u : G} (hY : Y * u * Y⁻¹ = u⁻¹) : Commute (Y * Y) u := by
  have e1 : Y * Y * u * (Y * Y)⁻¹ = u := by
    calc Y * Y * u * (Y * Y)⁻¹ = Y * (Y * u * Y⁻¹) * Y⁻¹ := by group
      _ = Y * u⁻¹ * Y⁻¹ := by rw [hY]
      _ = (Y * u * Y⁻¹)⁻¹ := by group
      _ = u := by rw [hY, inv_inv]
  exact mul_inv_eq_iff_eq_mul.1 e1

theorem commute_mul_of_conj_inv {Y E u : G} (hE : E * u * E⁻¹ = u⁻¹) (hY : Y * u * Y⁻¹ = u⁻¹) :
    Commute (Y * E) u := by
  have e1 : Y * E * u * (Y * E)⁻¹ = u := by
    calc Y * E * u * (Y * E)⁻¹ = Y * (E * u * E⁻¹) * Y⁻¹ := by group
      _ = Y * u⁻¹ * Y⁻¹ := by rw [hE]
      _ = (Y * u * Y⁻¹)⁻¹ := by group
      _ = u := by rw [hY, inv_inv]
  exact mul_inv_eq_iff_eq_mul.1 e1

theorem two_pow_mul_self {Y : G} {k : ℕ} (h : Y ^ 2 ^ k = 1) : (Y * Y) ^ 2 ^ k = 1 := by
  rw [← sq, ← pow_mul, pow_mul', h, one_pow]

theorem inv_mul_mul_eq {Y E : G} (hEE : E * E = 1) (hYY : Y * Y = 1) {j : ℕ}
    (hm : (Y * E) ^ (2 * j + 1) = 1) :
    ((Y * E) ^ (j + 1))⁻¹ * Y * (Y * E) ^ (j + 1) = E := by
  have hEinvE : E⁻¹ = E := inv_eq_of_mul_eq_one_right hEE
  have hYinvY : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hYY
  have hED : E * (Y * E) * E⁻¹ = (Y * E)⁻¹ := by
    rw [hEinvE, mul_inv_rev, hEinvE, hYinvY]
    calc E * (Y * E) * E = E * Y * (E * E) := by group
      _ = E * Y := by rw [hEE, mul_one]
  have hRR : (Y * E) ^ (j + 1) * (Y * E) ^ (j + 1) = Y * E := by
    rw [← pow_add, show j + 1 + (j + 1) = 2 * j + 1 + 1 by omega, pow_succ, hm, one_mul]
  have hER : E * (Y * E) ^ (j + 1) * E⁻¹ = ((Y * E) ^ (j + 1))⁻¹ := by
    rw [← conj_pow, hED, inv_pow]
  obtain ⟨R, hR⟩ : ∃ R, (Y * E) ^ (j + 1) = R := ⟨_, rfl⟩
  rw [hR] at hRR hER ⊢
  have hY : Y = R * R * E := by rw [hRR, mul_assoc, hEE, mul_one]
  calc R⁻¹ * Y * R = R * (E * R * E⁻¹) * E := by rw [hY]; group
    _ = E := by rw [hER]; group

theorem mul_self_eq_one_of_conj {y e r z : G} (he : e * e = 1) (hz : z * z = 1)
    (hze : z * e = e * z) (h : r⁻¹ * y * r * e⁻¹ = z) : y * y = 1 := by
  have hy' : r⁻¹ * y * r = z * e := by rw [← h]; group
  have hy'2 : r⁻¹ * y * r * (r⁻¹ * y * r) = 1 := by
    rw [hy']
    calc z * e * (z * e) = z * (e * z) * e := by group
      _ = z * z * (e * e) := by rw [← hze]; group
      _ = 1 := by rw [hz, he, one_mul]
  calc y * y = r * (r⁻¹ * y * r * (r⁻¹ * y * r)) * r⁻¹ := by group
    _ = 1 := by rw [hy'2, mul_one, mul_inv_cancel]

theorem conj_mul_self_conj (g a : G) : g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by
  group

theorem inv_conj_conj (g a ν : G) :
    g⁻¹ * (g * a * g⁻¹ * ν * (g * a * g⁻¹)⁻¹) * g = a * (g⁻¹ * ν * g) * a⁻¹ := by
  group

theorem conj_inv_conj (g a : G) : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by
  group

theorem inv_mul_conj_mul (g ν : G) : g⁻¹ * (g * ν * g⁻¹) * g = ν := by
  group

theorem inv_conj_conj' (g y ν : G) :
    g⁻¹ * (y * (g * ν * g⁻¹) * y⁻¹) * g = (g⁻¹ * y * g) * ν * (g⁻¹ * y * g)⁻¹ := by
  group

end Identities

set_option maxHeartbeats 8000000 in
theorem mul_self_eq_one_core
    {ν e y : CX} (hu : nuU ∈ zpowers (piX ν)) (hν : ν ^ 11 = 1)
    (heE : (e : Eam) ∉ commutator Eam) (he2 : e * e = 1)
    (heN : e ∈ normalizer (zpowers ν : Set CX)) (hyN : y ∈ normalizer (zpowers ν : Set CX))
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) : y * y = 1 := by
  have hK : ∀ n ∈ normalizer (zpowers ν : Set CX), piX n = 1 →
      n * n = 1 ∧ (∀ z : CX, n * z = z * n) ∧ (n : Eam) ∈ commutator Eam :=
    fun n hn h1 => four_props (eq_four_of_ker hu h1 (commute_of_ker hν h1 hn))
  have hnorm : ∀ a ∈ normalizer (zpowers ν : Set CX), piX a * piX ν * (piX a)⁻¹ ∈
      zpowers (piX ν) := by
    intro a ha
    have h1 : a * ν * a⁻¹ ∈ zpowers ν := (mem_normalizer_iff.1 ha ν).1 (mem_zpowers ν)
    have h2 : piX (a * ν * a⁻¹) ∈ (zpowers ν).map piX := mem_map_of_mem _ h1
    rw [MonoidHom.map_zpowers] at h2
    simpa only [map_mul, map_inv] using h2
  obtain ⟨k, hk⟩ := hy2
  by_cases hY1 : piX y = 1
  · exact (hK y hyN hY1).1
  have hE1 : piX e ≠ 1 := fun h => heE (hK e heN h).2.2
  have hEE : piX e * piX e = 1 := by simp only [← map_mul, he2, map_one]
  have hY2 : piX y ^ 2 ^ k = 1 := by simp only [← map_pow, hk, map_one]
  have hν' : piX ν ^ 11 = 1 := by simp only [← map_pow, hν, map_one]
  have hnorm_e := hnorm e heN
  have hnorm_y := hnorm y hyN
  obtain ⟨u, hu_def⟩ : ∃ u, piX ν = u := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ E, piX e = E := ⟨_, rfl⟩
  obtain ⟨Y, hY_def⟩ : ∃ Y, piX y = Y := ⟨_, rfl⟩
  rw [hu_def] at hu hν' hnorm_e hnorm_y
  rw [hE_def] at hE1 hEE hnorm_e
  rw [hY_def] at hY1 hY2 hnorm_y
  have hu11 : orderOf u = 11 := by
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    refine orderOf_eq_prime hν' fun h => nuU_ne_one ?_
    rw [h, zpowers_one_eq_bot] at hu
    exact mem_bot.1 hu
  have hEinv : E * u * E⁻¹ = u⁻¹ :=
    conj_eq_inv_of_normalizes hu hu11 hnorm_e ⟨1, by rw [pow_one, sq, hEE]⟩ hE1
  have hYinv : Y * u * Y⁻¹ = u⁻¹ := conj_eq_inv_of_normalizes hu hu11 hnorm_y ⟨k, hY2⟩ hY1
  have hYY : Y * Y = 1 :=
    eq_one_of_commute hu (commute_mul_self_of_conj_inv hYinv) ⟨k, two_pow_mul_self hY2⟩
  have hDu := commute_mul_of_conj_inv hEinv hYinv
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (Y * E)).ne'
  have hDm : (Y * E) ^ m = 1 := by
    refine eq_one_of_commute hu (hDu.pow_left m) ⟨a, ?_⟩
    rw [← pow_mul, Nat.mul_comm m, ← ho, pow_orderOf_eq_one]
  obtain ⟨j, rfl⟩ := hm
  have hRYR := inv_mul_mul_eq hEE hYY hDm
  have hrN : (y * e) ^ (j + 1) ∈ normalizer (zpowers ν : Set CX) :=
    pow_mem (mul_mem hyN heN) _
  have hzN : ((y * e) ^ (j + 1))⁻¹ * y * (y * e) ^ (j + 1) * e⁻¹ ∈
      normalizer (zpowers ν : Set CX) :=
    mul_mem (mul_mem (mul_mem (inv_mem hrN) hyN) hrN) (inv_mem heN)
  have hz1 : piX (((y * e) ^ (j + 1))⁻¹ * y * (y * e) ^ (j + 1) * e⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hY_def, hE_def, hRYR, mul_inv_cancel]
  obtain ⟨hzz, hzc, -⟩ := hK _ hzN hz1
  exact mul_self_eq_one_of_conj he2 hzz (hzc e) rfl

theorem factorization_natCard_CX
    : (Nat.card CX).factorization 11 = 1 := by
  rw [natCard_CX, show (77148607752437760 : ℕ) = 11 * 7013509795676160 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem eq_sylow_of_le
    [Fact (Nat.Prime 11)] {Q : Subgroup CX} (hQ : IsPGroup 11 Q)
    (hQ1 : Q ≠ ⊥) (P : Sylow 11 CX) (h : Q ≤ P) : Q = P := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hQ1 (Subgroup.eq_bot_of_card_eq Q (by rw [hn, pow_zero]))
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [P.card_eq_multiplicity, factorization_natCard_CX, hn, pow_one]
  exact Nat.le_self_pow hn0 11

theorem exists_conj_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (P P' : Sylow p M) :
    ∃ g : M, ∀ x : M, x ∈ (P : Subgroup M) ↔ g⁻¹ * x * g ∈ (P' : Subgroup M) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P' P
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem exists_conj_of_eleven
    {Q Q' : Subgroup CX} (hQ : IsPGroup 11 Q) (hQ1 : Q ≠ ⊥)
    (hQ' : IsPGroup 11 Q') (hQ'1 : Q' ≠ ⊥) :
    ∃ g : CX, ∀ x : CX, x ∈ Q ↔ g⁻¹ * x * g ∈ Q' := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨P', hP'⟩ := hQ'.exists_le_sylow
  rw [eq_sylow_of_le hQ hQ1 P hP, eq_sylow_of_le hQ' hQ'1 P' hP']
  exact exists_conj_sylow P P'

theorem conj_mem_zpowers_of {M : Type*} [Group M] {a ν : M} (h : a * ν * a⁻¹ ∈ zpowers ν)
    {x : M} (hx : x ∈ zpowers ν) : a * x * a⁻¹ ∈ zpowers ν := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← conj_zpow]
  exact zpow_mem h k

theorem mem_normalizer_zpowers {M : Type*} [Group M] [Finite M] {a ν : M}
    (h : a * ν * a⁻¹ ∈ zpowers ν) : a ∈ normalizer (zpowers ν : Set M) :=
  mem_normalizer_of_conj_mem fun _ hx => conj_mem_zpowers_of h hx

theorem isPGroup_zpowers {M : Type*} [Group M] {ν : M} (h : orderOf ν = 11) :
    IsPGroup 11 (zpowers ν) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem zpowers_ne_bot {M : Type*} [Group M] {ν : M} (h : orderOf ν = 11) : zpowers ν ≠ ⊥ :=
  fun h1 => by
    have h2 := Nat.card_zpowers ν
    rw [h1, Subgroup.card_bot, h] at h2
    norm_num at h2

theorem commutator_Eam_normal :
    (commutator Eam).Normal := by
  rw [commutator_def]
  infer_instance

theorem exists_outer_inverting_CX
    : ∃ e ν : CX, (e : Eam) ∉ commutator Eam ∧ e * e = 1 ∧
    orderOf ν = 11 ∧ e * ν * e⁻¹ ∈ zpowers ν := by
  obtain ⟨e₀, ν₀, he₀X, hν₀X, he₀E, he₀2, hν₀11, he₀ν₀⟩ := exists_outer_involution_inverting
  refine ⟨⟨e₀, he₀X⟩, ⟨ν₀, hν₀X⟩, he₀E, Subtype.ext he₀2,
    by rw [← Subgroup.orderOf_coe]; exact hν₀11, ?_⟩
  have e : (⟨e₀, he₀X⟩ : CX) * ⟨ν₀, hν₀X⟩ * (⟨e₀, he₀X⟩ : CX)⁻¹ = (⟨ν₀, hν₀X⟩ : CX)⁻¹ :=
    Subtype.ext he₀ν₀
  rw [e]
  exact inv_mem (mem_zpowers _)

theorem exists_outer_normalizing
    {ν₁ : CX} (hν₁11 : orderOf ν₁ = 11) :
    ∃ e₁ : CX, (e₁ : Eam) ∉ commutator Eam ∧ e₁ * e₁ = 1 ∧ e₁ * ν₁ * e₁⁻¹ ∈ zpowers ν₁ := by
  obtain ⟨e₀, ν₀, he₀E, he₀2, hν₀11, he₀ν⟩ := exists_outer_inverting_CX
  obtain ⟨g₀, hg₀⟩ := exists_conj_of_eleven (isPGroup_zpowers hν₁11) (zpowers_ne_bot hν₁11)
    (isPGroup_zpowers hν₀11) (zpowers_ne_bot hν₀11)
  refine ⟨g₀ * e₀ * g₀⁻¹, fun h => he₀E ?_, ?_, ?_⟩
  · have e1 : ((g₀ * e₀ * g₀⁻¹ : CX) : Eam) = (g₀ : Eam) * e₀ * (g₀ : Eam)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1] at h
    have h2 := commutator_Eam_normal.conj_mem _ h (g₀ : Eam)⁻¹
    rwa [conj_inv_conj] at h2
  · rw [conj_mul_self_conj, he₀2, mul_one, mul_inv_cancel]
  · rw [hg₀, inv_conj_conj]
    exact conj_mem_zpowers_of he₀ν ((hg₀ ν₁).1 (mem_zpowers ν₁))

theorem mem_commutator_of_pow_eleven
    {ν : Eam} (h : ν ^ 11 = 1) : ν ∈ commutator Eam := by
  have e : ν = ν ^ 6 * ν ^ 6 := by
    rw [← pow_add, show 6 + 6 = 11 + 1 from rfl, pow_succ, h, one_mul]
  rw [e]
  exact mul_self_mem_of_index_two short_F4_derived_standard_perfect_cover.1 _

theorem subgroupOf_props
    {Q : Subgroup Eam} (hQX : Q ≤ CX) (hQ11 : IsPGroup 11 Q)
    (hQ1 : Q ≠ ⊥) : IsPGroup 11 (Q.subgroupOf CX) ∧ Q.subgroupOf CX ≠ ⊥ := by
  refine ⟨hQ11.comap_of_injective CX.subtype Subtype.val_injective, fun h => hQ1 ?_⟩
  rw [eq_bot_iff]
  intro q hq
  have h1 : (⟨q, hQX hq⟩ : CX) ∈ Q.subgroupOf CX := hq
  rw [h, mem_bot] at h1
  exact (mem_bot).2 (congrArg Subtype.val h1)

theorem test_outer
    {Q : Subgroup Eam} (hQX : Q ≤ CX) {g ν₁ e₁ : CX}
    (hg : ∀ x : CX, x ∈ Q.subgroupOf CX ↔ g⁻¹ * x * g ∈ zpowers ν₁)
    (he₁E : (e₁ : Eam) ∉ commutator Eam) (he₁N : e₁ * ν₁ * e₁⁻¹ ∈ zpowers ν₁) :
    ∃ e ∈ centralizer ({xhatEam} : Set Eam), e ∉ commutator Eam ∧ ∀ q ∈ Q, e * q * e⁻¹ ∈ Q := by
  refine ⟨((g * e₁ * g⁻¹ : CX) : Eam), (g * e₁ * g⁻¹).2, fun h => he₁E ?_, fun q hq => ?_⟩
  · have e1 : ((g * e₁ * g⁻¹ : CX) : Eam) = (g : Eam) * (e₁ : Eam) * (g : Eam)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1] at h
    have h2 := commutator_Eam_normal.conj_mem _ h (g : Eam)⁻¹
    rwa [conj_inv_conj] at h2
  · obtain ⟨q', hq'⟩ : ∃ q' : CX, (q' : Eam) = q := ⟨⟨q, hQX hq⟩, rfl⟩
    have h1 : g⁻¹ * q' * g ∈ zpowers ν₁ := (hg q').1 (by rw [mem_subgroupOf, hq']; exact hq)
    have h3 : g * e₁ * g⁻¹ * q' * (g * e₁ * g⁻¹)⁻¹ ∈ Q.subgroupOf CX := by
      rw [hg, inv_conj_conj]
      exact conj_mem_zpowers_of he₁N h1
    rw [mem_subgroupOf] at h3
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hq'] using h3

theorem conj_normalizes
    {Q : Subgroup Eam} {g ν₁ y₀ : CX}
    (hg : ∀ x : CX, x ∈ Q.subgroupOf CX ↔ g⁻¹ * x * g ∈ zpowers ν₁)
    (hyN : ∀ q ∈ Q, (y₀ : Eam) * q * (y₀ : Eam)⁻¹ ∈ Q) :
    (g⁻¹ * y₀ * g) * ν₁ * (g⁻¹ * y₀ * g)⁻¹ ∈ zpowers ν₁ := by
  have h1 : g * ν₁ * g⁻¹ ∈ Q.subgroupOf CX := by
    rw [hg, inv_mul_conj_mul]
    exact mem_zpowers ν₁
  rw [mem_subgroupOf] at h1
  have h3 : y₀ * (g * ν₁ * g⁻¹) * y₀⁻¹ ∈ Q.subgroupOf CX := by
    rw [mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hyN _ h1
  rw [hg, inv_conj_conj'] at h3
  exact h3

theorem conj_two_pow {M : Type*} [Group M] {g y : M} {k : ℕ} (h : y ^ 2 ^ k = 1) :
    (g⁻¹ * y * g) ^ 2 ^ k = 1 := by
  have e : g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ := by rw [inv_inv]
  rw [e, conj_pow, h, mul_one, mul_inv_cancel]

theorem mul_self_of_conj_mul_self {M : Type*} [Group M] {g y : M}
    (h : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1) : y * y = 1 := by
  calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem test_two_elements
    {Q : Subgroup Eam} {g ν₁ e₁ : CX} (hu : nuU ∈ zpowers (piX ν₁))
    (hν₁ : ν₁ ^ 11 = 1) (hg : ∀ x : CX, x ∈ Q.subgroupOf CX ↔ g⁻¹ * x * g ∈ zpowers ν₁)
    (he₁E : (e₁ : Eam) ∉ commutator Eam) (he₁2 : e₁ * e₁ = 1)
    (he₁N : e₁ * ν₁ * e₁⁻¹ ∈ zpowers ν₁) {y : Eam} (hyX : y ∈ CX)
    (hyN : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) : y * y = 1 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : CX, (y₀ : Eam) = y := ⟨⟨y, hyX⟩, rfl⟩
  subst hy₀
  obtain ⟨k, hk⟩ := hy2
  have hk' : y₀ ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])
  have h := mul_self_eq_one_core hu hν₁ he₁E he₁2 (mem_normalizer_zpowers he₁N)
    (mem_normalizer_zpowers (conj_normalizes hg hyN)) ⟨k, conj_two_pow hk'⟩
  exact congrArg Subtype.val (mul_self_of_conj_mul_self h)

theorem rootElevenTest_xhatEam :
    RootElevenTest xhatEam := by
  obtain ⟨ν₁, hν₁11, hu⟩ := exists_nu1
  have hν₁ : ν₁ ^ 11 = 1 := by rw [← hν₁11, pow_orderOf_eq_one]
  obtain ⟨e₁, he₁E, he₁2, he₁N⟩ := exists_outer_normalizing hν₁11
  refine ⟨⟨ν₁, mem_commutator_of_pow_eleven (by rw [← Subgroup.coe_pow, hν₁, Subgroup.coe_one]),
    ν₁.2, by rw [Subgroup.orderOf_coe, hν₁11]⟩, fun Q hQX hQ11 hQ1 => ?_⟩
  obtain ⟨hQ', hQ'1⟩ := subgroupOf_props hQX hQ11 hQ1
  obtain ⟨g, hg⟩ := exists_conj_of_eleven hQ' hQ'1 (isPGroup_zpowers hν₁11)
    (zpowers_ne_bot hν₁11)
  exact ⟨test_outer hQX hg he₁E he₁N, fun y hyX hyN hy2 =>
    test_two_elements hu hν₁ hg he₁E he₁2 he₁N hyX hyN hy2⟩

end CFSG.EvenSmallLie.TwoE6
