module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem eq_one_of_odd_orderOf_of_mem_pCore {H : Type*} [Group H] [Finite H] {x : H}
    (hx : x ∈ CFSG.pCore 2 H) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hj0 : j = 0 := by
    by_contra hne
    have : Even (orderOf x) := by
      rw [hj]
      exact Nat.even_pow.2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.1 hj

theorem isPGroup_quotient_normalClosure_odd {H : Type*} [Group H] [Finite H] :
    IsPGroup 2 (H ⧸ Subgroup.normalClosure {g : H | Odd (orderOf g)}) := by
  intro x
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, b, hb, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf e) (orderOf_pos e).ne'
  refine ⟨a, ?_⟩
  have hord : orderOf (e ^ 2 ^ a) = b := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨b, hdec⟩, hdec,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hmem : e ^ 2 ^ a ∈ Subgroup.normalClosure {g : H | Odd (orderOf g)} :=
    Subgroup.subset_normalClosure (show Odd (orderOf (e ^ 2 ^ a)) from hord ▸ hb)
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 hmem

theorem perfect_of_isAltType_three [Finite Γ] {E : Subgroup Γ} (hshort : IsShort2 E)
    (hA : IsAltType E 3) : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E := by
  classical
  obtain ⟨α, hαs, hαk, -⟩ := hA
  have hcard : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hex : ∃ g : ↥E, Odd (orderOf g) ∧ α g ≠ 1 := by
    by_contra hne
    push Not at hne
    have hN : Subgroup.normalClosure {g : ↥E | Odd (orderOf g)} = ⊤ :=
      hshort.1 _ isPGroup_quotient_normalClosure_odd
    have hle : Subgroup.normalClosure {g : ↥E | Odd (orderOf g)} ≤ α.ker :=
      Subgroup.normalClosure_le_normal fun g hg => (MonoidHom.mem_ker).2 (hne g hg)
    rw [hN, top_le_iff] at hle
    have h1 : ∀ x : ↥(alternatingGroup (Fin 3)), x = 1 := by
      intro x
      obtain ⟨e, rfl⟩ := hαs x
      exact (MonoidHom.mem_ker.1 (hle ▸ Subgroup.mem_top e))
    have h2 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨g, hgodd, hαg⟩ := hex
  have hαg3 : α g ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(alternatingGroup (Fin 3))) (x := α g)
    rwa [hcard] at this
  have hg3 : g ^ 3 = 1 := by
    have h1 : g ^ 3 ∈ CFSG.pCore 2 ↥E := by
      rw [← hαk, MonoidHom.mem_ker, map_pow, hαg3]
    have h2 : Odd (orderOf (g ^ 3)) :=
      Odd.of_dvd_nat hgodd (orderOf_pow_dvd 3)
    exact eq_one_of_odd_orderOf_of_mem_pCore h1 h2
  have hord : orderOf (α g) = 3 := orderOf_eq_prime hαg3 hαg
  have hztop : Subgroup.zpowers (α g) = ⊤ := zpowers_eq_top_of_prime_card hcard hαg
  have hdecomp : ∀ e : ↥E, ∃ (q : ↥E) (k : ℤ), q ∈ CFSG.pCore 2 ↥E ∧ e = q * g ^ k := by
    intro e
    have : α e ∈ Subgroup.zpowers (α g) := hztop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    refine ⟨e * g ^ (-k), k, ?_, by rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]⟩
    rw [← hαk, MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, hk, mul_inv_cancel]
  set U : Subgroup ↥E := shortU ↥E with hU
  have hUnorm : U.Normal := by
    rw [hU]
    unfold shortU
    infer_instance
  have hUQ : U ≤ CFSG.pCore 2 ↥E := by
    have h1 : ⁅CFSG.pCore 2 ↥E, (⊤ : Subgroup ↥E)⁆ ≤ CFSG.pCore 2 ↥E :=
      Subgroup.commutator_le_left _ _
    exact h1
  set M : Subgroup ↥E := U ⊔ Subgroup.zpowers g with hM
  have hgM : g ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hconj : ∀ e : ↥E, e * g * e⁻¹ ∈ M := by
    intro e
    obtain ⟨q, j, hq, rfl⟩ := hdecomp e
    have h1 : (q * g ^ j) * g * (q * g ^ j)⁻¹ = ⁅q, g⁆ * g := by
      simp only [commutatorElement_def]
      group
    have h2 : ⁅q, g⁆ ∈ U :=
      Subgroup.commutator_mem_commutator hq (Subgroup.mem_top g)
    rw [h1]
    exact M.mul_mem (Subgroup.mem_sup_left h2) hgM
  have hMnorm : M.Normal := by
    refine ⟨fun n hn e => ?_⟩
    obtain ⟨u, hu, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hn
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h1 : e * (u * g ^ i) * e⁻¹ = (e * u * e⁻¹) * (e * g * e⁻¹) ^ i := by
      rw [conj_zpow]
      group
    rw [h1]
    exact M.mul_mem (Subgroup.mem_sup_left (hUnorm.conj_mem u hu e)) (M.zpow_mem (hconj e) i)
  have hMq : IsPGroup 2 (↥E ⧸ M) := by
    intro x
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, j, hq, rfl⟩ := hdecomp e
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥E)) ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hmk : (QuotientGroup.mk (q * g ^ j) : ↥E ⧸ M) = QuotientGroup.mk q := by
      rw [QuotientGroup.eq]
      simpa using M.zpow_mem hgM j
    rw [hmk, ← QuotientGroup.mk_pow, hk']
    rfl
  have hMtop : M = ⊤ := hshort.1 M hMq
  have hQU : CFSG.pCore 2 ↥E ≤ U := by
    intro q hq
    have hqM : q ∈ M := hMtop ▸ Subgroup.mem_top q
    obtain ⟨u, hu, k, hk, hqk⟩ := Subgroup.mem_sup_of_normal_left.1 hqM
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hgi : g ^ i ∈ CFSG.pCore 2 ↥E := by
      have h1 : g ^ i = u⁻¹ * q := by
        rw [← hqk]
        group
      rw [h1]
      exact (CFSG.pCore 2 ↥E).mul_mem ((CFSG.pCore 2 ↥E).inv_mem (hUQ hu)) hq
    have h3 : (3 : ℤ) ∣ i := by
      have h1 : α g ^ i = 1 := by
        rw [← map_zpow]
        exact (MonoidHom.mem_ker.1 (hαk ▸ hgi))
      have := orderOf_dvd_iff_zpow_eq_one.2 h1
      rwa [hord] at this
    have hgi1 : g ^ i = 1 := by
      obtain ⟨t, rfl⟩ := h3
      rw [zpow_mul]
      have : g ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg3]
      rw [this, one_zpow]
    rw [← hqk, hgi1, mul_one]
    exact hu
  have hQeq : (CFSG.pCore 2 ↥E).map E.subtype = pCoreOf 2 E := by
    rw [← CFSG.CGT.PushingUpLit.oTwoIn_eq_map, oTwoIn_eq_pCoreOf]
  rw [← map_shortU_eq_commutator E, ← hQeq]
  congr 1
  exact le_antisymm hUQ hQU

end CFSG.CGT.PushingUpLit.BHS6
