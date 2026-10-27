module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Thirteen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Reduction
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.LieType.SeitzGeneration.OuterQuotient

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux

open CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits
  CFSG.LieType.SeitzGeneration

section Tits


theorem conj_injective_titsD : Function.Injective (MulAut.conj : titsD →* MulAut titsD) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center titsD := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun a : MulAut titsD => a h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (calc g * h = (g * h * g⁻¹) * g := by group
      _ = h * g := by rw [h1]).symm
  rw [titsD_center, Subgroup.mem_bot] at hc
  exact hc

theorem false_of_commute_card_twentyfive {P : Subgroup titsD} (hP : Nat.card P = 25) {u : titsD}
    (hu : orderOf u = 2) (hc : ∀ p ∈ P, p * u = u * p) : False := by
  have hle : P ≤ Subgroup.centralizer ({u} : Set titsD) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc p hp)
  have hdvd : 25 ∣ Nat.card (Subgroup.centralizer ({u} : Set titsD)) :=
    hP ▸ Subgroup.card_dvd_of_le hle
  rcases card_centralizer_of_involution hu with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem titsD_no_thirteen_centralizes_plane {y : titsD} (hy : orderOf y = 13)
    {P : Subgroup titsD} (hP : Nat.card P = 25) (hPy : ∀ x ∈ P, x * y = y * x) : False :=
  no_order_thirteen_centralizes_card_twentyfive card_titsD
    (fun u y hu hy hc => by
      have hyC : y ∈ Subgroup.centralizer ({u} : Set titsD) :=
        Subgroup.mem_centralizer_singleton_iff.2 hc.symm
      have h13 := orderOf_dvd_natCard (⟨y, hyC⟩ : Subgroup.centralizer ({u} : Set titsD))
      rw [Subgroup.orderOf_mk, hy] at h13
      rcases card_centralizer_of_involution hu with h | h <;> rw [h] at h13 <;>
        norm_num at h13)
    (fun x y hx hy hc => mul_ne_mul_of_orderOf hx (Or.inr rfl) hy hc) hy hP hPy

theorem mem_range_conj_of_fix_card_twentyfive {P : Subgroup titsD} (hP : Nat.card P = 25)
    (α : MulAut titsD) (hα : ∀ f ∈ P, α f = f) :
    α ∈ (MulAut.conj : titsD →* MulAut titsD).range := by
  obtain ⟨a, rfl⟩ := titsConj_surjective α
  have hcomm : ∀ p ∈ P, (a : Equiv.Perm (Fin 1755)) * p = p * a := by
    intro p hp
    have h := congrArg Subtype.val (hα p hp)
    rw [coe_titsConj_apply] at h
    calc (a : Equiv.Perm (Fin 1755)) * p = a * p * (a : Equiv.Perm (Fin 1755))⁻¹ * a := by group
      _ = p * a := by rw [h]
  have hpos : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hodd : ¬ 2 ∣ orderOf a := by
    intro h2
    set u := a ^ (orderOf a / 2) with hu
    have hu2 : orderOf u = 2 := orderOf_pow_orderOf_div hpos h2
    have huD : (u : Equiv.Perm (Fin 1755)) ∈ titsD :=
      titsA_involution_mem_D u.2 (by rw [Subgroup.orderOf_coe]; exact hu2)
    refine false_of_commute_card_twentyfive hP (u := ⟨u, huD⟩)
      (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hu2]) fun p hp => Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [hu, Subgroup.coe_pow]
    exact ((Commute.pow_left (show Commute (a : Equiv.Perm (Fin 1755)) p from hcomm p hp)
      _).eq).symm
  have hsq : a ^ 2 ∈ titsD.subgroupOf titsA := Subgroup.sq_mem_of_index_two titsD_index a
  obtain ⟨m, hm⟩ : ∃ m, orderOf a = 2 * m + 1 := ⟨orderOf a / 2, by omega⟩
  have hapow : a = (a ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf a + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have haD : a ∈ titsD.subgroupOf titsA := by
    rw [hapow]
    exact Subgroup.pow_mem _ hsq _
  change titsConj a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner titsD
  rw [← map_titsConj_titsD]
  exact Subgroup.mem_map_of_mem _ haD

theorem prime_dvd_card_titsD {q : ℕ} (hq : q.Prime) (h : q ∣ 17971200) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 13 := by
  have hN : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [hN] at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).1 h1 with h4 | h4
    · rcases (Nat.Prime.dvd_mul hq).1 h4 with h6 | h6
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h6))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
          (hq.dvd_of_dvd_pow h6)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1
        (hq.dvd_of_dvd_pow h4))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h1)))

theorem tits_five_faithful {P : Subgroup titsD} (hP : Nat.card P = 25) (g : MulAut titsD)
    (hg : Nat.Coprime 5 (orderOf g)) (hfix : ∀ x ∈ P, g x = x) : g = 1 := by
  obtain ⟨x, rfl⟩ := mem_range_conj_of_fix_card_twentyfive hP g hfix
  by_contra hne
  have hx1 : x ≠ 1 := fun h => hne (by rw [h, map_one])
  rw [orderOf_injective _ conj_injective_titsD x] at hg
  have hxP : ∀ f ∈ P, x * f = f * x := fun f hf => by
    have h := hfix f hf
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
    exact h
  have hx1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  set q := (orderOf x).minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hx1'
  have hqd : q ∣ orderOf x := Nat.minFac_dvd _
  set y := x ^ (orderOf x / q) with hydef
  have hyo : orderOf y = q := orderOf_pow_orderOf_div (orderOf_pos x).ne' hqd
  have hyP : ∀ f ∈ P, y * f = f * y := fun f hf =>
    (Commute.pow_left (show Commute x f from hxP f hf) _).eq
  have hqD : q ∣ 17971200 := by
    have := orderOf_dvd_natCard x
    rw [card_titsD] at this
    exact hqd.trans this
  rcases prime_dvd_card_titsD hq hqD with h | h | h | h
  · rw [h] at hyo
    exact false_of_commute_card_twentyfive hP hyo fun p hp => (hyP p hp).symm
  · rw [h] at hyo
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 (G := P) (by rw [hP]; norm_num)
    have hz5 : orderOf (z : titsD) = 5 := by rw [Subgroup.orderOf_coe]; exact hz
    exact mul_ne_mul_of_orderOf hyo (Or.inl rfl) hz5 (hyP z z.2)
  · rw [h] at hqd
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 5) hqd hg
  · rw [h] at hyo
    exact titsD_no_thirteen_centralizes_plane hyo hP fun p hp => (hyP p hp).symm

theorem tits_three_faithful {P : Subgroup titsD} (hPe : IsElemAbelian 3 P) (hP : Nat.card P = 9)
    (g : MulAut titsD) (hg : Nat.Coprime 3 (orderOf g)) (hfix : ∀ x ∈ P, g x = x) : g = 1 :=
  faithful_of_forall_normalizer Nat.prime_three (noSignalizer hPe hP) g hg hfix

theorem le_conj_range_of_plane_titsD {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut titsD)} (hE : Nat.card E = p ^ 2) :
    E ≤ (MulAut.conj : titsD →* MulAut titsD).range :=
  le_inner_of_coprime_card_outer (by
    rw [hE, card_outer_titsD]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))

theorem isLocallyBalancedAbs_three_two_titsD :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 3 2 titsD :=
  isLocallyBalancedAbs_two_of_inner_faithful Nat.prime_three conj_injective_titsD
    (fun _ _ hE => le_conj_range_of_plane_titsD Nat.prime_three (by norm_num) hE)
    (fun _ hPe hP g hg hfix => tits_three_faithful hPe (by simpa using hP) g hg hfix)

theorem isLocallyBalancedAbs_five_two_titsD :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 5 2 titsD :=
  isLocallyBalancedAbs_two_of_inner_faithful Nat.prime_five conj_injective_titsD
    (fun _ _ hE => le_conj_range_of_plane_titsD Nat.prime_five (by norm_num) hE)
    (fun _ _ hP g hg hfix => tits_five_faithful (by simpa using hP) g hg hfix)

end Tits

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux
