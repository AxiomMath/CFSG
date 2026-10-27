module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Quotient

variable {C : Type*} [Group C] [Finite C]

theorem pPrimeCore_quotient_bot :
    CFSG.pPrimeCore 2 (C ⧸ CFSG.pPrimeCore 2 C) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  set O := CFSG.pPrimeCore 2 C with hO
  set π := QuotientGroup.mk' O with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hn : (K.comap π).Normal := hKn.comap π
  have h3 : (K.comap π).index = K.index := Subgroup.index_comap_of_surjective K hsurj
  have h1 := Subgroup.card_mul_index (K.comap π)
  have h2 := Subgroup.card_mul_index K
  have h4 : Nat.card C = Nat.card (C ⧸ O) * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hi : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card (K.comap π) = Nat.card K * Nat.card O := by
    have : Nat.card (K.comap π) * K.index = (Nat.card K * Nat.card O) * K.index := by
      calc Nat.card (K.comap π) * K.index = Nat.card C := by rw [← h3]; exact h1
        _ = Nat.card (C ⧸ O) * Nat.card O := h4
        _ = (Nat.card K * K.index) * Nat.card O := by rw [h2]
        _ = (Nat.card K * Nat.card O) * K.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hi this
  have hcop : Nat.Coprime 2 (Nat.card (K.comap π)) := by
    rw [hcard]
    exact Nat.Coprime.mul_right hKc (CFSG.pPrimeCore_coprime_card (p := 2) (G := C))
  have hle : K.comap π ≤ O := le_sSup ⟨hn, hcop⟩
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨c, rfl⟩ := hsurj k
  have hc : c ∈ O := hle hk
  exact (Subgroup.mem_bot).2 ((QuotientGroup.eq_one_iff c).2 hc)

end Quotient

section Roots

variable {C : Type*} [Group C]

theorem exists_sq_root_of_odd {O : Subgroup C} (hO : Odd (Nat.card O)) {o : C} (ho : o ∈ O) :
    ∃ m : ℤ, (o ^ m) * (o ^ m) = o := by
  have hdvd : orderOf o ∣ Nat.card O := by
    have := Subgroup.orderOf_dvd_natCard O ho
    exact this
  have hodd : Odd (orderOf o) := Odd.of_dvd_nat hO hdvd
  obtain ⟨j, hj⟩ := hodd
  refine ⟨((j + 1 : ℕ) : ℤ), ?_⟩
  rw [← zpow_add]
  have h2 : o ^ (orderOf o) = 1 := pow_orderOf_eq_one o
  have h3 : ((j + 1 : ℕ) : ℤ) + ((j + 1 : ℕ) : ℤ) = ((orderOf o + 1 : ℕ) : ℤ) := by
    rw [hj]; push_cast; ring
  rw [h3, zpow_natCast, pow_succ, h2, one_mul]

theorem exists_fixed_in_coset {O : Subgroup C} [O.Normal] (hO : Odd (Nat.card O)) {t x : C}
    (htt : t * t = 1) (hx : x⁻¹ * (t * x * t⁻¹) ∈ O) :
    ∃ h : C, t * h = h * t ∧ x⁻¹ * h ∈ O := by
  set o : C := x⁻¹ * (t * x * t⁻¹) with ho_def
  have hoO : o ∈ O := hx
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have e1 : t * x * t⁻¹ = x * o := by rw [ho_def]; group
  have e2 : t * (t * x * t⁻¹) * t⁻¹ = x := by
    rw [htinv]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [htt]; group
  have hto : t * o * t⁻¹ = o⁻¹ := by
    calc t * o * t⁻¹ = (t * x⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by rw [ho_def]; group
      _ = (t * x * t⁻¹)⁻¹ * x := by rw [e2]; group
      _ = (x * o)⁻¹ * x := by rw [e1]
      _ = o⁻¹ := by group
  obtain ⟨k, hk⟩ := exists_sq_root_of_odd hO hoO
  set m : C := o ^ k with hm
  have hmO : m ∈ O := zpow_mem hoO k
  have htm : t * m * t⁻¹ = m⁻¹ := by
    rw [hm, ← conj_zpow, hto, inv_zpow]
  refine ⟨x * m, ?_, by simpa using hmO⟩
  calc t * (x * m) = (t * x * t⁻¹) * (t * m * t⁻¹) * t := by group
    _ = (x * o) * m⁻¹ * t := by rw [e1, htm]
    _ = x * (m * m) * m⁻¹ * t := by rw [hm, hk]
    _ = x * m * t := by group

theorem exists_conj_of_odd {O : Subgroup C} [O.Normal] (hO : Odd (Nat.card O)) {a b : C}
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a⁻¹ * b ∈ O) :
    ∃ m ∈ O, m * a * m⁻¹ = b := by
  set o : C := a⁻¹ * b with ho_def
  have hoO : o ∈ O := hab
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hb : b = a * o := by rw [ho_def]; group
  have hao : a * o * a⁻¹ = o⁻¹ := by
    have h1 : (a * o) * (a * o) = 1 := by rw [← hb]; exact hbb
    calc a * o * a⁻¹ = a * o * a := by rw [hainv]
      _ = ((a * o) * (a * o)) * o⁻¹ := by group
      _ = o⁻¹ := by rw [h1]; group
  obtain ⟨k, hk⟩ := exists_sq_root_of_odd hO (O.inv_mem hoO)
  set m : C := o⁻¹ ^ k with hm
  have hmO : m ∈ O := zpow_mem (O.inv_mem hoO) k
  have ham : a * m * a⁻¹ = m⁻¹ := by
    rw [hm, ← conj_zpow]
    have : a * o⁻¹ * a⁻¹ = o := by
      calc a * o⁻¹ * a⁻¹ = (a * o * a⁻¹)⁻¹ := by group
        _ = o := by rw [hao]; group
    rw [this, inv_zpow, inv_inv]
  refine ⟨m, hmO, ?_⟩
  calc m * a * m⁻¹ = m * (a * m * a⁻¹)⁻¹ * a := by group
    _ = m * (m⁻¹)⁻¹ * a := by rw [ham]
    _ = (m * m) * a := by group
    _ = o⁻¹ * a := by rw [hm, hk]
    _ = (a * o * a⁻¹) * a := by rw [hao]
    _ = a * o := by group
    _ = b := hb.symm

end Roots

section Perm5

open Equiv Equiv.Perm

theorem perm5_normal_odd_bot (K : Subgroup (Equiv.Perm (Fin 5))) [K.Normal]
    (hK : Odd (Nat.card K)) : K = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hn : (K.subgroupOf (alternatingGroup (Fin 5))).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  ·
    have hinj : Function.Injective (fun k : K => Equiv.Perm.sign (k : Equiv.Perm (Fin 5))) := by
      intro k k' hkk
      have h1 : Equiv.Perm.sign ((k : Equiv.Perm (Fin 5)) * (k' : Equiv.Perm (Fin 5))⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have : Equiv.Perm.sign (k : Equiv.Perm (Fin 5)) =
            Equiv.Perm.sign (k' : Equiv.Perm (Fin 5)) := hkk
        rw [this]; simp
      have hA : (k : Equiv.Perm (Fin 5)) * (k' : Equiv.Perm (Fin 5))⁻¹ ∈
          alternatingGroup (Fin 5) := by
        rw [mem_alternatingGroup]; exact h1
      have hKk : (k : Equiv.Perm (Fin 5)) * (k' : Equiv.Perm (Fin 5))⁻¹ ∈ K :=
        K.mul_mem k.2 (K.inv_mem k'.2)
      have hmem : (⟨(k : Equiv.Perm (Fin 5)) * (k' : Equiv.Perm (Fin 5))⁻¹, hA⟩ :
          alternatingGroup (Fin 5)) ∈ K.subgroupOf (alternatingGroup (Fin 5)) := hKk
      rw [h, Subgroup.mem_bot] at hmem
      have : (k : Equiv.Perm (Fin 5)) * (k' : Equiv.Perm (Fin 5))⁻¹ = 1 :=
        congrArg Subtype.val hmem
      exact Subtype.ext (mul_inv_eq_one.1 this)
    have hle : Nat.card K ≤ 2 := by
      have := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card ℤˣ = 2 := by
        rw [Nat.card_eq_fintype_card]; decide
      omega
    have h1 : Nat.card K = 1 := by
      obtain ⟨j, hj⟩ := hK
      have : 0 < Nat.card K := Nat.card_pos
      omega
    exact Subgroup.eq_bot_of_card_eq K h1
  · exfalso
    have hA : alternatingGroup (Fin 5) ≤ K := by
      intro a ha
      have : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ K.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h]; exact Subgroup.mem_top _
      exact this
    have hdvd := Subgroup.card_dvd_of_le hA
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]; simp [Nat.card_eq_fintype_card, Nat.factorial]
    rw [h60] at hdvd
    obtain ⟨j, hj⟩ := hK
    omega

end Perm5

section HModelOdd

theorem normal_odd_hmodel (K : Subgroup HModel) [K.Normal] (hK : Odd (Nat.card K)) :
    ∀ x ∈ K, x.1 = 1 ∧ x.2.2 = 1 := by
  intro x hx
  constructor
  · have hn : (K.map (MonoidHom.fst (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5)))).Normal :=
      Subgroup.Normal.map inferInstance _ Prod.fst_surjective
    have hodd : Odd (Nat.card (K.map (MonoidHom.fst (DihedralGroup 4)
        (Z3 × Equiv.Perm (Fin 5))))) :=
      Odd.of_dvd_nat hK (Subgroup.card_map_dvd K _)
    have h8 : Nat.card (K.map (MonoidHom.fst (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5)))) ∣ 8 := by
      have := Subgroup.card_subgroup_dvd_card
        (K.map (MonoidHom.fst (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5))))
      rw [DihedralGroup.nat_card] at this
      simpa using this
    have h1 : Nat.card (K.map (MonoidHom.fst (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5)))) = 1 := by
      have hc : Nat.Coprime (Nat.card (K.map (MonoidHom.fst (DihedralGroup 4)
          (Z3 × Equiv.Perm (Fin 5))))) 8 := by
        have := (Nat.coprime_two_right.2 hodd).pow_right 3
        simpa using this
      exact Nat.Coprime.eq_one_of_dvd hc h8
    have hb := Subgroup.eq_bot_of_card_eq _ h1
    have hxm : x.1 ∈ K.map (MonoidHom.fst (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5))) :=
      ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at hxm
    exact hxm
  · let f : HModel →* Equiv.Perm (Fin 5) :=
      (MonoidHom.snd Z3 (Equiv.Perm (Fin 5))).comp (MonoidHom.snd (DihedralGroup 4) _)
    have hf : Function.Surjective f := fun σ => ⟨(1, 1, σ), rfl⟩
    have hn : (K.map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hodd : Odd (Nat.card (K.map f)) := Odd.of_dvd_nat hK (Subgroup.card_map_dvd K f)
    have hb := perm5_normal_odd_bot (K.map f) hodd
    have hxm : x.2.2 ∈ K.map f := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at hxm
    exact hxm

end HModelOdd

end CFSG.EvenSporadicStandard.TwoHS
