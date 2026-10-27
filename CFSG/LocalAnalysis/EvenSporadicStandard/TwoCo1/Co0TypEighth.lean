module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypEighthData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypTrace
public import CFSG.Monster.VisQuot.Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.B.TwoA.Census

theorem orderOf_negOneO_typ : orderOf negOneO = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negOneO_mul_self) negOneO_ne_one

theorem natCard_latticeO_typ :
    Nat.card latticeO = 8315553613086720000 := by
  have h2 : Nat.card (Subgroup.zpowers negOneO) = 2 := by
    rw [Nat.card_zpowers, orderOf_negOneO_typ]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers negOneO), h2,
    show Nat.card (latticeO ⧸ Subgroup.zpowers negOneO) = 4157776806543360000 from natCard_OLq]

theorem finite_latticeO_typ :
    Finite latticeO :=
  Nat.finite_of_card_ne_zero (by rw [natCard_latticeO_typ]; norm_num)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (v : G)
    (hv : IsPGroup 2 (Subgroup.zpowers v)) :
    ∃ g : G, ∃ s ∈ (S : Subgroup G), g * s * g⁻¹ = v := by
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow hv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q₀
  have hvmem : v ∈ ((g • S : Sylow 2 G) : Subgroup G) := hg ▸ hQ₀ (Subgroup.mem_zpowers v)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hvmem
  obtain ⟨s, hs, rfl⟩ := hvmem
  exact ⟨g, s, hs, rfl⟩

@[expose] noncomputable def typSylowPerm : Subgroup AutPerm :=
  sylowSub.subgroupOf AutPerm

theorem mem_typSylowPerm {p : AutPerm} :
    p ∈ typSylowPerm ↔ (p : Equiv.Perm (Fin 24)) ∈ sylowSub := Iff.rfl

theorem natCard_typSylowPerm : Nat.card typSylowPerm = 1024 := by
  rw [typSylowPerm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowSub_le).toEquiv,
    (sylowSub_facts).1]

@[expose] noncomputable def typSylowO :
    Sylow 2 latticeO :=
  haveI := finite_latticeO_typ
  Sylow.ofCard (monoSub typSylowPerm) (by
    rw [card_monoSub, natCard_typSylowPerm, natCard_latticeO_typ,
      show (8315553613086720000 : ℕ) = 2 ^ 22 * 1982582476875 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
    norm_num)

theorem coe_typSylowO :
    (typSylowO : Subgroup latticeO) = monoSub typSylowPerm := by
  have := finite_latticeO_typ
  exact Sylow.coe_ofCard _ _

theorem no_eighth_root_wt12
    {a : C}
    (ha : hammingNorm (a : Fin 24 → ZMod 2) = 12) (v : latticeO) : v ^ 8 ≠ gO a := by
  intro hv
  have := finite_latticeO_typ
  have hv16 : v ^ 16 = 1 := by
    calc v ^ 16 = (v ^ 8) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hv, pow_two, gO_mul_self]
  have hp2 : IsPGroup 2 (Subgroup.zpowers v) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf v ∣ 2 ^ 4 from orderOf_dvd_of_pow_eq_one hv16)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨g, s, hs, hgs⟩ := exists_conj_mem_sylow typSylowO v hp2
  rw [coe_typSylowO] at hs
  obtain ⟨b, p, hp, rfl⟩ := hs
  obtain ⟨e, he, hwt⟩ := gO_mul_PO_pow_eight b p (mem_typSylowPerm.1 hp)
  have h8 : g * (gO b * PO p) ^ 8 * g⁻¹ = gO a := by rw [← hv, ← hgs, conj_pow]
  rw [he] at h8
  have htr := congrArg (fun x => (mat x).trace) h8
  simp only [trace_mat_conj, trace_mat_gO, ha] at htr
  rcases hwt with h | h <;> rw [h] at htr <;> norm_num at htr

end CFSG.EvenSporadicStandard.TwoCo1
