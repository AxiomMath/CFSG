module

public import CFSG.GH74.Uniqueness.SU.SU7L193b

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L193

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem U_le_R (hc : Ctx19 S U M V x z A B R) : U ≤ R := by
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]; exact R.one_mem
  · have hu2 : u * u = 1 := by
      rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 u hu
    have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    exact (hc.c19.R_invol u hord).2 (Or.inl hu)

theorem fixed_le_core (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R)
    {Y : Subgroup G} (hYodd : Odd (Nat.card Y))
    (hRY : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y) {c : G} (hcY : c ∈ Y) (hcz : c * z = z * c) :
    c ∈ core z := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hcC : c ∈ C := mem_centralizer_iff.2 (fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcz.symm)
  obtain ⟨ψ, hψ, hker, hsc⟩ := L192.exists_surj_alt5_G hKI3 hKI4 hc
  have hOp := L192.op_eq hKI3 hKI4 hc
  have hodd : ∀ y ∈ Y, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard Y hy)
  have hOpMem : ∀ w : ↥C, w ∈ Op_p'p 2 ↥C → Odd (orderOf (w : G)) → w ∈ pPrimeCore 2 ↥C := by
    intro w hw hwodd
    refine Gen.odd_mem_pPrimeCore_of_mem_Op hw ?_
    rw [← Subgroup.orderOf_coe]; exact hwodd
  have hc' : (⟨c, hcC⟩ : ↥C) ∈ R.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
    apply hsc
    intro r hr
    have hrR : (r : G) ∈ R := hr
    have hrC : (r : G) ∈ C := r.2
    have hrz : (r : G) * z = z * r := RF.cent_comm hrC
    have hy : (r : G) * c⁻¹ * (r : G)⁻¹ ∈ Y := hRY r hrR c⁻¹ (Y.inv_mem hcY)
    have hcomm : c * (r : G) * c⁻¹ * (r : G)⁻¹ ∈ Y := by
      have e : c * (r : G) * c⁻¹ * (r : G)⁻¹ = c * ((r : G) * c⁻¹ * (r : G)⁻¹) := by group
      rw [e]; exact Y.mul_mem hcY hy
    have hmem : (⟨c, hcC⟩ : ↥C) * r * (⟨c, hcC⟩ : ↥C)⁻¹ * r⁻¹ ∈ Op_p'p 2 ↥C := by
      rw [hOp]
      have hrk : r ∈ R.subgroupOf C ⊔ pPrimeCore 2 ↥C := Subgroup.mem_sup_left hr
      have hn : (R.subgroupOf C ⊔ pPrimeCore 2 ↥C).Normal := by
        rw [← hOp]; infer_instance
      exact (R.subgroupOf C ⊔ pPrimeCore 2 ↥C).mul_mem (hn.conj_mem r hrk ⟨c, hcC⟩)
        ((R.subgroupOf C ⊔ pPrimeCore 2 ↥C).inv_mem hrk)
    exact hOpMem _ hmem (by
      show Odd (orderOf (c * (r : G) * c⁻¹ * (r : G)⁻¹))
      exact hodd _ hcomm)
  rw [← hOp] at hc'
  have hcodd : Odd (orderOf (⟨c, hcC⟩ : ↥C) ) := by
    rw [Subgroup.orderOf_mk]; exact hodd c hcY
  have := Gen.odd_mem_pPrimeCore_of_mem_Op hc' hcodd
  exact ⟨⟨c, hcC⟩, this, rfl⟩

theorem lemma193_c (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    (⨆ (Y : Subgroup G) (_ : Odd (Nat.card Y)) (_ : R ≤ normalizer (Y : Set G)), Y) =
      (pPrimeCore 2 ↥M).map M.subtype := by
  classical
  set O : Subgroup G := (pPrimeCore 2 ↥M).map M.subtype with hO
  have hOodd : Odd (Nat.card O) := by
    rw [hO, Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))
  apply le_antisymm
  · refine iSup_le fun Y => iSup_le fun hYodd => iSup_le fun hRY => ?_
    have hRY' : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y := fun r hr y hy =>
      (mem_normalizer_iff.1 (hRY hr) y).1 hy
    have hUY : U ≤ normalizer (Y : Set G) := fun u hu => hRY (U_le_R hc hu)
    obtain ⟨hYM, hcomm⟩ := lemma193_b hKI3 hKI4 hc Y hYodd hUY
    have hzU : z ∈ U := hc.c19.z_mem
    have hz2 : orderOf z = 2 := hc.conf.hz
    have hzT : z ∈ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl hzU
    have hzcore : core z ≤ O := lemma193_a hKI3 hc z hzT hz2
    have hOM : O ≤ M := Subgroup.map_subtype_le _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hzY : zpowers z ≤ normalizer (Y : Set G) := by
      rw [Subgroup.zpowers_le]; exact hUY hzU
    let _ : MulDistribMulAction ↥(zpowers z) ↥Y :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (zpowers z) Y hzY
    have : (zpowers z).Normalizes Y := ⟨hzY⟩
    have hsolv : Group.IsSolvable ↥Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hYodd
    have hcop : Nat.Coprime (Nat.card ↥Y) (Nat.card ↥(zpowers z)) := by
      rw [Nat.card_zpowers, hz2]
      exact Nat.coprime_two_right.2 hYodd
    obtain ⟨-, -, hfac, -⟩ :=
      CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization
        (A := ↥(zpowers z)) (H := ↥Y) hsolv hcop
    intro y hy
    obtain ⟨d, hd, c, hcfix, hyc⟩ := hfac ⟨y, hy⟩
    have hyeq : y = (d : G) * (c : G) := congrArg Subtype.val hyc
    have hdO : (d : G) ∈ O := by
      have hle : actionCommutator ↥(zpowers z) (⊤ : Subgroup ↥Y) ≤
          (⁅Y, U⁆).comap Y.subtype := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨k, -, a, rfl⟩
        show ((k⁻¹ * (a • k) : ↥Y) : G) ∈ ⁅Y, U⁆
        have e : ((k⁻¹ * (a • k) : ↥Y) : G) = ⁅(k : G)⁻¹, (a : G)⁆ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, commutatorElement_def]
          group
        rw [e]
        exact Subgroup.commutator_mem_commutator (Y.inv_mem k.2)
          (Subgroup.zpowers_le.2 hzU a.2)
      have := hle hd
      rw [Subgroup.mem_comap] at this
      exact hcomm this
    have hcz : (c : G) * z = z * c := by
      have h1 : (⟨z, Subgroup.mem_zpowers z⟩ : ↥(zpowers z)) • c = c :=
        hcfix ⟨z, Subgroup.mem_zpowers z⟩
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h2
      calc (c : G) * z = (z * c * z⁻¹) * z := by rw [h2]
        _ = z * c := by group
    have hcR : (c : G) ∈ core z := fixed_le_core hKI3 hKI4 hc hYodd hRY' c.2 hcz
    rw [hyeq]
    exact O.mul_mem hdO (hzcore hcR)
  ·
    have hRO : R ≤ normalizer (O : Set G) := by
      intro r hr
      apply Gen.mem_normalizer_of_conj_le
      intro w hw
      obtain ⟨m, hm, rfl⟩ := hw
      have hrM : r ∈ M := hc.conf.S_le (hc.c19.R_le hr)
      exact ⟨⟨r, hrM⟩ * m * ⟨r, hrM⟩⁻¹,
        (inferInstance : (pPrimeCore 2 ↥M).Normal).conj_mem m hm ⟨r, hrM⟩, rfl⟩
    exact le_iSup_of_le O (le_iSup_of_le hOodd (le_iSup_of_le hRO le_rfl))

end L193

end CFSG.GH74.Uniqueness.SU.SU7
