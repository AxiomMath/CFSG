module

public import CFSG.Assembly.Defs
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

theorem exists_perfect_normal_sup_oddCore_eq_top
    (hperf : commutator (K ⧸ classicalInvolutionOddCore K) = ⊤) :
    ∃ P : Subgroup K, P.Normal ∧ ⁅P, P⁆ = P ∧ P ⊔ classicalInvolutionOddCore K = ⊤ := by
  obtain ⟨n, hn⟩ : ∃ n, derivedSeries K (n + 1) = derivedSeries K n := by
    obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (derivedSeries K)
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact ⟨a, le_antisymm (derivedSeries_antitone K (Nat.le_succ a))
        (h ▸ derivedSeries_antitone K (Nat.succ_le_of_lt h1))⟩
    · exact ⟨b, le_antisymm (derivedSeries_antitone K (Nat.le_succ b))
        (h.symm ▸ derivedSeries_antitone K (Nat.succ_le_of_lt h1))⟩
  have hnormal : (derivedSeries K n).Normal := derivedSeries_normal K n
  refine ⟨derivedSeries K n, hnormal, ?_, ?_⟩
  · rw [← derivedSeries_succ, hn]
  · have hπ : Function.Surjective (QuotientGroup.mk' (classicalInvolutionOddCore K)) :=
      QuotientGroup.mk'_surjective _
    have htop : ∀ m, derivedSeries (K ⧸ classicalInvolutionOddCore K) m = ⊤ := by
      intro m
      induction m with
      | zero => exact derivedSeries_zero _
      | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact hperf
    have hmap := map_derivedSeries_eq hπ n
    rw [htop n] at hmap
    have := Subgroup.comap_map_eq (QuotientGroup.mk' (classicalInvolutionOddCore K))
      (derivedSeries K n)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm

theorem mem_of_mul_self_eq_one_of_sup_oddCore_eq_top (P : Subgroup K) [P.Normal]
    (hP : P ⊔ classicalInvolutionOddCore K = ⊤) {x : K} (hx : x * x = 1) : x ∈ P := by
  have hxmem : x ∈ (↑(P ⊔ classicalInvolutionOddCore K) : Set K) := by
    rw [hP]
    exact Subgroup.mem_top x
  rw [Subgroup.mul_normal P (classicalInvolutionOddCore K)] at hxmem
  obtain ⟨p, hp, o, ho, hxo⟩ := hxmem
  have h1 : (QuotientGroup.mk x : K ⧸ P) = QuotientGroup.mk o := by
    rw [← hxo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).mpr hp, one_mul]
  have h2 : orderOf (QuotientGroup.mk x : K ⧸ P) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_two, ← QuotientGroup.mk_mul, hx]
    rfl
  have hodd : Odd (Nat.card (classicalInvolutionOddCore K)) :=
    QuaternionStructure.odd_natCard_oddCore K
  have h3 : orderOf (QuotientGroup.mk x : K ⧸ P) ∣ Nat.card (classicalInvolutionOddCore K) := by
    rw [h1]
    exact (orderOf_map_dvd (QuotientGroup.mk' P) o).trans
      (Subgroup.orderOf_dvd_natCard _ ho)
  have hcop : Nat.Coprime 2 (Nat.card (classicalInvolutionOddCore K)) :=
    Nat.coprime_two_left.mpr hodd
  have h4 : orderOf (QuotientGroup.mk x : K ⧸ P) = 1 := by
    have := Nat.dvd_gcd h2 h3
    rwa [hcop, Nat.dvd_one] at this
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

theorem oddCore_eq_subgroupOf_of_normal (P : Subgroup K) [P.Normal] :
    classicalInvolutionOddCore P = (classicalInvolutionOddCore K).subgroupOf P := by
  apply le_antisymm
  · have hchar : (classicalInvolutionOddCore P).Characteristic := by
      change (CFSG.oddCore P).Characteristic
      rw [QuaternionStructure.oddCore_eq_pPrimeCore_two]
      infer_instance
    have hW : ((classicalInvolutionOddCore P).map P.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore P).map P.subtype)) := by
      rw [Subgroup.card_map_of_injective P.subtype_injective]
      exact QuaternionStructure.odd_natCard_oddCore P
    have hle : (classicalInvolutionOddCore P).map P.subtype ≤ classicalInvolutionOddCore K :=
      le_sSup ⟨hW, hodd⟩
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  · have hn : ((classicalInvolutionOddCore K).subgroupOf P).Normal := Subgroup.normal_subgroupOf
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore K).subgroupOf P)) := by
      have hdvd : Nat.card ((classicalInvolutionOddCore K).subgroupOf P) ∣
          Nat.card (classicalInvolutionOddCore K) := by
        let f : ↥((classicalInvolutionOddCore K).subgroupOf P) →* classicalInvolutionOddCore K :=
          (P.subtype.comp ((classicalInvolutionOddCore K).subgroupOf P).subtype).codRestrict
            (classicalInvolutionOddCore K) fun x => x.2
        refine Subgroup.card_dvd_of_injective f fun a b h => ?_
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
      exact Odd.of_dvd_nat (QuaternionStructure.odd_natCard_oddCore K) hdvd
    exact le_sSup ⟨hn, hodd⟩

theorem nonempty_oddCoreQuotientEquiv_of_sup_eq_top (P : Subgroup K) [P.Normal]
    (hP : P ⊔ classicalInvolutionOddCore K = ⊤) :
    Nonempty ((P ⧸ classicalInvolutionOddCore P) ≃* (K ⧸ classicalInvolutionOddCore K)) := by
  let φ : P →* K ⧸ classicalInvolutionOddCore K :=
    (QuotientGroup.mk' (classicalInvolutionOddCore K)).comp P.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : k ∈ (↑(P ⊔ classicalInvolutionOddCore K) : Set K) := by
      rw [hP]
      exact Subgroup.mem_top k
    rw [Subgroup.mul_normal P (classicalInvolutionOddCore K)] at hk
    obtain ⟨p, hp, o, ho, hko⟩ := hk
    refine ⟨⟨p, hp⟩, ?_⟩
    change (QuotientGroup.mk p : K ⧸ classicalInvolutionOddCore K) = QuotientGroup.mk k
    rw [← hko, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, mul_one]
  have hker : φ.ker = classicalInvolutionOddCore P := by
    rw [oddCore_eq_subgroupOf_of_normal P]
    ext x
    change (QuotientGroup.mk (x : K) : K ⧸ classicalInvolutionOddCore K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact Iff.rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CFSG.ClassicalInvolution
