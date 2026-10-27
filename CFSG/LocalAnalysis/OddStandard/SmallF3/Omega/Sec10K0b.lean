module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10K0_decomp [Finite G] {L : Subgroup G} {z x : G}
    (hLC : L ⊓ centralizer (L : Set G) = ⊥) (hz : z ∈ L) (hxN : x ∈ normalizer (L : Set G))
    (hxz : x * z = z * x) (hodd : Odd (orderOf x))
    (hout : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ≤ 2) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G),
      x = l * c ∧ l * z = z * l ∧ Odd (orderOf l) ∧ Odd (orderOf c) := by
  have hle : L ⊔ centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (L : Set G))
  have hx : x ∈ L ⊔ centralizer (L : Set G) :=
    mem_of_odd_orderOf_of_relIndex_le_two hle hout hxN hodd
  have hcomm : ∀ l ∈ L, ∀ c ∈ centralizer (L : Set G), l * c = c * l :=
    fun l hl c hc => Subgroup.mem_centralizer_iff.mp hc l hl
  obtain ⟨l, hl, c, hc, hxc⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
  have hcl : Commute l c := hcomm l hl c hc
  have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z hz
  have hlz : l * z = z * l := by
    have h1 : (l * z) * c = (z * l) * c := by
      calc (l * z) * c = l * (z * c) := by rw [mul_assoc]
        _ = l * (c * z) := by rw [hcz]
        _ = (l * c) * z := by rw [mul_assoc]
        _ = x * z := by rw [← hxc]
        _ = z * x := hxz
        _ = z * (l * c) := by rw [hxc]
        _ = (z * l) * c := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hpair : l ^ orderOf x * c ^ orderOf x = 1 := by
    have h := hcl.mul_pow (orderOf x)
    rw [← h, ← hxc, pow_orderOf_eq_one x]
  have hcinv : c ^ orderOf x = (l ^ orderOf x)⁻¹ := eq_inv_of_mul_eq_one_right hpair
  have hinv : l ^ orderOf x = (c ^ orderOf x)⁻¹ := by rw [hcinv, inv_inv]
  have hlpow : l ^ orderOf x = 1 := by
    have hlL : l ^ orderOf x ∈ L := Subgroup.pow_mem L hl (orderOf x)
    have hcC : c ^ orderOf x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.pow_mem (Subgroup.centralizer (L : Set G)) hc (orderOf x)
    have hmem : l ^ orderOf x ∈ L ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hlL, by rw [hinv]; exact Subgroup.inv_mem (Subgroup.centralizer (L : Set G)) hcC⟩
    have hbot : l ^ orderOf x ∈ (⊥ : Subgroup G) := by rw [← hLC]; exact hmem
    simpa using hbot
  have hcpow : c ^ orderOf x = 1 := by rw [hcinv, hlpow, inv_one]
  exact ⟨l, hl, c, hc, hxc, hlz, Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hlpow),
    Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hcpow)⟩

theorem sec10K0_oddCore_le_centralizer [Finite G] {t z : G} {L : Subgroup G} (hL : IsPSp43 L)
    (hz : z ∈ L) (hz2 : orderOf z = 2) (hLle : L ≤ centralizer ({t} : Set G))
    (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (L : Set G) := by
  haveI : IsSimpleGroup ↥L := isSimpleGroup_of_isPSp43 hL
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hoX : o ∈ centralizer ({t} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ ho
  have hoN : o ∈ normalizer (L : Set G) := hN hoX
  have hoL : o * l * o⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hoN l).mp hl
  have hwL : o * l * o⁻¹ * l⁻¹ ∈ L := L.mul_mem hoL (L.inv_mem hl)
  have hlX : l ∈ centralizer ({t} : Set G) := hLle hl
  have hwO : o * l * o⁻¹ * l⁻¹ ∈ oddCoreIn (centralizer ({t} : Set G)) := by
    have h1 : o * (l * o⁻¹ * l⁻¹) ∈ oddCoreIn (centralizer ({t} : Set G)) :=
      mul_mem ho (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hlX (inv_mem ho))
    simpa [mul_assoc] using h1
  let M : Subgroup ↥L := (L ⊓ oddCoreIn (centralizer ({t} : Set G))).subgroupOf L
  have hMnormal : M.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact ⟨L.mul_mem (L.mul_mem hg hn.1) (L.inv_mem hg),
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (hLle hg) hn.2⟩
    · intro hn
      have hLn : g⁻¹ * (g * n * g⁻¹) * g = n := by group
      refine ⟨?_, ?_⟩
      · rw [← hLn]
        exact L.mul_mem (L.mul_mem (L.inv_mem hg) hn.1) hg
      · rw [← hLn]
        have h := CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
          (hLle (L.inv_mem hg)) hn.2
        rw [inv_inv] at h
        exact h
  haveI := hMnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
  · have hw1 : o * l * o⁻¹ * l⁻¹ = 1 := by
      have hmemM : (⟨o * l * o⁻¹ * l⁻¹, hwL⟩ : ↥L) ∈ M :=
        Subgroup.mem_subgroupOf.mpr ⟨hwL, hwO⟩
      rw [hM] at hmemM
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmemM)
    have hol : o * l = l * o := by
      have h1 : (o * l) * o⁻¹ = l := by
        have h2 : (o * l * o⁻¹) * l⁻¹ = 1 := hw1
        exact (mul_inv_eq_one).mp h2
      exact (mul_inv_eq_iff_eq_mul).mp h1
    exact hol.symm
  · exfalso
    have hzO : z ∈ oddCoreIn (centralizer ({t} : Set G)) := by
      have hzM : (⟨z, hz⟩ : ↥L) ∈ M := by rw [hM]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hzM).2
    have hdvd : orderOf z ∣ Nat.card (oddCoreIn (centralizer ({t} : Set G))) := by
      have h := orderOf_dvd_natCard (⟨z, hzO⟩ : ↥(oddCoreIn (centralizer ({t} : Set G))))
      rwa [Subgroup.orderOf_mk] at h
    have h2 : 2 ∣ Nat.card (oddCoreIn (centralizer ({t} : Set G))) := by
      simpa [hz2] using hdvd
    exact (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn _).not_two_dvd_nat h2

theorem sec10K0_mem_oddCoreIn [Finite G] {t c : G} {L : Subgroup G}
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G))))
    (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hc : c ∈ centralizer (L : Set G))
    (hct : c ∈ centralizer ({t} : Set G)) (hodd : Odd (orderOf c)) :
    c ∈ oddCoreIn (centralizer ({t} : Set G)) := by
  let C : Subgroup G := centralizer (L : Set G)
  let X : Subgroup G := centralizer ({t} : Set G)
  let D : Subgroup G := C ⊓ X
  have hDC : D ≤ C := inf_le_left
  have hcyc : ∀ P : Sylow 2 ↥D, IsCyclic (P : Subgroup ↥D) :=
    isCyclic_sylow_of_le hDC h102
  obtain ⟨N, hNodd, hNmem⟩ := exists_subgroup_odd_elems D hcyc
  have hforward : ∀ y ∈ X, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    have hnD : n ∈ D := ((hNmem n).mp hn).1
    have hnC : n ∈ centralizer (L : Set G) := hnD.1
    have hnX : n ∈ X := hnD.2
    have hord : orderOf (y * n * y⁻¹) = orderOf n := by
      have h := (MulAut.conj y).orderOf_eq n
      rwa [MulAut.conj_apply] at h
    refine (hNmem (y * n * y⁻¹)).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · change y * n * y⁻¹ ∈ centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hyl : y⁻¹ * l * y ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp (hN (X.inv_mem hy)) l).mp hl
        simpa using h
      have hcomm : (y⁻¹ * l * y) * n = n * (y⁻¹ * l * y) :=
        Subgroup.mem_centralizer_iff.mp hnC (y⁻¹ * l * y) hyl
      calc l * (y * n * y⁻¹) = y * ((y⁻¹ * l * y) * n) * y⁻¹ := by group
        _ = y * (n * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
        _ = (y * n * y⁻¹) * l := by group
    · exact X.mul_mem (X.mul_mem hy hnX) (X.inv_mem hy)
    · rw [hord]; exact ((hNmem n).mp hn).2
  have hNX : N ≤ X := fun n hn => ((hNmem n).mp hn).1.2
  have hNle : N ≤ oddCoreIn X := by
    refine CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hNX (fun y hy => ?_) hNodd
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨fun hn => hforward y hy n hn, fun hn => by
      have hmem := hforward y⁻¹ (X.inv_mem hy) (y * n * y⁻¹) hn
      have heq : y⁻¹ * (y * n * y⁻¹) * (y⁻¹)⁻¹ = n := by group
      rwa [heq] at hmem⟩
  exact hNle ((hNmem c).mpr ⟨⟨hc, hct⟩, hodd⟩)

end CFSG.OddStandard.SmallF3.Omega
