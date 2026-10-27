module

public import CFSG.Assembly.DichotomyDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

open scoped commutatorElement

namespace CFSG.Assembly.Dichotomy

namespace CentralizerContainment

instance pCore_normal_assembly (p : ℕ) (X : Type*) [Group X] : (pCore p X).Normal := by
  exact CFSG.pCore_normal

theorem pCore_isPGroup_assembly (p : ℕ) (X : Type*) [Group X] : IsPGroup p (pCore p X) := by
  exact CFSG.pCore_isPGroup

theorem le_pCore_assembly {p : ℕ} {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hp : IsPGroup p N) : N ≤ pCore p X :=
  le_sSup ⟨hN, hp⟩

theorem eq_one_of_mem_of_odd_orderOf {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsPGroup 2 P) {x : X} (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hj
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem odd_orderOf_of_mem {X : Type*} [Group X] {Y : Subgroup X} (hY : Odd (Nat.card Y))
    {y : X} (hy : y ∈ Y) : Odd (orderOf y) :=
  Odd.of_dvd_nat hY (Subgroup.orderOf_dvd_natCard Y hy)

end CentralizerContainment

open CentralizerContainment

theorem central_involution_core_action_kernel {H : Type*} [Group H] [Finite H]
    (hchar : dichotomyCharP 2 H) {z : H} (hz : z ∈ Subgroup.center H) (hzo : orderOf z = 2) :
    z ∈ pCore 2 H ∧
      (∀ h : H, (∀ q ∈ pCore 2 H, ⁅q, h⁆ ∈ Subgroup.zpowers z) → h ∈ pCore 2 H) ∧
      ∀ A : Subgroup H, ⁅pCore 2 H, A⁆ ≤ Subgroup.zpowers z → A ≤ pCore 2 H := by
  set Q := pCore 2 H
  set N := Subgroup.zpowers z
  have hNcenter : N ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hz
  have hNnormal : N.Normal := Subgroup.normal_of_le_center hNcenter
  have hNcard : Nat.card N = 2 := (Nat.card_zpowers z).trans hzo
  have hNtwo : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by rw [hNcard, pow_one])
  have hNQ : N ≤ Q := le_pCore_assembly hNnormal hNtwo
  let π := QuotientGroup.mk' N
  let K : Subgroup H :=
    (Subgroup.centralizer ((Q.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N))).comap π
  have hQmap : (Q.map π).Normal :=
    (pCore_normal_assembly 2 H).map π (QuotientGroup.mk'_surjective N)
  have hKnormal : K.Normal := Subgroup.Normal.comap Subgroup.normal_centralizer π
  have hcomm (q h : H) : ⁅q, h⁆ ∈ N ↔ π q * π h = π h * π q := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).symm
  have hmemK (h : H) : h ∈ K ↔ ∀ q ∈ Q, ⁅q, h⁆ ∈ N := by
    change π h ∈ Subgroup.centralizer _ ↔ _
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hh q hq
      exact (hcomm q h).mpr (hh (π q) ⟨q, hq, rfl⟩)
    · rintro hh _ ⟨q, hq, rfl⟩
      exact (hcomm q h).mp (hh q hq)
  have hcentral (k : H) (hk : k ∈ K) (hodd : Odd (orderOf k)) :
      k ∈ Subgroup.centralizer (Q : Set H) := by
    let φ : MulAut Q := MulAut.conjNormal k
    let N' : Subgroup Q := N.subgroupOf Q
    have : N'.Normal := hNnormal.subgroupOf Q
    have hφ : φ ^ orderOf k = 1 := by
      change (MulAut.conjNormal k) ^ orderOf k = 1
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hcop : (orderOf k).Coprime (Nat.card N') := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ).toEquiv, hNcard]
      exact Nat.coprime_two_right.mpr hodd
    have hfix : ∀ n ∈ N', φ n = n := by
      intro n hn
      apply Subtype.ext
      change k * (n : H) * k⁻¹ = n
      rw [Subgroup.mem_center_iff.mp (hNcenter (Subgroup.mem_subgroupOf.mp hn)) k,
        mul_inv_cancel_right]
    have hdisp : ∀ q : Q, q⁻¹ * φ q ∈ N' := by
      intro q
      rw [Subgroup.mem_subgroupOf]
      have h1 := (hmemK k).mp hk (q : H)⁻¹ (Q.inv_mem q.2)
      have h2 : ((q⁻¹ * φ q : Q) : H) = ⁅(q : H)⁻¹, k⁆ := by
        rw [commutatorElement_def, inv_inv, Subgroup.coe_mul, MulAut.conjNormal_apply,
          Subgroup.coe_inv]
        simp only [mul_assoc]
      rw [h2]
      exact h1
    have hone := CFSG.SectionRank.Ccomm.coprime_automorphism_trivial_normal_factors N' φ
      (orderOf_pos k) hφ hcop hfix hdisp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' := congrArg (fun ψ : MulAut Q => ((ψ ⟨q, hq⟩ : Q) : H)) hone
    change k * q * k⁻¹ = q at hq'
    calc q * k = k * q * k⁻¹ * k := by rw [hq']
      _ = k * q := by rw [inv_mul_cancel_right]
  have hKtwo : IsPGroup 2 K := by
    intro g
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : H)).ne'
    have hdvd : b ∣ orderOf (g : H) := ⟨2 ^ a, by rw [hab, mul_comm]⟩
    have hdiv : orderOf (g : H) / b = 2 ^ a := by
      rw [hab, Nat.mul_div_cancel _ hb.pos]
    have horder : orderOf ((g : H) ^ 2 ^ a) = b := by
      rw [← hdiv]
      exact orderOf_pow_orderOf_div (orderOf_pos (g : H)).ne' hdvd
    have hmem : (g : H) ^ 2 ^ a ∈ K := K.pow_mem g.2 _
    have hQmem : (g : H) ^ 2 ^ a ∈ Q :=
      hchar (hcentral _ hmem (horder ▸ hb))
    have htriv := eq_one_of_mem_of_odd_orderOf (pCore_isPGroup_assembly 2 H) hQmem (horder ▸ hb)
    exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact htriv)⟩
  have hKQ : K ≤ Q := le_pCore_assembly hKnormal hKtwo
  refine ⟨hNQ (Subgroup.mem_zpowers z), fun h hh => hKQ ((hmemK h).mpr hh), ?_⟩
  intro A hA a ha
  exact hKQ ((hmemK a).mpr fun q hq => hA (Subgroup.commutator_mem_commutator hq ha))

end CFSG.Assembly.Dichotomy
