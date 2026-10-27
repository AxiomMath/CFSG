module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

variable {C : Type} [Group C]

theorem pow_odd_of_mul_self {v : C} (hv : v * v = 1) {k : ℕ} (hk : Odd k) : v ^ k = v := by
  obtain ⟨m, hm⟩ := hk
  rw [hm, pow_succ, pow_mul, sq, hv, one_pow, one_mul]

theorem mem_commutator_of_mem_commutator_subtype {L : Subgroup C} {g : ↥L} (hg : (g : C) ∈ ⁅L, L⁆) :
    g ∈ commutator ↥L := by
  have hmap : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    show Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⁅L, L⁆
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hg' : (g : C) ∈ (commutator ↥L).map L.subtype := by rw [hmap]; exact hg
  obtain ⟨c, hc, hcg⟩ := hg'
  have : c = g := Subtype.ext hcg
  rwa [this] at hc

theorem not_mem_commutator_of_abelian_sylow [Finite C] {L E : Subgroup C} {v : C}
    (hE : IsSylowOf 2 E L) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hvE : v ∈ E)
    (hvc : ∀ l ∈ L, l * v = v * l) (hv2 : v * v = 1) (hv1 : v ≠ 1) : v ∉ ⁅L, L⁆ := by
  intro hvK
  have hEL : E ≤ L := hE.le
  have hvL : v ∈ L := hEL hvE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hodd⟩ := isSylowOf_iff.1 hE
  set H : Subgroup L := E.subgroupOf L with hH
  let _ : CommGroup H := { (inferInstance : Group H) with
    mul_comm := fun a b => Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)) }
  let φ : H →* H := MonoidHom.id H
  have hidx : ¬ 2 ∣ H.index := hodd
  set vL : L := ⟨v, hvL⟩ with hvL_def
  have hvLH : vL ∈ H := hvE
  have htriv : MonoidHom.transfer φ vL = 1 := by
    have : vL ∈ (MonoidHom.transfer φ).ker :=
      Abelianization.commutator_subset_ker (MonoidHom.transfer φ)
        (mem_commutator_of_mem_commutator_subtype (g := vL) hvK)
    exact this
  have hcentral : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * vL ^ k * g₀ ∈ H → g₀⁻¹ * vL ^ k * g₀ = vL ^ k := by
    intro k g₀ _
    have hcomm' : ∀ c : L, c * vL = vL * c := fun c => Subtype.ext (hvc c c.2)
    have : Commute g₀ (vL ^ k) := (Commute.pow_right (hcomm' g₀) k)
    calc g₀⁻¹ * vL ^ k * g₀ = (vL ^ k) * g₀⁻¹ * g₀ := by rw [← this.inv_left.eq]
      _ = vL ^ k := by group
  have htr := MonoidHom.transfer_eq_pow φ vL hcentral
  rw [htriv] at htr
  have hodd' : Odd H.index := Nat.odd_iff.2 (by omega)
  have hvv : vL * vL = 1 := Subtype.ext hv2
  have hpow : vL ^ H.index = vL := pow_odd_of_mul_self hvv hodd'
  have h1 : (⟨vL ^ H.index, MonoidHom.transfer_eq_pow_aux vL hcentral⟩ : H) = 1 := by
    have := htr.symm
    simpa [φ] using this
  have h2 : vL ^ H.index = 1 := congrArg (fun x : H => (x : L)) h1
  rw [hpow] at h2
  exact hv1 (congrArg Subtype.val h2)


theorem le_sup_pPrimeCore_of_abelian_sylow [Finite C] {L E : Subgroup C} [L.Normal] {v : C}
    (hE : IsSylowOf 2 E L) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hvE : v ∈ E)
    (hvc : ∀ c : C, c * v = v * c) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (htrans : ∀ e ∈ E, e ≠ 1 → e ≠ v → ∃ c : C, c * e * c⁻¹ = e * v) :
    L ≤ E ⊔ pPrimeCore 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEL : E ≤ L := hE.le
  have hvK : v ∉ ⁅L, L⁆ :=
    not_mem_commutator_of_abelian_sylow hE hEcomm hvE (fun l _ => hvc l) hv2 hv1
  have hKn : (⁅L, L⁆ : Subgroup C).Normal := inferInstance
  have hEK : ∀ e ∈ E, e ∈ ⁅L, L⁆ → e = 1 := by
    intro e heE heK
    by_contra he1
    by_cases hev : e = v
    · exact hvK (hev ▸ heK)
    · obtain ⟨c, hc⟩ := htrans e heE he1 hev
      have h1 : e * v ∈ ⁅L, L⁆ := hc ▸ hKn.conj_mem e heK c
      have h2 : v ∈ ⁅L, L⁆ := by
        have : v = e⁻¹ * (e * v) := by group
        rw [this]; exact mul_mem (inv_mem heK) h1
      exact hvK h2
  obtain ⟨Q, hQ⟩ := hE.exists_sylow_eq_subgroupOf
  have hP : Subgroup.normalizer (Q : Subgroup L) ≤ Subgroup.centralizer (Q : Set L) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ E.subgroupOf L := by rw [← hQ]; exact hp
    have hnp : n * p * n⁻¹ ∈ E.subgroupOf L := by
      rw [← hQ]
      exact (Subgroup.mem_normalizer_iff.1 hn p).1 hp
    have hpE : (p : C) ∈ E := hp'
    have hnpE : ((n * p * n⁻¹ : L) : C) ∈ E := hnp
    have hcomm : (n : C) * (p : C) * (n : C)⁻¹ * (p : C)⁻¹ ∈ ⁅L, L⁆ := by
      have h1 : ⁅(n : C), (p : C)⁆ ∈ ⁅L, L⁆ := Subgroup.commutator_mem_commutator n.2 p.2
      simpa [commutatorElement_def] using h1
    have hmemE : (n : C) * (p : C) * (n : C)⁻¹ * (p : C)⁻¹ ∈ E := by
      have : (n : C) * (p : C) * (n : C)⁻¹ * (p : C)⁻¹ = ((n * p * n⁻¹ : L) : C) * (p : C)⁻¹ := by
        simp
      rw [this]
      exact E.mul_mem hnpE (E.inv_mem hpE)
    have h1 := hEK _ hmemE hcomm
    apply Subtype.ext
    have h2 : (n : C) * (p : C) * (n : C)⁻¹ = (p : C) := by
      have := mul_inv_eq_one.1 h1
      exact this
    show (p : C) * (n : C) = (n : C) * (p : C)
    calc (p : C) * (n : C) = ((n : C) * (p : C) * (n : C)⁻¹) * (n : C) := by rw [h2]
      _ = (n : C) * (p : C) := by group
  have hcompl := MonoidHom.ker_transferSylow_isComplement' Q hP
  set N : Subgroup L := (MonoidHom.transferSylow Q hP).ker with hN
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hQp : IsPGroup 2 ↥(Q : Subgroup L) := Q.isPGroup'
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hNodd : Odd (Nat.card N) := by
    have h1 : (Q : Subgroup L).index = Nat.card N := hcompl.index_eq_card
    have h2 : ¬ 2 ∣ (Q : Subgroup L).index := Q.not_dvd_index
    rw [← h1]
    exact Nat.odd_iff.2 (by omega)
  have hNidx : N.index = 2 ^ k := by
    rw [hcompl.symm.index_eq_card, hk]
  have hmem : ∀ l : L, Odd (orderOf l) → l ∈ N := by
    intro l hl
    have h1 : orderOf (QuotientGroup.mk' N l) ∣ orderOf l := orderOf_map_dvd _ _
    have h2 : orderOf (QuotientGroup.mk' N l) ∣ 2 ^ k := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' N l)
      have h' : Nat.card (↥L ⧸ N) = 2 ^ k := hNidx
      rwa [h'] at h
    have hcop : Nat.Coprime (2 ^ k) (orderOf l) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hl)
    have h3 : orderOf (QuotientGroup.mk' N l) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    have h4 : QuotientGroup.mk' N l = 1 := orderOf_eq_one_iff.1 h3
    exact (QuotientGroup.eq_one_iff _).1 h4
  set N' : Subgroup C := N.map L.subtype with hN'
  have hN'odd : Odd (Nat.card N') := by
    rw [hN', Subgroup.card_map_of_injective L.subtype_injective]
    exact hNodd
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    have hmemL : g * (n₀ : C) * g⁻¹ ∈ L := ‹L.Normal›.conj_mem _ n₀.2 g
    refine ⟨⟨g * (n₀ : C) * g⁻¹, hmemL⟩, ?_, rfl⟩
    apply hmem
    have hord : orderOf (g * (n₀ : C) * g⁻¹) = orderOf (n₀ : C) := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (n₀ : C)
      simpa [MulAut.conj_apply] using this
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk, hord, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn₀)
  have hN'le : N' ≤ pPrimeCore 2 C :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hN'n (Nat.coprime_two_left.2 hN'odd)
  intro l hl
  obtain ⟨⟨⟨n, hn⟩, ⟨q, hq⟩⟩, hnq⟩ := hcompl.2 ⟨l, hl⟩
  have hnq' : (n : C) * (q : C) = l := congrArg Subtype.val hnq
  have hqE : (q : C) ∈ E := by
    have : q ∈ E.subgroupOf L := by rw [← hQ]; exact hq
    exact this
  rw [← hnq', sup_comm]
  exact Subgroup.mul_mem_sup (hN'le ⟨n, hn, rfl⟩) hqE

end CFSG.GH74.GLS.Th2.P412
