module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement

section BarA

variable {G : Type} [Group G] [Finite G] {z : G}

theorem odd_card_ker_piC (z : G) : Odd (Nat.card (piC z).ker) := by
  rw [piC, QuotientGroup.ker_mk']
  exact CFSG.GH74.GLS.TwoThin.odd_card_pPrimeCore _

theorem eq_one_of_piC_eq_one_of_pow {a : ↥(Cz z)} {m : ℕ} (ha : orderOf a = 2 ^ m) (h : piC z a = 1) :
    a = 1 := by
  have hker : a ∈ (piC z).ker := h
  have hdvd : orderOf a ∣ Nat.card (piC z).ker := Subgroup.orderOf_dvd_natCard _ hker
  have hodd := odd_card_ker_piC z
  have hcop : Nat.Coprime (2 ^ m) (Nat.card (piC z).ker) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  rw [ha] at hdvd
  have h1 : 2 ^ m = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [← orderOf_eq_one_iff, ha, h1]


theorem imgBar_equiv_of_isPGroup49 {X : Subgroup G} (hX : IsPGroup 2 ↥X) (hXC : X ≤ Cz z) :
    Nonempty (↥X ≃* ↥(imgBar z X)) := by
  let φ : ↥(X.subgroupOf (Cz z)) →* CentralizerBar z := (piC z).comp (X.subgroupOf (Cz z)).subtype
  have hXa : IsPGroup 2 ↥(X.subgroupOf (Cz z)) := hX.comap_subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hXa) a
    have hm' : orderOf (a : ↥(Cz z)) = 2 ^ m := by rw [Subgroup.orderOf_coe]; exact hm
    exact Subtype.ext (eq_one_of_piC_eq_one_of_pow hm' ha)
  have hrange : φ.range = imgBar z X := by
    simp only [φ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨(Subgroup.subgroupOfEquivOfLe hXC).symm.trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩


theorem imgBar_inf_of_normal49 {S K : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hKn : (K.subgroupOf (Cz z)).Normal) : imgBar z S ⊓ imgBar z K = imgBar z (S ⊓ K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx.1
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 hx.2
    have hSa : IsPGroup 2 ↥(S.subgroupOf (Cz z)) := hS.comap_subtype
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hSa) ⟨a, ha⟩
    have hm' : orderOf a = 2 ^ m :=
      (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥(S.subgroupOf (Cz z)))).trans hm
    set o := b⁻¹ * a with ho
    have hker : o ∈ (piC z).ker := by
      rw [MonoidHom.mem_ker, ho, map_mul, map_inv, hba, inv_mul_cancel]
    have hbo : a = b * o := by rw [ho]; group
    have hb1 : QuotientGroup.mk' (K.subgroupOf (Cz z)) b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    have hmk : (QuotientGroup.mk' (K.subgroupOf (Cz z)) a) = QuotientGroup.mk' (K.subgroupOf (Cz z)) o := by
      rw [hbo, map_mul, hb1, one_mul]
    have hd1 : orderOf (QuotientGroup.mk' (K.subgroupOf (Cz z)) a) ∣ 2 ^ m := by
      rw [← hm']; exact orderOf_map_dvd _ a
    have hd2 : orderOf (QuotientGroup.mk' (K.subgroupOf (Cz z)) a) ∣ Nat.card (piC z).ker := by
      rw [hmk]
      exact (orderOf_map_dvd _ o).trans (Subgroup.orderOf_dvd_natCard _ hker)
    have hcop : Nat.Coprime (2 ^ m) (Nat.card (piC z).ker) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.2 (odd_card_ker_piC z))
    have h1 : orderOf (QuotientGroup.mk' (K.subgroupOf (Cz z)) a) = 1 := by
      have := Nat.dvd_gcd hd1 hd2
      rw [Nat.Coprime.gcd_eq_one hcop] at this
      exact Nat.dvd_one.1 this
    have hak : a ∈ K.subgroupOf (Cz z) :=
      (QuotientGroup.eq_one_iff a).1 (orderOf_eq_one_iff.1 h1)
    exact Subgroup.mem_map_of_mem _ (show a ∈ (S ⊓ K).subgroupOf (Cz z) from ⟨ha, hak⟩)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨Subgroup.mem_map_of_mem _ ha.1, Subgroup.mem_map_of_mem _ ha.2⟩


theorem eq_of_piC_eq49 {S : Subgroup G} (hS : IsPGroup 2 ↥S) {a b : ↥(Cz z)}
    (ha : a ∈ S.subgroupOf (Cz z)) (hb : b ∈ S.subgroupOf (Cz z)) (h : piC z a = piC z b) : a = b := by
  have hSa : IsPGroup 2 ↥(S.subgroupOf (Cz z)) := hS.comap_subtype
  have hab : a⁻¹ * b ∈ S.subgroupOf (Cz z) := mul_mem (inv_mem ha) hb
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hSa) ⟨a⁻¹ * b, hab⟩
  have hm' : orderOf (a⁻¹ * b) = 2 ^ m := (Subgroup.orderOf_coe (⟨a⁻¹ * b, hab⟩ : ↥(S.subgroupOf (Cz z)))).trans hm
  have h1 : piC z (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := eq_one_of_piC_eq_one_of_pow hm' h1
  exact (inv_mul_eq_one.1 h2)

theorem imgBar_inf_centralizer49 {S K : Subgroup G} (hK : IsPCompIn 2 (Cz z) K)
    (hKn : ∀ c ∈ Cz z, c ∈ normalizer (K : Set G)) :
    imgBar z S ⊓ centralizer (imgBar z K : Set (CentralizerBar z)) = imgBar z (S ⊓ cSec K) := by
  have hKC : K ≤ Cz z := hK.1
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx.1
    have hcent := Subgroup.mem_centralizer_iff.1 hx.2
    have hacs : (a : G) ∈ cSec K := by
      have haC : (a : G) ∈ Cz z := a.2
      refine ⟨hKn _ haC, TwoThin.mem_normalizer_pPrimeCoreOf (hKn _ haC), fun k hk => ?_⟩
      have hkm : piC z ⟨k, hKC hk⟩ ∈ imgBar z K := piC_mem_imgBar hKC hk
      have h1 := hcent _ hkm
      have hcx : ⁅k, (a : G)⁆ ∈ Cz z := by
        simp only [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hKC hk) haC) (inv_mem (hKC hk))) (inv_mem haC)
      have hOz : ⁅k, (a : G)⁆ ∈ Oz z := by
        refine (hatMk_eq_one_iff (Cz z) ⟨⁅k, (a : G)⁆, hcx⟩).1 ?_
        have e : (⟨⁅k, (a : G)⁆, hcx⟩ : ↥(Cz z)) = ⁅(⟨k, hKC hk⟩ : ↥(Cz z)), a⁆ := rfl
        rw [e, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 h1
      have hkc : ⁅k, (a : G)⁆ ∈ K := by
        have hn : (a : G) * k⁻¹ * (a : G)⁻¹ ∈ K :=
          (mem_normalizer_iff.1 (hKn _ haC) k⁻¹).1 (inv_mem hk)
        have e : ⁅k, (a : G)⁆ = k * ((a : G) * k⁻¹ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem hk hn
      exact CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf.Oz_inf_le hKC ⟨hkc, hOz⟩
    exact Subgroup.mem_map_of_mem _ (show a ∈ (S ⊓ cSec K).subgroupOf (Cz z) from ⟨ha, hacs⟩)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨Subgroup.mem_map_of_mem _ ha.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro w hw
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hw
    have haS : (a : G) ∈ cSec K := ha.2
    have hb' : (b : G) ∈ K := hb
    have hcs := haS.2.2 (b : G) hb'
    have hOz : ⁅(b : G), (a : G)⁆ ∈ Oz z := pPrimeCoreOf_le_Oz hK hcs
    have hcx : ⁅(b : G), (a : G)⁆ ∈ Cz z := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem b.2 a.2) (inv_mem b.2)) (inv_mem a.2)
    have h1 := (hatMk_eq_one_iff (Cz z) ⟨⁅(b : G), (a : G)⁆, hcx⟩).2 hOz
    have e : (⟨⁅(b : G), (a : G)⁆, hcx⟩ : ↥(Cz z)) = ⁅b, a⁆ := rfl
    rw [e, map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1

end BarA

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
