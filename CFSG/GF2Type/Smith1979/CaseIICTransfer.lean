module

public import CFSG.GF2Type.Smith1979.CaseIICParity
public import CFSG.GF2Type.Smith1979.CaseI25Nu
public import CFSG.GF2Type.Smith1979.CaseI25Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case2

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_NLbar_of_conj_le (C : Cons311 S g) {x : S.O} (hxM : x ∈ S.Mbar)
    (hx : ∀ h ∈ S.Lbar g, x⁻¹ * h * x ∈ normalizer (S.Lbar g : Set S.O)) : x ∈ NLbar S g := by
  refine ⟨hxM, ?_⟩
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (S.Mbar.inv_mem hxM)
  have hle : S.Lbar ((m : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    rw [Lbar_mul S m]
    rintro _ ⟨y, hy, rfl⟩
    have : (MulAut.conj (S.ρ m)).toMonoidHom y = x⁻¹ * y * x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hm, inv_inv]
    rw [this]
    exact hx y hy
  have heq := C.weaklyClosed m m.2 hle
  rw [Lbar_mul S m] at heq
  have hmn : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) := mem_normalizer_of_map_conj_eq heq
  rw [hm] at hmn
  simpa using (normalizer (S.Lbar g : Set S.O)).inv_mem hmn

section Main

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
include H C

theorem exists_hom_Mbar_of_nu (ν : NLbar S g →* Multiplicative (ZMod 2))
    (hν : ν ⟨t, CaseI25Transfer.mem_NLbar_of_mem_Lbar ht⟩ ≠ 1) :
    ∃ V : S.Mbar →* Multiplicative (ZMod 2), V (CaseI25Transfer.tM ht) ≠ 1 := by
  haveI : Finite S.Mbar := inferInstance
  obtain ⟨P, hsyl, -, hPN⟩ := CaseI25Transfer.exists_sylow_data H C ht
  set N : Subgroup S.Mbar := (NLbar S g).subgroupOf S.Mbar with hNdef
  have hPle : P ≤ N := fun x hx => Subgroup.mem_subgroupOf.mpr ⟨x.2, hPN x hx⟩
  have hodd : ¬ 2 ∣ N.index := by
    obtain ⟨-, -, hndvd⟩ := hsyl
    rw [Subgroup.relIndex_top_right] at hndvd
    intro h2
    exact hndvd (h2.trans (Subgroup.index_dvd_of_le hPle))
  let ϕ : N →* Multiplicative (ZMod 2) := CaseI25Transfer.nuOn ν N le_rfl
  have hc2 : (CaseI25Transfer.tM ht) ^ 2 = 1 :=
    Subtype.ext (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem ht)
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  have := S.isElementaryAbelian_Lbar H.conj_mem
  have hL2 : IsPGroup 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 (S.Lbar g)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hLM).symm
  have hcL : CaseI25Transfer.tM ht ∈ (S.Lbar g).subgroupOf S.Mbar :=
    Subgroup.mem_subgroupOf.mpr ht
  have hLc : ∀ h ∈ (S.Lbar g).subgroupOf S.Mbar,
      h * CaseI25Transfer.tM ht = CaseI25Transfer.tM ht * h := fun h hh =>
    Subtype.ext (Lbar_comm S H.conj_mem (Subgroup.mem_subgroupOf.mp hh) ht)
  have hwc : ∀ x : S.Mbar, (∀ h ∈ (S.Lbar g).subgroupOf S.Mbar, x⁻¹ * h * x ∈ N) → x ∈ N :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (mem_NLbar_of_conj_le C x.2 fun h hh =>
      (Subgroup.mem_subgroupOf.mp (hx ⟨h, hLM hh⟩ (Subgroup.mem_subgroupOf.mpr hh))).2)
  have hcN : CaseI25Transfer.tM ht ∈ N :=
    Subgroup.mem_subgroupOf.mpr (CaseI25Transfer.mem_NLbar_of_mem_Lbar ht)
  have hϕc : ϕ ⟨CaseI25Transfer.tM ht, hcN⟩ ≠ 1 := hν
  exact ⟨MonoidHom.transfer ϕ,
    Parity.transfer_ne_one_of_weakly_closed hodd ϕ hc2 hL2 hcL hLc hwc hcN hϕc⟩

theorem not_mem_commutator_Mbar_of_nu (ν : NLbar S g →* Multiplicative (ZMod 2))
    (hν : ν ⟨t, CaseI25Transfer.mem_NLbar_of_mem_Lbar ht⟩ ≠ 1) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  obtain ⟨V, hV⟩ := exists_hom_Mbar_of_nu H C ht ν hν
  intro hmem
  obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp hmem
  have hxc : x = CaseI25Transfer.tM ht := Subtype.ext hxt
  rw [hxc] at hx
  exact Parity.not_mem_commutator_of_hom V hV hx

end Main

section Kbar

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
include H

theorem exists_functional_of_Kbar (Kb : Subgroup S.O)
    (hKN : ∀ n ∈ NLbar S g, ∀ k ∈ Kb, n * k * n⁻¹ ∈ Kb) (htK : t ∉ Kb)
    (hLK : ∀ l ∈ S.Lbar g, l ∈ Kb ∨ t * l ∈ Kb) :
    ∃ f : S.Lbar g →* Multiplicative (ZMod 2),
      (∀ (n : NLbar S g) (l : S.Lbar g), f (Case25.conjLbar S g n l) = f l) ∧
        f ⟨t, ht⟩ ≠ 1 := by
  classical
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  let f : S.Lbar g → Multiplicative (ZMod 2) := fun l =>
    if (l : S.O) ∈ Kb then 1 else Multiplicative.ofAdd 1
  have hfK : ∀ l : S.Lbar g, (l : S.O) ∈ Kb → f l = 1 := fun l hl => by simp [f, hl]
  have hfnK : ∀ l : S.Lbar g, (l : S.O) ∉ Kb → f l = Multiplicative.ofAdd 1 :=
    fun l hl => by simp [f, hl]
  have hmul : ∀ a b : S.Lbar g, f (a * b) = f a * f b := by
    intro a b
    by_cases ha : (a : S.O) ∈ Kb <;> by_cases hb : (b : S.O) ∈ Kb
    · rw [hfK a ha, hfK b hb, hfK (a * b) (Kb.mul_mem ha hb), mul_one]
    · have hab : ((a * b : S.Lbar g) : S.O) ∉ Kb := fun h => hb (by
        have := Kb.mul_mem (Kb.inv_mem ha) h
        simpa using this)
      rw [hfK a ha, hfnK b hb, hfnK _ hab, one_mul]
    · have hab : ((a * b : S.Lbar g) : S.O) ∉ Kb := fun h => ha (by
        have := Kb.mul_mem h (Kb.inv_mem hb)
        simpa using this)
      rw [hfnK a ha, hfK b hb, hfnK _ hab, mul_one]
    · have hta : t * (a : S.O) ∈ Kb := (hLK a a.2).resolve_left ha
      have htb : t * (b : S.O) ∈ Kb := (hLK b b.2).resolve_left hb
      have h1 : (a : S.O) * t = t * (a : S.O) := Lbar_comm S H.conj_mem a.2 ht
      have e : (t * (a : S.O)) * (t * (b : S.O)) = (a : S.O) * (b : S.O) := by
        calc (t * (a : S.O)) * (t * (b : S.O)) = t * ((a : S.O) * t) * (b : S.O) := by group
          _ = t * (t * (a : S.O)) * (b : S.O) := by rw [h1]
          _ = (t * t) * (a : S.O) * (b : S.O) := by group
          _ = (a : S.O) * (b : S.O) := by rw [htt, one_mul]
      have hab : ((a * b : S.Lbar g) : S.O) ∈ Kb := by
        have : ((a * b : S.Lbar g) : S.O) = (a : S.O) * (b : S.O) := rfl
        rw [this, ← e]
        exact Kb.mul_mem hta htb
      rw [hfK _ hab, hfnK a ha, hfnK b hb]
      decide
  refine ⟨MonoidHom.mk' f hmul, fun n l => ?_, ?_⟩
  · have hiff : ∀ l : S.Lbar g, ((Case25.conjLbar S g n l : S.Lbar g) : S.O) ∈ Kb ↔
        (l : S.O) ∈ Kb := by
      intro l
      rw [Case25.coe_conjLbar]
      refine ⟨fun h => ?_, hKN n n.2 l⟩
      have := hKN n⁻¹ (inv_mem n.2) _ h
      simpa [mul_assoc] using this
    show f _ = f l
    by_cases hl : (l : S.O) ∈ Kb
    · rw [hfK l hl, hfK _ ((hiff l).mpr hl)]
    · rw [hfnK l hl, hfnK _ (fun h => hl ((hiff l).mp h))]
  · show f ⟨t, ht⟩ ≠ 1
    rw [hfnK ⟨t, ht⟩ htK]
    decide

end Kbar

section Final

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
include H C ht

theorem not_mem_commutator_Mbar_II (Kb : Subgroup S.O)
    (hKN : ∀ n ∈ NLbar S g, ∀ k ∈ Kb, n * k * n⁻¹ ∈ Kb) (htK : t ∉ Kb)
    (hLK : ∀ l ∈ S.Lbar g, l ∈ Kb ∨ t * l ∈ Kb) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  obtain ⟨f, hf, hft⟩ := exists_functional_of_Kbar H ht Kb hKN htK hLK
  obtain ⟨ν, hν⟩ := Case25.exists_nu_extending H C f hf
  refine not_mem_commutator_Mbar_of_nu H C ht ν ?_
  rw [hν t ht]
  exact hft

end Final

end Case2

end CFSG.GF2Type.Smith1979
