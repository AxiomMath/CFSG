module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem normal_le_fusionOddCore_of_fixedPointFree {Y : Type*} [Group Y] [Finite Y]
    (S : Subgroup Y) [S.Normal] (t : Y) (ht : t * t = 1)
    (hfix : ∀ s ∈ S, t * s = s * t → s = 1) : S ≤ fusionOddCore Y := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hfpf : MonoidHom.FixedPointFree (MulAut.conjNormal (H := S) t) := by
    intro g hg
    have hg' : t * (g : Y) * t⁻¹ = g := congrArg Subtype.val hg
    rw [hti] at hg'
    have : t * (g : Y) = (g : Y) * t := by
      calc t * (g : Y) = (t * (g : Y) * t) * t := by rw [mul_assoc, mul_assoc, ht, mul_one]
        _ = (g : Y) * t := by rw [hg']
    exact Subtype.ext (hfix g g.2 this)
  have hinv : Function.Involutive (MulAut.conjNormal (H := S) t) := by
    intro g
    apply Subtype.ext
    show t * (t * (g : Y) * t⁻¹) * t⁻¹ = g
    rw [hti]
    calc t * (t * (g : Y) * t) * t = (t * t) * (g : Y) * (t * t) := by group
      _ = g := by rw [ht]; group
  have hodd : Odd (Nat.card S) := hfpf.odd_card_of_involutive hinv
  exact le_sSup ⟨inferInstance, hodd⟩

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

@[expose] def cQuot (C : Subgroup G) : Subgroup (egQD C) :=
  ((centralizer (C : Set G)).subgroupOf (normalizer (C : Set G))).map
    (QuotientGroup.mk' (C.subgroupOf (normalizer (C : Set G))))

omit [Finite G] in
theorem normal_centralizer_subgroupOf (C : Subgroup G) :
    ((centralizer (C : Set G)).subgroupOf (normalizer (C : Set G))).Normal := by
  refine ⟨fun x hx n => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  rw [mem_centralizer_iff] at hx ⊢
  intro c hc
  have hn := (n : normalizer (C : Set G)).2
  have h1 : (n : G)⁻¹ * c * (n : G) ∈ C := by
    have := (mem_normalizer_iff.1 (inv_mem hn) c).1 hc
    simpa using this
  have h2 := hx _ h1
  calc c * ((n : G) * (x : G) * (n : G)⁻¹)
      = (n : G) * (((n : G)⁻¹ * c * (n : G)) * (x : G)) * (n : G)⁻¹ := by group
    _ = (n : G) * ((x : G) * ((n : G)⁻¹ * c * (n : G))) * (n : G)⁻¹ := by rw [h2]
    _ = (n : G) * (x : G) * (n : G)⁻¹ * c := by group

omit [Finite G] in
theorem cQuot_normal (C : Subgroup G) : (cQuot C).Normal := by
  have := normal_centralizer_subgroupOf C
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

variable (h : Setup L A C z)
include h

theorem zt_mul_self : zt h * zt h = 1 := by
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.1 (orderOf_zt h).dvd

theorem le_centralizer_self : C ≤ centralizer (C : Set G) := fun c hc =>
  mem_centralizer_iff.2 fun c' hc' => h.hC.comm c' hc' c hc

theorem mem_A_of_mem_centralizer {l : G} (hlL : l ∈ L) (hl : l ∈ centralizer (C : Set G)) :
    l ∈ A :=
  h.hF.cent l hlL fun a ha => (mem_centralizer_iff.1 hl a (h.hC.A_le ha)).symm

theorem z_not_mem_centralizer : z ∉ centralizer (C : Set G) := by
  intro hz
  obtain ⟨a₁, ha₁, -, -, ha₁1, -⟩ := h.hF.orbits
  obtain ⟨c, hcC, hc⟩ := h.hC.onto a₁ ha₁
  have hcz : c * z = z * c := mem_centralizer_iff.1 hz c hcC
  apply ha₁1
  rw [← hc]
  calc z * c * z⁻¹ * c⁻¹ = (z * c) * z⁻¹ * c⁻¹ := rfl
    _ = (c * z) * z⁻¹ * c⁻¹ := by rw [hcz]
    _ = 1 := by group

theorem eq_one_of_comm {n : egQD C} (hn : n ∈ cQuot C) (hc : zt h * n = n * zt h) : n = 1 := by
  obtain ⟨m, hm, rfl⟩ := hn
  have hmC : (m : G) ∈ centralizer (C : Set G) := mem_subgroupOf.1 hm
  have hcent : QuotientGroup.mk' (C.subgroupOf (normalizer (C : Set G))) m ∈
      centralizer ({zt h} : Set (egQD C)) := mem_centralizer_singleton_iff.2 hc.symm
  rw [centralizer_quot_eq h] at hcent
  have hle : zpowers (zt h) ≤ centralizer ((psi h).range : Set (egQD C)) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => by
      obtain ⟨n, rfl⟩ := hy
      exact psi_comm h n
  obtain ⟨a, ⟨l, rfl⟩, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hcent
  have hlL : (l : G) ∈ L := (mem_inf.1 l.2).2
  rcases mem_zpowers_zt h hb with hb1 | hb1
  · rw [hb1, mul_one] at hab
    have h3 : (m : G)⁻¹ * (l : G) ∈ C := mem_subgroupOf.1 (QuotientGroup.eq.1 hab)
    have hlc : (l : G) ∈ centralizer (C : Set G) := by
      have : (l : G) = (m : G) * ((m : G)⁻¹ * (l : G)) := by group
      rw [this]
      exact mul_mem hmC (le_centralizer_self h h3)
    have hlA : (l : G) ∈ A := mem_A_of_mem_centralizer h hlL hlc
    have hmC' : (m : G) ∈ C := by
      have : (m : G) = (l : G) * ((m : G)⁻¹ * (l : G))⁻¹ := by group
      rw [this]
      exact mul_mem (h.hC.A_le hlA) (inv_mem h3)
    exact (QuotientGroup.eq_one_iff m).2 (mem_subgroupOf.2 hmC')
  · exfalso
    rw [hb1] at hab
    have h2 : (QuotientGroup.mk' (C.subgroupOf (normalizer (C : Set G))) m : egQD C) =
        QuotientGroup.mk (inclusion (egNL_le_normalizer_C h) l *
          ⟨z, z_mem_normalizer_C h⟩ : normalizer (C : Set G)) := hab
    have h3 : (m : G)⁻¹ * ((l : G) * z) ∈ C := mem_subgroupOf.1 (QuotientGroup.eq.1 h2)
    have hlzc : (l : G) * z ∈ centralizer (C : Set G) := by
      have : (l : G) * z = (m : G) * ((m : G)⁻¹ * ((l : G) * z)) := by group
      rw [this]
      exact mul_mem hmC (le_centralizer_self h h3)
    have hlA : (l : G) ∈ A := by
      refine h.hF.cent _ hlL fun a ha => ?_
      have h1 := mem_centralizer_iff.1 hlzc a (h.hC.A_le ha)
      have h2' : z * a = a * z := Quad.z_comm_A h.hs h.hAL ha
      have : a * l * z = l * a * z := by
        calc a * l * z = a * (l * z) := by group
          _ = l * z * a := h1
          _ = l * (z * a) := by group
          _ = l * (a * z) := by rw [h2']
          _ = l * a * z := by group
      exact (mul_right_cancel this).symm
    have hlc : (l : G) ∈ centralizer (C : Set G) := le_centralizer_self h (h.hC.A_le hlA)
    apply z_not_mem_centralizer h
    have : z = (l : G)⁻¹ * ((l : G) * z) := by group
    rw [this]
    exact mul_mem (inv_mem hlc) hlzc

theorem cQuot_le_oddCore : cQuot C ≤ fusionOddCore (egQD C) := by
  have := cQuot_normal C
  exact normal_le_fusionOddCore_of_fixedPointFree (cQuot C) (zt h) (zt_mul_self h)
    fun s hs hcomm => eq_one_of_comm h hs hcomm

end CSide

end CFSG.EvenSporadicStandard.M24Std
