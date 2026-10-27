module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC37b
public import CFSG.Quasithin.H13.L32AC37c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H V₂ : Subgroup G}

theorem mem_centralizerMod_of_fix_H_F4 [IsMulCommutative ↥V] (S14 : L32NSet14.Setting_F4 G T L V V₂)
    {n : ℕ}
    {π : ↥H →* SpecialLinearGroup (Fin n) (ZMod 2)}
    {β : ↥(conjClosure V H) →* Multiplicative (Fin n → ZMod 2)}
    (hβker : β.ker = (fsuV1 T V).subgroupOf (conjClosure V H))
    (hβ : ∀ (k : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = k * x * (k : G)⁻¹ →
      β x' = Multiplicative.ofAdd (((π k : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (β x))))
    {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (haU : a ∈ conjClosure V H)
    {k : ↥H}
    (hk : ((π k : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      (Multiplicative.toAdd (β ⟨a, haU⟩)) = Multiplicative.toAdd (β ⟨a, haU⟩)) :
    (k : G) ∈ centralizerMod (fsuV1 T V) H V₂ := by
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hker : ∀ y : ↥(conjClosure V H), β y = 1 ↔ (y : G) ∈ fsuV1 T V := fun y => by
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  have hconjU : ∀ u ∈ conjClosure V H, (k : G) * u * (k : G)⁻¹ ∈ conjClosure V H :=
    fun u hu => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H k.2) u).mp hu
  have hfix : ∀ u (hu : u ∈ V₂), β ⟨(k : G) * u * (k : G)⁻¹, hconjU u (hVU (S14.hV2.2.1 hu))⟩ =
      β ⟨u, hVU (S14.hV2.2.1 hu)⟩ := by
    intro u hu
    rw [hβ k ⟨u, hVU (S14.hV2.2.1 hu)⟩
      ⟨(k : G) * u * (k : G)⁻¹, hconjU u (hVU (S14.hV2.2.1 hu))⟩ rfl]
    rcases S14.mem_V2_F4 ha haV hu with h | h
    · rw [(hker ⟨u, hVU (S14.hV2.2.1 hu)⟩).mpr h, toAdd_one, mulVec_zero, ofAdd_zero]
    · have hau : a * u ∈ conjClosure V H := mul_mem haU (hVU (S14.hV2.2.1 hu))
      have e : (⟨u, hVU (S14.hV2.2.1 hu)⟩ : ↥(conjClosure V H)) = ⟨a, haU⟩ * ⟨a * u, hau⟩ :=
        Subtype.ext (by
          show u = a * (a * u)
          rw [← mul_assoc, S14.mul_self_V_F4 (S14.hV2.2.1 ha), one_mul])
      rw [e, map_mul, (hker ⟨a * u, hau⟩).mpr h, mul_one, hk, ofAdd_toAdd]
  refine mem_centralizerMod.mpr ⟨k.2,
    Subgroup.mem_normalizer_fintype fun v hv => ?_, fun u hu => ?_⟩
  · have hv2 : v ∈ V₂ := S14.hV2.1 hv
    have h1 := hfix v hv2
    rw [(hker ⟨v, hVU (S14.hV2.2.1 hv2)⟩).mpr hv] at h1
    exact (hker _).mp h1
  · have hm : (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ conjClosure V H :=
      mul_mem (hconjU u (hVU (S14.hV2.2.1 hu))) (inv_mem (hVU (S14.hV2.2.1 hu)))
    have e : (⟨(k : G) * u * (k : G)⁻¹ * u⁻¹, hm⟩ : ↥(conjClosure V H)) =
        ⟨(k : G) * u * (k : G)⁻¹, hconjU u (hVU (S14.hV2.2.1 hu))⟩ *
          (⟨u, hVU (S14.hV2.2.1 hu)⟩)⁻¹ := rfl
    have h1 : β ⟨(k : G) * u * (k : G)⁻¹ * u⁻¹, hm⟩ = 1 := by
      rw [e, map_mul, map_inv, hfix u hu, mul_inv_cancel]
    exact (hker _).mp h1

theorem false_of_slSection_H_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂) {n : ℕ}
    {π : ↥H →* SpecialLinearGroup (Fin n) (ZMod 2)} (hπ : Function.Surjective π)
    {β : ↥(conjClosure V H) →* Multiplicative (Fin n → ZMod 2)}
    (hβker : β.ker = (fsuV1 T V).subgroupOf (conjClosure V H))
    (hβ : ∀ (k : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = k * x * (k : G)⁻¹ →
      β x' = Multiplicative.ofAdd (((π k : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (β x)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hVW : V ≤ conjClosure V (centralizerMod (fsuV1 T V) H V₂) := le_conjClosure _ _
  have hker : ∀ y : ↥(conjClosure V H), β y = 1 ↔ (y : G) ∈ fsuV1 T V := fun y => by
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  have haU : a ∈ conjClosure V H := hVU (hV2.2.1 ha)
  have hbU : b ∈ conjClosure V H := hVU hb
  have hw0 : Multiplicative.toAdd (β ⟨b, hbU⟩) ≠ 0 := fun h =>
    hbV (hV2.1 ((hker ⟨b, hbU⟩).mp (by rw [← ofAdd_toAdd (β ⟨b, hbU⟩), h, ofAdd_zero])))
  have hww : Multiplicative.toAdd (β ⟨b, hbU⟩) ≠ Multiplicative.toAdd (β ⟨a, haU⟩) := by
    intro h
    have hab : β (⟨a, haU⟩⁻¹ * ⟨b, hbU⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact (Multiplicative.toAdd.injective h).symm
    have h1 := (hker _).mp hab
    apply hbV
    have e : b = a * (a⁻¹ * b) := by group
    rw [e]
    exact mul_mem ha (hV2.1 h1)
  apply (lemma14_7_37_one_of_F4 h1222 h1332 h1334 h4 S hV2).ne
  refine le_antisymm (conjClosure_mono le_rfl (centralizerMod_le_left _ _ _)) fun x hx => ?_
  obtain ⟨g, hg2, hgw⟩ := exists_sl_fix_of_ne hw0 hww (Multiplicative.toAdd (β ⟨x, hx⟩))
  obtain ⟨k, rfl⟩ := hπ g
  have hkC := mem_centralizerMod_of_fix_H_F4 S14 hβker hβ ha haV haU hg2
  have hkb : (k : G) * b * (k : G)⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H k.2) b).mp hbU
  have hkbW : (k : G) * b * (k : G)⁻¹ ∈ conjClosure V (centralizerMod (fsuV1 T V) H V₂) :=
    mem_conjClosure hkC hb
  have hβkb := hβ k ⟨b, hbU⟩ ⟨_, hkb⟩ rfl
  obtain ⟨y, hyU, hyW, hy⟩ : ∃ y, ∃ hyU : y ∈ conjClosure V H,
      y ∈ conjClosure V (centralizerMod (fsuV1 T V) H V₂) ∧ β ⟨y, hyU⟩ = β ⟨x, hx⟩ := by
    rcases hgw with h | h
    · exact ⟨_, hkb, hkbW, by rw [hβkb, h, ofAdd_toAdd]⟩
    · refine ⟨b⁻¹ * ((k : G) * b * (k : G)⁻¹), mul_mem (inv_mem hbU) hkb,
        mul_mem (inv_mem (hVW hb)) hkbW, ?_⟩
      have e : (⟨b⁻¹ * ((k : G) * b * (k : G)⁻¹), mul_mem (inv_mem hbU) hkb⟩ :
          ↥(conjClosure V H)) = (⟨b, hbU⟩ : ↥(conjClosure V H))⁻¹ * ⟨_, hkb⟩ := rfl
      rw [e, map_mul, map_inv, hβkb, h, ofAdd_add, ofAdd_toAdd, ofAdd_toAdd, inv_mul_cancel_left]
  have hyx : β ((⟨y, hyU⟩ : ↥(conjClosure V H))⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  have h1 := (hker _).mp hyx
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact mul_mem hyW (hVW (Subgroup.mem_inf.mp h1).1)

end CFSG.Quasithin.H13.L32A.C
