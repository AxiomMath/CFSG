module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8CaseTwo

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

namespace Std

variable {G : Type} [Group G] {L : Subgroup G} {W : Type} [Group W] [Finite W]
  {M : Child8Weyl W} (S : Std L M) {c : G}

theorem mul_s_mem {w : W} (hw : w ∉ M.Wp) : w * M.s ∈ M.Wp := (M.mem_or_mul_mem w).resolve_left hw

@[expose] noncomputable def extFun (c : G) (w : W) : G := by
  classical
  exact if hw : w ∈ M.Wp then S.phi ⟨w, hw⟩ else S.phi ⟨w * M.s, mul_s_mem hw⟩ * c

theorem extFun_of_mem {w : W} (hw : w ∈ M.Wp) : S.extFun c w = S.phi ⟨w, hw⟩ := by
  classical
  simp only [extFun, hw, ↓reduceDIte]

theorem extFun_of_not_mem {w : W} (hw : w ∉ M.Wp) :
    S.extFun c w = S.phi ⟨w * M.s, mul_s_mem hw⟩ * c := by
  classical
  simp only [extFun, hw, ↓reduceDIte]

theorem phi_mul_c (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x)) (x : M.Wp) :
    c * S.phi x = S.phi (M.sConj x) * c := by
  rw [← hc x]
  group

theorem extFun_mul (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x)) (hc1 : c * c = 1)
    (a b : W) : S.extFun c (a * b) = S.extFun c a * S.extFun c b := by
  have hss := M.s_mul_self
  by_cases ha : a ∈ M.Wp <;> by_cases hb : b ∈ M.Wp
  · rw [S.extFun_of_mem (mul_mem ha hb), S.extFun_of_mem ha, S.extFun_of_mem hb, ← map_mul]
    rfl
  · have hab : a * b ∉ M.Wp := fun h => hb (by simpa using mul_mem (inv_mem ha) h)
    rw [S.extFun_of_not_mem hab, S.extFun_of_mem ha, S.extFun_of_not_mem hb, ← mul_assoc,
      ← map_mul]
    congr 2
    exact Subtype.ext (mul_assoc a b M.s)
  · have hab : a * b ∉ M.Wp := fun h => ha (by simpa using mul_mem h (inv_mem hb))
    rw [S.extFun_of_not_mem hab, S.extFun_of_not_mem ha, S.extFun_of_mem hb,
      mul_assoc (S.phi ⟨a * M.s, mul_s_mem ha⟩) c, S.phi_mul_c hc, ← mul_assoc, ← map_mul]
    have e : (⟨a * b * M.s, mul_s_mem hab⟩ : M.Wp) =
        ⟨a * M.s, mul_s_mem ha⟩ * M.sConj ⟨b, hb⟩ := by
      apply Subtype.ext
      rw [coe_mul, M.coe_sConj, M.s_inv]
      change a * b * M.s = a * M.s * (M.s * b * M.s)
      calc a * b * M.s = a * (M.s * M.s) * b * M.s := by rw [hss, mul_one]
        _ = a * M.s * (M.s * b * M.s) := by group
    rw [e]
  · have hab : a * b ∈ M.Wp := by
      have h := mul_mem (mul_s_mem ha) (M.conj_mem (mul_s_mem hb) M.s)
      have e : a * M.s * (M.s * (b * M.s) * M.s⁻¹) = a * b := by
        calc a * M.s * (M.s * (b * M.s) * M.s⁻¹) = a * (M.s * M.s) * b := by group
          _ = a * b := by rw [hss, mul_one]
      rwa [e] at h
    rw [S.extFun_of_mem hab, S.extFun_of_not_mem ha, S.extFun_of_not_mem hb]
    have e : (⟨a * b, hab⟩ : M.Wp) =
        ⟨a * M.s, mul_s_mem ha⟩ * M.sConj ⟨b * M.s, mul_s_mem hb⟩ := by
      apply Subtype.ext
      rw [coe_mul, M.coe_sConj, M.s_inv]
      change a * b = a * M.s * (M.s * (b * M.s) * M.s)
      calc a * b = a * (M.s * M.s) * b * (M.s * M.s) := by rw [hss, mul_one, mul_one]
        _ = a * M.s * (M.s * (b * M.s) * M.s) := by group
    rw [e, map_mul, ← hc, inv_eq_of_mul_eq_one_right hc1]
    group

@[expose] noncomputable def extHom (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x))
    (hc1 : c * c = 1) : W →* G where
  toFun := S.extFun c
  map_one' := by rw [S.extFun_of_mem (one_mem _)]; exact map_one S.phi
  map_mul' := S.extFun_mul hc hc1

theorem extHom_injective (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x))
    (hc1 : c * c = 1) (hcL : c ∉ L) : Function.Injective (S.extHom hc hc1) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  change S.extFun c w = 1 at hw
  by_cases h : w ∈ M.Wp
  · rw [S.extFun_of_mem h] at hw
    exact congrArg Subtype.val (S.phi_injective (hw.trans (map_one S.phi).symm))
  · rw [S.extFun_of_not_mem h] at hw
    exact absurd (by rw [eq_inv_of_mul_eq_one_right hw]; exact inv_mem (S.phi_mem _)) hcL

theorem extHom_z (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x)) (hc1 : c * c = 1) :
    S.extHom hc hc1 M.z = S.zG :=
  S.extFun_of_mem M.z_mem

theorem mem_range_extHom (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x))
    (hc1 : c * c = 1) (hcN : c ∈ normalizer (L : Set G)) (g : G) :
    g ∈ (S.extHom hc hc1).range ↔ g * S.extHom hc hc1 M.z = S.extHom hc hc1 M.z * g := by
  rw [S.extHom_z, ← S.mem_normalizer_iff_comm]
  constructor
  · rintro ⟨w, rfl⟩
    change S.extFun c w ∈ normalizer (L : Set G)
    by_cases h : w ∈ M.Wp
    · rw [S.extFun_of_mem h]
      exact le_normalizer (S.phi_mem _)
    · rw [S.extFun_of_not_mem h]
      exact mul_mem (le_normalizer (S.phi_mem _)) hcN
  · intro hg
    rcases S.mem_or_mul_inv_mem hc hg with h | h
    · obtain ⟨x, rfl⟩ := S.exists_phi_eq h
      exact ⟨x, S.extFun_of_mem x.2⟩
    · obtain ⟨x, hx⟩ := S.exists_phi_eq h
      have hxs : (x : W) * M.s ∉ M.Wp := fun h' => M.s_not_mem (by
        simpa using mul_mem (inv_mem x.2) h')
      refine ⟨(x : W) * M.s, ?_⟩
      change S.extFun c ((x : W) * M.s) = g
      rw [S.extFun_of_not_mem hxs]
      have e : (⟨(x : W) * M.s * M.s, mul_s_mem hxs⟩ : M.Wp) = x :=
        Subtype.ext (by
          change (x : W) * M.s * M.s = x
          rw [mul_assoc, M.s_mul_self, mul_one])
      rw [e, hx]
      group

theorem mem_range_phi_iff {g : G} : g ∈ S.phi.range ↔ g ∈ L :=
  ⟨fun ⟨x, hx⟩ => hx ▸ S.phi_mem x, fun h => S.exists_phi_eq h⟩

end Std

theorem childO8PlusCover_of_child8Weyl
    {W : Type} [Group W] [Finite W] (M : Child8Weyl W) :
    ChildO8PlusCover := by
  intro G _ _ L hset hZ hZ2 hX
  have := hset.simple
  obtain ⟨S⟩ := exists_std M hset (card_center_eq_two hset hZ hZ2 hX) hX
  by_cases hN : ∃ h ∈ normalizer (L : Set G), h ∉ L
  · obtain ⟨c, hcN, hcL, hc⟩ := S.exists_outer hN
    rcases S.mul_self_eq hc with hc1 | hcz
    · exact M.false_of_case_two hset.nonab (S.extHom_injective hc hc1 hcL)
        (S.mem_range_extHom hc hc1 hcN)
    · refine M.toCaseThree.false_of (ψ := S.phi) (c := c) hc hcz S.phi_injective (fun g => ?_)
        hset.nonab (fun h => hcL (S.mem_range_phi_iff.1 h))
      change g * S.zG = S.zG * g ↔ _
      rw [← S.mem_normalizer_iff_comm, S.mem_range_phi_iff, S.mem_range_phi_iff]
      refine ⟨S.mem_or_mul_inv_mem hc, fun h => ?_⟩
      rcases h with h | h
      · exact le_normalizer h
      · have e : g = g * c⁻¹ * c := by group
        rw [e]
        exact mul_mem (le_normalizer h) hcN
  · push Not at hN
    refine M.toCaseOne.false_of hset.nonab S.phi_injective fun g => ?_
    change g ∈ S.phi.range ↔ g * S.zG = S.zG * g
    rw [← S.mem_normalizer_iff_comm, S.mem_range_phi_iff]
    exact ⟨fun h => le_normalizer h, hN g⟩

end CFSG.EvenSmallLie.OmegaEight.Child8
