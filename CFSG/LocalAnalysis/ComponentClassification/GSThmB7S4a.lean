module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_center_of_normal {S N : Subgroup X} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN1 : N ≠ ⊥) :
    ∃ w ∈ N, w ≠ 1 ∧ ∀ t ∈ S, t * w = w * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hn : (N.subgroupOf S).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    simpa using hN g g.2 n hn
  have hne : N.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff]
    intro w hw
    have : (⟨w, hNS hw⟩ : ↥S) ∈ N.subgroupOf S := mem_subgroupOf.mpr hw
    rw [hbot, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hwN, hwZ⟩ := mem_inf.mp w.2
  refine ⟨((w : ↥S) : X), mem_subgroupOf.mp hwN, fun h1 => hw1 (Subtype.ext (Subtype.ext h1)),
    fun t ht => ?_⟩
  have := mem_center_iff.mp hwZ ⟨t, ht⟩
  exact congrArg Subtype.val this

namespace Setting

variable (s : Setting X)

theorem exists_c (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent) :
    ∃ c ∈ B0 s.h s.y, c * c = 1 ∧ s.h.a * c ∈ Lay s.h s.y := by
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨β, hβB, hβL, hβ0⟩ := d.hBL
  have hcL : ⁅β, d.y⁆ ∈ Lay d.h d.y := d.commutator_mem_L hβL
  have hc1 : ⁅β, d.y⁆ ≠ 1 := d.commutator_ne_one hβB hβ0
  have hcm : ⁅β, d.y⁆ ∈ ⁅d.h.B, zpowers d.y⁆ := commutator_mem_commutator hβB (mem_zpowers _)
  have haa := s.a_mul_a
  have hone : (1 : X) ∈ B0 s.h s.y := one_mem _
  rcases s.h61 with h1 | ⟨b, hb2, -, -, hbB0, -, hcomm, -⟩
  · change ⁅β, s.y⁆ ∈ ⁅s.h.B, zpowers s.y⁆ at hcm
    rw [h1] at hcm
    rcases eq_one_or_of_mem_zpowers s.h.orderOf_a hcm with h | h
    · exact absurd h hc1
    · refine ⟨1, hone, mul_one 1, ?_⟩
      rw [mul_one, ← h]
      exact hcL
  · have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hab : b * s.h.a = s.h.a * b := s.h.comm_a (s.B0_le_S hbB0)
    rcases Six.mem_closure_pair_cases haa hbb hab (hcomm hcm) with h | h | h | h
    · exact absurd h hc1
    · refine ⟨1, hone, mul_one 1, ?_⟩
      rw [mul_one, ← h]
      exact hcL
    · exfalso
      have hbL : b ∈ Lay s.h s.y := h ▸ hcL
      have := s.B0_inf_L ▸ mem_inf.mpr ⟨hbB0, hbL⟩
      rw [mem_bot.mp this, orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    · exact ⟨b, hbB0, hbb, h ▸ hcL⟩

theorem center_cases (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) {w : X} (hwS : w ∈ s.h.S) (hwZ : ∀ t ∈ s.h.S, t * w = w * t) :
    w = 1 ∨ w = s.h.a ∨ w = (s.toData hConj hComp hOut hCent).z ∨
      w = s.h.a * (s.toData hConj hComp hOut hCent).z := by
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨c, hc, hcc, hacL⟩ := s.exists_c hConj hComp hOut hCent
  obtain ⟨σ, hσS, -, hσ⟩ := d.hout c hc hcc hacL
  have hzS : d.z ∈ s.h.S := d.z_mem_S
  have hzz : d.z * d.z = 1 := d.z_mul_z
  have hPZ : ∀ v ∈ s.h.P, (∀ t ∈ s.h.S, t * v = v * t) → v = 1 ∨ v = s.h.a := by
    intro v hvP hvZ
    have hv : v ∈ s.h.P ⊓ centralizer (s.h.S : Set X) :=
      mem_inf.mpr ⟨hvP, mem_centralizer_iff.mpr hvZ⟩
    rw [s.hC] at hv
    exact eq_one_or_of_mem_zpowers s.h.orderOf_a hv
  rcases hσ w hwS (fun t ht => (hwZ t (s.h.D_le_S ht)).symm) (hwZ σ hσS).symm with h | h
  · rcases hPZ w h hwZ with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hzw : ∀ t ∈ s.h.S, t * (d.z * w) = d.z * w * t := fun t ht => by
      rw [← mul_assoc, d.hzS t ht, mul_assoc, hwZ t ht, mul_assoc]
    have hz' : d.z⁻¹ = d.z := inv_eq_of_mul_eq_one_right hzz
    rcases hPZ _ h hzw with h1 | h1
    · right; right; left
      rw [eq_inv_of_mul_eq_one_right h1, hz']
    · right; right; right
      calc w = d.z * (d.z * w) := by rw [← mul_assoc, hzz, one_mul]
        _ = s.h.a * d.z := by rw [h1, d.hzS _ s.h.a_mem_S]

theorem conj_mem_conjugate_P {g : X} (hg : g ∈ normalizer (s.h.S : Set X)) {t w : X}
    (ht : t ∈ s.h.S) (hw : w ∈ conjugate s.h.P g) : t * w * t⁻¹ ∈ conjugate s.h.P g := by
  rw [mem_conjugate_iff] at hw ⊢
  have htg : g * t * g⁻¹ ∈ s.h.S := (mem_normalizer_iff.mp hg t).mp ht
  have := s.h.conj_mem_P htg hw
  rwa [show g * t * g⁻¹ * (g * w * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * w * t⁻¹) * g⁻¹ by group]
    at this

theorem conjugate_P_le_S {g : X} (hg : g ∈ normalizer (s.h.S : Set X)) :
    conjugate s.h.P g ≤ s.h.S := by
  intro w hw
  rw [mem_conjugate_iff] at hw
  have := (mem_normalizer_iff.mp (inv_mem hg) _).mp ((mem_inf.mp hw).1)
  rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this

theorem P_inf_conjugate_eq_bot {g : X} (hg : g ∈ normalizer (s.h.S : Set X))
    (hga : g⁻¹ * s.h.a * g ≠ s.h.a) : s.h.P ⊓ conjugate s.h.P g = ⊥ := by
  by_contra hne
  have hS2 : IsPGroup 2 s.h.S := s.h.isPGroup_S
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal hS2 (inf_le_left.trans s.h.P_le_S)
    (fun t ht v hv => mem_inf.mpr ⟨s.h.conj_mem_P ht (mem_inf.mp hv).1,
      s.conj_mem_conjugate_P hg ht (mem_inf.mp hv).2⟩) hne
  obtain ⟨hwP, hwg⟩ := mem_inf.mp hw
  have hPZ : ∀ v ∈ s.h.P, (∀ t ∈ s.h.S, t * v = v * t) → v ≠ 1 → v = s.h.a := by
    intro v hvP hvZ hv1
    have hv : v ∈ s.h.P ⊓ centralizer (s.h.S : Set X) :=
      mem_inf.mpr ⟨hvP, mem_centralizer_iff.mpr hvZ⟩
    rw [s.hC] at hv
    exact (eq_one_or_of_mem_zpowers s.h.orderOf_a hv).resolve_left hv1
  have hwa := hPZ w hwP hwZ hw1
  rw [mem_conjugate_iff] at hwg
  have hpZ : ∀ t ∈ s.h.S, t * (g * w * g⁻¹) = g * w * g⁻¹ * t := by
    intro t ht
    have htg : g⁻¹ * t * g ∈ s.h.S := by
      have := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
      rwa [inv_inv] at this
    have h1 := hwZ _ htg
    calc t * (g * w * g⁻¹) = g * ((g⁻¹ * t * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = g * w * g⁻¹ * t := by group
  have hp1 : g * w * g⁻¹ ≠ 1 := fun h1 => hw1 (by
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hpa := hPZ _ hwg hpZ hp1
  apply hga
  calc g⁻¹ * s.h.a * g = g⁻¹ * (g * w * g⁻¹) * g := by rw [hpa]
    _ = w := by group
    _ = s.h.a := hwa

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
