module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1S1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Sing
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SGen

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_t_conj_A (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {y : G} (hy : y ∈ A) :
    t * y * t = y := by
  have hty : y * t = t * y := h.cfg.t_cent y hy
  rw [← hty, mul_assoc, y7a_t_sq h, mul_one]

private lemma y7a_conj_zpow (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hxz : x * z * x⁻¹ = z) {a : G} (ha : a ∈ zpowers z) : x * a * x⁻¹ = a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← conj_zpow, hxz]

private lemma y7a_mem_z_of_sq_one (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {a : G}
    (ha1 : a ^ 2 = 1)
    (hUW : a ∈ (closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) :
    a ∈ zpowers z := by
  have key : (a ≠ 1 → a ≠ z → a ^ 2 = z) → a ∈ zpowers z := by
    intro hneq
    by_cases h1 : a = 1 ∨ a = z
    · rcases h1 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    · push_neg at h1
      exact absurd ((hneq h1.1 h1.2).symm.trans ha1) h.cfg.z_ne
  rcases hUW with hU | hW
  · exact key (y6q8_sq_U h.cfg.rel a hU).2
  · exact key (y6q8_sq_W h.cfg.rel a hW).2

theorem y7a_S_trans (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {P3 : Subgroup G}
    (hP3t : ∀ k ∈ P3, k * t * k⁻¹ = t) (hP3V : ∀ k ∈ P3, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (h9 : IsOrbitMod P3 (zpowers z) ((A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)))) :
    ∀ w ∈ y7aS A V t, ∀ w' ∈ y7aS A V t, ∃ k ∈ P3, (k * w * k⁻¹)⁻¹ * w' ∈ V := by
  intro w hw w' hw'
  obtain ⟨a, ha, ha1, haz, v, hv, rfl⟩ := (y7a_S_iff h).mp hw
  obtain ⟨a', ha', ha'1, ha'z, v', hv', rfl⟩ := (y7a_S_iff h).mp hw'
  have haO : a ∈ (A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) :=
    ⟨ha, fun hUW => haz (y7a_mem_z_of_sq_one h ha1 hUW)⟩
  have ha'O : a' ∈ (A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) :=
    ⟨ha', fun hUW => ha'z (y7a_mem_z_of_sq_one h ha'1 hUW)⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
  have hTZ : P3 ≤ normalizer (zpowers z : Set G) := by
    intro k hk
    have hkz : Commute k z := by
      rw [commute_iff_eq]
      calc k * z = (k * z * k⁻¹) * k := by group
        _ = z * k := by rw [hP3z k hk]
    refine Subgroup.centralizer_le_normalizer (zpowers z : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hkz.zpow_right i).eq.symm
  obtain ⟨k, hkP, hkζ⟩ := y6_orbitMod_trans hTZ h9 haO ha'O
  refine ⟨k, hkP, ?_⟩
  set ζ : G := (k * a * k⁻¹)⁻¹ * a' with hζdef
  have hζz : ζ ∈ zpowers z := hkζ
  have hζA : ζ ∈ A := (Subgroup.zpowers_le.mpr (y7a_z_mem_A h)) hζz
  have hζV : ζ ∈ V := (Subgroup.zpowers_le.mpr (y7a_z_mem_V h)) hζz
  have hV1 : k * v * k⁻¹ ∈ V := hP3V k hkP v hv
  have hkt : k * t * k⁻¹ = t := hP3t k hkP
  have htζ : t * ζ * t = ζ := y7a_t_conj_A h hζA
  have hconj : k * (a * t * v) * k⁻¹ = (k * a * k⁻¹) * t * (k * v * k⁻¹) := by
    calc k * (a * t * v) * k⁻¹ = (k * a * k⁻¹) * (k * t * k⁻¹) * (k * v * k⁻¹) := by
          group
      _ = (k * a * k⁻¹) * t * (k * v * k⁻¹) := by rw [hkt]
  have key : (k * (a * t * v) * k⁻¹)⁻¹ * (a' * t * v') = (k * v * k⁻¹)⁻¹ * ζ * v' := by
    rw [hconj]
    calc ((k * a * k⁻¹) * t * (k * v * k⁻¹))⁻¹ * (a' * t * v')
        = (k * v * k⁻¹)⁻¹ * (t * ζ * t) * v' := by
          rw [hζdef]
          simp only [mul_inv_rev, hti]
          group
      _ = (k * v * k⁻¹)⁻¹ * ζ * v' := by rw [htζ]
  rw [key]
  exact V.mul_mem (V.mul_mem (V.inv_mem hV1) hζV) hv'

theorem y7a_S_faith (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxC1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G))
    (hxV : x ∈ normalizer (V : Set G))
    (hxY : x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (hfix : ∀ w ∈ y7aS A V t, w⁻¹ * (x * w * x⁻¹) ∈ V) :
    ∀ u ∈ y7aU16 A C0 V, u⁻¹ * (x * u * x⁻¹) ∈ V := by
  intro u hu
  obtain ⟨huC1, huNotAV⟩ := hu
  rcases y7a_C1_elems h u huC1 with ⟨a, ha, v, hv, rfl⟩ | ⟨a, ha, v, hv, rfl⟩
  · exact absurd (Subgroup.mul_mem_sup ha hv) huNotAV
  · have hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t := (y7a_mem_NAt_iff h hxC1).mp hxY
    have hyA : x * a * x⁻¹ ∈ A := (Subgroup.mem_set_normalizer_iff.mp hxA a).mp ha
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
    have hsing : ∀ a ∈ A, a * a = 1 → a⁻¹ * (x * a * x⁻¹) ∈ zpowers z := by
      intro a ha ha1
      by_cases haz : a ∈ zpowers z
      · rw [y7a_conj_zpow h (y7a_fix_z h hxC1) haz]
        exact (zpowers z).mul_mem ((zpowers z).inv_mem haz) haz
      · have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha1
        have hw : a * t ∈ y7aS A V t := by
          rw [y7a_S_iff h]
          exact ⟨a, ha, ha2, haz, 1, V.one_mem, by rw [mul_one]⟩
        have hfixw : (a * t)⁻¹ * (x * (a * t) * x⁻¹) ∈ V := hfix (a * t) hw
        have hyA' : x * a * x⁻¹ ∈ A := (Subgroup.mem_set_normalizer_iff.mp hxA a).mp ha
        rcases hxt with hxt1 | hxt2
        · have hkey : (a * t)⁻¹ * (x * (a * t) * x⁻¹) = a⁻¹ * (x * a * x⁻¹) := by
            rw [show x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) by group, hxt1]
            rw [show (a * t)⁻¹ = t * a⁻¹ by rw [mul_inv_rev, hti]]
            rw [show (t * a⁻¹) * ((x * a * x⁻¹) * t)
                  = t * (a⁻¹ * (x * a * x⁻¹)) * t by group]
            rw [y7a_t_conj_A h (A.mul_mem (A.inv_mem ha) hyA')]
          have hmemA : a⁻¹ * (x * a * x⁻¹) ∈ A := A.mul_mem (A.inv_mem ha) hyA'
          have hmemV : a⁻¹ * (x * a * x⁻¹) ∈ V := hkey ▸ hfixw
          have hmem : a⁻¹ * (x * a * x⁻¹) ∈ A ⊓ V := ⟨hmemA, hmemV⟩
          rwa [y7a_A_inf_V h] at hmem
        · have hkey : (a * t)⁻¹ * (x * (a * t) * x⁻¹) = a⁻¹ * (x * a * x⁻¹) * z := by
            rw [show x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) by group, hxt2]
            rw [show (a * t)⁻¹ = t * a⁻¹ by rw [mul_inv_rev, hti]]
            rw [show (t * a⁻¹) * ((x * a * x⁻¹) * (z * t))
                  = t * (a⁻¹ * (x * a * x⁻¹) * z) * t by group]
            rw [y7a_t_conj_A h (A.mul_mem (A.mul_mem (A.inv_mem ha) hyA') (y7a_z_mem_A h))]
          have hmemA : a⁻¹ * (x * a * x⁻¹) * z ∈ A :=
            A.mul_mem (A.mul_mem (A.inv_mem ha) hyA') (y7a_z_mem_A h)
          have hmemV : a⁻¹ * (x * a * x⁻¹) * z ∈ V := hkey ▸ hfixw
          have hmem : a⁻¹ * (x * a * x⁻¹) * z ∈ zpowers z := by
            have hinf : a⁻¹ * (x * a * x⁻¹) * z ∈ A ⊓ V := ⟨hmemA, hmemV⟩
            rwa [y7a_A_inf_V h] at hinf
          rw [show a⁻¹ * (x * a * x⁻¹) = (a⁻¹ * (x * a * x⁻¹) * z) * z⁻¹ by group]
          exact (zpowers z).mul_mem hmem ((zpowers z).inv_mem (Subgroup.mem_zpowers z))
    have htriv : ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ zpowers z :=
      y7a_triv_of_sing h hxA (y7a_fix_z h hxC1) hsing
    have hza : a⁻¹ * (x * a * x⁻¹) ∈ zpowers z := htriv a ha
    have hzaV : a⁻¹ * (x * a * x⁻¹) ∈ V :=
      (Subgroup.zpowers_le.mpr (y7a_z_mem_V h)) hza
    have hwV : x * v * x⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp hxV v).mp hv
    rcases hxt with hxt1 | hxt2
    · have hkey : (a * t * v)⁻¹ * (x * (a * t * v) * x⁻¹)
          = v⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * (x * v * x⁻¹) := by
        rw [show x * (a * t * v) * x⁻¹
              = (x * a * x⁻¹) * (x * t * x⁻¹) * (x * v * x⁻¹) by group, hxt1]
        rw [show (a * t * v)⁻¹ = v⁻¹ * (t * a⁻¹) by rw [mul_inv_rev, mul_inv_rev, hti]]
        rw [show (v⁻¹ * (t * a⁻¹)) * ((x * a * x⁻¹) * t * (x * v * x⁻¹))
              = v⁻¹ * (t * (a⁻¹ * (x * a * x⁻¹)) * t) * (x * v * x⁻¹) by group]
        rw [y7a_t_conj_A h (A.mul_mem (A.inv_mem ha) hyA)]
      rw [hkey]
      exact V.mul_mem (V.mul_mem (V.inv_mem hv) hzaV) hwV
    · have hkey : (a * t * v)⁻¹ * (x * (a * t * v) * x⁻¹)
          = v⁻¹ * (a⁻¹ * (x * a * x⁻¹) * z) * (x * v * x⁻¹) := by
        rw [show x * (a * t * v) * x⁻¹
              = (x * a * x⁻¹) * (x * t * x⁻¹) * (x * v * x⁻¹) by group, hxt2]
        rw [show (a * t * v)⁻¹ = v⁻¹ * (t * a⁻¹) by rw [mul_inv_rev, mul_inv_rev, hti]]
        rw [show (v⁻¹ * (t * a⁻¹)) * ((x * a * x⁻¹) * (z * t) * (x * v * x⁻¹))
              = v⁻¹ * (t * (a⁻¹ * (x * a * x⁻¹) * z) * t) * (x * v * x⁻¹) by group]
        rw [y7a_t_conj_A h (A.mul_mem (A.mul_mem (A.inv_mem ha) hyA) (y7a_z_mem_A h))]
      rw [hkey]
      exact V.mul_mem (V.mul_mem (V.inv_mem hv) (V.mul_mem hzaV (y7a_z_mem_V h))) hwV

end CFSG.OddStandard.HigherRank.YamadaG23
