module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Aux

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Normalize

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) {ω : G} (hω : ω = tau ∨ ω = t * tau)
  (hn : NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂)) {m : G}
include hc hω hn

theorem mem_normalizer_D_of_LO (hm : m ∈ ctxLO t tau x₁ x₂)
    (hmV : ∀ a ∈ fourGrp x₁ x₂, m * a = a * m) (hmq : m * (t * lam) = (t * lam) * m) :
    ∀ d ∈ ctxD ω x₁ x₂, m * d * m⁻¹ ∈ ctxD ω x₁ x₂ := by
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hz' : m * (x₁ * x₂) ^ 2 * m⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [hmV ((x₁ * x₂) ^ 2) hzV]; group
  have hωm : m * ω * m⁻¹ ∈ ctxN ω x₁ x₂ := hn.2 m hm ω (subset_closure (by simp))
  have hω' : m * ω * m⁻¹ = ω ∨ m * ω * m⁻¹ = ω * (x₁ * x₂) ^ 2 := by
    have hmem := (mem_ctxN_iff hc hω (m * ω * m⁻¹)).mp hωm
    rcases hmem with hV | ⟨a, ha, haeq⟩
    · exfalso
      have hb : m⁻¹ * (m * ω * m⁻¹) * m = m * ω * m⁻¹ := by
        calc m⁻¹ * (m * ω * m⁻¹) * m = m⁻¹ * ((m * ω * m⁻¹) * m) := by group
          _ = m⁻¹ * (m * (m * ω * m⁻¹)) := by rw [hmV (m * ω * m⁻¹) hV]
          _ = m * ω * m⁻¹ := by group
      have hωeq : ω = m * ω * m⁻¹ := by
        calc ω = m⁻¹ * (m * ω * m⁻¹) * m := by group
          _ = m * ω * m⁻¹ := hb
      exact omega_not_mem_V hc hω (by rw [hωeq]; exact hV)
    · have hωq : (t * lam) * ω = ω * (t * lam) := q_comm_omega hc hω
      have hqa : (t * lam) * a * (t * lam)⁻¹ = a := by
        have h1 : (t * lam) * (ω * a) * (t * lam)⁻¹ = ω * a := by
          rw [← haeq]; exact conj_comm_of_cent hωq hmq
        have h2 : (t * lam) * (ω * a) * (t * lam)⁻¹ =
            ω * ((t * lam) * a * (t * lam)⁻¹) := by
          calc (t * lam) * (ω * a) * (t * lam)⁻¹
              = ((t * lam) * ω) * a * (t * lam)⁻¹ := by group
            _ = (ω * (t * lam)) * a * (t * lam)⁻¹ := by rw [hωq]
            _ = ω * ((t * lam) * a * (t * lam)⁻¹) := by group
        rw [h2] at h1
        exact mul_left_cancel h1
      rcases CV_q hc ha hqa with h | h
      · left; rw [haeq, h, mul_one]
      · right; rw [haeq, h]
  intro d hd
  have hd' := (mem_ctxD_iff hc hω d).mp hd
  apply (mem_ctxD_iff hc hω (m * d * m⁻¹)).mpr
  rcases hd' with rfl | rfl | rfl | rfl
  · left; group
  · rcases hω' with h | h
    · right; left; exact h
    · right; right; right; exact h
  · right; right; left; exact hz'
  · have hmul : m * (ω * (x₁ * x₂) ^ 2) * m⁻¹ =
        (m * ω * m⁻¹) * (m * (x₁ * x₂) ^ 2 * m⁻¹) := by group
    rw [hmul]
    rcases hω' with h | h <;> rw [h, hz']
    · right; right; right; rfl
    · right; left; rw [mul_assoc, z_mul_self hc, mul_one]

end Normalize

section Sp

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau) {W : Subgroup G} {v : G}
  (hv : Ctx4V t x₁ x₂ lam tau W v)
include hc hv

theorem v_mem_LO : v ∈ ctxLO t tau x₁ x₂ :=
  normalizer_le_of_charIn hc.char_O hv.v_norm

theorem Sp_le_cent : ctxSp t tau x₁ x₂ lam v ≤ centralizer ({t * lam} : Set G) := by
  unfold ctxSp
  apply sup_le
  · exact inf_le_right
  · apply zpowers_le.mpr
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hv.v_cent_tl.symm

theorem Sp_isPGroup : IsPGroup 2 (ctxSp t tau x₁ x₂ lam v) := by
  refine hv.sylow.2.1.to_le ?_
  unfold ctxSp
  apply sup_le
  · exact inf_le_left.trans hv.U_le
  · exact zpowers_le.mpr hv.v_mem

theorem le_card_Sp : 2 ^ 7 ≤ Nat.card (ctxSp t tau x₁ x₂ lam v) := by
  set C : Subgroup G := ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) with hC
  have hCS : C ≤ ctxSp t tau x₁ x₂ lam v := by
    rw [ctxSp]; exact le_sup_left
  have hvS : v ∈ ctxSp t tau x₁ x₂ lam v := by
    rw [ctxSp]; exact mem_sup_right (mem_zpowers v)
  have hvC : v ∉ C := by
    intro hvc; exact hv.v_not_mem hvc.1
  have hcardC : Nat.card C = 2 ^ 6 := by rw [hC]; exact hc.card_CU_tl
  have hdvd : Nat.card C ∣ Nat.card (ctxSp t tau x₁ x₂ lam v) := Subgroup.card_dvd_of_le hCS
  obtain ⟨k, hk⟩ := hdvd
  have hSpos : 0 < Nat.card (ctxSp t tau x₁ x₂ lam v) :=
    Finite.card_pos_iff.mpr ⟨v, hvS⟩
  have hne : Nat.card (ctxSp t tau x₁ x₂ lam v) ≠ Nat.card C := by
    intro heq
    have hEqC : C = ctxSp t tau x₁ x₂ lam v :=
      Subgroup.eq_of_le_of_card_ge hCS (le_of_eq heq)
    exact hvC (by rw [hEqC]; exact hvS)
  have hk2 : 2 ≤ k := by
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hk; omega
    have hk1 : k ≠ 1 := by
      intro h1; rw [h1, mul_one] at hk; exact hne hk
    omega
  calc 2 ^ 7 = 2 * 2 ^ 6 := by norm_num
    _ = 2 * Nat.card C := by rw [hcardC]
    _ ≤ k * Nat.card C := Nat.mul_le_mul_right (Nat.card C) hk2
    _ = Nat.card C * k := by rw [mul_comm]
    _ = Nat.card (ctxSp t tau x₁ x₂ lam v) := hk.symm

theorem D_le_Sp {ω : G} (hω : ω = tau ∨ ω = t * tau) :
    ctxD ω x₁ x₂ ≤ ctxSp t tau x₁ x₂ lam v :=
  (D_le_CU hc hω).trans le_sup_left

theorem D_normal_Sp {ω : G} (hω : ω = tau ∨ ω = t * tau)
    (hn : NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂)) :
    NormalIn (ctxD ω x₁ x₂) (ctxSp t tau x₁ x₂ lam v) := by
  refine ⟨D_le_Sp hc hv hω, ?_⟩
  have hUleM : ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ := hc.U_sylow.1
  have hvLO : v ∈ ctxLO t tau x₁ x₂ := v_mem_LO hc hv
  have hsub : ctxSp t tau x₁ x₂ lam v ≤ normalizer (ctxD ω x₁ x₂ : Set G) := by
    unfold ctxSp
    apply sup_le
    · intro c hcC
      rw [mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        have hcq : c * (t * lam) = (t * lam) * c :=
          (mem_centralizer_iff.mp hcC.2 (t * lam) (Set.mem_singleton _)).symm
        exact mem_normalizer_D_of_cent hc.toCtx4Q hω (hUleM hcC.1) hcq d hd
      · intro hd
        have hcInvC : c⁻¹ ∈ ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) :=
          inv_mem hcC
        have hcq : c⁻¹ * (t * lam) = (t * lam) * c⁻¹ := by
          have hcq0 : c * (t * lam) = (t * lam) * c :=
            (mem_centralizer_iff.mp hcC.2 (t * lam) (Set.mem_singleton _)).symm
          calc c⁻¹ * (t * lam) = c⁻¹ * ((t * lam) * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * (t * lam)) * c⁻¹ := by rw [← hcq0]
            _ = (t * lam) * c⁻¹ := by group
        have h := mem_normalizer_D_of_cent hc.toCtx4Q hω (hUleM hcInvC.1) hcq
          (c * d * c⁻¹) hd
        rwa [show c⁻¹ * (c * d * c⁻¹) * c⁻¹⁻¹ = d by group] at h
    · apply zpowers_le.mpr
      rw [mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        exact mem_normalizer_D_of_LO hc.toCtx4Q hω hn hvLO hv.v_cent_V hv.v_cent_tl d hd
      · intro hd
        have hvInvLO : v⁻¹ ∈ ctxLO t tau x₁ x₂ := inv_mem hvLO
        have hvInvV : ∀ a ∈ fourGrp x₁ x₂, v⁻¹ * a = a * v⁻¹ := by
          intro a ha
          calc v⁻¹ * a = v⁻¹ * (a * v) * v⁻¹ := by group
            _ = v⁻¹ * (v * a) * v⁻¹ := by rw [← hv.v_cent_V a ha]
            _ = a * v⁻¹ := by group
        have hvInvtl : v⁻¹ * (t * lam) = (t * lam) * v⁻¹ := by
          calc v⁻¹ * (t * lam) = v⁻¹ * ((t * lam) * v) * v⁻¹ := by group
            _ = v⁻¹ * (v * (t * lam)) * v⁻¹ := by rw [← hv.v_cent_tl]
            _ = (t * lam) * v⁻¹ := by group
        have h := mem_normalizer_D_of_LO hc.toCtx4Q hω hn hvInvLO hvInvV hvInvtl
          (v * d * v⁻¹) hd
        rwa [show v⁻¹ * (v * d * v⁻¹) * v⁻¹⁻¹ = d by group] at h
  intro g hg k hk
  have hgN : g ∈ normalizer (ctxD ω x₁ x₂ : Set G) := hsub hg
  exact (mem_normalizer_iff.mp hgN k).mp hk

end Sp

end CFSG.OddStandard.SmallF3.HarrisU33.L34
