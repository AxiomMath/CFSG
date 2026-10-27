module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Center
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

theorem eq_of_mem_centerOf_K0 (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1)
    (hshape : N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥)
    (hSKc : ∀ a ∈ centerOf N.SK, ∀ b ∈ centerOf N.SK, a ≠ 1 → b ≠ 1 → a = b)
    (hNP : ∀ a ∈ N.K, (∀ y ∈ N.SK, a * y = y * a) → a ∈ N.SK) :
    ∀ u₁ ∈ centerOf N.S, u₁ ∈ N.K0 → ∀ u₂ ∈ centerOf N.S, u₂ ∈ N.K0 → u₁ ≠ 1 → u₂ ≠ 1 →
      u₁ = u₂ := by
  rcases hshape with h | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
  · intro u₁ hu₁ hu₁K u₂ hu₂ hu₂K h1 h2
    rw [h] at hu₁K hu₂K
    have mem : ∀ u ∈ centerOf N.S, u ∈ N.K → u ∈ centerOf N.SK := fun u hu huK =>
      ⟨⟨hu.1, huK⟩, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hu.2 y hy.1⟩
    exact hSKc u₁ (mem u₁ hu₁ hu₁K) u₂ (mem u₂ hu₂ hu₂K) h1 h2
  · have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hdich := conj_eq_or_eq N hZ hK0 hcomm
    have hK'' : CFSG.conjugate N.K s₀⁻¹ = CFSG.conjugate N.K s₀ := by
      rcases hdich s₀⁻¹ (N.S.inv_mem hs₀S) with h | h
      · exfalso
        apply hne
        ext x
        rw [BenderBranch.mem_conjugate_iff]
        have key : s₀ * x * s₀⁻¹ ∈ N.K ↔ s₀ * x * s₀⁻¹ ∈ CFSG.conjugate N.K s₀⁻¹ := by
          rw [h]
        rw [key, BenderBranch.mem_conjugate_iff]
        have : s₀⁻¹ * (s₀ * x * s₀⁻¹) * s₀⁻¹⁻¹ = x := by group
        rw [this]
      · exact h
    have key : ∀ u ∈ centerOf N.S, u ∈ N.K0 → ∃ a ∈ centerOf N.SK, (u = 1 ↔ a = 1) ∧
        u = a * (s₀ * a * s₀⁻¹) := by
      intro u hu huK0
      rw [hK0] at huK0
      obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp huK0
      have hus : ∀ t ∈ N.S, t * (a * b) = (a * b) * t := fun t ht =>
        Subgroup.mem_centralizer_iff.mp hu.2 t ht
      have hay : ∀ y ∈ N.SK, a * y = y * a := by
        intro y hy
        have h1 := hus y hy.1
        have h2 : y * b = b * y := hc y hy.2 b hb
        have : a * y * b = y * a * b := by
          calc a * y * b = a * (y * b) := by rw [mul_assoc]
            _ = a * (b * y) := by rw [h2]
            _ = (a * b) * y := by rw [mul_assoc]
            _ = y * (a * b) := h1.symm
            _ = y * a * b := by rw [mul_assoc]
        exact mul_right_cancel this
      have haSK : a ∈ N.SK := hNP a ha hay
      have haZ : a ∈ centerOf N.SK :=
        ⟨haSK, Subgroup.mem_centralizer_iff.mpr fun y hy => (hay y hy).symm⟩
      have hA' : s₀ * a * s₀⁻¹ ∈ CFSG.conjugate N.K s₀ := by
        rw [← hK'', BenderBranch.mem_conjugate_iff]
        have : s₀⁻¹ * (s₀ * a * s₀⁻¹) * s₀⁻¹⁻¹ = a := by group
        rw [this]
        exact ha
      have hB' : s₀ * b * s₀⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hb
      have hfix : s₀ * (a * b) * s₀⁻¹ = a * b := by
        rw [hus s₀ hs₀S]
        group
      have hAB : a * b = (s₀ * b * s₀⁻¹) * (s₀ * a * s₀⁻¹) := by
        calc a * b = s₀ * (a * b) * s₀⁻¹ := hfix.symm
          _ = (s₀ * a * s₀⁻¹) * (s₀ * b * s₀⁻¹) := by group
          _ = (s₀ * b * s₀⁻¹) * (s₀ * a * s₀⁻¹) := (hc _ hB' _ hA').symm
      have hdiff : a⁻¹ * (s₀ * b * s₀⁻¹) = b * (s₀ * a * s₀⁻¹)⁻¹ := by
        calc a⁻¹ * (s₀ * b * s₀⁻¹)
            = a⁻¹ * ((s₀ * b * s₀⁻¹) * (s₀ * a * s₀⁻¹)) * (s₀ * a * s₀⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * b) * (s₀ * a * s₀⁻¹)⁻¹ := by rw [← hAB]
          _ = b * (s₀ * a * s₀⁻¹)⁻¹ := by group
      have hdK : a⁻¹ * (s₀ * b * s₀⁻¹) ∈ N.K := N.K.mul_mem (N.K.inv_mem ha) hB'
      have hdK' : a⁻¹ * (s₀ * b * s₀⁻¹) ∈ CFSG.conjugate N.K s₀ := by
        rw [hdiff]
        exact (CFSG.conjugate N.K s₀).mul_mem hb ((CFSG.conjugate N.K s₀).inv_mem hA')
      have h1 : a⁻¹ * (s₀ * b * s₀⁻¹) = 1 := inf_conj_eq_one N hZ hcomm hdK hdK'
      have hbA : s₀ * b * s₀⁻¹ = a := by
        calc s₀ * b * s₀⁻¹ = a * (a⁻¹ * (s₀ * b * s₀⁻¹)) := by group
          _ = a := by rw [h1]; group
      have hbA' : b = s₀ * a * s₀⁻¹ := by
        have h2 : b * (s₀ * a * s₀⁻¹)⁻¹ = 1 := by rw [← hdiff]; exact h1
        calc b = (b * (s₀ * a * s₀⁻¹)⁻¹) * (s₀ * a * s₀⁻¹) := by group
          _ = s₀ * a * s₀⁻¹ := by rw [h2]; group
      refine ⟨a, haZ, ⟨fun h1' => ?_, fun h1' => ?_⟩, ?_⟩
      ·
        have hab1 : a * b = 1 := h1'
        have hbinv : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab1
        have haK' : a ∈ CFSG.conjugate N.K s₀ := by
          rw [hbinv]
          exact (CFSG.conjugate N.K s₀).inv_mem hb
        exact inf_conj_eq_one N hZ hcomm ha haK'
      · rw [hbA', h1']
        group
      · rw [← hbA']
    intro u₁ hu₁ hu₁K u₂ hu₂ hu₂K h1 h2
    obtain ⟨a₁, ha₁, hiff₁, e₁⟩ := key u₁ hu₁ hu₁K
    obtain ⟨a₂, ha₂, hiff₂, e₂⟩ := key u₂ hu₂ hu₂K
    have : a₁ = a₂ :=
      hSKc a₁ ha₁ a₂ ha₂ (fun h => h1 (hiff₁.mpr h)) (fun h => h2 (hiff₂.mpr h))
    rw [e₁, e₂, this]

theorem exists_zK (N : Notation25 hs) (hin : Ch1.InducesInner N.z N.K) (hzSC : N.z ∉ N.SC)
    (hK0SC : N.K0 ⊓ N.SC = ⊥)
    (huniq : ∀ u₁ ∈ centerOf N.S, u₁ ∈ N.K0 → ∀ u₂ ∈ centerOf N.S, u₂ ∈ N.K0 → u₁ ≠ 1 →
      u₂ ≠ 1 → u₁ = u₂) :
    ∃ zK : G, zK ∈ N.K0 ∧ zK⁻¹ * N.z ∈ N.SC ∧
      centerOf N.S ⊓ N.SK0 = Subgroup.zpowers zK ∧ Nat.card (Subgroup.zpowers zK) = 2 := by
  obtain ⟨w, hwSC, c, hcK0, hzwc⟩ := N.exists_decomp hin
  have hz2 : N.z * N.z = 1 := by
    have := N.tuple.z_sq
    rwa [sq] at this
  have hzS : N.z ∈ N.S := N.z_mem_S
  have hwS : w ∈ N.S := N.SC_le_S hwSC
  have hcw : c * w = w * c :=
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hwSC) c hcK0
  have hc' : c = w⁻¹ * N.z := by rw [hzwc]; group
  have hcS : c ∈ N.S := by
    rw [hc']
    exact N.S.mul_mem (N.S.inv_mem hwS) hzS
  have hc2 : c * c = 1 := by
    have h1 : (w * c) * (w * c) = 1 := by rw [← hzwc]; exact hz2
    have h2 : (w * w) * (c * c) = 1 := by
      calc (w * w) * (c * c) = w * (w * c) * c := by group
        _ = w * (c * w) * c := by rw [hcw]
        _ = (w * c) * (w * c) := by group
        _ = 1 := h1
    have h3 : c * c = (w * w)⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : c * c ∈ N.K0 ⊓ N.SC :=
      ⟨N.K0.mul_mem hcK0 hcK0, by rw [h3]; exact N.SC.inv_mem (N.SC.mul_mem hwSC hwSC)⟩
    rw [hK0SC, Subgroup.mem_bot] at h4
    exact h4
  have hc1 : c ≠ 1 := by
    intro h
    apply hzSC
    rw [hzwc, h, mul_one]
    exact hwSC
  have hcZ : c ∈ centerOf N.S := by
    refine ⟨hcS, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have hzc : t * N.z * t⁻¹ = N.z := by rw [N.comm_z_of_mem_S ht]; group
    have hd : t * c * t⁻¹ * c⁻¹ = (t * w * t⁻¹)⁻¹ * w := by
      calc t * c * t⁻¹ * c⁻¹ = (t * w⁻¹ * t⁻¹) * (t * N.z * t⁻¹) * (N.z⁻¹ * w) := by
            rw [hc']; group
        _ = (t * w⁻¹ * t⁻¹) * N.z * (N.z⁻¹ * w) := by rw [hzc]
        _ = (t * w * t⁻¹)⁻¹ * w := by group
    have hd0 : t * c * t⁻¹ * c⁻¹ ∈ N.K0 ⊓ N.SC := by
      refine ⟨?_, ?_⟩
      · exact N.K0.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_K0 ht) c).mp hcK0)
          (N.K0.inv_mem hcK0)
      · rw [hd]
        exact N.SC.mul_mem (N.SC.inv_mem
          ((Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_SC ht) w).mp hwSC)) hwSC
    rw [hK0SC, Subgroup.mem_bot] at hd0
    calc t * c = (t * c * t⁻¹ * c⁻¹) * c * t := by group
      _ = c * t := by rw [hd0]; group
  refine ⟨c, hcK0, ?_, ?_, ?_⟩
  · have : c⁻¹ * N.z = w := by
      rw [hzwc]
      calc c⁻¹ * (w * c) = c⁻¹ * (c * w) := by rw [hcw]
        _ = w := by group
    rw [this]
    exact hwSC
  · ext u
    constructor
    · intro hu
      by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · have : u = c := huniq u hu.1 hu.2.2 c hcZ hcK0 hu1 hc1
        rw [this]
        exact Subgroup.mem_zpowers c
    · intro hu
      exact (Subgroup.zpowers_le.mpr (show c ∈ centerOf N.S ⊓ N.SK0 from ⟨hcZ, hcS, hcK0⟩)) hu
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hc2) hc1

end CFSG.QuasithinUnique.Unc25Small
