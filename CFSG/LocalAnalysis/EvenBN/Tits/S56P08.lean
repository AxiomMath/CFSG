module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P11
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Hyper

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace S56

theorem mem_sup_zpowers_of_conj {Γ : Type*} [Group Γ] {H : Subgroup Γ} {a : Γ} (ha2 : a * a ∈ H)
    (hconj : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (hconj' : ∀ h ∈ H, a⁻¹ * h * a ∈ H) {w : Γ}
    (hw : w ∈ H ⊔ zpowers a) : w ∈ H ∨ ∃ h ∈ H, w = h * a := by
  let S : Subgroup Γ :=
    { carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = h * a}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro x w (hx | ⟨h, hh, rfl⟩) (hw | ⟨h', hh', rfl⟩)
        · exact Or.inl (mul_mem hx hw)
        · exact Or.inr ⟨x * h', mul_mem hx hh', by group⟩
        · exact Or.inr ⟨h * (a * w * a⁻¹), mul_mem hh (hconj w hw), by group⟩
        · refine Or.inl ?_
          have e : h * a * (h' * a) = h * (a * h' * a⁻¹) * (a * a) := by group
          rw [e]
          exact mul_mem (mul_mem hh (hconj h' hh')) ha2
      inv_mem' := by
        rintro x (hx | ⟨h, hh, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨(a⁻¹ * h⁻¹ * a) * (a * a)⁻¹,
            mul_mem (hconj' _ (inv_mem hh)) (inv_mem ha2), ?_⟩
          group }
  have hsup : H ⊔ zpowers a ≤ S := by
    refine sup_le (fun h hh => Or.inl hh) ?_
    rw [zpowers_le]
    exact Or.inr ⟨1, one_mem _, by group⟩
  exact hsup hw

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_c1_mem_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y * z₀ * y⁻¹ ∈ d.s56Q0 := by
  obtain ⟨hc1, -, -, -, hε1, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  obtain ⟨hα, -, -, -, -⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hcP := s56_P11_le_P d hc1
  have hcM : y * z₀ * y⁻¹ ∈ d.M := by
    refine (mem_inf.1 ((hd.s56_P0_inf_M_iff h49).2 ⟨s56_P_le_P0 d hcP,
      d.s56Eps (y * z₀ * y⁻¹), ?_, hd.s56_conj_t _⟩)).2
    rw [hε1]
    exact s56_U11_le_E d hd hα
  have hidx : (d.E ⊓ d.F).relIndex d.E ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := d.E ⊓ d.F) (K := d.E)
    rw [inf_eq_left.2 (inf_le_left : d.E ⊓ d.F ≤ d.E), hd.s56_card_E_inf_F, hd.A_facts.1] at h
    omega
  refine hd.s56_mem_Q0_of_cent_hyperplane h49 hcM inf_le_left hidx fun h hh => ?_
  have := s56_P_conj_F d hcP (mem_inf.1 hh).2
  calc y * z₀ * y⁻¹ * h = (y * z₀ * y⁻¹ * h * (y * z₀ * y⁻¹)⁻¹) * (y * z₀ * y⁻¹) := by group
    _ = h * (y * z₀ * y⁻¹) := by rw [this]

theorem Hyp.s56_exists_f_mul_c1_mem_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G}
    (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ f ∈ d.F, f * (y * z₀ * y⁻¹) ∈ d.s56Q2 := by
  obtain ⟨hc1, -, -, -, -, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  have hcP := s56_P11_le_P d hc1
  have hcQ0 := hd.s56_c1_mem_Q0 h49 hz hsq hy hy3 hy1
  have hcM : y * z₀ * y⁻¹ ∈ d.M := hd.s56_Q0_le_M h49 hcQ0
  generalize y * z₀ * y⁻¹ = c at hcP hcQ0 hcM ⊢
  have hcF : ∀ f ∈ d.F, c * f = f * c := fun f hf => by
    have := s56_P_conj_F d hcP hf
    calc c * f = (c * f * c⁻¹) * c := by group
      _ = f * c := by rw [this]
  have hv7 := hd.s56_pv7_mem_F
  have hv8E := s56_pv8_mem_E d
  have hEcases : ∀ e ∈ d.E, e ∈ d.F ∨ ∃ f ∈ d.F, e = d.pv 8 * f := by
    intro e he
    rcases hd.s56_E_cases he with h | h
    · exact Or.inl h
    · refine Or.inr ⟨d.pv 8 * e, h, ?_⟩
      calc e = (d.pv 8 * d.pv 8) * e := by rw [hd.s56_E_sq hv8E, one_mul]
        _ = d.pv 8 * (d.pv 8 * e) := by group
  by_cases h8 : c * d.pv 8 = d.pv 8 * c
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, s56_mem_Q2_iff]
    refine ⟨hcM, fun e he => ?_⟩
    rcases hEcases e he with hf | ⟨f, hf, rfl⟩
    · exact (hcF e hf).symm
    · calc d.pv 8 * f * c = d.pv 8 * (f * c) := by group
        _ = d.pv 8 * (c * f) := by rw [hcF f hf]
        _ = (d.pv 8 * c) * f := by group
        _ = (c * d.pv 8) * f := by rw [h8]
        _ = c * (d.pv 8 * f) := by group
  · have hcomm := ((hd.s56_mem_Q0_iff h49).1 hcQ0).2 (d.pv 8) hv8E
    rcases hd.s56_mem_zpowers_z hcomm with h1 | h1
    · exfalso
      apply h8
      calc c * d.pv 8 = (c * d.pv 8 * c⁻¹ * (d.pv 8)⁻¹) * (d.pv 8 * c) := by group
        _ = d.pv 8 * c := by rw [h1, one_mul]
    · have h2 : c * d.pv 8 = d.z * (d.pv 8 * c) := by
        calc c * d.pv 8 = (c * d.pv 8 * c⁻¹ * (d.pv 8)⁻¹) * (d.pv 8 * c) := by group
          _ = d.z * (d.pv 8 * c) := by rw [h1]
      have hv78 : d.pv 7 * d.pv 8 = d.pv 8 * d.z * d.pv 7 := by
        calc d.pv 7 * d.pv 8 = (d.pv 7 * d.pv 8 * (d.pv 7)⁻¹) * d.pv 7 := by group
          _ = d.pv 8 * d.z * d.pv 7 := by rw [s56_pv7_conj_pv8]
      have hzv7 : d.z * d.pv 7 = d.pv 7 * d.z := hd.s56_F_comm hd.s56_z_mem_F hv7
      have hzv8 : d.z * d.pv 8 = d.pv 8 * d.z := hd.s56_E_comm hd.s56_z_mem_E hv8E
      have hw8 : (d.pv 7 * c) * d.pv 8 = d.pv 8 * (d.pv 7 * c) := by
        calc (d.pv 7 * c) * d.pv 8 = d.pv 7 * (c * d.pv 8) := by group
          _ = d.pv 7 * (d.z * (d.pv 8 * c)) := by rw [h2]
          _ = (d.pv 7 * d.z) * (d.pv 8 * c) := by group
          _ = (d.z * d.pv 7) * (d.pv 8 * c) := by rw [hzv7]
          _ = d.z * ((d.pv 7 * d.pv 8) * c) := by group
          _ = d.z * ((d.pv 8 * d.z * d.pv 7) * c) := by rw [hv78]
          _ = (d.z * d.pv 8) * d.z * (d.pv 7 * c) := by group
          _ = (d.pv 8 * d.z) * d.z * (d.pv 7 * c) := by rw [hzv8]
          _ = d.pv 8 * (d.z * d.z) * (d.pv 7 * c) := by group
          _ = d.pv 8 * (d.pv 7 * c) := by rw [hd.s56_z_sq, mul_one]
      have hwF : ∀ f ∈ d.F, f * (d.pv 7 * c) = (d.pv 7 * c) * f := fun f hf => by
        calc f * (d.pv 7 * c) = (f * d.pv 7) * c := by group
          _ = (d.pv 7 * f) * c := by rw [hd.s56_F_comm hf hv7]
          _ = d.pv 7 * (f * c) := by group
          _ = d.pv 7 * (c * f) := by rw [hcF f hf]
          _ = (d.pv 7 * c) * f := by group
      refine ⟨d.pv 7, hv7, ?_⟩
      rw [s56_mem_Q2_iff]
      refine ⟨mul_mem (hd.s56_F_le_M hv7) hcM, fun e he => ?_⟩
      rcases hEcases e he with hf | ⟨f, hf, rfl⟩
      · exact hwF e hf
      · calc d.pv 8 * f * (d.pv 7 * c) = d.pv 8 * (f * (d.pv 7 * c)) := by group
          _ = d.pv 8 * ((d.pv 7 * c) * f) := by rw [hwF f hf]
          _ = (d.pv 8 * (d.pv 7 * c)) * f := by group
          _ = ((d.pv 7 * c) * d.pv 8) * f := by rw [hw8]
          _ = (d.pv 7 * c) * (d.pv 8 * f) := by group

theorem Hyp.s56_t_not_comm_z0 (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.t * z₀ ≠ z₀ * d.t := by
  intro h
  have h1 := hd.s56_z0_conj_t hz
  rw [← h] at h1
  apply hd.s56_z_ne_one
  have h2 : d.t * z₀ * z₀⁻¹ = d.t * d.z := by rw [← h1]
  have h3 : d.t = d.t * d.z := by rw [← h2]; group
  exact (mul_eq_left.1 h3.symm)

theorem Hyp.s56_exists_y5 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hr : d.ρ.range = ⊤) :
    ∃ y₅ : G, N.IsV5 d y₅ ∧ y₅ * z₀ = z₀ * y₅ ∧ y₅ * y₅ = d.z ∧
      (∀ a ∈ d.A, y₅ * a = a * y₅) ∧ y₅ * d.pv 7 * y₅⁻¹ = d.pv 7 * d.pv 11 ∧
      y₅ * d.t = d.t * y₅ := by
  rcases hd.s56y_C_structure with hC | ⟨y, hyC, hyρ, hyy, hCy, hycomm, hyA, hconj, -⟩
  · exfalso
    obtain ⟨y, hyC, hyρ, -⟩ := hd.s56_exists_y hr
    rcases hd.centralizer_A with ⟨hr', -⟩ | ⟨-, hC'⟩
    · exact s56_subgroupOf_ne_top (hr'.symm.trans hr)
    · have h := hC' y hyC hyρ
      have hyA : y ∈ d.A := by
        have : y ∈ centralizer (d.A : Set G) := by
          rw [h]
          exact mem_sup_right (mem_zpowers _)
        rw [hC] at this
        exact this
      have := hd.s56y_ρ_mem_titsD_of_mem_A hyA hyC
      rw [hyρ] at this
      exact Model.parrottV_five.2.1 this
  · have hyt : y * d.t = d.t * y := mem_centralizer_singleton_iff.1 hyC
    have hyM : y ∈ d.M := d.s56_centralizer_A_le_M (by
      rw [hCy]
      exact mem_sup_right (mem_zpowers _))
    by_cases hyz : y * z₀ = z₀ * y
    · exact ⟨y, ⟨hyC, hyρ⟩, hyz, hyy, hycomm, hconj, hyt⟩
    · have hδ := hd.s56_M_comm_z0 h49 hz hyM
      rcases hd.s56_mem_zpowers_z hδ with h1 | h1
      · exfalso
        apply hyz
        calc y * z₀ = (y * z₀ * y⁻¹ * z₀⁻¹) * (z₀ * y) := by group
          _ = z₀ * y := by rw [h1, one_mul]
      · have hy2 : y * z₀ = d.z * (z₀ * y) := by
          calc y * z₀ = (y * z₀ * y⁻¹ * z₀⁻¹) * (z₀ * y) := by group
            _ = d.z * (z₀ * y) := by rw [h1]
        have hz0t := hd.s56_z0_conj_t hz
        have hA : z₀ * d.t = d.t * d.z * z₀ := by
          calc z₀ * d.t = (z₀ * d.t * z₀⁻¹) * z₀ := by group
            _ = d.t * d.z * z₀ := by rw [hz0t]
        have hzt : d.z * d.t = d.t * d.z := hd.L_comm_t d.z_mem
        have hB : d.t * z₀ = d.z * z₀ * d.t := by
          calc d.t * z₀ = d.t * z₀ * (d.t * d.t) := by rw [hd.t_mul_self, mul_one]
            _ = d.t * (z₀ * d.t) * d.t := by group
            _ = d.t * (d.t * d.z * z₀) * d.t := by rw [hA]
            _ = (d.t * d.t) * d.z * z₀ * d.t := by group
            _ = d.z * z₀ * d.t := by rw [hd.t_mul_self, one_mul]
        have hFt : ∀ f ∈ d.F, d.t * f = f * d.t := fun f hf =>
          congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨d.t, s56_t_mem_B d⟩
            ⟨f, s56_F_le_B d hf⟩)
        have hAt : ∀ a ∈ d.A, d.t * a = a * d.t := fun a ha =>
          congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨d.t, s56_t_mem_A d⟩ ⟨a, ha⟩)
        refine ⟨d.t * y, ⟨mul_mem d.t_mem_centralizer hyC, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        · have e : (⟨d.t * y, mul_mem d.t_mem_centralizer hyC⟩ : centralizer ({d.t} : Set G)) =
              ⟨d.t, d.t_mem_centralizer⟩ * ⟨y, hyC⟩ := rfl
          rw [e, map_mul, hd.ρ_t, one_mul]
          exact hyρ
        · calc d.t * y * z₀ = d.t * (y * z₀) := by group
            _ = d.t * (d.z * (z₀ * y)) := by rw [hy2]
            _ = d.z * (d.t * z₀) * y := by
                calc d.t * (d.z * (z₀ * y)) = (d.t * d.z) * (z₀ * y) := by group
                  _ = (d.z * d.t) * (z₀ * y) := by rw [hzt]
                  _ = d.z * (d.t * z₀) * y := by group
            _ = d.z * (d.z * z₀ * d.t) * y := by rw [hB]
            _ = (d.z * d.z) * z₀ * (d.t * y) := by group
            _ = z₀ * (d.t * y) := by rw [hd.s56_z_sq, one_mul]
        · calc d.t * y * (d.t * y) = (d.t * d.t) * (y * y) := by
                calc d.t * y * (d.t * y) = d.t * (y * d.t) * y := by group
                  _ = d.t * (d.t * y) * y := by rw [hyt]
                  _ = (d.t * d.t) * (y * y) := by group
            _ = d.z := by rw [hd.t_mul_self, one_mul, hyy]
        · intro a ha
          calc d.t * y * a = d.t * (y * a) := by group
            _ = d.t * (a * y) := by rw [hycomm a ha]
            _ = (d.t * a) * y := by group
            _ = (a * d.t) * y := by rw [hAt a ha]
            _ = a * (d.t * y) := by group
        · have hv7 := hd.s56_pv7_mem_F
          have hv11 := s56_U11_le_F d (s56_pv11_mem_U11 d)
          calc d.t * y * d.pv 7 * (d.t * y)⁻¹
              = d.t * (y * d.pv 7 * y⁻¹) * d.t⁻¹ := by group
            _ = d.t * (d.pv 7 * d.pv 11) * d.t⁻¹ := by rw [hconj]
            _ = (d.t * d.pv 7 * d.t⁻¹) * (d.t * d.pv 11 * d.t⁻¹) := by group
            _ = d.pv 7 * d.pv 11 := by
                have e7 : d.t * d.pv 7 * d.t⁻¹ = d.pv 7 := by rw [hFt _ hv7]; group
                have e11 : d.t * d.pv 11 * d.t⁻¹ = d.pv 11 := by rw [hFt _ hv11]; group
                rw [e7, e11]
        · calc d.t * y * d.t = d.t * (y * d.t) := by group
            _ = d.t * (d.t * y) := by rw [hyt]

theorem Hyp.s56_mem_V_of_Q2_P (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hQD : d.ρ.range = titsD.subgroupOf titsA → d.s56Q0 = d.s56Q ⊔ zpowers d.t)
    (hQA : ∀ y₅ : G, N.IsV5 d y₅ → d.s56Q0 = d.s56Q ⊔ zpowers d.t ⊔ zpowers y₅)
    (hKV : ∀ x ∈ d.s56V, d.s56Eps x ∈ d.s56U11 →
      x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ zpowers d.z)
    {w : G} (hwQ2 : w ∈ d.s56Q2) (hwP : w ∈ d.s56P) (hwz : w * z₀ = z₀ * w)
    (hwε : d.s56Eps w ∈ d.s56U11) : w ∈ d.s56V := by
  have hwQ0 : w ∈ d.s56Q0 := hd.s56_Q2_le_Q0 h49 hwQ2
  have hnorm : ∀ g ∈ d.M, (∀ q ∈ d.s56Q, g * q * g⁻¹ ∈ d.s56Q) ∧
      ∀ q ∈ d.s56Q, g⁻¹ * q * g ∈ d.s56Q := fun g hg => by
    have h := hd.s56_M_le_normalizer_Q h49 hg
    exact ⟨fun q hq => (mem_normalizer_iff.1 h q).1 hq,
      fun q hq => (mem_normalizer_iff''.1 h q).1 hq⟩
  have htM : d.t ∈ d.M := s56_t_mem_M d
  have hdecomp : ∀ h ∈ d.s56Q ⊔ zpowers d.t, h ∈ d.s56Q ∨ ∃ q ∈ d.s56Q, h = q * d.t :=
    fun h hh => S56.mem_sup_zpowers_of_conj (H := d.s56Q) (a := d.t)
      (by rw [hd.t_mul_self]; exact one_mem _) (fun h hh => (hnorm _ htM).1 h hh)
      (fun h hh => (hnorm _ htM).2 h hh) hh
  have hqt : ∀ q ∈ d.s56Q, (q * d.t) * z₀ = z₀ * (q * d.t) → False := fun q hq h => by
    apply hd.s56_t_not_comm_z0 hz
    apply mul_left_cancel (a := q)
    calc q * (d.t * z₀) = (q * d.t) * z₀ := by group
      _ = z₀ * (q * d.t) := h
      _ = (z₀ * q) * d.t := by group
      _ = (q * z₀) * d.t := by rw [← hz.comm_Q q hq]
      _ = q * (z₀ * d.t) := by group
  have hVmem : w ∈ d.s56Q → w ∈ d.s56V := fun hwq => s56_mem_V_iff.2 ⟨hwq, hwQ2⟩
  rcases hd.centralizer_A with ⟨hr, -⟩ | ⟨hr, -⟩
  ·
    rw [hQD hr] at hwQ0
    rcases hdecomp w hwQ0 with hwq | ⟨q, hq, rfl⟩
    · exact hVmem hwq
    · exact (hqt q hq hwz).elim
  ·
    obtain ⟨y₅, hy5V, hy5z, hy5sq, hy5A, hy5v7, hy5t⟩ := hd.s56_exists_y5 h49 hz hr
    have hy5C : y₅ ∈ centralizer (d.A : Set G) :=
      mem_centralizer_iff.2 fun a ha => (hy5A a ha).symm
    have hy5M : y₅ ∈ d.M := d.s56_centralizer_A_le_M hy5C
    have hy5M' : y₅⁻¹ ∈ d.M := inv_mem hy5M
    have hy5t' : y₅⁻¹ * d.t = d.t * y₅⁻¹ := by
      calc y₅⁻¹ * d.t = y₅⁻¹ * d.t * y₅ * y₅⁻¹ := by group
        _ = y₅⁻¹ * (d.t * y₅) * y₅⁻¹ := by group
        _ = y₅⁻¹ * (y₅ * d.t) * y₅⁻¹ := by rw [hy5t]
        _ = d.t * y₅⁻¹ := by group
    have hzQ : d.z ∈ d.s56Q := hd.s56_E_le_Q h49 hd.s56_z_mem_E
    have hconjH : ∀ (g : G), g ∈ d.M → g * d.t = d.t * g →
        ∀ h ∈ d.s56Q ⊔ zpowers d.t, g * h * g⁻¹ ∈ d.s56Q ⊔ zpowers d.t := fun g hg hgt h hh => by
      rcases hdecomp h hh with hq | ⟨q, hq, rfl⟩
      · exact mem_sup_left ((hnorm g hg).1 h hq)
      · have e : g * (q * d.t) * g⁻¹ = (g * q * g⁻¹) * d.t := by
          calc g * (q * d.t) * g⁻¹ = (g * q * g⁻¹) * (g * d.t * g⁻¹) := by group
            _ = (g * q * g⁻¹) * d.t := by rw [hgt]; group
        rw [e]
        exact mul_mem (mem_sup_left ((hnorm g hg).1 q hq)) (mem_sup_right (mem_zpowers _))
    have hsqH : y₅ * y₅ ∈ d.s56Q ⊔ zpowers d.t := by rw [hy5sq]; exact mem_sup_left hzQ
    rw [hQA y₅ hy5V] at hwQ0
    rcases S56.mem_sup_zpowers_of_conj hsqH (hconjH y₅ hy5M hy5t)
        (fun h hh => by
          have := hconjH y₅⁻¹ hy5M' hy5t' h hh
          simpa using this) hwQ0 with hwH | ⟨h, hhH, rfl⟩
    · rcases hdecomp w hwH with hwq | ⟨q, hq, rfl⟩
      · exact hVmem hwq
      · exact (hqt q hq hwz).elim
    ·
      have hhz : h * z₀ = z₀ * h := by
        apply mul_right_cancel (b := y₅)
        calc h * z₀ * y₅ = h * (z₀ * y₅) := by group
          _ = h * (y₅ * z₀) := by rw [hy5z]
          _ = (h * y₅) * z₀ := by group
          _ = z₀ * (h * y₅) := hwz
          _ = z₀ * h * y₅ := by group
      rcases hdecomp h hhH with hq | ⟨q, hq, rfl⟩
      ·
        exfalso
        have hqV : h ∈ d.s56V := by
          refine s56_mem_V_iff.2 ⟨hq, ?_⟩
          rw [s56_mem_Q2_iff]
          refine ⟨hd.s56_Q0_le_M h49 (hd.s56_Q_le_Q0 hq), fun e he => ?_⟩
          have h1 := ((s56_mem_Q2_iff).1 hwQ2).2 e he
          have h2 : e * y₅ = y₅ * e := (hy5A e (d.s56_E_le_A he)).symm
          apply mul_right_cancel (b := y₅)
          calc e * h * y₅ = e * (h * y₅) := by group
            _ = (h * y₅) * e := h1
            _ = h * (y₅ * e) := by group
            _ = h * (e * y₅) := by rw [h2]
            _ = h * e * y₅ := by group
        have hεy : d.s56Eps y₅ = 1 := hd.s56_eps_of_comm hy5t
        have hεq : d.s56Eps h ∈ d.s56U11 := by
          have := hd.s56_eps_mul h y₅
          rw [hεy] at this
          have e : d.s56Eps (h * y₅) = d.s56Eps h := by
            rw [this]; group
          rwa [← e]
        have hK := hKV h hqV hεq
        have hv7F := hd.s56_pv7_mem_F
        have hv11E := s56_pv11_mem_E d
        have hv11F : d.pv 11 ∈ d.F := s56_U11_le_F d (s56_pv11_mem_U11 d)
        have hw7 := s56_P_conj_F d hwP hv7F
        have hq11 : h * d.pv 11 * h⁻¹ = d.pv 11 := by
          rw [s56_V_comm_E hqV hv11E]; group
        have hqv7 : h * d.pv 7 * h⁻¹ = d.pv 7 * d.pv 11 := by
          have h1 : h * (y₅ * d.pv 7 * y₅⁻¹) * h⁻¹ = d.pv 7 := by
            have e : h * y₅ * d.pv 7 * (h * y₅)⁻¹ = h * (y₅ * d.pv 7 * y₅⁻¹) * h⁻¹ := by group
            rw [← e]
            exact hw7
          rw [hy5v7] at h1
          have e2 : h * (d.pv 7 * d.pv 11) * h⁻¹ = (h * d.pv 7 * h⁻¹) * (h * d.pv 11 * h⁻¹) := by
            group
          rw [e2, hq11] at h1
          calc h * d.pv 7 * h⁻¹ = (h * d.pv 7 * h⁻¹ * d.pv 11) * d.pv 11 := by
                rw [mul_assoc (h * d.pv 7 * h⁻¹), hd.s56_E_sq hv11E, mul_one]
            _ = d.pv 7 * d.pv 11 := by rw [h1]
        have hcomm : h * d.pv 7 * h⁻¹ * (d.pv 7)⁻¹ = d.pv 11 := by
          rw [hqv7, s56_pv7_inv]
          calc d.pv 7 * d.pv 11 * d.pv 7 = (d.pv 11 * d.pv 7) * d.pv 7 := by
                rw [hd.s56_F_comm hv7F hv11F]
            _ = d.pv 11 := by
                rw [mul_assoc, hd.s56_F_sq hv7F, mul_one]
        rw [hcomm] at hK
        exact hd.s56_pv11_not_mem hK
      · exact (hqt q hq hhz).elim

theorem Hyp.s56_c1_mem_FV (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hQD : d.ρ.range = titsD.subgroupOf titsA → d.s56Q0 = d.s56Q ⊔ zpowers d.t)
    (hQA : ∀ y₅ : G, N.IsV5 d y₅ → d.s56Q0 = d.s56Q ⊔ zpowers d.t ⊔ zpowers y₅)
    (hKV : ∀ x ∈ d.s56V, d.s56Eps x ∈ d.s56U11 →
      x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ zpowers d.z) :
    ∃ f ∈ d.F, f * (y * z₀ * y⁻¹) ∈ d.s56V := by
  obtain ⟨f, hf, hw⟩ := hd.s56_exists_f_mul_c1_mem_Q2 h49 hz hsq hy hy3 hy1
  obtain ⟨hc1, -, -, -, hε1, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  obtain ⟨hcomm01, -, -⟩ := hd.s56_z0_conj_comm h49 hz hy hy3 hy1
  obtain ⟨hα, -, -, -, -⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hcP := s56_P11_le_P d hc1
  have hfP : f ∈ d.s56P := hd.s56_B_le_P (s56_F_le_B d hf)
  have hz0P := hd.s56_z0_mem_P h49 hz
  refine ⟨f, hf, hd.s56_mem_V_of_Q2_P h49 hz hQD hQA hKV hw (mul_mem hfP hcP) ?_ ?_⟩
  · have hfz : z₀ * f = f * z₀ := by
      have := s56_P_conj_F d hz0P hf
      calc z₀ * f = (z₀ * f * z₀⁻¹) * z₀ := by group
        _ = f * z₀ := by rw [this]
    calc f * (y * z₀ * y⁻¹) * z₀ = f * ((y * z₀ * y⁻¹) * z₀) := by group
      _ = f * (z₀ * (y * z₀ * y⁻¹)) := by rw [hcomm01]
      _ = (f * z₀) * (y * z₀ * y⁻¹) := by group
      _ = (z₀ * f) * (y * z₀ * y⁻¹) := by rw [hfz]
      _ = z₀ * (f * (y * z₀ * y⁻¹)) := by group
  · rw [hd.s56_eps_mul_P h49 hfP hcP, hd.s56_eps_eq_one_of_mem_B (s56_F_le_B d hf), one_mul, hε1]
    exact hα

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
