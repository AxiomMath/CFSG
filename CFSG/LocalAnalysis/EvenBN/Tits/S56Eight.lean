module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Z2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.s56_J_sup_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.s56J ⊔ d.s56Q2 = d.s56Q0 := by
  have hJQ0 := hd.s56_J_le_Q0 h49
  have hQ2Q0 := hd.s56_Q2_le_Q0 h49
  have hle : d.s56J ⊔ d.s56Q2 ≤ d.s56Q0 := sup_le hJQ0 hQ2Q0
  obtain ⟨-, hQ2c, -, -, hQ0c, -⟩ := hd.s56_structure_M h49
  have hJM : d.s56J ≤ d.M := hd.s56_J_le_M
  have hQ2M : d.s56Q2 ≤ d.M := fun _ hq => ((s56_mem_Q2_iff).1 hq).1
  haveI : (d.s56Q2.subgroupOf d.M).Normal :=
    ⟨fun n hn g => hd.s56_Q2_conj_mem g.2 hn⟩
  have hrel : d.s56Q2.relIndex (d.s56J ⊔ d.s56Q2) = d.s56Q2.relIndex d.s56J := by
    have h := Subgroup.relIndex_sup_right (H := d.s56J.subgroupOf d.M)
      (K := d.s56Q2.subgroupOf d.M)
    rw [← Subgroup.subgroupOf_sup hJM hQ2M,
      Subgroup.relIndex_subgroupOf (sup_le hJM hQ2M),
      Subgroup.relIndex_subgroupOf hJM] at h
    exact h
  have h1 := Subgroup.relIndex_mul_card (H := d.s56Q2) (K := d.s56J)
  rw [inf_comm, hd.s56_J_inf_Q2, hd.A_facts.1, hd.s56_card_J] at h1
  have h2 := Subgroup.relIndex_mul_card (H := d.s56Q2) (K := d.s56J ⊔ d.s56Q2)
  rw [inf_of_le_left le_sup_right, hrel] at h2
  have h16 : d.s56Q2.relIndex d.s56J = 16 := by omega
  rw [h16] at h2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← h2, hQ0c, hQ2c]
  omega

theorem Hyp.s56_Q0_eq_J_mul_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G}
    (hq : q ∈ d.s56Q0) : ∃ j ∈ d.s56J, ∃ w ∈ d.s56Q2, q = j * w := by
  rw [← hd.s56_J_sup_Q2 h49] at hq
  let P : Subgroup G :=
    { carrier := {x | ∃ j ∈ d.s56J, ∃ w ∈ d.s56Q2, x = j * w}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨j, hj, w, hw, rfl⟩ ⟨j', hj', w', hw', rfl⟩
        exact ⟨j * j', mul_mem hj hj', (j'⁻¹ * w * j'⁻¹⁻¹) * w',
          mul_mem (hd.s56_Q2_conj_mem (inv_mem (hd.s56_J_le_M hj')) hw) hw', by group⟩
      inv_mem' := by
        rintro _ ⟨j, hj, w, hw, rfl⟩
        exact ⟨j⁻¹, inv_mem hj, j * w⁻¹ * j⁻¹,
          hd.s56_Q2_conj_mem (hd.s56_J_le_M hj) (inv_mem hw), by group⟩ }
  have hsup : d.s56J ⊔ d.s56Q2 ≤ P :=
    sup_le (fun j hj => ⟨j, hj, 1, one_mem _, by simp⟩)
      (fun w hw => ⟨1, one_mem _, w, hw, by simp⟩)
  exact hsup hq

theorem Hyp.s56_Q2_comm_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) {w w' : G}
    (hw : w ∈ d.s56Q2) (hw' : w' ∈ d.s56Q2) : w * w' * w⁻¹ * w'⁻¹ ∈ d.E := by
  have hsq := hd.s56_Q2_sq_mem_E_all h49
  have h1 := hsq (w * w') (mul_mem hw hw')
  have ha := hsq w⁻¹ (inv_mem hw)
  have hb := hsq w'⁻¹ (inv_mem hw')
  have hcomm : (w⁻¹ * w⁻¹) * w' = w' * (w⁻¹ * w⁻¹) :=
    ((s56_mem_Q2_iff).1 hw').2 _ ha
  have e : w * w' * w⁻¹ * w'⁻¹ = (w * w' * (w * w')) * (w⁻¹ * w⁻¹) * (w'⁻¹ * w'⁻¹) := by
    calc w * w' * w⁻¹ * w'⁻¹
        = w * w' * (w * (w⁻¹ * w⁻¹)) * (w' * (w'⁻¹ * w'⁻¹)) := by group
      _ = w * w' * w * ((w⁻¹ * w⁻¹) * w') * (w'⁻¹ * w'⁻¹) := by group
      _ = w * w' * w * (w' * (w⁻¹ * w⁻¹)) * (w'⁻¹ * w'⁻¹) := by rw [hcomm]
      _ = (w * w' * (w * w')) * (w⁻¹ * w⁻¹) * (w'⁻¹ * w'⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem h1 ha) hb

theorem Hyp.s56_Q_comm_le_S (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₁ * e) :
    ⁅d.s56Q, d.s56Q⁆ ≤ d.E ⊔ zpowers z₁ := by
  have hz₁sq := hd.s56_Q2_sq_mem_E_all h49 z₁ hz₁
  set S : Subgroup G := d.E ⊔ zpowers z₁ with hS
  have hES : d.E ≤ S := le_sup_left
  refine Subgroup.commutator_le.2 fun q hq q' hq' => ?_
  obtain ⟨j, hj, w, hw, rfl⟩ := hd.s56_Q0_eq_J_mul_Q2 h49 (hd.s56_Q_le_Q0 hq)
  obtain ⟨j', hj', w', hw', rfl⟩ := hd.s56_Q0_eq_J_mul_Q2 h49 (hd.s56_Q_le_Q0 hq')
  have hJS := fun j hj s hs => hd.s56_J_conj_S h49 hz₁ hε hz₁sq (j := j) hj (s := s) hs
  have hjE : ∀ e ∈ d.E, j' * e * j'⁻¹ ∈ d.E := fun e he =>
    (mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M hj')) e).1 he
  have hwj' : w * j' * w⁻¹ * j'⁻¹ ∈ S := by
    have h := hd.s56_J_comm_Q2_mem h49 hz₁ hε hdich hj' hw
    have e : w * j' * w⁻¹ * j'⁻¹ = (j' * w * j'⁻¹ * w⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem h
  have hww' := hd.s56_Q2_comm_mem_E h49 hw hw'
  have hjj' := hd.s56_J_comm_le_E hj hj'
  have hjw' := hd.s56_J_comm_Q2_mem h49 hz₁ hε hdich hj hw'
  have e : (j * w) * (j' * w') * (j * w)⁻¹ * (j' * w')⁻¹ =
      j * ((w * j' * w⁻¹ * j'⁻¹) * (j' * (w * w' * w⁻¹ * w'⁻¹) * j'⁻¹)) * j⁻¹ *
        ((j * j' * j⁻¹ * j'⁻¹) * (j' * (j * w' * j⁻¹ * w'⁻¹) * j'⁻¹)) := by group
  show (j * w) * (j' * w') * (j * w)⁻¹ * (j' * w')⁻¹ ∈ S
  rw [e]
  refine mul_mem ?_ ?_
  · exact hJS j hj _ (mul_mem hwj' (hES (hjE _ hww')))
  · exact mul_mem (hES hjj') (hd.s56_J_conj_S h49 hz₁ hε hz₁sq hj' hjw')

theorem Hyp.s56_C_conj_X_mem_E (hd : d.Hyp) {c g : G} (hc : c ∈ centralizer (d.A : Set G))
    (hg : g ∈ zpowers d.x₅) : c⁻¹ * (g * c * g⁻¹) ∈ d.E := by
  have hxM := hd.s56_x5_mem_M
  have hNC := s56_M_le_normalizer_C d
  let T : Subgroup G :=
    { carrier := {g | g ∈ d.M ∧ ∀ c ∈ centralizer (d.A : Set G), c⁻¹ * (g * c * g⁻¹) ∈ d.E}
      one_mem' := ⟨one_mem _, fun c hc => by simpa using one_mem d.E⟩
      mul_mem' := by
        rintro g h ⟨hgM, hg⟩ ⟨hhM, hh⟩
        refine ⟨mul_mem hgM hhM, fun c hc => ?_⟩
        have hc' : h * c * h⁻¹ ∈ centralizer (d.A : Set G) :=
          (mem_normalizer_iff.1 (hNC hhM) c).1 hc
        have h1 := hg _ hc'
        have e : c⁻¹ * (g * h * c * (g * h)⁻¹) =
            (c⁻¹ * (h * c * h⁻¹)) * ((h * c * h⁻¹)⁻¹ * (g * (h * c * h⁻¹) * g⁻¹)) := by group
        rw [e]
        exact mul_mem (hh c hc) h1
      inv_mem' := by
        rintro g ⟨hgM, hg⟩
        refine ⟨inv_mem hgM, fun c hc => ?_⟩
        have hc' : g⁻¹ * c * g ∈ centralizer (d.A : Set G) := by
          have := (mem_normalizer_iff.1 (hNC (inv_mem hgM)) c).1 hc
          simpa using this
        have h1 := hg _ hc'
        have e : c⁻¹ * (g⁻¹ * c * g⁻¹⁻¹) = ((g⁻¹ * c * g)⁻¹ * (g * (g⁻¹ * c * g) * g⁻¹))⁻¹ := by
          group
        rw [e]
        exact inv_mem h1 }
  have hxT : d.x₅ ∈ T := by
    refine ⟨hxM, fun c hc => ?_⟩
    have hxc : d.x₅ * c * d.x₅⁻¹ ∈ centralizer (d.A : Set G) :=
      (mem_normalizer_iff.1 (hNC hxM) c).1 hc
    exact S56.conj_mem_of_index_le_four hd.s56_orderOf_x5 hd.s56_E_le_C (hd.s56_ME hxM)
      (hNC hxM) hd.s56_relIndex_E_C_le (mul_mem (inv_mem hc) hxc)
  exact ((zpowers_le.2 hxT) hg).2 c hc

theorem Hyp.s56_Q_inf_C (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.s56Q ⊓ centralizer (d.A : Set G) = d.E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z₁, hz₁Q2, hz₁Q, hεz, -, hdich⟩ := hd.s56_exists_z1 h49
  have hSQ := hd.s56_Q_comm_le_S h49 hz₁Q2 hεz hdich
  have hEQ := hd.s56_E_le_Q h49
  refine le_antisymm (fun c hc => ?_) (fun e he => ⟨hEQ he, hd.s56_E_le_C he⟩)
  obtain ⟨hcQ, hcC⟩ := mem_inf.1 hc
  have hCp : IsPGroup 2 (centralizer (d.A : Set G)) := hd.s56_centralizer_A.1
  have hXN : zpowers d.x₅ ≤ normalizer (centralizer (d.A : Set G) : Set G) :=
    hd.s56_X_le_M.trans (s56_M_le_normalizer_C d)
  obtain ⟨c₁, hc₁, k, hk, rfl⟩ := S56.coprime_decomp_mem (p := 2) (r := 5) (by norm_num) hCp
    hd.s56_X_isPGroup hXN hcC
  have hc₁E : c₁ ∈ d.E := by
    have hle : ⁅centralizer (d.A : Set G), zpowers d.x₅⁆ ≤ d.E := by
      refine Subgroup.commutator_le.2 fun c' hc' g hg => ?_
      have := hd.s56_C_conj_X_mem_E (inv_mem hc') hg
      simpa [commutatorElement_def, mul_assoc] using this
    exact hle hc₁
  have hkQ : k ∈ d.s56Q := by
    have : k = c₁⁻¹ * (c₁ * k) := by group
    rw [this]
    exact mul_mem (inv_mem (hEQ hc₁E)) hcQ
  obtain ⟨hkC, hkX⟩ := mem_inf.1 hk
  have hQ2 : IsPGroup 2 d.s56Q := IsPGroup.to_le (s56_Q0_isPGroup d) hd.s56_Q_le_Q0
  have hQX : zpowers d.x₅ ≤ normalizer (d.s56Q : Set G) :=
    hd.s56_X_le_M.trans (hd.s56_M_le_normalizer_Q h49)
  have hkS := hSQ (S56.centralizer_le_derived_of_commutator_eq (p := 2) (r := 5) (by norm_num)
    hQ2 hd.s56_X_isPGroup hQX hd.s56_Q_comm_X (mem_inf.2 ⟨hkQ, hkX⟩))
  have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he =>
    (((s56_mem_Q2_iff).1 hz₁Q2).2 e he).symm
  have hz₁sq := hd.s56_Q2_sq_mem_E_all h49 z₁ hz₁Q2
  have hkE : k ∈ d.E := by
    rcases s56y_mem_sup_zpowers (A := d.E) hcen hz₁sq hkS with h | ⟨e, he, rfl⟩
    · exact h
    · exfalso
      have hz₁C : z₁ ∈ centralizer (d.A : Set G) := by
        have : z₁ = (z₁ * e) * e⁻¹ := by group
        rw [this]
        exact mul_mem hkC (inv_mem (hd.s56_E_le_C he))
      have hcomm := ((hd.s56_mem_centralizer_A_iff).1 hz₁C).2
      have h1 := hd.s56_conj_t z₁
      rw [hεz] at h1
      have h2 : z₁ * d.t * z₁⁻¹ = d.t := by rw [hcomm]; group
      rw [h2] at h1
      have : d.z = 1 := by
        have h3 : d.t * 1 = d.t * d.z := by rw [mul_one]; exact h1
        exact (mul_left_cancel h3).symm
      exact hd.s56_z_ne_one this
  exact mul_mem (hc₁E) hkE

theorem Hyp.s56_CQX_le_S (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₁ * e) :
    d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) ≤ d.E ⊔ zpowers z₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ2 : IsPGroup 2 d.s56Q := IsPGroup.to_le (s56_Q0_isPGroup d) hd.s56_Q_le_Q0
  have hQX : zpowers d.x₅ ≤ normalizer (d.s56Q : Set G) :=
    hd.s56_X_le_M.trans (hd.s56_M_le_normalizer_Q h49)
  exact fun w hw => hd.s56_Q_comm_le_S h49 hz₁ hε hdich
    (S56.centralizer_le_derived_of_commutator_eq (p := 2) (r := 5) (by norm_num)
      hQ2 hd.s56_X_isPGroup hQX hd.s56_Q_comm_X hw)

theorem Hyp.s56_E_le_Q2 (hd : d.Hyp) : d.E ≤ d.s56Q2 := fun e he =>
  (s56_mem_Q2_iff).2 ⟨s56_E_le_M d he, fun e' he' => hd.s56_E_comm he' he⟩

theorem Hyp.s56_eps_of_comm (hd : d.Hyp) {m : G} (hm : m * d.t = d.t * m) : d.s56Eps m = 1 := by
  rw [s56Eps]
  have : m * d.t * m⁻¹ = d.t := by rw [hm]; group
  rw [this, hd.t_mul_self]

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
