module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610D

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem S_cent_alpha {α : G} (hα : AlphaSpec S z t α) {y : G} (hyS : y ∈ S)
    (hyα : y * α = α * y) : y = 1 ∨ y = t ∨ y = α ∨ y = α * t := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  rcases hα.list y hyS with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exfalso
    rw [h1] at hyα
    exact h.sigma_z_a hα hyα
  · exfalso
    rw [h1] at hyα
    apply h.sigma_z_a hα
    have h2 : z * α * t = α * z * t := by
      calc z * α * t = z * (α * t) := by group
        _ = z * (t * α) := by rw [hαt]
        _ = (z * t) * α := by group
        _ = α * (z * t) := hyα
        _ = α * z * t := by group
    exact mul_right_cancel h2
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))
  · exfalso
    rw [h1] at hyα
    exact h.sigma_r_a hα hyα
  · exfalso
    rw [h1] at hyα
    apply h.sigma_r_a hα
    have h2 : (α * z) * α * t = α * (α * z) * t := by
      calc (α * z) * α * t = (α * z) * (α * t) := by group
        _ = (α * z) * (t * α) := by rw [hαt]
        _ = (α * z * t) * α := by group
        _ = α * (α * z * t) := hyα
        _ = α * (α * z) * t := by group
    exact mul_right_cancel h2

theorem Zg_comm_E {α : G} (hα : AlphaSpec S z t α) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) {e : G} (he : e ∈ E) : a * e = e * a := by
  have hZS : (zpowers α ⊔ zpowers t : Subgroup G) ≤ S :=
    sup_le (zpowers_le.2 hα.mem) (zpowers_le.2 h.t_mem_S)
  exact h.S_comm_E a (hZS ha) e he

theorem F_conj_E {α : G} (hα : AlphaSpec S z t α) {f : G} (hf : f ∈ Fsub h hα) {e : G}
    (he : e ∈ E) :
    ∃ a ∈ (zpowers α ⊔ zpowers t : Subgroup G), f * e * f⁻¹ = a * e := by
  let D : Subgroup G :=
    { carrier := {e | e ∈ E ∧ ∃ a ∈ (zpowers α ⊔ zpowers t : Subgroup G), f * e * f⁻¹ = a * e}
      mul_mem' := by
        rintro e₁ e₂ ⟨h₁, a₁, ha₁, hf₁⟩ ⟨h₂, a₂, ha₂, hf₂⟩
        refine ⟨mul_mem h₁ h₂, a₁ * a₂, mul_mem ha₁ ha₂, ?_⟩
        have hc : e₁ * a₂ = a₂ * e₁ := (h.Zg_comm_E hα ha₂ h₁).symm
        calc f * (e₁ * e₂) * f⁻¹ = (f * e₁ * f⁻¹) * (f * e₂ * f⁻¹) := by group
          _ = (a₁ * e₁) * (a₂ * e₂) := by rw [hf₁, hf₂]
          _ = a₁ * (e₁ * a₂) * e₂ := by group
          _ = a₁ * (a₂ * e₁) * e₂ := by rw [hc]
          _ = (a₁ * a₂) * (e₁ * e₂) := by group
      one_mem' := ⟨one_mem _, 1, one_mem _, by group⟩
      inv_mem' := by
        rintro e ⟨he, a, ha, hfe⟩
        refine ⟨inv_mem he, a⁻¹, inv_mem ha, ?_⟩
        have hc : e⁻¹ * a⁻¹ = a⁻¹ * e⁻¹ := by
          have := h.Zg_comm_E hα (inv_mem ha) (inv_mem he)
          exact this.symm
        calc f * e⁻¹ * f⁻¹ = (f * e * f⁻¹)⁻¹ := by group
          _ = (a * e)⁻¹ := by rw [hfe]
          _ = e⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * e⁻¹ := hc }
  have hEle : E ≤ D := by
    have := h.oe.econfig.gen
    rw [this]
    rw [closure_le]
    intro e he
    obtain ⟨heE, he2, he1⟩ := he
    by_cases het : e = t
    · refine ⟨heE, 1, one_mem _, ?_⟩
      rw [het, h.conj_t_of_M hf.1, one_mul]
    · exact ⟨heE, hf.2 e ⟨heE, he2, he1, het⟩⟩
  exact (hEle he).2

theorem Zg_comm {α : G} (hα : AlphaSpec S z t α) {a b : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (hb : b ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : a * b = b * a := by
  have hcomm : Commute α t := h.t_comm_S α hα.mem
  rcases (h.mem_Zg hα).1 ha with h1 | h1 | h1 | h1 <;>
    rcases (h.mem_Zg hα).1 hb with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
    first
    | exact (Commute.refl _).eq
    | exact (Commute.one_left _).eq
    | exact (Commute.one_right _).eq
    | exact hcomm.eq
    | exact hcomm.symm.eq
    | exact ((Commute.refl α).mul_right hcomm).eq
    | exact ((Commute.refl α).mul_right hcomm).symm.eq
    | exact (hcomm.symm.mul_right (Commute.refl t)).eq
    | exact (hcomm.symm.mul_right (Commute.refl t)).symm.eq

theorem Zg_sq {α : G} (hα : AlphaSpec S z t α) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : a * a = 1 := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  rcases (h.mem_Zg hα).1 ha with h1 | h1 | h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact h.t_sq
  · rw [h1]; exact hα.sq
  · rw [h1]
    calc α * t * (α * t) = α * (t * α) * t := by group
      _ = α * (α * t) * t := by rw [← hαt]
      _ = (α * α) * (t * t) := by group
      _ = 1 := by rw [hα.sq, h.t_sq, one_mul]

theorem QF_comm_Z {α : G} (hα : AlphaSpec S z t α) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : q * a = a * q := by
  have hqα : q * α = α * q := mem_centralizer_singleton_iff.1 hq.2
  have hqt : q * t = t * q := by
    have := h.conj_t_of_M hq.1.1
    calc q * t = (q * t * q⁻¹) * q := by group
      _ = t * q := by rw [this]
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  rcases (h.mem_Zg hα).1 ha with h1 | h1 | h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact hqt
  · rw [h1]; exact hqα
  · rw [h1]
    calc q * (α * t) = (q * α) * t := by group
      _ = (α * q) * t := by rw [hqα]
      _ = α * (q * t) := by group
      _ = α * (t * q) := by rw [hqt]
      _ = (α * t) * q := by group

theorem QF_cent_E {α : G} (hα : AlphaSpec S z t α) {c : G}
    (hc : c ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) (hcE : ∀ e ∈ E, c * e = e * c) :
    c = 1 ∨ c = t ∨ c = α ∨ c = α * t :=
  h.S_cent_alpha hα (h.cent_E_M hc.1.1 hcE) (mem_centralizer_singleton_iff.1 hc.2)

theorem QF_comm {α : G} (hα : AlphaSpec S z t α) {q q' : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hq' : q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ∃ c, (c = 1 ∨ c = t ∨ c = α ∨ c = α * t) ∧ q * q' = c * (q' * q) := by
  set c : G := (q' * q)⁻¹ * (q * q') with hcdef
  have hcQ : c ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
    mul_mem (inv_mem (mul_mem hq' hq)) (mul_mem hq hq')
  have hcE : ∀ e ∈ E, c * e = e * c := by
    intro e he
    obtain ⟨a, ha, hqe⟩ := h.F_conj_E hα hq.1 he
    obtain ⟨a', ha', hq'e⟩ := h.F_conj_E hα hq'.1 he
    have hqa' : q * a' * q⁻¹ = a' := by rw [h.QF_comm_Z hα hq ha']; group
    have hq'a : q' * a * q'⁻¹ = a := by rw [h.QF_comm_Z hα hq' ha]; group
    have h1 : (q * q') * e * (q * q')⁻¹ = a' * (a * e) := by
      calc (q * q') * e * (q * q')⁻¹ = q * (q' * e * q'⁻¹) * q⁻¹ := by group
        _ = q * (a' * e) * q⁻¹ := by rw [hq'e]
        _ = (q * a' * q⁻¹) * (q * e * q⁻¹) := by group
        _ = a' * (a * e) := by rw [hqa', hqe]
    have h2 : (q' * q) * e * (q' * q)⁻¹ = a * (a' * e) := by
      calc (q' * q) * e * (q' * q)⁻¹ = q' * (q * e * q⁻¹) * q'⁻¹ := by group
        _ = q' * (a * e) * q'⁻¹ := by rw [hqe]
        _ = (q' * a * q'⁻¹) * (q' * e * q'⁻¹) := by group
        _ = a * (a' * e) := by rw [hq'a, hq'e]
    have haa' : a' * a = a * a' := h.Zg_comm hα ha' ha
    have h3 : (q * q') * e * (q * q')⁻¹ = (q' * q) * e * (q' * q)⁻¹ := by
      rw [h1, h2]
      calc a' * (a * e) = (a' * a) * e := by group
        _ = (a * a') * e := by rw [haa']
        _ = a * (a' * e) := by group
    have h4 : c * e * c⁻¹ = e := by
      calc c * e * c⁻¹ = (q' * q)⁻¹ * ((q * q') * e * (q * q')⁻¹) * (q' * q) := by
            rw [hcdef]; group
        _ = (q' * q)⁻¹ * ((q' * q) * e * (q' * q)⁻¹) * (q' * q) := by rw [h3]
        _ = e := by group
    calc c * e = (c * e * c⁻¹) * c := by group
      _ = e * c := by rw [h4]
  have hc4 := h.QF_cent_E hα hcQ hcE
  have hcZ : c ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 hc4
  refine ⟨c, hc4, ?_⟩
  have h5 := h.QF_comm_Z hα (mul_mem hq' hq) hcZ
  calc q * q' = (q' * q) * c := by rw [hcdef]; group
    _ = c * (q' * q) := h5

theorem QF_sq {α : G} (hα : AlphaSpec S z t α) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q * q = 1 ∨ q * q = t ∨ q * q = α ∨ q * q = α * t := by
  have hcQ : q * q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := mul_mem hq hq
  apply h.QF_cent_E hα hcQ
  intro e he
  obtain ⟨a, ha, hqe⟩ := h.F_conj_E hα hq.1 he
  have hqa : q * a * q⁻¹ = a := by rw [h.QF_comm_Z hα hq ha]; group
  have haa : a * a = 1 := h.Zg_sq hα ha
  have h1 : (q * q) * e * (q * q)⁻¹ = e := by
    calc (q * q) * e * (q * q)⁻¹ = q * (q * e * q⁻¹) * q⁻¹ := by group
      _ = q * (a * e) * q⁻¹ := by rw [hqe]
      _ = (q * a * q⁻¹) * (q * e * q⁻¹) := by group
      _ = a * (a * e) := by rw [hqa, hqe]
      _ = (a * a) * e := by group
      _ = e := by rw [haa, one_mul]
  calc (q * q) * e = ((q * q) * e * (q * q)⁻¹) * (q * q) := by group
    _ = e * (q * q) := by rw [h1]

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
