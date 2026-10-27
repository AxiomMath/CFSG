module

public import CFSG.CGT.Timmesfeld75.Sec3Eleven
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB3
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB8
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {P Q : Subgroup G}

theorem not_mem_cfgM_of_not_mem_normIn (c : Cfg P Q) {p : G} (hp : p ∈ P)
    (hpL : p ∉ normIn P Q) : p ∉ cfgM P Q := fun hM => hpL (by
  rw [← c.inf_cfgM]
  exact ⟨hp, hM⟩)

theorem eq_one_of_comm (c : Cfg P Q) {p e : G} (hp : p ∈ P) (hpL : p ∉ normIn P Q)
    (he : e ∈ normIn Q P) (h : p * e = e * p) : e = 1 := by
  have hpM := not_mem_cfgM_of_not_mem_normIn c hp hpL
  have h1 : e ∈ cfgM P Q ⊓ Subgroup.centralizer ({p} : Set G) :=
    ⟨Cfg.normIn_le_cfgM_right P Q he, Subgroup.mem_centralizer_iff.2 fun h' hh' => by
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact h⟩
  rw [c.cfgM_inf_centralizer hp hpM] at h1
  have h2 : e ∈ P ⊓ Q := ⟨normIn_le _ _ h1, normIn_le _ _ he⟩
  rw [c.inf, Subgroup.mem_bot] at h2
  exact h2

variable [Finite G]

theorem s3_relation (hS : Sec3 P Q) (hI : Sec3Iso P Q)
    (hQc : Nat.card Q = Nat.card (normIn Q P) * 2) {p q u : G} (hp : p ∈ P)
    (hpL : p ∉ normIn P Q) (hq : q ∈ Q) (hqL : q ∉ normIn Q P) (hu : u ∈ normIn P Q) :
    ⁅p, ⁅q, u⁆⁆ = u := by
  obtain ⟨hN, f, hf, hiso⟩ := hI
  have hpM := not_mem_cfgM_of_not_mem_normIn hS.cfg hp hpL
  have := hN
  obtain ⟨t, htX, htt, hconj, hord⟩ := hS.exists_swap_orderOf_three_of_mem hf hiso hp hpM
  have hM : IsElemAbelian 2 (cfgM P Q) := hS.cfg.isElemAbelian_cfgM
  have hpX : p ∈ P ⊔ Q := Subgroup.mem_sup_left hp
  have haa : p * p = 1 := elemAbelian_mul_self hS.cfg.wc.1 hp
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hodd : Odd (orderOf (p * t)) := by rw [hord]; decide
  have hne : p * t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hno : ¬ ∃ S : Subgroup G, S ≤ P ⊔ Q ∧ IsPGroup 2 S ∧ p ∈ S ∧ t ∈ S := by
    rintro ⟨S, -, hS2, hpS, htS⟩
    exact not_exists_isPGroup_two_mem_of_odd_orderOf (x := p * t) rfl hodd hne
      ⟨S, hS2, hpS, htS⟩
  have hC := hS.cfgM_inf_centralizer_inf_centralizer_of_not_common_two_group hpX haa htX htt hno
  have huM : u ∈ cfgM P Q := Cfg.normIn_le_cfgM_left P Q hu
  have hu'M : t * u * t⁻¹ ∈ cfgM P Q := hS.cfg.conj_mem_cfgM htX huM
  have hau : p * u * p⁻¹ = u := by
    rw [elemAbelian_mul_comm hS.cfg.wc.1 hp (normIn_le P Q hu)]
    group
  have hv : p * (t * u * t⁻¹) * p⁻¹ ∈ cfgM P Q := hS.cfg.conj_mem_cfgM hpX hu'M
  have hrel := conj_conj_eq_mul_of_orderOf_mul_eq_three hM haa htt hord hau huM hu'M hv hC
  have h1 : ⁅p, t * u * t⁻¹⁆ = u := by
    simp only [commutatorElement_def]
    rw [hrel]
    group
  have hq₀ : t * p * t⁻¹ ∈ Q := by
    have := conj_mem_conjSubgroup t hp
    rwa [hconj] at this
  have hq₀L : t * p * t⁻¹ ∉ normIn Q P := by
    intro h0
    apply hpM
    have h2 : t⁻¹ * (t * p * t⁻¹) * t⁻¹⁻¹ ∈ cfgM P Q :=
      hS.cfg.conj_mem_cfgM ((P ⊔ Q).inv_mem htX) (Cfg.normIn_le_cfgM_right P Q h0)
    have e : t⁻¹ * (t * p * t⁻¹) * t⁻¹⁻¹ = p := by group
    rwa [e] at h2
  have htu' : t * (t * u * t⁻¹) * t⁻¹ = u := by
    calc t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [htt]; group
  have hconj' : t⁻¹ * u * t = t * u * t⁻¹ := by rw [hti]
  have h3' : (t * p * t⁻¹) * u * (t * p * t⁻¹)⁻¹ = (t * u * t⁻¹) * u := by
    calc (t * p * t⁻¹) * u * (t * p * t⁻¹)⁻¹ = t * (p * (t⁻¹ * u * t) * p⁻¹) * t⁻¹ := by group
      _ = t * (p * (t * u * t⁻¹) * p⁻¹) * t⁻¹ := by rw [hconj']
      _ = t * (u * (t * u * t⁻¹)) * t⁻¹ := by rw [hrel]
      _ = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by group
      _ = (t * u * t⁻¹) * u := by rw [htu']
  have h3 : ⁅t * p * t⁻¹, u⁆ = t * u * t⁻¹ := by
    simp only [commutatorElement_def]
    rw [h3']
    group
  have hq₀i : (t * p * t⁻¹)⁻¹ ∈ Q := Q.inv_mem hq₀
  have hq₀iL : (t * p * t⁻¹)⁻¹ ∉ normIn Q P := fun h0 => hq₀L (by
    simpa using (normIn Q P).inv_mem h0)
  have hℓ : (t * p * t⁻¹)⁻¹ * q ∈ normIn Q P :=
    mul_mem_of_not_mem_of_card (normIn_le Q P) hQc hq₀i hq hq₀iL hqL
  have hcomm : u * ((t * p * t⁻¹)⁻¹ * q) = ((t * p * t⁻¹)⁻¹ * q) * u := hS.cfg.comm_L_L₁ hu hℓ
  have h4 : ⁅q, u⁆ = t * u * t⁻¹ := by
    rw [← h3]
    simp only [commutatorElement_def]
    have e : q = (t * p * t⁻¹) * ((t * p * t⁻¹)⁻¹ * q) := by group
    set q₀ := t * p * t⁻¹ with hq₀def
    set ℓ := q₀⁻¹ * q with hℓdef
    have e2 : q * u * q⁻¹ = q₀ * u * q₀⁻¹ := by
      rw [e]
      calc q₀ * ℓ * u * (q₀ * ℓ)⁻¹ = q₀ * (ℓ * u * ℓ⁻¹) * q₀⁻¹ := by group
        _ = q₀ * (u * ℓ * ℓ⁻¹) * q₀⁻¹ := by rw [← hcomm]
        _ = q₀ * u * q₀⁻¹ := by group
    rw [e2]
  rw [h4]
  exact h1

end CFSG.CGT.T75R
