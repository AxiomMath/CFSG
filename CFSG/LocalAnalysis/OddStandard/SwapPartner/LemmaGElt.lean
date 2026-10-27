module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}

private theorem centData_ne_one (hC : CentData z ι) : z ≠ 1 := by
  intro h
  have h1 : orderOf z = 1 := by rw [h, orderOf_one]
  rw [hC.order] at h1
  exact absurd h1 (by norm_num)

private theorem pow_mul_self_eq_one {H : Type} [Group H] {x : H} (h : x * x = 1) (n : ℕ) :
    x ^ n * x ^ n = 1 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two, h]
  rw [← pow_add, show n + n = 2 * n from by ring, pow_mul, h2, one_pow]

private theorem mul_self_eq_one_of_comm {H : Type} [Group H] {a b : H}
    (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

private theorem card_cycleType_eq_of_support_card {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    {k : ℕ} (hs : σ.support.card = 2 * k) : Multiset.card σ.cycleType = k := by
  have h := card_support_eq_two_mul_card_cycleType hσ
  omega

private theorem conj_E_pow {g z : G} {ι : Perm (Fin 10) →* G}
    (hz : g * z * g⁻¹ = ι τ₀) (hx : g * ι τ₀ * g⁻¹ = z) (i j : ℕ) :
    g * (z ^ i * (ι τ₀) ^ j) * g⁻¹ = (ι τ₀) ^ i * z ^ j := by
  calc g * (z ^ i * (ι τ₀) ^ j) * g⁻¹
      = (g * z ^ i * g⁻¹) * (g * (ι τ₀) ^ j * g⁻¹) := by group
    _ = (g * z * g⁻¹) ^ i * (g * ι τ₀ * g⁻¹) ^ j := by
          rw [← conj_pow (i := i) (a := g) (b := z),
              ← conj_pow (i := j) (a := g) (b := ι τ₀)]
    _ = (ι τ₀) ^ i * z ^ j := by rw [hz, hx]

private theorem conj_mem_CEgrp {g : G} (hC : CentData z ι)
    (hz : g * z * g⁻¹ = ι τ₀) (hx : g * ι τ₀ * g⁻¹ = z)
    {c : G} (hc : c ∈ CEgrp z ι) : g * c * g⁻¹ ∈ CEgrp z ι := by
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1
  have hcx : c * (ι τ₀) = (ι τ₀) * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  unfold CEgrp
  rw [mem_inf]
  constructor
  · rw [mem_centralizer_singleton_iff]
    have hgz : g⁻¹ * z * g = ι τ₀ := by rw [← hx]; group
    calc (g * c * g⁻¹) * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (c * (ι τ₀)) * g⁻¹ := by rw [hgz]
      _ = g * ((ι τ₀) * c) * g⁻¹ := by rw [hcx]
      _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [hgz]
      _ = z * (g * c * g⁻¹) := by group
  · rw [mem_centralizer_singleton_iff]
    have hgx : g⁻¹ * (ι τ₀) * g = z := by rw [← hz]; group
    calc (g * c * g⁻¹) * (ι τ₀) = g * (c * (g⁻¹ * (ι τ₀) * g)) * g⁻¹ := by group
      _ = g * (c * z) * g⁻¹ := by rw [hgx]
      _ = g * (z * c) * g⁻¹ := by rw [hcz]
      _ = g * ((g⁻¹ * (ι τ₀) * g) * c) * g⁻¹ := by rw [hgx]
      _ = (ι τ₀) * (g * c * g⁻¹) := by group

private theorem conj_mem_Egrp {g : G} (hC : CentData z ι)
    (hz : g * z * g⁻¹ = ι τ₀) (hx : g * ι τ₀ * g⁻¹ = z)
    {e : G} (he : e ∈ Egrp z ι) : g * e * g⁻¹ ∈ Egrp z ι := by
  obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 he
  rw [mem_Egrp_iff hC]
  refine ⟨j, i, ?_⟩
  rw [conj_E_pow hz hx (i : ℕ) (j : ℕ)]
  exact ((show Commute z (ι τ₀) from hC.comm τ₀).symm.pow_pow (i : ℕ) (j : ℕ)).eq

private theorem sq_eq_one_of_mem_Egrp (hC : CentData z ι) {e : G} (he : e ∈ Egrp z ι) :
    e * e = 1 := by
  obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 he
  have hx1 : (ι τ₀) * (ι τ₀) = 1 := by rw [← map_mul, τ₀_mul_self, map_one]
  calc (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) * (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ))
      = (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) ^ 2 := by rw [pow_two]
    _ = (z ^ (i:ℕ)) ^ 2 * ((ι τ₀) ^ (j:ℕ)) ^ 2 :=
        ((show Commute z (ι τ₀) from hC.comm τ₀).pow_pow (i:ℕ) (j:ℕ)).mul_pow 2
    _ = 1 := by
          rw [pow_two, pow_two, pow_mul_self_eq_one hC.mul_self (i:ℕ),
              pow_mul_self_eq_one hx1 (j:ℕ), one_mul]

private theorem pairOrder_z_swap_one (hC : CentData z ι) :
    pairOrder z (ι (swap 0 1)) = N10 1 := by
  have hr1 : (swap 0 1 : Perm (Fin 10)) = liftS8 r₁' := by rw [liftS8_r₁']; rfl
  have h2 : (swap 0 1 : Perm (Fin 10)) * swap 0 1 = 1 := by decide
  have hcard : Multiset.card (swap 0 1 : Perm (Fin 10)).cycleType = 1 := by
    rw [hr1, cycleType_liftS8, card_cycleType_r₁']
  rw [pairOrder, hC.card_inf_centralizer (swap 0 1),
      two_mul_card_centralizer_perm_ten h2, hcard]

private theorem pairOrder_z_z_swap_mul_tau (hC : CentData z ι) :
    pairOrder z (z * ι ((swap 0 1 : Perm (Fin 10)) * τ₀)) = N10 2 := by
  have h2 : ((swap 0 1 : Perm (Fin 10)) * τ₀) * (swap 0 1 * τ₀) = 1 := by decide
  have hcard : Multiset.card ((swap 0 1 : Perm (Fin 10)) * τ₀).cycleType = 2 :=
    card_cycleType_eq_of_support_card h2 (by decide)
  rw [pairOrder_mul_right (p := z) (q := ι ((swap 0 1) * τ₀)) (hC.comm ((swap 0 1) * τ₀)),
      pairOrder, hC.card_inf_centralizer ((swap 0 1) * τ₀),
      two_mul_card_centralizer_perm_ten h2, hcard]

private theorem N10_one_ne_two : N10 1 ≠ N10 2 := by
  norm_num [N10, Nat.factorial]

private theorem eq_z_or_eq_x1_of_mem_Egrp_of_isConj (hC : CentData z ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) {w : G} (hw : w ∈ Egrp z ι) (hc : IsConj z w) :
    w = z ∨ w = ι τ₀ := by
  obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 hw
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hc
  · exact absurd (isConj_one_left.mp hc) (centData_ne_one hC)
  · exact Or.inr (by simp)
  · exact Or.inl (by simp)
  · exact absurd hc hP2

theorem GElt.of_swap_of_comm_A (hC : CentData z ι) (hz : g * z * g⁻¹ = ι τ₀)
    (hx : g * ι τ₀ * g⁻¹ = z)
    (hA : ∀ ρ ∈ alternatingGroup (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g) :
    GElt z ι g := by
  have hgA : g ∈ centralizer (Agrp ι : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨ρ, hρ, rfl⟩ := mem_Agrp_iff.1 ha
    exact (hA ρ hρ).symm
  have hcommA : ∀ a ∈ Agrp ι, a * g = g * a := fun a ha => mem_centralizer_iff.1 hgA a ha
  have hggA : g * g ∈ centralizer (Agrp ι : Set G) := mul_mem hgA hgA
  have hgz : g * z = ι τ₀ * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = ι τ₀ * g := by rw [hz]
  have hgx : g * ι τ₀ = z * g := by
    calc g * ι τ₀ = (g * ι τ₀ * g⁻¹) * g := by group
      _ = z * g := by rw [hx]
  have hggCE : g * g ∈ CEgrp z ι := by
    unfold CEgrp
    rw [mem_inf]
    constructor
    · rw [mem_centralizer_singleton_iff]
      calc (g * g) * z = g * (g * z) := by group
        _ = g * (ι τ₀ * g) := by rw [hgz]
        _ = (g * ι τ₀) * g := by group
        _ = (z * g) * g := by rw [hgx]
        _ = z * (g * g) := by group
    · rw [mem_centralizer_singleton_iff]
      calc (g * g) * (ι τ₀) = g * (g * (ι τ₀)) := by group
        _ = g * (z * g) := by rw [hgx]
        _ = (g * z) * g := by group
        _ = (ι τ₀ * g) * g := by rw [hgz]
        _ = (ι τ₀) * (g * g) := by group
  have hggE : g * g ∈ Egrp z ι := by
    have : g * g ∈ centralizer (Agrp ι : Set G) ⊓ CEgrp z ι := mem_inf.2 ⟨hggA, hggCE⟩
    rwa [centralizer_Agrp_inf_CEgrp hC] at this
  obtain ⟨i, j, hij⟩ := (mem_Egrp_iff hC).1 hggE
  have hEq : z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) = (ι τ₀) ^ (i:ℕ) * z ^ (j:ℕ) := by
    have key : g * (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) * g⁻¹
        = z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) := by
      calc g * (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) * g⁻¹ = g * (g * g) * g⁻¹ := by rw [← hij]
        _ = g * g := by group
        _ = z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) := hij
    rw [conj_E_pow hz hx (i:ℕ) (j:ℕ)] at key
    exact key.symm
  have hsq : g * g = 1 ∨ g * g = z * ι τ₀ := by
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hEq hij ⊢
    · exact Or.inl hij
    · exact absurd hEq (hC.ne_z τ₀)
    · exact absurd hEq.symm (hC.ne_z τ₀)
    · exact Or.inr hij
  set d : G := ι (liftS8 r₁') with hd_def
  have hdCE : d ∈ CEgrp z ι :=
    Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨r₁', rfl⟩)
  have hgdCE : g * d * g⁻¹ ∈ CEgrp z ι := conj_mem_CEgrp hC hz hx hdCE
  set e₀ : G := d⁻¹ * (g * d * g⁻¹) with he0_def
  have he0CE : e₀ ∈ CEgrp z ι := mul_mem (inv_mem hdCE) hgdCE
  have he0A : e₀ ∈ centralizer (Agrp ι : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨ρ, hρ, rfl⟩ := mem_Agrp_iff.1 ha
    have hsignρ : sign ρ = 1 := Equiv.Perm.mem_alternatingGroup.mp hρ
    have hdadA : d * ι (liftS8 ρ) * d⁻¹ ∈ Agrp ι := by
      rw [hd_def]
      have heq : ι (liftS8 r₁') * ι (liftS8 ρ) * (ι (liftS8 r₁'))⁻¹
          = ι (liftS8 (r₁' * ρ * r₁'⁻¹)) := by
        simp only [map_mul, map_inv]
      rw [heq]
      exact mem_Agrp_iff.2 ⟨r₁' * ρ * r₁'⁻¹,
        Equiv.Perm.mem_alternatingGroup.2 (by
          rw [map_mul, map_mul, map_inv, hsignρ, sign_r₁']; norm_num),
        rfl⟩
    have h1 : g * ι (liftS8 ρ) * g⁻¹ = ι (liftS8 ρ) := by rw [hA ρ hρ]; group
    have hga : g⁻¹ * ι (liftS8 ρ) * g = ι (liftS8 ρ) := by
      calc g⁻¹ * ι (liftS8 ρ) * g = g⁻¹ * (g * ι (liftS8 ρ) * g⁻¹) * g := by rw [h1]
        _ = ι (liftS8 ρ) := by group
    have hca : (g * d * g⁻¹) * ι (liftS8 ρ) * (g * d * g⁻¹)⁻¹
        = d * ι (liftS8 ρ) * d⁻¹ := by
      calc (g * d * g⁻¹) * ι (liftS8 ρ) * (g * d * g⁻¹)⁻¹
          = g * (d * (g⁻¹ * ι (liftS8 ρ) * g) * d⁻¹) * g⁻¹ := by group
        _ = g * (d * ι (liftS8 ρ) * d⁻¹) * g⁻¹ := by rw [hga]
        _ = d * ι (liftS8 ρ) * d⁻¹ := by rw [← hcommA _ hdadA]; group
    have he0conj : e₀ * ι (liftS8 ρ) * e₀⁻¹ = ι (liftS8 ρ) := by
      calc e₀ * ι (liftS8 ρ) * e₀⁻¹
          = d⁻¹ * ((g * d * g⁻¹) * ι (liftS8 ρ) * (g * d * g⁻¹)⁻¹) * d := by
              rw [he0_def]; group
        _ = d⁻¹ * (d * ι (liftS8 ρ) * d⁻¹) * d := by rw [hca]
        _ = ι (liftS8 ρ) := by group
    have hcomm : e₀ * ι (liftS8 ρ) = ι (liftS8 ρ) * e₀ := by
      calc e₀ * ι (liftS8 ρ) = (e₀ * ι (liftS8 ρ) * e₀⁻¹) * e₀ := by group
        _ = ι (liftS8 ρ) * e₀ := by rw [he0conj]
    exact hcomm.symm
  have he0E : e₀ ∈ Egrp z ι := by
    have : e₀ ∈ centralizer (Agrp ι : Set G) ⊓ CEgrp z ι := mem_inf.2 ⟨he0A, he0CE⟩
    rwa [centralizer_Agrp_inf_CEgrp hC] at this
  have he0sq : e₀ * e₀ = 1 := sq_eq_one_of_mem_Egrp hC he0E
  have hge0 : g * e₀ * g⁻¹ = e₀ := by
    have hgd : g * d * g⁻¹ = d * e₀ := by rw [he0_def]; group
    have h1 : g * (g * d * g⁻¹) * g⁻¹ = d := by
      calc g * (g * d * g⁻¹) * g⁻¹ = (g * g) * d * (g * g)⁻¹ := by group
        _ = d := by
              rw [show (g * g) * d = d * (g * g) from
                mul_comm_of_mem_Egrp_of_mem_CEgrp hC hggE hdCE]
              group
    rw [hgd] at h1
    have h2 : g * (d * e₀) * g⁻¹ = (d * e₀) * (g * e₀ * g⁻¹) := by
      rw [show g * (d * e₀) * g⁻¹ = (g * d * g⁻¹) * (g * e₀ * g⁻¹) from by group, hgd]
    rw [h2] at h1
    have h3 : e₀ * (g * e₀ * g⁻¹) = 1 := by
      have := congrArg (fun t => d⁻¹ * t) h1
      simpa [mul_assoc] using this
    have h4 : g * e₀ * g⁻¹ = e₀⁻¹ := eq_inv_of_mul_eq_one_right h3
    rw [h4]
    exact (mul_eq_one_iff_eq_inv.mp he0sq).symm
  have he0cases : e₀ = 1 ∨ e₀ = z * ι τ₀ := by
    obtain ⟨i, j, hij⟩ := (mem_Egrp_iff hC).1 he0E
    have hEq : z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) = (ι τ₀) ^ (i:ℕ) * z ^ (j:ℕ) := by
      have key : g * (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) * g⁻¹
          = z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) := by
        calc g * (z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ)) * g⁻¹ = g * e₀ * g⁻¹ := by rw [← hij]
          _ = e₀ := hge0
          _ = z ^ (i:ℕ) * (ι τ₀) ^ (j:ℕ) := hij
      rw [conj_E_pow hz hx (i:ℕ) (j:ℕ)] at key
      exact key.symm
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hEq hij ⊢
    · exact Or.inl hij
    · exact absurd hEq (hC.ne_z τ₀)
    · exact absurd hEq.symm (hC.ne_z τ₀)
    · exact Or.inr hij
  refine ⟨hz, hx, hA, hsq, e₀, he0cases, ?_⟩
  intro ρ
  by_cases hsign : sign ρ = 1
  · rw [if_pos hsign, mul_one]
    rw [hA ρ (Equiv.Perm.mem_alternatingGroup.2 hsign)]
    group
  · rw [if_neg hsign]
    have hsignneg : sign ρ = -1 := by
      rcases Int.units_eq_one_or (sign ρ) with h1 | h1
      · exact absurd h1 hsign
      · exact h1
    set α : Perm (Fin 8) := r₁' * ρ with hα_def
    have hsignα : sign α = 1 := by
      rw [hα_def, map_mul, sign_r₁', hsignneg]
      norm_num
    have hmemα : α ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 hsignα
    have hρα : ρ = r₁' * α := by
      rw [hα_def, ← mul_assoc, r₁'_mul_self, one_mul]
    have hιρ : ι (liftS8 ρ) = d * ι (liftS8 α) := by
      rw [hρα, map_mul, map_mul, hd_def]
    have hcomm_e0 : e₀ * ι (liftS8 α) = ι (liftS8 α) * e₀ :=
      mul_comm_of_mem_Egrp_of_mem_CEgrp hC he0E
        (Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨α, rfl⟩))
    have hgsg : g * ι (liftS8 α) * g⁻¹ = ι (liftS8 α) := by rw [hA α hmemα]; group
    have hgd : g * d * g⁻¹ = d * e₀ := by rw [he0_def]; group
    calc g * ι (liftS8 ρ) * g⁻¹
        = g * (d * ι (liftS8 α)) * g⁻¹ := by rw [hιρ]
      _ = (g * d * g⁻¹) * (g * ι (liftS8 α) * g⁻¹) := by group
      _ = (d * e₀) * ι (liftS8 α) := by rw [hgd, hgsg]
      _ = d * (e₀ * ι (liftS8 α)) := by group
      _ = d * (ι (liftS8 α) * e₀) := by rw [hcomm_e0]
      _ = (d * ι (liftS8 α)) * e₀ := by group
      _ = ι (liftS8 ρ) * e₀ := by rw [← hιρ]

theorem GElt.comm_x₂ (hC : CentData z ι) (hg : GElt z ι g) :
    g * (z * ι τ₀) = (z * ι τ₀) * g := by
  have h : g * (z * ι τ₀) * g⁻¹ = z * ι τ₀ := by
    calc g * (z * ι τ₀) * g⁻¹ = (g * z * g⁻¹) * (g * ι τ₀ * g⁻¹) := by group
      _ = (ι τ₀) * z := by rw [hg.conj_z, hg.conj_x₁]
      _ = z * (ι τ₀) := (hC.comm τ₀).symm
  calc g * (z * ι τ₀) = (g * (z * ι τ₀) * g⁻¹) * g := by group
    _ = (z * ι τ₀) * g := by rw [h]

theorem GElt.mem_centralizer_Agrp (hg : GElt z ι g) : g ∈ centralizer (Agrp ι : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  obtain ⟨ρ, hρ, rfl⟩ := mem_Agrp_iff.1 ha
  exact (hg.comm_A ρ hρ).symm

theorem GElt.mem_normalizer_Egrp (hC : CentData z ι) (hg : GElt z ι g) :
    g ∈ normalizer ((Egrp z ι : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro e
  constructor
  · intro he; exact conj_mem_Egrp hC hg.conj_z hg.conj_x₁ he
  · intro he
    have hz' : g⁻¹ * z * (g⁻¹)⁻¹ = ι τ₀ := by rw [inv_inv, ← hg.conj_x₁]; group
    have hx' : g⁻¹ * (ι τ₀) * (g⁻¹)⁻¹ = z := by rw [inv_inv, ← hg.conj_z]; group
    have h := conj_mem_Egrp hC hz' hx' he
    simp only [inv_inv] at h
    rwa [show g⁻¹ * (g * e * g⁻¹) * g = e from by group] at h

theorem GElt.mul_mem_Egrp (hC : CentData z ι) (hg : GElt z ι g) {e : G} (he : e ∈ Egrp z ι) :
    GElt z ι (g * e) := by
  have heCE : e ∈ CEgrp z ι := Egrp_le_CEgrp hC he
  have heA : e ∈ centralizer (Agrp ι : Set G) := Egrp_le_centralizer_Agrp hC he
  have hez : e * z = z * e := mem_centralizer_singleton_iff.1 (mem_inf.1 heCE).1
  have hex : e * (ι τ₀) = (ι τ₀) * e := mem_centralizer_singleton_iff.1 (mem_inf.1 heCE).2
  refine GElt.of_swap_of_comm_A hC ?_ ?_ ?_
  · calc (g * e) * z * (g * e)⁻¹ = g * (e * z * e⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [show e * z * e⁻¹ = z from by rw [hez]; group]
      _ = ι τ₀ := hg.conj_z
  · calc (g * e) * (ι τ₀) * (g * e)⁻¹ = g * (e * (ι τ₀) * e⁻¹) * g⁻¹ := by group
      _ = g * (ι τ₀) * g⁻¹ := by
            rw [show e * (ι τ₀) * e⁻¹ = ι τ₀ from by rw [hex]; group]
      _ = z := hg.conj_x₁
  · intro ρ hρ
    have hes : e * ι (liftS8 ρ) = ι (liftS8 ρ) * e :=
      (mem_centralizer_iff.1 heA (ι (liftS8 ρ)) (mem_Agrp_iff.2 ⟨ρ, hρ, rfl⟩)).symm
    calc (g * e) * ι (liftS8 ρ) = g * (e * ι (liftS8 ρ)) := by group
      _ = g * (ι (liftS8 ρ) * e) := by rw [hes]
      _ = (g * ι (liftS8 ρ)) * e := by group
      _ = (ι (liftS8 ρ) * g) * e := by rw [hg.comm_A ρ hρ]
      _ = ι (liftS8 ρ) * (g * e) := by group

theorem GElt.sq_cases (hC : CentData z ι) (hg : GElt z ι g) :
    (g * g = 1 ∧ z * g * (z * g) = z * ι τ₀) ∨ (g * g = z * ι τ₀ ∧ z * g * (z * g) = 1) := by
  have hx1 : (ι τ₀) * (ι τ₀) = 1 := by rw [← map_mul, τ₀_mul_self, map_one]
  have hzg : g * z = ι τ₀ * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = ι τ₀ * g := by rw [hg.conj_z]
  have hxg : g * (ι τ₀) = z * g := by
    calc g * (ι τ₀) = (g * (ι τ₀) * g⁻¹) * g := by group
      _ = z * g := by rw [hg.conj_x₁]
  have hsq : z * g * (z * g) = z * (ι τ₀) * (g * g) := by
    calc z * g * (z * g) = z * (g * z) * g := by group
      _ = z * (ι τ₀ * g) * g := by rw [hzg]
      _ = z * (ι τ₀) * (g * g) := by group
  rcases hg.sq with h | h
  · exact Or.inl ⟨h, by rw [hsq, h, mul_one]⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [hsq, h]
    exact mul_self_eq_one_of_comm (a := z) (b := ι τ₀) (hC.comm τ₀) hC.mul_self hx1

theorem GElt.pairOrder_eq_N10_one_iff (hC : CentData z ι) (hg : GElt z ι g) :
    pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1 ↔
      ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g := by
  constructor
  · intro hpair
    obtain ⟨e₀, he₀, hform⟩ := hg.e₀
    have hgd : g * ι (swap 0 1) * g⁻¹ = ι (swap 0 1) * e₀ := by
      have h := hform r₁'
      rw [if_neg (by rw [sign_r₁']; decide), liftS8_r₁'] at h
      simpa only [r₁] using h
    have hpair' : pairOrder z (ι (swap 0 1) * e₀) = N10 1 := by
      have hc := pairOrder_conj g (ι τ₀) (ι (liftS8 r₁'))
      rw [hg.conj_x₁] at hc
      have hd : ι (liftS8 r₁') = ι (swap 0 1) := by rw [liftS8_r₁']; rfl
      rw [hd, hgd, hpair] at hc
      exact hc
    rcases he₀ with he₀ | he₀
    · intro ρ
      have h := hform ρ
      rw [he₀] at h
      have h1 : (if sign ρ = 1 then (1 : G) else 1) = 1 := by split <;> rfl
      rw [h1, mul_one] at h
      calc g * ι (liftS8 ρ) = (g * ι (liftS8 ρ) * g⁻¹) * g := by group
        _ = ι (liftS8 ρ) * g := by rw [h]
    · exfalso
      have hdx2 : ι (swap 0 1) * (z * ι τ₀) = z * ι ((swap 0 1 : Perm (Fin 10)) * τ₀) := by
        calc ι (swap 0 1) * (z * ι τ₀) = (ι (swap 0 1) * z) * ι τ₀ := by group
          _ = (z * ι (swap 0 1)) * ι τ₀ := by rw [(hC.comm (swap 0 1)).symm]
          _ = z * (ι (swap 0 1) * ι τ₀) := by group
          _ = z * ι ((swap 0 1) * τ₀) := by rw [map_mul]
      rw [he₀] at hpair'
      have hp2 : pairOrder z (ι (swap 0 1) * (z * ι τ₀)) = N10 2 := by
        rw [hdx2]
        exact pairOrder_z_z_swap_mul_tau hC
      exact N10_one_ne_two (hpair'.symm.trans hp2)
  · intro hcomm
    have hgd : g * ι (swap 0 1) * g⁻¹ = ι (swap 0 1) := by
      have hd : ι (liftS8 r₁') = ι (swap 0 1) := by rw [liftS8_r₁']; rfl
      rw [← hd, hcomm r₁']
      group
    have hc := pairOrder_conj g (ι τ₀) (ι (swap 0 1))
    rw [hg.conj_x₁, hgd] at hc
    rw [← hc]
    exact pairOrder_z_swap_one hC

theorem GElt.pairOrder_eq_N10_two_iff (hC : CentData z ι) (hg : GElt z ι g) :
    pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2 ↔
      ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) * g⁻¹ =
        ι (liftS8 ρ) * (if sign ρ = 1 then 1 else z * ι τ₀) := by
  constructor
  · intro hpair
    obtain ⟨e₀, he₀, hform⟩ := hg.e₀
    have hgd : g * ι (swap 0 1) * g⁻¹ = ι (swap 0 1) * e₀ := by
      have h := hform r₁'
      rw [if_neg (by rw [sign_r₁']; decide), liftS8_r₁'] at h
      simpa only [r₁] using h
    have hpair' : pairOrder z (ι (swap 0 1) * e₀) = N10 2 := by
      have hc := pairOrder_conj g (ι τ₀) (ι (liftS8 r₁'))
      rw [hg.conj_x₁] at hc
      have hd : ι (liftS8 r₁') = ι (swap 0 1) := by rw [liftS8_r₁']; rfl
      rw [hd, hgd, hpair] at hc
      exact hc
    have he₀x2 : e₀ = z * ι τ₀ := by
      rcases he₀ with he₀ | he₀
      · exfalso
        rw [he₀] at hpair'
        have hp1 : pairOrder z (ι (swap 0 1) * 1) = N10 1 := by
          rw [mul_one]
          exact pairOrder_z_swap_one hC
        exact N10_one_ne_two (hp1.symm.trans hpair')
      · exact he₀
    intro ρ
    have h := hform ρ
    rw [he₀x2] at h
    exact h
  · intro hform
    have hgd : g * ι (swap 0 1) * g⁻¹ = ι (swap 0 1) * (z * ι τ₀) := by
      have h := hform r₁'
      rw [if_neg (by rw [sign_r₁']; decide), liftS8_r₁'] at h
      simpa only [r₁] using h
    have hdx2 : ι (swap 0 1) * (z * ι τ₀) = z * ι ((swap 0 1 : Perm (Fin 10)) * τ₀) := by
      calc ι (swap 0 1) * (z * ι τ₀) = (ι (swap 0 1) * z) * ι τ₀ := by group
        _ = (z * ι (swap 0 1)) * ι τ₀ := by rw [(hC.comm (swap 0 1)).symm]
        _ = z * (ι (swap 0 1) * ι τ₀) := by group
        _ = z * ι ((swap 0 1) * τ₀) := by rw [map_mul]
    have hc := pairOrder_conj g (ι τ₀) (ι (liftS8 r₁'))
    rw [hg.conj_x₁] at hc
    have hd : ι (liftS8 r₁') = ι (swap 0 1) := by rw [liftS8_r₁']; rfl
    rw [hd, hgd, hdx2] at hc
    rw [← hc]
    exact pairOrder_z_z_swap_mul_tau hC

theorem GElt.exists_twist_frame (hC : CentData z ι) (hg : GElt z ι g) :
    ∃ κ : Perm (Fin 10) →* G, CentData (ι τ₀) κ ∧ κ τ₀ = z ∧ ∀ σ, κ σ = g * ι σ * g⁻¹ := by
  refine ⟨(MulAut.conj g).toMonoidHom.comp ι, ?_, ?_, ?_⟩
  · have h := centData_conj hC g
    rw [hg.conj_z] at h
    exact h
  · change g * ι τ₀ * g⁻¹ = z
    rw [hg.conj_x₁]
  · intro σ
    exact MulAut.conj_apply g (ι σ)

end CFSG.OddStandard.AltStdSec.SwapPartner
