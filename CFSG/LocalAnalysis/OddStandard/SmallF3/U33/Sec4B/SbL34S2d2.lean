module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2d2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2d1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open scoped commutatorElement
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem conj_V_of_mem_LO {x : G} (hx : x ∈ ctxLO t tau x₁ x₂) {v : G} (hv : v ∈ fourGrp x₁ x₂) :
    x * v * x⁻¹ ∈ fourGrp x₁ x₂ := by
  rw [← Z_O_eq hc hs]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx v).mp (V_le_O hc hv), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro b hb
  have hb' : x⁻¹ * b * x ∈ ctxO t tau x₁ x₂ := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hx) b).mp hb
  have hcomm := V_comm_O hc hb' hv
  calc b * (x * v * x⁻¹) = x * ((x⁻¹ * b * x) * v) * x⁻¹ := by group
    _ = x * (v * (x⁻¹ * b * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * v * x⁻¹) * b := by group

theorem acts_mul {x y : G} (hx : x ∈ ctxLO t tau x₁ x₂) (hy : y ∈ ctxLO t tau x₁ x₂)
    (hxa : ∀ o ∈ ctxO t tau x₁ x₂, x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂)
    (hya : ∀ o ∈ ctxO t tau x₁ x₂, y * o * y⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ o ∈ ctxO t tau x₁ x₂, (x * y) * o * (x * y)⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  intro o ho
  have h2 : x * (y * o * y⁻¹ * o⁻¹) * x⁻¹ ∈ fourGrp x₁ x₂ :=
    conj_V_of_mem_LO hc hs hx (hya o ho)
  have h3 : x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := hxa o ho
  have heq : (x * y) * o * (x * y)⁻¹ * o⁻¹ =
      x * (y * o * y⁻¹ * o⁻¹) * x⁻¹ * (x * o * x⁻¹ * o⁻¹) := by group
  rw [heq]
  exact mul_mem h2 h3

theorem acts_inv {x : G} (hx : x ∈ ctxLO t tau x₁ x₂)
    (hxa : ∀ o ∈ ctxO t tau x₁ x₂, x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ o ∈ ctxO t tau x₁ x₂, x⁻¹ * o * (x⁻¹)⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  intro o ho
  have ho' : x⁻¹ * o * x ∈ ctxO t tau x₁ x₂ := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hx) o).mp ho
  have hcomm := hxa (x⁻¹ * o * x) ho'
  have heq : x⁻¹ * o * (x⁻¹)⁻¹ * o⁻¹ =
      (x * (x⁻¹ * o * x) * x⁻¹ * (x⁻¹ * o * x)⁻¹)⁻¹ := by group
  rw [heq]
  exact inv_mem hcomm

theorem acts_conj {x y : G} (hy : y ∈ ctxLO t tau x₁ x₂)
    (hxa : ∀ o ∈ ctxO t tau x₁ x₂, x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ o ∈ ctxO t tau x₁ x₂, (y * x * y⁻¹) * o * (y * x * y⁻¹)⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  intro o ho
  have ho' : y⁻¹ * o * y ∈ ctxO t tau x₁ x₂ := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hy) o).mp ho
  have hinner := hxa (y⁻¹ * o * y) ho'
  have hconj := conj_V_of_mem_LO hc hs hy hinner
  have heq : (y * x * y⁻¹) * o * (y * x * y⁻¹)⁻¹ * o⁻¹ =
      y * (x * (y⁻¹ * o * y) * x⁻¹ * (y⁻¹ * o * y)⁻¹) * y⁻¹ := by group
  rw [heq]
  exact hconj

private theorem rho_acts_of_sq
    (h2 : ∀ o ∈ ctxO t tau x₁ x₂, rho ^ 2 * o * (rho ^ 2)⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ o ∈ ctxO t tau x₁ x₂, rho * o * rho⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  have hρLO : rho ∈ ctxLO t tau x₁ x₂ := M_le_LO hc hs hc.rho_mem_M
  have hρ2LO : rho ^ 2 ∈ ctxLO t tau x₁ x₂ := pow_mem hρLO 2
  have h3 : rho ^ 3 = 1 := by
    have := pow_orderOf_eq_one rho
    rwa [hc.ord_rho] at this
  have h4eq : rho ^ 2 * rho ^ 2 = rho := by
    calc rho ^ 2 * rho ^ 2 = rho ^ (2 + 2) := (pow_add rho 2 2).symm
      _ = rho ^ (3 + 1) := by norm_num
      _ = rho ^ 3 * rho ^ 1 := pow_add rho 3 1
      _ = rho := by rw [h3, one_mul, pow_one]
  intro o ho
  have h4 := acts_mul hc hs hρ2LO hρ2LO h2 h2 o ho
  rwa [h4eq] at h4

private theorem rho_acts_of_acts_of_mem {k : G}
    (hk : k = rho ∨ k = rho⁻¹ ∨ k = lam ∨ k = rho * lam ∨ k = rho⁻¹ * lam)
    (hkP : ∀ o ∈ ctxO t tau x₁ x₂, k * o * k⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ o ∈ ctxO t tau x₁ x₂, rho * o * rho⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  have hρLO : rho ∈ ctxLO t tau x₁ x₂ := M_le_LO hc hs hc.rho_mem_M
  have hlamLO : lam ∈ ctxLO t tau x₁ x₂ := M_le_LO hc hs hc.lam_mem_M
  rcases hk with hk | hk | hk | hk | hk
  · rw [hk] at hkP
    exact hkP
  · rw [hk] at hkP
    simpa using acts_inv hc hs (inv_mem hρLO) hkP
  · rw [hk] at hkP
    have hconjP := acts_conj hc hs (x := lam) (y := rho) hρLO hkP
    have hkinvP := acts_inv hc hs hlamLO hkP
    have hmulP := acts_mul hc hs (mul_mem (mul_mem hρLO hlamLO) (inv_mem hρLO))
      (inv_mem hlamLO) hconjP hkinvP
    have heq : rho * lam * rho⁻¹ * lam⁻¹ = rho ^ 2 :=
      rho_conj_inv_lam_types (k := lam) hc hs (Or.inl rfl)
    exact rho_acts_of_sq hc hs (fun o ho => by
      have := hmulP o ho
      rwa [heq] at this)
  · rw [hk] at hkP
    have hkLO : rho * lam ∈ ctxLO t tau x₁ x₂ := mul_mem hρLO hlamLO
    have hconjP := acts_conj hc hs (x := rho * lam) (y := rho) hρLO hkP
    have hkinvP := acts_inv hc hs hkLO hkP
    have hmulP := acts_mul hc hs (mul_mem (mul_mem hρLO hkLO) (inv_mem hρLO))
      (inv_mem hkLO) hconjP hkinvP
    have heq : rho * (rho * lam) * rho⁻¹ * (rho * lam)⁻¹ = rho ^ 2 :=
      rho_conj_inv_lam_types (k := rho * lam) hc hs (Or.inr (Or.inl rfl))
    exact rho_acts_of_sq hc hs (fun o ho => by
      have := hmulP o ho
      rwa [heq] at this)
  · rw [hk] at hkP
    have hkLO : rho⁻¹ * lam ∈ ctxLO t tau x₁ x₂ := mul_mem (inv_mem hρLO) hlamLO
    have hconjP := acts_conj hc hs (x := rho⁻¹ * lam) (y := rho) hρLO hkP
    have hkinvP := acts_inv hc hs hkLO hkP
    have hmulP := acts_mul hc hs (mul_mem (mul_mem hρLO hkLO) (inv_mem hρLO))
      (inv_mem hkLO) hconjP hkinvP
    have heq : rho * (rho⁻¹ * lam) * rho⁻¹ * (rho⁻¹ * lam)⁻¹ = rho ^ 2 :=
      rho_conj_inv_lam_types (k := rho⁻¹ * lam) hc hs (Or.inr (Or.inr rfl))
    exact rho_acts_of_sq hc hs (fun o ho => by
      have := hmulP o ho
      rwa [heq] at this)

private theorem conj_mem_X_of_acts {x : G} (hx : x ∈ ctxLO t tau x₁ x₂)
    (hxP : ∀ o ∈ ctxO t tau x₁ x₂, x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ h ∈ ctxX t tau x₁ x₂, x * h * x⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [fourGrp, ctxX]
    exact Subgroup.closure_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto)
  intro h hh
  rw [ctxX] at hh ⊢
  induction hh using Subgroup.closure_induction with
  | mem s hs =>
      have hsX : s ∈ ctxX t tau x₁ x₂ := subset_closure hs
      have hsO : s ∈ ctxO t tau x₁ x₂ := X_le_O hc hsX
      have h1 : x * s * x⁻¹ * s⁻¹ ∈ ctxX t tau x₁ x₂ := hVX (hxP s hsO)
      rw [show x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s by group]
      exact mul_mem h1 hsX
  | one => simp
  | mul a b ha hb iha ihb =>
      rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
      exact mul_mem iha ihb
  | inv a ha iha =>
      rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
      exact inv_mem iha

theorem rho_acts_nontrivially :
    ¬ ∀ o ∈ ctxO t tau x₁ x₂, rho * o * rho⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂ := by
  intro hρ
  have hρLO : rho ∈ ctxLO t tau x₁ x₂ := M_le_LO hc hs hc.rho_mem_M
  let Psub : Subgroup G :=
    { carrier := {x : G | x ∈ ctxLO t tau x₁ x₂ ∧
        ∀ o ∈ ctxO t tau x₁ x₂, x * o * x⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂}
      one_mem' := ⟨one_mem _, by intro o ho; simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxP⟩ ⟨hy, hyP⟩
        exact ⟨mul_mem hx hy, acts_mul hc hs hx hy hxP hyP⟩
      inv_mem' := by
        rintro x ⟨hx, hxP⟩
        exact ⟨inv_mem hx, acts_inv hc hs hx hxP⟩ }
  have hzpow : zpowers rho ≤ Psub := Subgroup.zpowers_le.mpr ⟨hρLO, hρ⟩
  have hQle : ctxQ t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
    rw [ctxQ, Subgroup.commutator_le]
    intro o ho g hg
    have hPg := (hzpow hg).2 o ho
    have heq : ⁅o, g⁆ = (g * o * g⁻¹ * o⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact inv_mem hPg
  have hcard := Subgroup.card_le_of_le hQle
  rw [hc.card_Q, card_fourGrp hc] at hcard
  norm_num at hcard

theorem mem_M_of_acts {g : G} (hg : g ∈ ctxLO t tau x₁ x₂)
    (h : ∀ o ∈ ctxO t tau x₁ x₂, g * o * g⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) : g ∈ ctxM t tau x₁ x₂ := by
  have hfor := conj_mem_X_of_acts hc hs hg h
  have hback : ∀ h' ∈ ctxX t tau x₁ x₂, g⁻¹ * h' * (g⁻¹)⁻¹ ∈ ctxX t tau x₁ x₂ :=
    conj_mem_X_of_acts hc hs (inv_mem hg) (acts_inv hc hs hg h)
  rw [ctxM, Subgroup.mem_normalizer_iff]
  intro h'
  exact ⟨hfor h', fun hh => by
    have h'' := hback (g * h' * g⁻¹) hh
    have heq : g⁻¹ * (g * h' * g⁻¹) * (g⁻¹)⁻¹ = h' := by group
    rwa [heq] at h''⟩

theorem CL_Obar_holds : ∀ g ∈ ctxLO t tau x₁ x₂,
    (∀ o ∈ ctxO t tau x₁ x₂, g * o * g⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) → g ∈ ctxO t tau x₁ x₂ := by
  intro g hg hgP
  have hgM : g ∈ ctxM t tau x₁ x₂ := mem_M_of_acts hc hs hg hgP
  obtain ⟨o, ho, k, hkS, hgk⟩ := decomp_M hc hs hgM
  have hoLO : o ∈ ctxLO t tau x₁ x₂ := M_le_LO hc hs (hc.O_le_M ho)
  have hkP : ∀ o' ∈ ctxO t tau x₁ x₂, k * o' * k⁻¹ * o'⁻¹ ∈ fourGrp x₁ x₂ := by
    have hoinvP : ∀ o' ∈ ctxO t tau x₁ x₂, o⁻¹ * o' * (o⁻¹)⁻¹ * o'⁻¹ ∈ fourGrp x₁ x₂ :=
      acts_inv hc hs hoLO (fun o' ho' => O_comm_le hc ho ho')
    have hk_eq : k = o⁻¹ * g := by rw [hgk]; group
    rw [hk_eq]
    exact acts_mul hc hs (inv_mem hoLO) hg hoinvP hgP
  have hk1 : k = 1 := by
    by_contra hkne
    have hρP : ∀ o' ∈ ctxO t tau x₁ x₂, rho * o' * rho⁻¹ * o'⁻¹ ∈ fourGrp x₁ x₂ := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkS
      rcases hkS with hk1' | hkρ | hkρinv | hk_lam | hk_rholam | hk_rhoinvlam
      · exact absurd hk1' hkne
      · exact rho_acts_of_acts_of_mem hc hs (Or.inl hkρ) hkP
      · exact rho_acts_of_acts_of_mem hc hs (Or.inr (Or.inl hkρinv)) hkP
      · exact rho_acts_of_acts_of_mem hc hs (Or.inr (Or.inr (Or.inl hk_lam))) hkP
      · exact rho_acts_of_acts_of_mem hc hs (Or.inr (Or.inr (Or.inr (Or.inl hk_rholam)))) hkP
      · exact rho_acts_of_acts_of_mem hc hs (Or.inr (Or.inr (Or.inr (Or.inr hk_rhoinvlam)))) hkP
    exact (rho_acts_nontrivially hc hs) hρP
  rw [hgk, hk1, mul_one]
  exact ho

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
