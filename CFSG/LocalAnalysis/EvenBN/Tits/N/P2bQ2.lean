module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bAbs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P2b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data

section Abstract

variable {G : Type*} [Group G]

theorem sq_mul_of_comm {y w : G} (h : y * w = w * y) : y * w * (y * w) = y * y * (w * w) :=
  calc y * w * (y * w) = y * (w * y) * w := by group
    _ = y * (y * w) * w := by rw [h]
    _ = y * y * (w * w) := by group

theorem conj_mul_comm {y w : G} (h : y * w = w * y) : y * w * y⁻¹ = w :=
  calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [h]
    _ = w := by group

end Abstract

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem t_mem_Q2 (hd : d.Hyp) : d.t ∈ d.s56Q2 :=
  s56_mem_Q2_iff.2 ⟨s56_A_le_M d (mem_sup_right (mem_zpowers _)),
    fun e he => hd.L_comm_t (s56_E_le_L d he)⟩

theorem eps_t (hd : d.Hyp) : d.s56Eps d.t = 1 :=
  calc d.s56Eps d.t = d.t * (d.t * d.t * d.t⁻¹) := rfl
    _ = d.t * d.t := by group
    _ = 1 := hd.t_mul_self

theorem t_mul_mul_t (hd : d.Hyp) (v : G) : d.t * v * d.t = d.s56Eps v * v := by
  have h := hd.s56_conj_t v
  have h' : v * d.t = d.t * d.s56Eps v * v :=
    calc v * d.t = (v * d.t * v⁻¹) * v := by group
      _ = d.t * d.s56Eps v * v := by rw [h]
  calc d.t * v * d.t = d.t * (v * d.t) := by group
    _ = d.t * (d.t * d.s56Eps v * v) := by rw [h']
    _ = (d.t * d.t) * d.s56Eps v * v := by group
    _ = d.s56Eps v * v := by rw [hd.t_mul_self, one_mul]

theorem sq_t_mul (hd : d.Hyp) (v : G) : d.t * v * (d.t * v) = d.s56Eps v * (v * v) :=
  calc d.t * v * (d.t * v) = d.t * v * d.t * v := by group
    _ = d.s56Eps v * v * v := by rw [t_mul_mul_t hd]
    _ = d.s56Eps v * (v * v) := by group

theorem t_mem_normalizer_V (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.t ∈ normalizer (d.s56V : Set G) :=
  hd.s56_M_le_normalizer_V h49 (s56_A_le_M d (mem_sup_right (mem_zpowers _)))

theorem t_not_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) : d.t ∉ d.s56V := fun hv =>
  hd.t_not_mem (s56_E_le_L d ((hd.s56_V_eps_eq_one_iff h49 hv).1 (eps_t hd)))

theorem z_ne_one (hd : d.Hyp) : d.z ≠ 1 := fun h => by
  have := hd.s56_orderOf_z
  rw [h, orderOf_one] at this
  omega

theorem z_mem_sylT (hd : d.Hyp) : d.z ∈ sylT d := by
  have hzC : d.z ∈ centralizer ({d.t} : Set G) := hd.L_le d.z_mem
  refine ⟨⟨d.z, hzC⟩, ?_, rfl⟩
  show d.ρ ⟨d.z, hzC⟩ ∈ (Model.parrottU 1).subgroupOf titsA
  rw [mem_subgroupOf, hd.ρ_eq_θ ⟨d.z, d.z_mem⟩, d.θ_z, ← Model.parrottV_twelve]
  exact subset_closure ⟨12, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem y_sq (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G} (hy5 : IsV5 d y) (hyT : y ∈ sylT d)
    (hyz : y * z₀ = z₀ * y) (ht9 : d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G)) :
    y * y = d.z := by
  obtain ⟨hyC, hyρ⟩ := hy5
  have hzC : d.z ∈ centralizer ({d.t} : Set G) := hd.L_le d.z_mem
  have hyyC : y * y ∈ centralizer ({d.t} : Set G) := mul_mem hyC hyC
  have hyy : y * y ∈ sylT d ⊓ centralizer ({z₀} : Set G) := by
    refine mem_inf.2 ⟨mul_mem hyT hyT, mem_centralizer_singleton_iff.2 ?_⟩
    calc y * y * z₀ = y * (y * z₀) := by group
      _ = y * (z₀ * y) := by rw [hyz]
      _ = (y * z₀) * y := by group
      _ = z₀ * y * y := by rw [hyz]
      _ = z₀ * (y * y) := by group
  have hzz : d.z ∈ sylT d ⊓ centralizer ({z₀} : Set G) :=
    mem_inf.2 ⟨z_mem_sylT hd, mem_centralizer_singleton_iff.2 (hz.cen hd.s56_z_mem_E).symm⟩
  refine hd.s56y_ρ_inj ht9 hyyC hzC hyy hzz ?_
  have e : (⟨y * y, hyyC⟩ : centralizer ({d.t} : Set G)) = ⟨y, hyC⟩ * ⟨y, hyC⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul, hyρ, Model.parrottV_five.2.2,
    hd.ρ_eq_θ ⟨d.z, d.z_mem⟩, d.θ_z]

theorem y_not_mem_A (hd : d.Hyp) {y : G} (hy5 : IsV5 d y) : y ∉ d.A := by
  obtain ⟨hyC, hyρ⟩ := hy5
  intro h
  have := hd.s56y_ρ_mem_titsD_of_mem_A h hyC
  rw [hyρ] at this
  exact Model.parrottV_five.2.1 this

theorem t_mul_y_not_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy5 : IsV5 d y)
    (hyt : y * d.t = d.t * y) : d.t * y ∉ d.s56V := by
  intro hv
  have hε : d.s56Eps (d.t * y) = 1 := by
    have e : d.t * y * d.t * (d.t * y)⁻¹ = d.t :=
      calc d.t * y * d.t * (d.t * y)⁻¹ = d.t * (y * d.t) * y⁻¹ * d.t⁻¹ := by group
        _ = d.t * (d.t * y) * y⁻¹ * d.t⁻¹ := by rw [hyt]
        _ = d.t := by group
    rw [s56Eps, e, hd.t_mul_self]
  have hE : d.t * y ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hv).1 hε
  apply y_not_mem_A hd hy5
  have e : y = d.t * (d.t * y) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
  rw [e]
  exact mul_mem (mem_sup_right (mem_zpowers _)) (s56_E_le_A d hE)

theorem Q2_cases_D (h49 : d.Thm49Statement) (hd : d.Hyp) (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t)
    {q : G} (hq : q ∈ d.s56Q2) : q ∈ d.s56V ∨ ∃ v ∈ d.s56V, q = d.t * v := by
  rw [hQ] at hq
  exact mem_sup_zpowers_cases (t_mem_normalizer_V h49 hd)
    (by rw [hd.t_mul_self]; exact one_mem _) hq

theorem Q2_cases_top (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G}
    (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y) (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    (hy2 : y * y = d.z) {q : G} (hq : q ∈ d.s56Q2) :
    q ∈ d.s56V ∨ (∃ v ∈ d.s56V, q = d.t * v) ∨ (∃ v ∈ d.s56V, q = y * v) ∨
      ∃ v ∈ d.s56V, q = y * (d.t * v) := by
  have hle : d.s56V ⊔ zpowers d.t ≤ d.s56Q2 :=
    sup_le (s56_V_le_Q2 d) (zpowers_le.2 (t_mem_Q2 hd))
  have hyn : y ∈ normalizer ((d.s56V ⊔ zpowers d.t : Subgroup G) : Set G) := by
    have hyc' : y ∈ centralizer ((d.s56V ⊔ zpowers d.t : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      exact (hyc h (hle hh)).symm
    exact Subgroup.centralizer_le_normalizer ((d.s56V ⊔ zpowers d.t : Subgroup G) : Set G) hyc'
  have hy2' : y * y ∈ d.s56V ⊔ zpowers d.t := by
    rw [hy2]
    exact mem_sup_left (hd.s56_E_le_V h49 hd.s56_z_mem_E)
  have ht2 : d.t * d.t ∈ d.s56V := by rw [hd.t_mul_self]; exact one_mem _
  rw [hQ] at hq
  rcases mem_sup_zpowers_cases hyn hy2' hq with hc | ⟨h, hh, rfl⟩
  · rcases mem_sup_zpowers_cases (t_mem_normalizer_V h49 hd) ht2 hc with hc | ⟨v, hv, rfl⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  · rcases mem_sup_zpowers_cases (t_mem_normalizer_V h49 hd) ht2 hh with hh | ⟨v, hv, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h, hh, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩))

theorem orbit_t_V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    {x | ∃ v ∈ d.s56V, v * d.t * v⁻¹ = x} = (fun e => d.t * e) '' (d.E : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨d.s56Eps v, hd.s56_V_eps_mem_E hv, (hd.s56_conj_t v).symm⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨v, hv, hve⟩ := hd.s56_V_eps_surj h49 hz e he
    exact ⟨v, hv, by rw [hd.s56_conj_t v, hve]⟩

theorem orbit_t_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    {x | ∃ q ∈ d.s56Q2, q * d.t * q⁻¹ = x} = (fun e => d.t * e) '' (d.E : Set G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    exact ⟨d.s56Eps q, hd.s56_eps_mem_E (s56_mem_Q2_iff.1 hq).1, (hd.s56_conj_t q).symm⟩
  · rw [← orbit_t_V h49 hd hz]
    rintro x ⟨v, hv, rfl⟩
    exact ⟨v, s56_V_le_Q2 d hv, rfl⟩

theorem sq_y_t_mul (hd : d.Hyp) {y v : G} (hy2 : y * y = d.z) (hyw : y * (d.t * v) = d.t * v * y) :
    y * (d.t * v) * (y * (d.t * v)) = d.z * (d.s56Eps v * (v * v)) := by
  rw [sq_mul_of_comm hyw, hy2, sq_t_mul hd]

theorem inv_cases_D (h49 : d.Thm49Statement) (hd : d.Hyp) (hV : IsElemAbelian 2 d.s56V)
    (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t) {s : G} (hs : s ∈ d.s56Q2) (hsV : s ∉ d.s56V)
    (hs2 : s * s = 1) : ∃ e ∈ d.E, s = d.t * e := by
  rcases Q2_cases_D h49 hd hQ hs with h | ⟨v, hv, rfl⟩
  · exact absurd h hsV
  · have h1 := sq_t_mul hd v
    rw [hs2, elemAb_mul_self hV hv, mul_one] at h1
    exact ⟨v, (hd.s56_V_eps_eq_one_iff h49 hv).1 h1.symm, rfl⟩

theorem inv_cases_top (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V) {y : G} (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y)
    (hyc : ∀ q ∈ d.s56Q2, y * q = q * y) (hy2 : y * y = d.z) {s : G} (hs : s ∈ d.s56Q2)
    (hsV : s ∉ d.s56V) (hs2 : s * s = 1) :
    (∃ e ∈ d.E, s = d.t * e) ∨ ∃ e ∈ d.E, s = d.t * y * z₀ * e := by
  have hyt : y * d.t = d.t * y := hyc _ (t_mem_Q2 hd)
  rcases Q2_cases_top h49 hd hQ hyc hy2 hs with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · exact absurd h hsV
  · left
    have h1 := sq_t_mul hd v
    rw [hs2, elemAb_mul_self hV hv, mul_one] at h1
    exact ⟨v, (hd.s56_V_eps_eq_one_iff h49 hv).1 h1.symm, rfl⟩
  · exfalso
    have h1 := sq_mul_of_comm (hyc v (s56_V_le_Q2 d hv))
    rw [hs2, hy2, elemAb_mul_self hV hv, mul_one] at h1
    exact z_ne_one hd h1.symm
  · right
    have htv : d.t * v ∈ d.s56Q2 := mul_mem (t_mem_Q2 hd) (s56_V_le_Q2 d hv)
    have h1 := sq_y_t_mul hd hy2 (hyc _ htv)
    rw [hs2, elemAb_mul_self hV hv, mul_one] at h1
    have hεv : d.s56Eps v = d.z :=
      (eq_inv_of_mul_eq_one_right h1.symm).trans (inv_eq_of_mul_eq_one_right hd.s56_z_sq)
    have hz0Q2 : z₀ ∈ d.s56Q2 := hz.mem_Q2
    have hvQ2 : v ∈ d.s56Q2 := s56_V_le_Q2 d hv
    have hz0inv : z₀⁻¹ ∈ d.s56Q2 := inv_mem hz0Q2
    set e := z₀⁻¹ * v with he
    have heV : e ∈ d.s56V := mul_mem (inv_mem hz.mem_V) hv
    have heps : d.s56Eps e = 1 := by
      rw [he, hd.s56_eps_mul_Q2' hz0inv hvQ2, hd.s56_eps_inv_Q2 hz0Q2, hz.eps, hεv]
      exact hd.s56_z_sq
    refine ⟨e, (hd.s56_V_eps_eq_one_iff h49 heV).1 heps, ?_⟩
    have hv' : v = z₀ * e := by rw [he]; group
    rw [hv']
    calc y * (d.t * (z₀ * e)) = (y * d.t) * (z₀ * e) := by group
      _ = (d.t * y) * (z₀ * e) := by rw [hyt]
      _ = d.t * y * z₀ * e := by group

theorem t_mul_E_inv (h49 : d.Thm49Statement) (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    d.t * e ∈ d.s56Q2 ∧ d.t * e ∉ d.s56V ∧ d.t * e * (d.t * e) = 1 := by
  have heV : e ∈ d.s56V := hd.s56_E_le_V h49 he
  refine ⟨mul_mem (t_mem_Q2 hd) (hd.s56_E_le_Q2 he), fun h => t_not_mem_V h49 hd ?_, ?_⟩
  · have e' : d.t = d.t * e * e⁻¹ := by group
    rw [e']
    exact mul_mem h (inv_mem heV)
  · rw [sq_t_mul hd, (hd.s56_V_eps_eq_one_iff h49 heV).2 he, hd.s56_E_sq he, one_mul]

theorem t_y_z0_E_inv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V) {y : G} (hy5 : IsV5 d y) (hyQ : y ∈ d.s56Q2) (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    (hy2 : y * y = d.z) {e : G} (he : e ∈ d.E) :
    d.t * y * z₀ * e ∈ d.s56Q2 ∧ d.t * y * z₀ * e ∉ d.s56V ∧
      d.t * y * z₀ * e * (d.t * y * z₀ * e) = 1 := by
  have heV : e ∈ d.s56V := hd.s56_E_le_V h49 he
  have hyt : y * d.t = d.t * y := hyc _ (t_mem_Q2 hd)
  have hvV : z₀ * e ∈ d.s56V := mul_mem hz.mem_V heV
  refine ⟨mul_mem (mul_mem (mul_mem (t_mem_Q2 hd) hyQ) hz.mem_Q2) (hd.s56_E_le_Q2 he),
    fun h => t_mul_y_not_mem_V h49 hd hy5 hyt ?_, ?_⟩
  · have e' : d.t * y = d.t * y * z₀ * e * (z₀ * e)⁻¹ := by group
    rw [e']
    exact mul_mem h (inv_mem hvV)
  · have hs : d.t * y * z₀ * e = y * (d.t * (z₀ * e)) := by
      calc d.t * y * z₀ * e = (d.t * y) * (z₀ * e) := by group
        _ = (y * d.t) * (z₀ * e) := by rw [hyt]
        _ = y * (d.t * (z₀ * e)) := by group
    have htv : d.t * (z₀ * e) ∈ d.s56Q2 := mul_mem (t_mem_Q2 hd) (s56_V_le_Q2 d hvV)
    have hε : d.s56Eps (z₀ * e) = d.z := by
      rw [hd.s56_eps_mul_Q2' hz.mem_Q2 (hd.s56_E_le_Q2 he), hz.eps,
        (hd.s56_V_eps_eq_one_iff h49 heV).2 he, mul_one]
    have hVe : (z₀ * e) * (z₀ * e) = 1 := elemAb_mul_self hV hvV
    rw [hs, sq_y_t_mul hd hy2 (hyc _ htv), hε, hVe, mul_one]
    exact hd.s56_z_sq

theorem conj_tyz0_V (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G} (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    {v : G} (hv : v ∈ d.s56V) :
    v * (d.t * y * z₀) * v⁻¹ = d.t * y * z₀ * d.s56Eps v := by
  have hε := hd.s56_V_eps_mem_E hv
  have h1 : v * (d.t * y * z₀) * v⁻¹ = (v * d.t * v⁻¹) * (v * y * v⁻¹) * (v * z₀ * v⁻¹) := by group
  rw [h1, hd.s56_conj_t v, conj_mul_comm (hyc v (s56_V_le_Q2 d hv)).symm,
    conj_mul_comm (hz.comm_V hv)]
  have hεy : d.s56Eps v * y = y * d.s56Eps v := (hyc _ (hd.s56_E_le_Q2 hε)).symm
  have hεz : z₀ * d.s56Eps v = d.s56Eps v * z₀ := hz.cen hε
  calc d.t * d.s56Eps v * y * z₀ = d.t * (d.s56Eps v * y) * z₀ := by group
    _ = d.t * (y * d.s56Eps v) * z₀ := by rw [hεy]
    _ = d.t * y * (d.s56Eps v * z₀) := by group
    _ = d.t * y * (z₀ * d.s56Eps v) := by rw [← hεz]
    _ = d.t * y * z₀ * d.s56Eps v := by group

theorem Q2_conj_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G}
    (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y) (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    (hy2 : y * y = d.z) (hyz : y * z₀ = z₀ * y) :
    ∀ q ∈ d.s56Q2, ∃ e ∈ d.E, q * z₀ * q⁻¹ = z₀ * e := by
  have htz : d.t * z₀ * d.t = d.z * z₀ := by rw [t_mul_mul_t hd, hz.eps]
  have hzz : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have ht' : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_self
  have hzQ2 : d.z ∈ d.s56Q2 := hd.s56_E_le_Q2 hd.s56_z_mem_E
  intro q hq
  rcases Q2_cases_top h49 hd hQ hyc hy2 hq with h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · exact ⟨1, one_mem _, by rw [mul_one]; exact conj_mul_comm (hz.comm_V h)⟩
  · refine ⟨d.z, hd.s56_z_mem_E, ?_⟩
    have e : d.t * v * z₀ * (d.t * v)⁻¹ = d.t * (v * z₀ * v⁻¹) * d.t⁻¹ := by group
    rw [e, conj_mul_comm (hz.comm_V hv), ht', htz, hzz]
  · refine ⟨1, one_mem _, ?_⟩
    have e : y * v * z₀ * (y * v)⁻¹ = y * (v * z₀ * v⁻¹) * y⁻¹ := by group
    rw [e, conj_mul_comm (hz.comm_V hv), conj_mul_comm hyz, mul_one]
  · refine ⟨d.z, hd.s56_z_mem_E, ?_⟩
    have e : y * (d.t * v) * z₀ * (y * (d.t * v))⁻¹ =
        y * (d.t * (v * z₀ * v⁻¹) * d.t⁻¹) * y⁻¹ := by group
    rw [e, conj_mul_comm (hz.comm_V hv), ht', htz, hzz]
    have hyzz : y * (z₀ * d.z) = z₀ * d.z * y :=
      calc y * (z₀ * d.z) = (y * z₀) * d.z := by group
        _ = (z₀ * y) * d.z := by rw [hyz]
        _ = z₀ * (y * d.z) := by group
        _ = z₀ * (d.z * y) := by rw [hyc d.z hzQ2]
        _ = z₀ * d.z * y := by group
    exact conj_mul_comm hyzz

theorem orbit_tyz0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G}
    (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y) (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    (hy2 : y * y = d.z) (hyz : y * z₀ = z₀ * y) :
    {x | ∃ q ∈ d.s56Q2, q * (d.t * y * z₀) * q⁻¹ = x} =
        (fun e => d.t * y * z₀ * e) '' (d.E : Set G) ∧
      {x | ∃ v ∈ d.s56V, v * (d.t * y * z₀) * v⁻¹ = x} =
        (fun e => d.t * y * z₀ * e) '' (d.E : Set G) := by
  have hV : {x | ∃ v ∈ d.s56V, v * (d.t * y * z₀) * v⁻¹ = x} =
      (fun e => d.t * y * z₀ * e) '' (d.E : Set G) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨d.s56Eps v, hd.s56_V_eps_mem_E hv, (conj_tyz0_V hd hz hyc hv).symm⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨v, hv, hve⟩ := hd.s56_V_eps_surj h49 hz e he
      exact ⟨v, hv, by rw [conj_tyz0_V hd hz hyc hv, hve]⟩
  refine ⟨Set.Subset.antisymm ?_ ?_, hV⟩
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨e', he', hqz⟩ := Q2_conj_z0 h49 hd hz hQ hyc hy2 hyz q hq
    have hε := hd.s56_eps_mem_E (s56_mem_Q2_iff.1 hq).1
    refine ⟨d.s56Eps q * e', mul_mem hε he', ?_⟩
    have h1 : q * (d.t * y * z₀) * q⁻¹ = (q * d.t * q⁻¹) * (q * y * q⁻¹) * (q * z₀ * q⁻¹) := by
      group
    rw [h1, hd.s56_conj_t q, conj_mul_comm (hyc q hq).symm, hqz]
    have hεy : d.s56Eps q * y = y * d.s56Eps q := (hyc _ (hd.s56_E_le_Q2 hε)).symm
    have hεz : z₀ * d.s56Eps q = d.s56Eps q * z₀ := hz.cen hε
    symm
    calc d.t * d.s56Eps q * y * (z₀ * e') = d.t * (d.s56Eps q * y) * z₀ * e' := by group
      _ = d.t * (y * d.s56Eps q) * z₀ * e' := by rw [hεy]
      _ = d.t * y * (d.s56Eps q * z₀) * e' := by group
      _ = d.t * y * (z₀ * d.s56Eps q) * e' := by rw [← hεz]
      _ = d.t * y * z₀ * (d.s56Eps q * e') := by group
  · rw [← hV]
    rintro x ⟨v, hv, rfl⟩
    exact ⟨v, s56_V_le_Q2 d hv, rfl⟩

theorem mem_E_of_comm (h49 : d.Thm49Statement) (hd : d.Hyp) {c v : G} (hv : v ∈ d.s56V)
    (hvc : v * c = c * v) (hvx : v * (d.t * c) = d.t * c * v) : v ∈ d.E := by
  have h1 : v * d.t * c = d.t * v * c :=
    calc v * d.t * c = v * (d.t * c) := by group
      _ = d.t * c * v := hvx
      _ = d.t * (c * v) := by group
      _ = d.t * (v * c) := by rw [← hvc]
      _ = d.t * v * c := by group
  have h2 : v * d.t = d.t * v := mul_right_cancel h1
  have h3 : v * d.t * v⁻¹ = d.t := by rw [h2]; group
  have h4 := hd.s56_conj_t v
  rw [h3] at h4
  have hε : d.s56Eps v = 1 := (mul_eq_left.1 h4.symm)
  exact (hd.s56_V_eps_eq_one_iff h49 hv).1 hε

theorem t_mul_E_mul_t (hd : d.Hyp) {e : G} (he : e ∈ d.E) : d.t * e * d.t = e :=
  calc d.t * e * d.t = d.t * (e * d.t) := by group
    _ = d.t * (d.t * e) := by rw [hd.L_comm_t (s56_E_le_L d he)]
    _ = (d.t * d.t) * e := by group
    _ = e := by rw [hd.t_mul_self, one_mul]

theorem card_le_64_D (h49 : d.Thm49Statement) (hd : d.Hyp) (hV : IsElemAbelian 2 d.s56V)
    (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t) {x : G} (hx : x ∈ d.s56Q2) (hxV : x ∉ d.s56V)
    (hx2 : x * x = 1) {D : Subgroup G} (hDQ : D ≤ d.s56Q2) (hDx : ∀ a ∈ D, a * x = x * a)
    (hD : IsElemAbelian 2 D) : Nat.card D ≤ 64 := by
  have hc : ∀ a ∈ d.s56Q2, a ∉ d.s56V → a * a = 1 → a ∈ {s | ∃ e ∈ d.E, s = d.t * e} :=
    fun a ha haV ha2 => inv_cases_D h49 hd hV hQ ha haV ha2
  have hE32 : Nat.card d.E ≤ 32 := hd.A_facts.1.le
  refine card_le_of_inv (V := d.s56V) (Q₂ := d.s56Q2) (Es := d.E)
    (W := {s | ∃ e ∈ d.E, s = d.t * e}) (hc x hx hxV hx2) ?_ ?_ hc hDQ hDx hD hE32
  · rintro w ⟨e, he, rfl⟩ v hv hvw
    exact mem_E_of_comm h49 hd hv (elemAb_comm hV hv (hd.s56_E_le_V h49 he)) hvw
  · rintro a ⟨e, he, rfl⟩ b ⟨e', he', rfl⟩
    left
    have : d.t * e * (d.t * e') = e * e' :=
      calc d.t * e * (d.t * e') = (d.t * e * d.t) * e' := by group
        _ = e * e' := by rw [t_mul_E_mul_t hd he]
    rw [this]
    exact mul_mem (hd.s56_E_le_V h49 he) (hd.s56_E_le_V h49 he')

theorem c_comm_E (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G} (hyc : ∀ q ∈ d.s56Q2, y * q = q * y)
    {e : G} (he : e ∈ d.E) : y * z₀ * e = e * (y * z₀) :=
  calc y * z₀ * e = y * (z₀ * e) := by group
    _ = y * (e * z₀) := by rw [hz.cen he]
    _ = (y * e) * z₀ := by group
    _ = (e * y) * z₀ := by rw [hyc e (hd.s56_E_le_Q2 he)]
    _ = e * (y * z₀) := by group

theorem t_c_t (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G} (hyc : ∀ q ∈ d.s56Q2, y * q = q * y) :
    d.t * (y * z₀) * d.t = d.z * (y * z₀) := by
  have htz : d.t * z₀ * d.t = d.z * z₀ := by rw [t_mul_mul_t hd, hz.eps]
  have hyt : y * d.t = d.t * y := hyc _ (t_mem_Q2 hd)
  have hzQ2 : d.z ∈ d.s56Q2 := hd.s56_E_le_Q2 hd.s56_z_mem_E
  calc d.t * (y * z₀) * d.t = (d.t * y) * z₀ * d.t := by group
    _ = (y * d.t) * z₀ * d.t := by rw [← hyt]
    _ = y * (d.t * z₀ * d.t) := by group
    _ = y * (d.z * z₀) := by rw [htz]
    _ = (y * d.z) * z₀ := by group
    _ = (d.z * y) * z₀ := by rw [hyc d.z hzQ2]
    _ = d.z * (y * z₀) := by group

theorem c_sq (hz : d.S56Z0 z₀) (hV : IsElemAbelian 2 d.s56V) {y : G} (hy2 : y * y = d.z)
    (hyz : y * z₀ = z₀ * y) : y * z₀ * (y * z₀) = d.z :=
  calc y * z₀ * (y * z₀) = y * (z₀ * y) * z₀ := by group
    _ = y * (y * z₀) * z₀ := by rw [← hyz]
    _ = (y * y) * (z₀ * z₀) := by group
    _ = d.z := by rw [hy2, elemAb_mul_self hV hz.mem_V, mul_one]

theorem card_le_64_top (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V) {y : G} (hQ : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y)
    (hyc : ∀ q ∈ d.s56Q2, y * q = q * y) (hy2 : y * y = d.z) (hyz : y * z₀ = z₀ * y) {x : G}
    (hx : x ∈ d.s56Q2) (hxV : x ∉ d.s56V) (hx2 : x * x = 1) {D : Subgroup G}
    (hDQ : D ≤ d.s56Q2) (hDx : ∀ a ∈ D, a * x = x * a) (hD : IsElemAbelian 2 D) :
    Nat.card D ≤ 64 := by
  have hyt : y * d.t = d.t * y := hyc _ (t_mem_Q2 hd)
  have hzE := hd.s56_z_mem_E
  have hc : ∀ a ∈ d.s56Q2, a ∉ d.s56V → a * a = 1 →
      a ∈ {s | (∃ e ∈ d.E, s = d.t * e) ∨ ∃ e ∈ d.E, s = d.t * y * z₀ * e} :=
    fun a ha haV ha2 => inv_cases_top h49 hd hz hV hQ hyc hy2 ha haV ha2
  have hE32 : Nat.card d.E ≤ 32 := hd.A_facts.1.le
  refine card_le_of_inv (V := d.s56V) (Q₂ := d.s56Q2) (Es := d.E)
    (W := {s | (∃ e ∈ d.E, s = d.t * e) ∨ ∃ e ∈ d.E, s = d.t * y * z₀ * e})
    (hc x hx hxV hx2) ?_ ?_ hc hDQ hDx hD hE32
  · rintro w (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) v hv hvw
    · exact mem_E_of_comm h49 hd hv (elemAb_comm hV hv (hd.s56_E_le_V h49 he)) hvw
    · have hvy : Commute v y := (hyc v (s56_V_le_Q2 d hv)).symm
      have hvz : Commute v z₀ := hz.comm_V hv
      have hve : Commute v e := elemAb_comm hV hv (hd.s56_E_le_V h49 he)
      refine mem_E_of_comm h49 hd (c := y * z₀ * e) hv ((hvy.mul_right hvz).mul_right hve).eq ?_
      simpa only [mul_assoc] using hvw
  · have tt : ∀ e ∈ d.E, ∀ e' ∈ d.E, d.t * e * (d.t * e') = e * e' := fun e he e' _ =>
      calc d.t * e * (d.t * e') = (d.t * e * d.t) * e' := by group
        _ = e * e' := by rw [t_mul_E_mul_t hd he]
    have tc : ∀ e ∈ d.E, ∀ e' ∈ d.E,
        d.t * e * (d.t * y * z₀ * e') = (y * z₀) * (e * e') := fun e he e' _ =>
      calc d.t * e * (d.t * y * z₀ * e') = (d.t * e * d.t) * (y * z₀) * e' := by group
        _ = e * (y * z₀) * e' := by rw [t_mul_E_mul_t hd he]
        _ = (y * z₀) * e * e' := by rw [← c_comm_E hd hz hyc he]
        _ = (y * z₀) * (e * e') := by group
    have ct : ∀ e ∈ d.E, ∀ e' ∈ d.E,
        d.t * y * z₀ * e * (d.t * e') = (y * z₀) * (d.z * (e * e')) := fun e he e' _ =>
      calc d.t * y * z₀ * e * (d.t * e') = (d.t * (y * z₀)) * (e * d.t) * e' := by group
        _ = (d.t * (y * z₀)) * (d.t * e) * e' := by rw [hd.L_comm_t (s56_E_le_L d he)]
        _ = (d.t * (y * z₀) * d.t) * e * e' := by group
        _ = (d.z * (y * z₀)) * e * e' := by rw [t_c_t hd hz hyc]
        _ = (y * z₀ * d.z) * e * e' := by rw [← c_comm_E hd hz hyc hzE]
        _ = (y * z₀) * (d.z * (e * e')) := by group
    have cc : ∀ e ∈ d.E, ∀ e' ∈ d.E,
        d.t * y * z₀ * e * (d.t * y * z₀ * e') = e * e' := fun e he e' _ =>
      calc d.t * y * z₀ * e * (d.t * y * z₀ * e')
          = (d.t * (y * z₀)) * (e * d.t) * (y * z₀) * e' := by group
        _ = (d.t * (y * z₀)) * (d.t * e) * (y * z₀) * e' := by
            rw [hd.L_comm_t (s56_E_le_L d he)]
        _ = (d.t * (y * z₀) * d.t) * e * (y * z₀) * e' := by group
        _ = (d.z * (y * z₀)) * e * (y * z₀) * e' := by rw [t_c_t hd hz hyc]
        _ = d.z * (y * z₀) * (e * (y * z₀)) * e' := by group
        _ = d.z * (y * z₀) * ((y * z₀) * e) * e' := by rw [← c_comm_E hd hz hyc he]
        _ = d.z * ((y * z₀) * (y * z₀)) * e * e' := by group
        _ = d.z * d.z * e * e' := by rw [c_sq hz hV hy2 hyz]
        _ = e * e' := by rw [hd.s56_z_sq, one_mul]
    have hEV : ∀ e ∈ d.E, e ∈ d.s56V := fun e he => hd.s56_E_le_V h49 he
    have hz1 := z_ne_one hd
    rintro a (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) b (⟨e', he', rfl⟩ | ⟨e', he', rfl⟩)
    · left
      rw [tt e he e' he']
      exact mul_mem (hEV e he) (hEV e' he')
    · right
      rw [tc e he e' he', sq_mul_of_comm (c_comm_E hd hz hyc (mul_mem he he')), c_sq hz hV hy2 hyz,
        hd.s56_E_sq (mul_mem he he'), mul_one]
      exact hz1
    · right
      have hw : d.z * (e * e') ∈ d.E := mul_mem hzE (mul_mem he he')
      rw [ct e he e' he', sq_mul_of_comm (c_comm_E hd hz hyc hw), c_sq hz hV hy2 hyz,
        hd.s56_E_sq hw, mul_one]
      exact hz1
    · left
      rw [cc e he e' he']
      exact mul_mem (hEV e he) (hEV e' he')

theorem tyz0e_not_comm (hd : d.Hyp) (hz : d.S56Z0 z₀) {y : G}
    (hyc : ∀ q ∈ d.s56Q2, y * q = q * y) {e : G} (he : e ∈ d.E) :
    d.t * (d.t * y * z₀ * e) ≠ d.t * y * z₀ * e * d.t := by
  intro h
  have h1 : d.t * (d.t * y * z₀ * e) = (y * z₀) * e :=
    calc d.t * (d.t * y * z₀ * e) = (d.t * d.t) * (y * z₀) * e := by group
      _ = (y * z₀) * e := by rw [hd.t_mul_self, one_mul]
  have h2 : d.t * y * z₀ * e * d.t = d.z * ((y * z₀) * e) :=
    calc d.t * y * z₀ * e * d.t = (d.t * (y * z₀)) * (e * d.t) := by group
      _ = (d.t * (y * z₀)) * (d.t * e) := by rw [hd.L_comm_t (s56_E_le_L d he)]
      _ = (d.t * (y * z₀) * d.t) * e := by group
      _ = (d.z * (y * z₀)) * e := by rw [t_c_t hd hz hyc]
      _ = d.z * ((y * z₀) * e) := by group
  rw [h1, h2] at h
  exact z_ne_one hd (mul_eq_right.1 h.symm)

theorem inv_set_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V)
    (hyc : ∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y → ∀ q ∈ d.s56Q2, y * q = q * y)
    (hD : d.ρ.range = titsD.subgroupOf titsA → d.s56Q2 = d.s56V ⊔ zpowers d.t)
    (htop : ∀ y, IsV5 d y → d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y)
    (hex : d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y)
    (ht9 : d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G)) :
    {s | s ∈ d.s56Q2 ∧ s ∉ d.s56V ∧ s * s = 1} =
      (fun e => d.t * e) '' (d.E : Set G) ∪
        {s | ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y ∧ ∃ e ∈ d.E, s = d.t * y * z₀ * e} := by
  ext s
  constructor
  · rintro ⟨hs, hsV, hs2⟩
    rcases hd.card_M_N_values h49 with ⟨hr, -⟩ | ⟨hr, -⟩
    · obtain ⟨e, he, rfl⟩ := inv_cases_D h49 hd hV (hD hr) hs hsV hs2
      exact Or.inl ⟨e, he, rfl⟩
    · obtain ⟨y, hy5, hyT, hyz⟩ := hex hr
      rcases inv_cases_top h49 hd hz hV (htop y hy5) (hyc y hy5 hyT hyz)
        (y_sq hd hz hy5 hyT hyz ht9) hs hsV hs2 with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact Or.inl ⟨e, he, rfl⟩
      · exact Or.inr ⟨y, hy5, hyT, hyz, e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨y, hy5, hyT, hyz, e, he, rfl⟩)
    · exact t_mul_E_inv h49 hd he
    · exact t_y_z0_E_inv h49 hd hz hV hy5
        (by rw [htop y hy5]; exact mem_sup_right (mem_zpowers y)) (hyc y hy5 hyT hyz)
        (y_sq hd hz hy5 hyT hyz ht9) he

theorem inv_comm_t (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V)
    (hyc : ∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y → ∀ q ∈ d.s56Q2, y * q = q * y)
    (hD : d.ρ.range = titsD.subgroupOf titsA → d.s56Q2 = d.s56V ⊔ zpowers d.t)
    (htop : ∀ y, IsV5 d y → d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y)
    (hex : d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y)
    (ht9 : d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G)) {s : G} (hs : s ∈ d.s56Q2)
    (hsV : s ∉ d.s56V) (hs2 : s * s = 1) (hst : s * d.t = d.t * s) : ∃ e ∈ d.E, s = d.t * e := by
  have h := (inv_set_eq h49 hd hz hV hyc hD htop hex ht9).subset ⟨hs, hsV, hs2⟩
  rcases h with ⟨e, he, rfl⟩ | ⟨y, hy5, hyT, hyz, e, he, rfl⟩
  · exact ⟨e, he, rfl⟩
  · exact absurd hst.symm (tyz0e_not_comm hd hz (hyc y hy5 hyT hyz) he)

theorem card_le_64 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hV : IsElemAbelian 2 d.s56V)
    (hyc : ∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y → ∀ q ∈ d.s56Q2, y * q = q * y)
    (hD : d.ρ.range = titsD.subgroupOf titsA → d.s56Q2 = d.s56V ⊔ zpowers d.t)
    (htop : ∀ y, IsV5 d y → d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y)
    (hex : d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y)
    (ht9 : d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G)) {x : G} (hx : x ∈ d.s56Q2)
    (hxV : x ∉ d.s56V) (hx2 : x * x = 1) {D : Subgroup G} (hDQ : D ≤ d.s56Q2)
    (hDx : ∀ a ∈ D, a * x = x * a) (hDe : IsElemAbelian 2 D) : Nat.card D ≤ 64 := by
  rcases hd.card_M_N_values h49 with ⟨hr, -⟩ | ⟨hr, -⟩
  · exact card_le_64_D h49 hd hV (hD hr) hx hxV hx2 hDQ hDx hDe
  · obtain ⟨y, hy5, hyT, hyz⟩ := hex hr
    exact card_le_64_top h49 hd hz hV (htop y hy5) (hyc y hy5 hyT hyz)
      (y_sq hd hz hy5 hyT hyz ht9) hyz hx hxV hx2 hDQ hDx hDe

theorem maxElemAbelian2_Q2 (hV : IsElemAbelian 2 d.s56V) (hVcard : Nat.card d.s56V = 2 ^ 10)
    (hb : ∀ x ∈ d.s56Q2, x ∉ d.s56V → x * x = 1 → ∀ D : Subgroup G, D ≤ d.s56Q2 →
      (∀ a ∈ D, a * x = x * a) → IsElemAbelian 2 D → Nat.card D ≤ 64) :
    maxElemAbelian2 d.s56Q2 = {d.s56V} := by
  have hlt : ∀ D : Subgroup G, D ≤ d.s56Q2 → IsElemAbelian 2 D → ¬ D ≤ d.s56V →
      Nat.card D ≤ 64 := by
    intro D hDQ hDe hDV
    obtain ⟨a, haD, haV⟩ := SetLike.not_le_iff_exists.1 hDV
    exact hb a (hDQ haD) haV (elemAb_mul_self hDe haD) D hDQ
      (fun b hb' => elemAb_comm hDe hb' haD) hDe
  ext D
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hDQ, hDe, hDmax⟩
    have hVD : Nat.card d.s56V ≤ Nat.card D := hDmax _ (s56_V_le_Q2 d) hV
    have hDV : D ≤ d.s56V := by
      by_contra h
      have := hlt D hDQ hDe h
      rw [hVcard] at hVD
      omega
    exact Subgroup.eq_of_le_of_card_ge hDV hVD
  · rintro rfl
    refine ⟨s56_V_le_Q2 d, hV, fun D' hD'Q hD'e => ?_⟩
    by_cases hD'V : D' ≤ d.s56V
    · exact Subgroup.card_le_of_le hD'V
    · have := hlt D' hD'Q hD'e hD'V
      rw [hVcard]
      omega

theorem pRank_Q2_centralizer (hd : d.Hyp)
    (hb : ∀ x ∈ d.s56Q2, x ∉ d.s56V → x * x = 1 → ∀ D : Subgroup G, D ≤ d.s56Q2 →
      (∀ a ∈ D, a * x = x * a) → IsElemAbelian 2 D → Nat.card D ≤ 64)
    (h49 : d.Thm49Statement) {x : G} (hx : x ∈ d.s56Q2) (hxV : x ∉ d.s56V) (hx2 : x * x = 1) :
    CFSG.Open.pRank 2 (d.s56Q2 ⊓ centralizer ({x} : Set G)) = 6 := by
  have hcomm : ∀ r ∈ d.E, r * x = x * r := fun r hr => (s56_mem_Q2_iff.1 hx).2 r hr
  have hxE : x ∉ d.E := fun h => hxV (hd.s56_E_le_V h49 h)
  have hAe : IsElemAbelian 2 d.A := hd.A_facts.2.2.1
  have hEe : IsElemAbelian 2 d.E := elemAb_mono hAe (s56_E_le_A d)
  obtain ⟨hS1, hS2, hS3⟩ := sqSub_props hx2 hxE hEe hcomm
  refine pRank_eq_of_bounds (E₀ := sqSub d.E hx2 hcomm) (k₀ := 6) ?_ hS2 ?_ ?_
  · intro r hr
    refine mem_inf.2 ⟨?_, hS1 hr⟩
    rcases mem_sqSub.1 hr with h | ⟨e, he, rfl⟩
    · exact hd.s56_E_le_Q2 h
    · exact mul_mem hx (hd.s56_E_le_Q2 he)
  · rw [hS3, hd.A_facts.1]
    norm_num
  · intro E' hE' hE'e
    exact hb x hx hxV hx2 E' (fun a ha => (mem_inf.1 (hE' ha)).1)
      (fun a ha => mem_centralizer_singleton_iff.1 (mem_inf.1 (hE' ha)).2) hE'e

end CFSG.LocalAnalysis.EvenBN.Tits.N.P2b
