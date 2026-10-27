module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8E1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Fields

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Orbit

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem centralizes_orbit {t : Γ} (ht : t * t = 1) {K : Subgroup Γ} (hK : IsComponent K)
    (hne : cj t K ≠ K) (g : Γ) (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hgK' : ∀ y ∈ cj t K, g * y * g⁻¹ ∈ cj t K)
    (hfix : ∀ k ∈ K, g * (k * (t * k * t⁻¹)) * g⁻¹ = k * (t * k * t⁻¹)) :
    (∀ k ∈ K, g * k * g⁻¹ = k) ∧ (∀ y ∈ cj t K, g * y * g⁻¹ = y) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hK' := isComponent_cj t hK
  have hcomm : ∀ x ∈ K, ∀ y ∈ cj t K, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (le_centralizer_of_ne hK hK' hne.symm hx) y hy).symm
  have hKp : commutator ↥K = ⊤ := Group.isPerfect_def.mp hK.1.1
  have hKp' : commutator ↥(cj t K) = ⊤ := Group.isPerfect_def.mp hK'.1.1
  refine ⟨centralizes_of_fixed hKp hcomm g hgK hgK' (fun k hk => ⟨t * k * t⁻¹, ⟨k, hk, rfl⟩,
    hfix k hk⟩), ?_⟩
  refine centralizes_of_fixed hKp' (fun x hx y hy => (hcomm y hy x hx).symm) g hgK' hgK ?_
  intro y hy
  have hk : t * y * t⁻¹ ∈ K := (mem_cj ht).1 hy
  refine ⟨t * y * t⁻¹, hk, ?_⟩
  have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
    rw [hti]; calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group
  have hfk := hfix _ hk
  rw [e, hcomm _ hk y hy] at hfk
  exact hfk

theorem centralizes_sup_orbit {t : Γ} (ht : t * t = 1) {K : Subgroup Γ} (hK : IsComponent K)
    (hne : cj t K ≠ K) (g : Γ) (h1 : ∀ k ∈ K, g * k * g⁻¹ = k)
    (h2 : ∀ y ∈ cj t K, g * y * g⁻¹ = y) : ∀ x ∈ K ⊔ cj t K, g * x * g⁻¹ = x := by
  have hK' := isComponent_cj t hK
  have hcomm : ∀ x ∈ K, ∀ y ∈ cj t K, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (le_centralizer_of_ne hK hK' hne.symm hx) y hy).symm
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    _ = a * b := by rw [h1 a ha, h2 b hb]

end Orbit

section U1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' →
    K' = K ∨ K' = cj (tG hb a.toPA6.toPA5) K)
  (hne : cj (tG hb a.toPA6.toPA5) K ≠ K) (hd : a.dcase = DCase.d8)

theorem u1_sq (hd : a.dcase = DCase.d8) : a.u₁ * a.u₁ = 1 := by
  obtain ⟨ho, -⟩ := a.d8_props hd
  have := pow_orderOf_eq_one a.u₁
  rwa [ho, pow_two] at this

theorem u1_mem_Cen (hd : a.dcase = DCase.d8) : a.u₁ ∈ Cen a.ub := by
  obtain ⟨-, h, -⟩ := a.d8_props hd
  exact h

@[expose] def u1G (hd : a.dcase = DCase.d8) : ↥(Cen a.ub) := ⟨a.u₁, u1_mem_Cen a hd⟩

@[expose] def ubG (a : PA5 L t E z) : ↥(Cen a.ub) := ⟨a.ub, mem_Cen.2 rfl⟩

theorem ubG_central (a : PA5 L t E z) (x : ↥(Cen a.ub)) : ubG a * x = x * ubG a :=
  Subtype.ext (mem_Cen.1 x.2).symm

theorem t_conj_u1 (hb : PAB G L t E W z) (a : PA7 L t E z) (hd : a.dcase = DCase.d8) :
    tG hb a.toPA6.toPA5 * u1G a hd * (tG hb a.toPA6.toPA5)⁻¹ = ubG a.toPA6.toPA5 * u1G a hd := by
  obtain ⟨-, -, -, htu1, -⟩ := a.d8_props hd
  apply Subtype.ext
  simpa [tG, u1G, ubG] using htu1

theorem u1_conj_t (hb : PAB G L t E W z) (a : PA7 L t E z) (hd : a.dcase = DCase.d8) :
    u1G a hd * tG hb a.toPA6.toPA5 * (u1G a hd)⁻¹ = tG hb a.toPA6.toPA5 * ubG a.toPA6.toPA5 := by
  have hsq : u1G a hd * u1G a hd = 1 := Subtype.ext (u1_sq a hd)
  have htt := tG_mul_tG hb a.toPA6.toPA5
  have hti : (tG hb a.toPA6.toPA5)⁻¹ = tG hb a.toPA6.toPA5 := inv_eq_of_mul_eq_one_right htt
  have hui : (u1G a hd)⁻¹ = u1G a hd := inv_eq_of_mul_eq_one_right hsq
  have h1 := t_conj_u1 hb a hd
  rw [hti] at h1
  set T := tG hb a.toPA6.toPA5
  set U := u1G a hd
  set B := ubG a.toPA6.toPA5
  have h2 : T * U = B * U * T := by
    calc T * U = T * U * (T * T) := by rw [htt, mul_one]
      _ = (T * U * T) * T := by simp only [mul_assoc]
      _ = B * U * T := by rw [h1]
  have hBU : B * U = U * B := ubG_central a.toPA6.toPA5 U
  have hBT : B * T = T * B := ubG_central a.toPA6.toPA5 T
  rw [hui]
  calc U * T * U = U * (T * U) := by rw [mul_assoc]
    _ = U * (B * U * T) := by rw [h2]
    _ = (U * B * U) * T := by simp only [mul_assoc]
    _ = (B * U * U) * T := by rw [← hBU]
    _ = B * T := by rw [mul_assoc B, hsq, mul_one]
    _ = T * B := hBT

theorem t_conj_u1_conj (hb : PAB G L t E W z) (a : PA7 L t E z) (hd : a.dcase = DCase.d8)
    (y : ↥(Cen a.ub)) :
    tG hb a.toPA6.toPA5 * (u1G a hd * y * (u1G a hd)⁻¹) * (tG hb a.toPA6.toPA5)⁻¹ =
      u1G a hd * (tG hb a.toPA6.toPA5 * y * (tG hb a.toPA6.toPA5)⁻¹) * (u1G a hd)⁻¹ := by
  have h1 := t_conj_u1 hb a hd
  have hBc := ubG_central a.toPA6.toPA5
  set T := tG hb a.toPA6.toPA5
  set U := u1G a hd
  set B := ubG a.toPA6.toPA5
  calc T * (U * y * U⁻¹) * T⁻¹ = (T * U * T⁻¹) * (T * y * T⁻¹) * (T * U * T⁻¹)⁻¹ := by group
    _ = (B * U) * (T * y * T⁻¹) * (B * U)⁻¹ := by rw [h1]
    _ = B * (U * (T * y * T⁻¹) * U⁻¹) * B⁻¹ := by group
    _ = U * (T * y * T⁻¹) * U⁻¹ := by rw [hBc (U * (T * y * T⁻¹) * U⁻¹)]; group

include hb a hK horb hne

theorem sw_u1_centralizes (hd : a.dcase = DCase.d8) :
    (∀ k ∈ K, u1G a hd * k * (u1G a hd)⁻¹ = k) ∧
      (∀ y ∈ cj (tG hb a.toPA6.toPA5) K, u1G a hd * y * (u1G a hd)⁻¹ = y) := by
  obtain ⟨-, -, -, hJ4⟩ := sw_struct hb a hK horb hne
  obtain ⟨-, -, hu1J, -⟩ := a.d8_props hd
  have htt := tG_mul_tG hb a.toPA6.toPA5
  set T := tG hb a.toPA6.toPA5 with hT
  set U := u1G a hd with hU
  have hUJ : ∀ j ∈ JG hb a.toPA6.toPA5, U * j * U⁻¹ = j := by
    intro j hj
    have h := Subgroup.mem_centralizer_iff.1 hu1J (j : G) hj
    have h2 : U * j = j * U := Subtype.ext h.symm
    rw [h2]; group
  have hcj : IsComponent (cj U K) := isComponent_cj _ hK
  have hconjU : ∀ x, T * (U * x * U⁻¹) * T⁻¹ = U * (T * x * T⁻¹) * U⁻¹ :=
    t_conj_u1_conj hb a hd
  rcases horb _ hcj with hA | hB
  · refine centralizes_orbit htt hK hne U ?_ ?_ ?_
    · intro k hk
      have : U * k * U⁻¹ ∈ cj U K := ⟨k, hk, rfl⟩
      rwa [hA] at this
    · intro y hy
      rw [mem_cj htt] at hy ⊢
      have : U * (T * y * T⁻¹) * U⁻¹ ∈ cj U K := ⟨_, hy, rfl⟩
      rw [hA] at this
      rw [hconjU]; exact this
    · intro k hk
      exact hUJ _ (hJ4 k hk)
  · exfalso
    have hsig : ∀ x, (T * U) * x * (T * U)⁻¹ = T * (U * x * U⁻¹) * T⁻¹ := fun x => by group
    have hmain := centralizes_orbit htt hK hne (T * U) (by
      intro k hk
      rw [hsig]
      have : U * k * U⁻¹ ∈ cj U K := ⟨k, hk, rfl⟩
      rw [hB, mem_cj htt] at this
      exact this) (by
      intro y hy
      rw [hsig, hconjU]
      rw [mem_cj htt] at hy
      have : U * (T * y * T⁻¹) * U⁻¹ ∈ cj U K := ⟨_, hy, rfl⟩
      rw [hB] at this
      exact this) (by
      intro k hk
      rw [hsig, hUJ _ (hJ4 k hk)]
      have h2 : (k * (T * k * T⁻¹)) * T = T * (k * (T * k * T⁻¹)) :=
        JG_comm_t hb a.toPA6.toPA5 (hJ4 k hk)
      calc T * (k * (T * k * T⁻¹)) * T⁻¹ = ((k * (T * k * T⁻¹)) * T) * T⁻¹ := by rw [h2]
        _ = k * (T * k * T⁻¹) := by group)
    have hlay := centralizes_sup_orbit htt hK hne (T * U) hmain.1 hmain.2
    apply PA7.E1_not_cent_t hb a
    intro e he
    have heL := a.E₁_le he
    rw [componentLayerOf_eq, layer_eq_of_orbit hb a.toPA6.toPA5 hK horb] at heL
    obtain ⟨x', hx', rfl⟩ := heL
    have h1 : (T * U) * x' = x' * (T * U) := by
      have := hlay x' hx'
      exact mul_inv_eq_iff_eq_mul.1 this
    have h1' : t * a.u₁ * (x' : G) = (x' : G) * (t * a.u₁) := congrArg Subtype.val h1
    have hF0 : a.u₁ ∈ a.F₀ := by
      obtain ⟨-, -, -, -, hF, -⟩ := a.d8_props hd
      rw [hF]; exact mem_sup_right (mem_zpowers _)
    have h2 : a.u₁ * (x' : G) = (x' : G) * a.u₁ :=
      (Subgroup.mem_centralizer_iff.1 (a.E₁_cent_F₀ he) a.u₁ hF0)
    have hsq := u1_sq a hd
    calc (x' : G) * t = (x' : G) * t * (a.u₁ * a.u₁) := by rw [hsq, mul_one]
      _ = ((x' : G) * (t * a.u₁)) * a.u₁ := by simp only [mul_assoc]
      _ = (t * a.u₁ * (x' : G)) * a.u₁ := by rw [h1']
      _ = t * (a.u₁ * (x' : G)) * a.u₁ := by simp only [mul_assoc]
      _ = t * ((x' : G) * a.u₁) * a.u₁ := by rw [h2]
      _ = t * (x' : G) * (a.u₁ * a.u₁) := by simp only [mul_assoc]
      _ = t * (x' : G) := by rw [hsq, mul_one]

end U1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
