module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section EStr

variable {Y : Type} [Group Y] [Finite Y]

structure EStr (c : Y) (X E : Subgroup Y) (ρ : Y → AEQ 6) : Prop where
  hc : c * c = 1
  hc1 : c ≠ 1
  XC : X ≤ Subgroup.centralizer ({c} : Set Y)
  rho_mul : ∀ g ∈ Subgroup.centralizer ({c} : Set Y), ∀ h ∈ Subgroup.centralizer ({c} : Set Y),
    ρ (g * h) = ρ g * ρ h
  rho_one : ρ 1 = 1
  X_conj : ∀ g ∈ Subgroup.centralizer ({c} : Set Y), ∀ y ∈ X, g * y * g⁻¹ ∈ X
  rho_ae : ∀ y ∈ X, ρ y ∈ TL4.aeModel 6
  rho_surj : ∀ x ∈ TL4.aeModel 6, ∃ y ∈ X, ρ y = x
  rho_ker : ∀ y ∈ X, ρ y = 1 → y = 1 ∨ y = c
  c_mem : c ∈ X
  rho_c : ρ c = 1
  E_iff : ∀ y, y ∈ E ↔ y ∈ X ∧ TC.Thin.permQ 6 (ρ y) = 1
  E_card : Nat.card E = 32
  E_sq : ∀ x ∈ E, x * x = 1
  E_conj : ∀ g ∈ Subgroup.centralizer ({c} : Set Y), ∀ e ∈ E, g * e * g⁻¹ ∈ E

namespace EStr

variable {c : Y} {X E : Subgroup Y} {ρ : Y → AEQ 6} (S : EStr c X E ρ)

include S

theorem E_le_X {e : Y} (he : e ∈ E) : e ∈ X := ((S.E_iff e).1 he).1

theorem E_le_C {e : Y} (he : e ∈ E) : e ∈ Subgroup.centralizer ({c} : Set Y) := S.XC (S.E_le_X he)

theorem c_mem_E : c ∈ E := (S.E_iff c).2 ⟨S.c_mem, by rw [S.rho_c, map_one]⟩

theorem E_comm {x y : Y} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have h := S.E_sq (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (S.E_sq x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (S.E_sq y hy)
  have h2 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h
  calc x * y = (x * y)⁻¹ := h2.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

theorem rho_inv {g : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y)) : ρ g⁻¹ = (ρ g)⁻¹ := by
  have h : ρ g * ρ g⁻¹ = 1 := by
    rw [← S.rho_mul g hg g⁻¹ (Subgroup.inv_mem _ hg), mul_inv_cancel, S.rho_one]
  exact eq_inv_of_mul_eq_one_right h

theorem rho_conj {g y : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y))
    (hy : y ∈ Subgroup.centralizer ({c} : Set Y)) : ρ (g * y * g⁻¹) = ρ g * ρ y * (ρ g)⁻¹ := by
  rw [S.rho_mul _ (Subgroup.mul_mem _ hg hy) _ (Subgroup.inv_mem _ hg), S.rho_mul _ hg _ hy,
    S.rho_inv hg]

theorem rho_comm_el {g h : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y))
    (hh : h ∈ Subgroup.centralizer ({c} : Set Y)) :
    ρ (g * h * g⁻¹ * h⁻¹) = ρ g * ρ h * (ρ g)⁻¹ * (ρ h)⁻¹ := by
  rw [S.rho_mul _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg)) _
    (Subgroup.inv_mem _ hh), S.rho_conj hg hh, S.rho_inv hh]

theorem rho_comm {g h : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y))
    (hh : h ∈ Subgroup.centralizer ({c} : Set Y)) (e : g * h = h * g) : ρ g * ρ h = ρ h * ρ g := by
  rw [← S.rho_mul g hg h hh, ← S.rho_mul h hh g hg, e]

theorem rho_E {e : Y} (he : e ∈ E) : InU (ρ e) := ⟨S.rho_ae e (S.E_le_X he), ((S.E_iff e).1 he).2⟩

theorem E_surj {x : AEQ 6} (hx : InU x) : ∃ e ∈ E, ρ e = x := by
  obtain ⟨y, hy, hyx⟩ := S.rho_surj x hx.1
  exact ⟨y, (S.E_iff y).2 ⟨hy, by rw [hyx]; exact hx.2⟩, hyx⟩

theorem ker_E {z : Y} (hz : z ∈ E) (h1 : ρ z = 1) : z = 1 ∨ z = c := S.rho_ker z (S.E_le_X hz) h1

theorem exists_four (a b d e : Y) : ∃ x ∈ E, x ≠ a ∧ x ≠ b ∧ x ≠ d ∧ x ≠ e := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set Y) ⊆ ↑({a, b, d, e} : Finset Y) := by
    intro x hx
    by_cases h1 : x = a
    · simp [h1]
    by_cases h2 : x = b
    · simp [h2]
    by_cases h3 : x = d
    · simp [h3]
    have := hcon x hx h1 h2 h3
    simp [this]
  have h4 : Nat.card E ≤ 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc Set.ncard (E : Set Y) ≤ Set.ncard (↑({a, b, d, e} : Finset Y) : Set Y) :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({a, b, d, e} : Finset Y).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  have := S.E_card
  omega

theorem cent_of_V (F : AE6Fin) {g : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y))
    (hgV : TC.Thin.permQ 6 (ρ g) = 1) : ∀ e ∈ E, g * e = e * g := by
  classical
  have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  set κ : Y → Y := fun e => g * e * g⁻¹ * e⁻¹ with hκdef
  have hκE : ∀ e ∈ E, κ e ∈ E := fun e he =>
    E.mul_mem (S.E_conj g hg e he) (E.inv_mem he)
  have hκρ : ∀ e ∈ E, ρ (κ e) = 1 := by
    intro e he
    have heC := S.E_le_C he
    show ρ (g * e * g⁻¹ * e⁻¹) = 1
    rw [S.rho_comm_el hg heC]
    have hcm := V_comm hgV (S.rho_E he).2
    calc ρ g * ρ e * (ρ g)⁻¹ * (ρ e)⁻¹ = (ρ e * ρ g) * (ρ g)⁻¹ * (ρ e)⁻¹ := by rw [hcm]
      _ = 1 := by group
  have hκker : ∀ e ∈ E, κ e = 1 ∨ κ e = c := fun e he => S.ker_E (hκE e he) (hκρ e he)
  have hcen : ∀ x : Y, (x = 1 ∨ x = c) → ∀ y ∈ Subgroup.centralizer ({c} : Set Y), y * x = x * y := by
    rintro x (rfl | rfl) y hy
    · simp
    · exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hge : ∀ e : Y, g * e * g⁻¹ = κ e * e := fun e => by
    show g * e * g⁻¹ = g * e * g⁻¹ * e⁻¹ * e
    group
  have hinv : ∀ y ∈ X, ∀ e ∈ E, κ (y * e * y⁻¹) = κ e := by
    intro y hy e he
    have hyC := S.XC hy
    have hyinv : y⁻¹ ∈ X := X.inv_mem hy
    have hgyX : g * y * g⁻¹ ∈ X := S.X_conj g hg y hy
    have hwX : y⁻¹ * g * y * g⁻¹ ∈ X := by
      have := X.mul_mem hyinv hgyX
      simpa [mul_assoc] using this
    have hwρ : TC.Thin.permQ 6 (ρ (y⁻¹ * g * y * g⁻¹)) = 1 := by
      have e1 : y⁻¹ * g * y * g⁻¹ = y⁻¹ * (g * y * g⁻¹) := by group
      have hgyC : g * y * g⁻¹ ∈ Subgroup.centralizer ({c} : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hyC) (Subgroup.inv_mem _ hg)
      have hρw : ρ (y⁻¹ * (g * y * g⁻¹)) = (ρ y)⁻¹ * (ρ g * ρ y * (ρ g)⁻¹) := by
        rw [S.rho_mul y⁻¹ (Subgroup.inv_mem _ hyC) _ hgyC, S.rho_inv hyC, S.rho_conj hg hyC]
      rw [e1, hρw]
      simp only [map_mul, map_inv, hgV]
      group
    have hwE : y⁻¹ * g * y * g⁻¹ ∈ E := (S.E_iff _).2 ⟨hwX, hwρ⟩
    set w := y⁻¹ * g * y * g⁻¹ with hw
    have hgy : g * y = y * w * g := by rw [hw]; group
    set k := κ e with hk
    have hkE : k = 1 ∨ k = c := hκker e he
    have hwC := S.E_le_C hwE
    have hwk : w * k = k * w := (hcen k hkE w hwC)
    have hyk : y * k = k * y := hcen k hkE y hyC
    have hwe : w * e = e * w := S.E_comm hwE he
    have key : g * (y * e * y⁻¹) * g⁻¹ = k * (y * e * y⁻¹) := by
      calc g * (y * e * y⁻¹) * g⁻¹ = (g * y) * e * (g * y)⁻¹ := by group
        _ = (y * w * g) * e * (y * w * g)⁻¹ := by rw [hgy]
        _ = y * w * (g * e * g⁻¹) * w⁻¹ * y⁻¹ := by group
        _ = y * w * (k * e) * w⁻¹ * y⁻¹ := by rw [hge e]
        _ = y * (w * k) * e * w⁻¹ * y⁻¹ := by group
        _ = y * (k * w) * e * w⁻¹ * y⁻¹ := by rw [hwk]
        _ = y * k * (w * e) * w⁻¹ * y⁻¹ := by group
        _ = y * k * (e * w) * w⁻¹ * y⁻¹ := by rw [hwe]
        _ = y * k * e * y⁻¹ := by group
        _ = k * y * e * y⁻¹ := by rw [hyk]
        _ = k * (y * e * y⁻¹) := by group
    show g * (y * e * y⁻¹) * g⁻¹ * (y * e * y⁻¹)⁻¹ = k
    rw [key]
    group
  have hmul : ∀ e ∈ E, ∀ e' ∈ E, κ (e * e') = κ e * κ e' := by
    intro e he e' he'
    have heC := S.E_le_C he
    have hk' : κ e' = 1 ∨ κ e' = c := hκker e' he'
    have hcom : e * κ e' = κ e' * e := hcen _ hk' e heC
    show g * (e * e') * g⁻¹ * (e * e')⁻¹ = κ e * κ e'
    calc g * (e * e') * g⁻¹ * (e * e')⁻¹ = (g * e * g⁻¹) * (g * e' * g⁻¹) * e'⁻¹ * e⁻¹ := by group
      _ = (κ e * e) * (κ e' * e') * e'⁻¹ * e⁻¹ := by rw [hge e, hge e']
      _ = κ e * (e * κ e' * e⁻¹) := by group
      _ = κ e * κ e' := by rw [hcom]; group
  have hκ1 : κ 1 = 1 := by simp [hκdef]
  have hκc : κ c = 1 := by
    show g * c * g⁻¹ * c⁻¹ = 1
    rw [hgc]
    group
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀, hne₀⟩ := hcon
  have hκe₀ : κ e₀ = c := by
    rcases hκker e₀ he₀ with h | h
    · exact absurd (by
        show g * e₀ = e₀ * g
        have : κ e₀ = 1 := h
        have h2 : g * e₀ * g⁻¹ * e₀⁻¹ = 1 := this
        calc g * e₀ = g * e₀ * g⁻¹ * e₀⁻¹ * (e₀ * g) := by group
          _ = e₀ * g := by rw [h2, one_mul]) hne₀
    · exact h
  have he₀ne : e₀ ≠ 1 ∧ e₀ ≠ c := by
    constructor
    · rintro rfl
      exact S.hc1 (hκe₀.symm.trans hκ1)
    · rintro rfl
      exact S.hc1 (hκe₀.symm.trans hκc)
  have hall : ∀ e ∈ E, e ≠ 1 → e ≠ c → κ e = c := by
    intro e he h1 h2
    have hρe : ρ e ≠ 1 := fun h => (S.ker_E he h).elim h1 h2
    have hρe₀ : ρ e₀ ≠ 1 := fun h => (S.ker_E he₀ h).elim he₀ne.1 he₀ne.2
    obtain ⟨γ, hγ, hγe⟩ := F.trans (ρ e₀) (ρ e) (S.rho_E he₀) (S.rho_E he) hρe₀ hρe
    obtain ⟨y, hy, rfl⟩ := S.rho_surj γ hγ
    have hyC := S.XC hy
    have hye₀ : y * e₀ * y⁻¹ ∈ E := S.E_conj y hyC e₀ he₀
    set z := (y * e₀ * y⁻¹)⁻¹ * e with hz
    have hzE : z ∈ E := E.mul_mem (E.inv_mem hye₀) he
    have hzρ : ρ z = 1 := by
      have e1 : ρ (y * e₀ * y⁻¹) = ρ e := by rw [S.rho_conj hyC (S.E_le_C he₀), hγe]
      have haC : y * e₀ * y⁻¹ ∈ Subgroup.centralizer ({c} : Set Y) := S.E_le_C hye₀
      rw [hz, S.rho_mul _ (Subgroup.inv_mem _ haC) _ (S.E_le_C he), S.rho_inv haC, e1, inv_mul_cancel]
    have hzκ : κ z = 1 := by
      rcases S.ker_E hzE hzρ with h | h
      · rw [h]; exact hκ1
      · rw [h]; exact hκc
    have hee : e = (y * e₀ * y⁻¹) * z := by rw [hz]; group
    rw [hee, hmul _ hye₀ z hzE, hinv y hy e₀ he₀, hκe₀, hzκ, mul_one]
  obtain ⟨e₁, he₁, h₁1, h₁c, -, -⟩ := S.exists_four 1 c 1 c
  obtain ⟨e₂, he₂, h₂1, h₂c, h₂e₁, h₂e₁c⟩ := S.exists_four 1 c e₁ (e₁ * c)
  have hκe₁ := hall e₁ he₁ h₁1 h₁c
  have hκe₂ := hall e₂ he₂ h₂1 h₂c
  have hprod : e₁ * e₂ ≠ 1 ∧ e₁ * e₂ ≠ c := by
    have he₁2 := S.E_sq e₁ he₁
    constructor
    · intro h
      apply h₂e₁
      calc e₂ = e₁ * (e₁ * e₂) := by rw [← mul_assoc, he₁2, one_mul]
        _ = e₁ := by rw [h, mul_one]
    · intro h
      apply h₂e₁c
      calc e₂ = e₁ * (e₁ * e₂) := by rw [← mul_assoc, he₁2, one_mul]
        _ = e₁ * c := by rw [h]
  have hκp := hall (e₁ * e₂) (E.mul_mem he₁ he₂) hprod.1 hprod.2
  rw [hmul e₁ he₁ e₂ he₂, hκe₁, hκe₂, S.hc] at hκp
  exact S.hc1 hκp.symm

end EStr

end EStr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
