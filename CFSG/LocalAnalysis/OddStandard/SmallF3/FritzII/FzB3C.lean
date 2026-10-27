module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs_3c_commute (hS : FzbsStr t q tau lam rho u Z E X W R T) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W) : Commute a b := hS.W_comm a ha b hb

private lemma fzbs_3c_comm_t (hS : FzbsStr t q tau lam rho u Z E X W R T) {r : G}
    (hr : r ∈ R) : r * t * r⁻¹ * t⁻¹ ∈ Z := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
  have htW : t ∈ W := hS.XW hS.t_mem
  have hχZ : t * (r * t * r⁻¹) ∈ Z := hS.R_t r hr
  have hχW : t * (r * t * r⁻¹) ∈ W := hS.XW (hS.EX (hS.ZE hχZ))
  have heq : r * t * r⁻¹ * t⁻¹ = t * (r * t * r⁻¹) := by
    have h1 : r * t * r⁻¹ = t * (t * (r * t * r⁻¹)) := by
      rw [← mul_assoc, ht2, one_mul]
    calc r * t * r⁻¹ * t⁻¹
        = t * (t * (r * t * r⁻¹)) * t⁻¹ := congrArg (fun u => u * t⁻¹) h1
      _ = t * (r * t * r⁻¹) := by
            rw [hS.W_comm t htW (t * (r * t * r⁻¹)) hχW]
            group
  rw [heq]; exact hχZ

private lemma fzbs_3c_comm_mul (hS : FzbsStr t q tau lam rho u Z E X W R T) {r a b : G}
    (hr : r ∈ R) (ha : a ∈ W) (hb : b ∈ W) :
    r * (a * b) * r⁻¹ * (a * b)⁻¹ = (r * a * r⁻¹ * a⁻¹) * (r * b * r⁻¹ * b⁻¹) := by
  have hbW : r * b * r⁻¹ * b⁻¹ ∈ W := mul_mem (hS.R_W r hr b hb) (inv_mem hb)
  have hcomm : a * (r * b * r⁻¹ * b⁻¹) * a⁻¹ = r * b * r⁻¹ * b⁻¹ := by
    rw [hS.W_comm a ha _ hbW]; group
  calc r * (a * b) * r⁻¹ * (a * b)⁻¹
      = (r * a * r⁻¹ * a⁻¹) * (a * (r * b * r⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = (r * a * r⁻¹ * a⁻¹) * (r * b * r⁻¹ * b⁻¹) := by rw [hcomm]

private lemma fzbs_3c_comm_E (hS : FzbsStr t q tau lam rho u Z E X W R T) {r e : G}
    (hr : r ∈ R) (he : e ∈ E) : r * e * r⁻¹ * e⁻¹ ∈ Z := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
  have htW : t ∈ W := hS.XW hS.t_mem
  have heX : e ∈ X := hS.EX he
  have heW : e ∈ W := hS.XW heX
  have heiW : e⁻¹ ∈ W := inv_mem heW
  have he2Z : e ^ 2 ∈ Z := hS.E_sq e he
  have hyW : r * e * r⁻¹ ∈ W := hS.R_W r hr e heW
  have hy2 : (r * e * r⁻¹) ^ 2 = e ^ 2 := by
    rw [show (r * e * r⁻¹) ^ 2 = r * e ^ 2 * r⁻¹ by rw [pow_two, pow_two]; group]
    exact hS.R_Z r hr (e ^ 2) he2Z
  have hc2 : (r * e * r⁻¹ * e⁻¹) ^ 2 = 1 := by
    rw [(fzbs_3c_commute hS hyW heiW).mul_pow 2, hy2]
    rw [pow_two, pow_two]
    group
  have hcW : r * e * r⁻¹ * e⁻¹ ∈ W := mul_mem hyW heiW
  rcases hS.W_invol (r * e * r⁻¹ * e⁻¹) hcW hc2 with hcZ | htcZ
  · exact hcZ
  · set c : G := r * e * r⁻¹ * e⁻¹ with hc
    set z : G := t * c with hz
    have hzZ : z ∈ Z := by simpa [hz] using htcZ
    have hzW : z ∈ W := hS.XW (hS.EX (hS.ZE hzZ))
    have hz2 : z * z = 1 := by rw [← pow_two]; exact hS.Z_sq z hzZ
    set χ : G := t * (r * t * r⁻¹) with hχ
    have hχZ : χ ∈ Z := by rw [hχ]; exact hS.R_t r hr
    have hχW : χ ∈ W := hS.XW (hS.EX (hS.ZE hχZ))
    have hreorder : (t * χ) * z * ((t * z) * e) = χ * e := by
      calc (t * χ) * z * ((t * z) * e)
          = t * χ * (z * t) * (z * e) := by group
        _ = t * χ * (t * z) * (z * e) := by rw [hS.W_comm z hzW t htW]
        _ = t * (χ * t) * (z * z) * e := by group
        _ = t * (t * χ) * (z * z) * e := by rw [hS.W_comm χ hχW t htW]
        _ = (t * t) * χ * (z * z) * e := by group
        _ = χ * e := by rw [ht2, hz2]; group
    have hy_eq : r * e * r⁻¹ = c * e := by rw [hc]; group
    have hcz : c = t * z := by rw [hz]; rw [← mul_assoc, ht2, one_mul]
    have h2 : r ^ 2 * e * (r ^ 2)⁻¹ = χ * e := by
      calc r ^ 2 * e * (r ^ 2)⁻¹
          = r * (r * e * r⁻¹) * r⁻¹ := by rw [pow_two]; group
        _ = r * (c * e) * r⁻¹ := by rw [hy_eq]
        _ = r * ((t * z) * e) * r⁻¹ := by rw [hcz]
        _ = (r * t * r⁻¹) * (r * z * r⁻¹) * (r * e * r⁻¹) := by group
        _ = (t * χ) * z * (c * e) := by
              rw [show r * t * r⁻¹ = t * χ by rw [hχ, ← mul_assoc, ht2, one_mul],
                  hS.R_Z r hr z hzZ, hy_eq]
        _ = χ * e := by rw [hcz]; exact hreorder
    have h1 : r ^ 2 * e * (r ^ 2)⁻¹ = e := by
      rw [hS.W_comm (r ^ 2) (hS.R_sq r hr) e heW]
      group
    have hχe : χ * e = e := by rw [← h2, h1]
    have hχ1 : χ = 1 := by
      have : χ * e = 1 * e := by rw [hχe, one_mul]
      exact mul_right_cancel this
    have hchi1 : t * (r * t * r⁻¹) = 1 := by rw [← hχ]; exact hχ1
    rcases (fzbs_chi_eq_one hS hr).mp hchi1 with hrW | hrw
    · have hc1 : c = 1 := by rw [hc, hS.W_comm r hrW e heW]; group
      rw [hc1]; exact one_mem Z
    · set w : G := r * tau⁻¹ with hw
      have hwW : w ∈ W := by rw [hw]; exact hrw
      have hr_eq : r = w * tau := by rw [hw]; group
      have hrer : r * e * r⁻¹ = e⁻¹ := by
        rw [hr_eq]
        rw [show (w * tau) * e * (w * tau)⁻¹ = w * (tau * e * tau⁻¹) * w⁻¹ by group]
        rw [hS.tau_X e heX]
        rw [hS.W_comm w hwW e⁻¹ heiW]
        group
      have hc_eq : c = (e ^ 2)⁻¹ := by rw [hc, hrer, pow_two]; group
      rw [hc_eq]; exact inv_mem he2Z

theorem fzbs_comm_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {r x : G} (hr : r ∈ R)
    (hx : x ∈ X) : r * x * r⁻¹ * x⁻¹ ∈ Z := by
  rcases hS.X_split x hx with hxE | htxE
  · exact fzbs_3c_comm_E hS hr hxE
  · have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
    have htW : t ∈ W := hS.XW hS.t_mem
    set x' : G := t * x with hx'
    have hx'E : x' ∈ E := by simpa [hx'] using htxE
    have hx'W : x' ∈ W := hS.XW (hS.EX hx'E)
    have hx_eq : x = t * x' := by rw [hx', ← mul_assoc, ht2, one_mul]
    rw [hx_eq, fzbs_3c_comm_mul hS hr htW hx'W]
    exact mul_mem (fzbs_3c_comm_t hS hr) (fzbs_3c_comm_E hS hr hx'E)

theorem fzbs_R_E (hS : FzbsStr t q tau lam rho u Z E X W R T) {r e : G} (hr : r ∈ R)
    (he : e ∈ E) : r * e * r⁻¹ ∈ E := by
  have hc : r * e * r⁻¹ * e⁻¹ ∈ Z := fzbs_comm_X hS hr (hS.EX he)
  have hE : r * e * r⁻¹ * e⁻¹ ∈ E := hS.ZE hc
  rw [show r * e * r⁻¹ = (r * e * r⁻¹ * e⁻¹) * e by group]
  exact mul_mem hE he

theorem fzbs_aq (hS : FzbsStr t q tau lam rho u Z E X W R T) {r : G} (hr : r ∈ R) :
    q⁻¹ * (r * q * r⁻¹) ∈ X ∧ (q⁻¹ * (r * q * r⁻¹)) ^ 2 = t * (r * t * r⁻¹) := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hqiW : q⁻¹ ∈ W := inv_mem hS.q_mem
  have hbW : r * q * r⁻¹ ∈ W := hS.R_W r hr q hS.q_mem
  have haW : q⁻¹ * (r * q * r⁻¹) ∈ W := mul_mem hqiW hbW
  have hb2 : (r * q * r⁻¹) ^ 2 = r * t * r⁻¹ := by
    rw [show (r * q * r⁻¹) ^ 2 = r * q ^ 2 * r⁻¹ by rw [pow_two, pow_two]; group,
        hS.q_sq]
  have ha2 : (q⁻¹ * (r * q * r⁻¹)) ^ 2 = t * (r * t * r⁻¹) := by
    rw [(fzbs_3c_commute hS hqiW hbW).mul_pow 2, hb2]
    rw [show (q⁻¹) ^ 2 = t by rw [inv_pow, hS.q_sq, hti]]
  refine ⟨?_, ha2⟩
  rw [hS.X_iff (q⁻¹ * (r * q * r⁻¹)) haW, ha2]
  exact hS.R_t r hr

theorem fzbs_W_X_mul (hS : FzbsStr t q tau lam rho u Z E X W R T) {w w' : G} (hw : w ∈ W)
    (hw' : w' ∈ W) : w * w' ∈ X ↔ (w ∈ X ↔ w' ∈ X) := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
  by_cases hwX : w ∈ X
  · by_cases hw'X : w' ∈ X
    · exact ⟨fun _ => ⟨fun _ => hw'X, fun _ => hwX⟩, fun _ => mul_mem hwX hw'X⟩
    · have hnot : w * w' ∉ X := by
        intro h
        apply hw'X
        have hmem : w⁻¹ * (w * w') ∈ X := mul_mem (inv_mem hwX) h
        have heq : w⁻¹ * (w * w') = w' := by group
        rw [heq] at hmem
        exact hmem
      exact ⟨fun h => absurd h hnot, fun h => absurd (h.mp hwX) hw'X⟩
  · by_cases hw'X : w' ∈ X
    · have hnot : w * w' ∉ X := by
        intro h
        apply hwX
        have hmem : (w * w') * w'⁻¹ ∈ X := mul_mem h (inv_mem hw'X)
        have heq : (w * w') * w'⁻¹ = w := by group
        rw [heq] at hmem
        exact hmem
      exact ⟨fun h => absurd h hnot, fun h => absurd (h.mpr hw'X) hwX⟩
    · have hqw : q * w ∈ X := (hS.W_split w hw).resolve_left hwX
      have hqw' : q * w' ∈ X := (hS.W_split w' hw').resolve_left hw'X
      have hmem' : t * (q * w) * (q * w') ∈ X := mul_mem (mul_mem hS.t_mem hqw) hqw'
      have heq : t * (q * w) * (q * w') = w * w' := by
        calc t * (q * w) * (q * w')
            = t * q * w * q * w' := by group
          _ = t * q * (w * q) * w' := by group
          _ = t * q * (q * w) * w' := by rw [hS.W_comm w hw q hS.q_mem]
          _ = t * (q * q) * w * w' := by group
          _ = t * t * w * w' := by rw [show q * q = t by rw [← pow_two]; exact hS.q_sq]
          _ = w * w' := by rw [ht2]; group
      exact ⟨fun _ => ⟨fun h => absurd h hwX, fun h => absurd h hw'X⟩,
        fun _ => by rw [← heq]; exact hmem'⟩

theorem fzbs_R_W_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {r w : G} (hr : r ∈ R)
    (hw : w ∈ W) : r * w * r⁻¹ * w⁻¹ ∈ X := by
  by_cases hwX : w ∈ X
  · exact mul_mem (hS.R_X r hr w hwX) (inv_mem hwX)
  · have hqw : q * w ∈ X := (hS.W_split w hw).resolve_left hwX
    have hqW : q ∈ W := hS.q_mem
    set y : G := q * w with hy
    have hyX : y ∈ X := by simpa [hy] using hqw
    have hyW : y ∈ W := hS.XW hyX
    have haX : q⁻¹ * (r * q * r⁻¹) ∈ X := (fzbs_aq hS hr).1
    have hxcomm : r * y * r⁻¹ * y⁻¹ ∈ X := mul_mem (hS.R_X r hr y hyX) (inv_mem hyX)
    have hAw : r * y * r⁻¹ * y⁻¹ ∈ W := hS.XW hxcomm
    have hqA : q⁻¹ * (r * y * r⁻¹ * y⁻¹) * q = r * y * r⁻¹ * y⁻¹ := by
      rw [hS.W_comm q⁻¹ (inv_mem hqW) _ hAw]
      group
    have hw_eq : w = q⁻¹ * y := by rw [hy]; group
    have hrb : r * q⁻¹ * r⁻¹ = (q⁻¹ * (r * q * r⁻¹))⁻¹ * q⁻¹ := by group
    have hkey : r * w * r⁻¹ * w⁻¹
        = (q⁻¹ * (r * q * r⁻¹))⁻¹ * (r * y * r⁻¹ * y⁻¹) := by
      rw [hw_eq]
      calc r * (q⁻¹ * y) * r⁻¹ * (q⁻¹ * y)⁻¹
          = (r * q⁻¹ * r⁻¹) * (r * y * r⁻¹) * y⁻¹ * q := by group
        _ = ((q⁻¹ * (r * q * r⁻¹))⁻¹ * q⁻¹) * (r * y * r⁻¹) * y⁻¹ * q := by rw [hrb]
        _ = (q⁻¹ * (r * q * r⁻¹))⁻¹ * (q⁻¹ * (r * y * r⁻¹ * y⁻¹) * q) := by group
        _ = (q⁻¹ * (r * q * r⁻¹))⁻¹ * (r * y * r⁻¹ * y⁻¹) := by rw [hqA]
    rw [hkey]
    exact mul_mem (inv_mem haX) hxcomm

theorem fzbs_W_sq_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {w : G} (hw : w ∈ W) :
    w ^ 2 ∈ X := by
  by_cases hwX : w ∈ X
  · exact pow_mem hwX 2
  · have hqw : q * w ∈ X := (hS.W_split w hw).resolve_left hwX
    have ht2 : t * t = 1 := by simpa [pow_two] using hS.t_sq
    have hsq : (q * w) ^ 2 = t * w ^ 2 := by
      rw [(fzbs_3c_commute hS hS.q_mem hw).mul_pow 2, hS.q_sq]
    have heq : w ^ 2 = t * (q * w) ^ 2 := by
      rw [hsq, ← mul_assoc, ht2, one_mul]
    rw [heq]
    exact mul_mem hS.t_mem (pow_mem hqw 2)

end CFSG.OddStandard.SmallF3.FritzII
