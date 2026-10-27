module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.t_conj_D {d : G} (hd : d ∈ D) : t * d * t⁻¹ = theta t d * d := by
  have hdBp := H.D_le_Bp W W2 hD hd
  have hθA : theta t d ∈ A := H.theta_mem_A W hdBp
  have hθ2 : theta t d * theta t d = 1 := by rw [← sq]; exact W.A_sq _ hθA
  have hθinv : (theta t d)⁻¹ = theta t d := inv_eq_of_mul_eq_one_right hθ2
  have e1 : t * d * t⁻¹ = (theta t d)⁻¹ * d := by
    simp only [theta]
    group
  rw [e1, hθinv]

theorem ThCyc.b_conj_theta {d : G} (hd : d ∈ D) : b * theta t d * b⁻¹ = theta t d := by
  have hθA : theta t d ∈ A := H.theta_mem_A W (H.D_le_Bp W W2 hD hd)
  have hθ2 : theta t d * theta t d = 1 := by rw [← sq]; exact W.A_sq _ hθA
  rw [W2.b_inv _ (W2.A_le hθA)]
  exact inv_eq_of_mul_eq_one_right hθ2

theorem ThCyc.inf_centralizer_bt_eq_A (h4 : ∀ d ∈ D, d ^ 4 = theta t d) :
    D ⊓ centralizer ({b * t} : Set G) = A := by
  have hbL : b ∈ L := W.B_le W2.b_mem
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    have hxbt : x * (b * t) = (b * t) * x := mem_centralizer_singleton_iff.1 hxc
    have hxBp := H.D_le_Bp W W2 hD hx
    have hθA : theta t x ∈ A := H.theta_mem_A W hxBp
    have hcomm : theta t x * x = x * theta t x := mem_centralizer_iff.1 hxBp.1 _ hθA
    have hc : b * (t * x * t⁻¹) * b⁻¹ = x := by
      calc b * (t * x * t⁻¹) * b⁻¹ = (b * t) * x * (b * t)⁻¹ := by group
        _ = (x * (b * t)) * (b * t)⁻¹ := by rw [← hxbt]
        _ = x := by group
    have e1 : b * x * b⁻¹ = theta t x * x := by
      have h1 : b * (theta t x * x) * b⁻¹ = (b * theta t x * b⁻¹) * (b * x * b⁻¹) := by group
      rw [H.t_conj_D W W2 hD hx, h1, H.b_conj_theta W W2 hD hx] at hc
      calc b * x * b⁻¹ = (theta t x)⁻¹ * (theta t x * (b * x * b⁻¹)) := by group
        _ = (theta t x)⁻¹ * x := by rw [hc]
        _ = theta t x * x := by
          have hθ2 : theta t x * theta t x = 1 := by rw [← sq]; exact W.A_sq _ hθA
          rw [inv_eq_of_mul_eq_one_right hθ2]
    have hρ := H.D_rho_mem_A W W2 hD hx
    rw [e1] at hρ
    have hx2 : x ^ 2 ∈ A := by
      have h1 : x * (theta t x * x) = theta t x * x ^ 2 := by
        rw [sq, ← mul_assoc, ← hcomm]
        group
      rw [h1] at hρ
      have := A.mul_mem (A.inv_mem hθA) hρ
      simpa using this
    have h4' : x ^ 4 = 1 := by
      have h3 := W.A_sq _ hx2
      rw [← pow_mul] at h3
      exact h3
    have hθ1 : theta t x = 1 := by rw [← h4 x hx]; exact h4'
    have hxAa : x ∈ Aa := (H.D_theta_eq_one_iff W W2 hD hx).1 hθ1
    rw [hθ1, one_mul] at e1
    have hxb : x * b = b * x := by
      calc x * b = (b * x * b⁻¹) * b := by rw [e1]
        _ = b * x := by group
    exact W2.mem_A_of_sq_eq_one W hxAa (sq_eq_one_of_conj_eq_inv (W2.b_inv x hxAa) hxb)
  · intro hx
    refine ⟨hD.Aa_le (W2.A_le hx), mem_centralizer_singleton_iff.2 ?_⟩
    have hbx : b * x = x * b := ((W.mem_B_iff b hbL).1 W2.b_mem x hx)
    have hAL : A ≤ L := le_trans (fun y hy => ((W.mem_A_iff y).1 hy).1) W.S_le
    have htx : t * x = x * t := H.comm_of_mem_L (hAL hx)
    calc x * (b * t) = (x * b) * t := by group
      _ = (b * x) * t := by rw [hbx]
      _ = b * (x * t) := by group
      _ = b * (t * x) := by rw [htx]
      _ = (b * t) * x := by group

theorem ThCyc.psi_mem_A (hsq : ∀ d ∈ D, d ^ 2 ∈ A) {d : G} (hd : d ∈ D) :
    d ^ 2 * theta t d ∈ A :=
  A.mul_mem (hsq d hd) (H.theta_mem_A W (H.D_le_Bp W W2 hD hd))

@[expose] noncomputable def psiD (hsq : ∀ d ∈ D, d ^ 2 ∈ A) : ↥D →* ↥A :=
  MonoidHom.mk' (fun d => ⟨(d : G) ^ 2 * theta t d, H.psi_mem_A W W2 hD hsq d.2⟩) (fun d d' => by
    apply Subtype.ext
    have hd'Bp := H.D_le_Bp W W2 hD d'.2
    have hθA : theta t (d : G) ∈ A := H.theta_mem_A W (H.D_le_Bp W W2 hD d.2)
    have hc : theta t (d : G) * (d' : G) ^ 2 = (d' : G) ^ 2 * theta t (d : G) :=
      mem_centralizer_iff.1 (H.D_le_Bp W W2 hD (D.pow_mem d'.2 2)).1 _ hθA
    show ((d : G) * d') ^ 2 * theta t ((d : G) * d') =
      ((d : G) ^ 2 * theta t d) * ((d' : G) ^ 2 * theta t d')
    rw [(show Commute (d : G) d' from hD.comm _ d.2 _ d'.2).mul_pow 2,
      H.theta_mul W (H.D_le_Bp W W2 hD d.2) hd'Bp]
    calc (d : G) ^ 2 * (d' : G) ^ 2 * (theta t d * theta t d')
        = (d : G) ^ 2 * ((d' : G) ^ 2 * theta t d) * theta t d' := by group
      _ = (d : G) ^ 2 * (theta t d * (d' : G) ^ 2) * theta t d' := by rw [← hc]
      _ = _ := by group)

theorem ThCyc.card_inf_centralizer_bt (hsq : ∀ d ∈ D, d ^ 2 ∈ A)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card ↥(D ⊓ centralizer ({b * t} : Set G)) = 2 ^ 8 := by
  set ψ := psiD H W W2 hD hsq with hψ
  have hbt : ∀ d ∈ D, (b * t) * d * (b * t)⁻¹ = theta t d * d⁻¹ := by
    intro d hd
    calc (b * t) * d * (b * t)⁻¹ = b * (t * d * t⁻¹) * b⁻¹ := by group
      _ = b * (theta t d * d) * b⁻¹ := by rw [H.t_conj_D W W2 hD hd]
      _ = (b * theta t d * b⁻¹) * (b * d * b⁻¹) := by group
      _ = theta t d * d⁻¹ := by rw [H.b_conj_theta W W2 hD hd, hb d hd]
  have hiff : ∀ d ∈ D, d ∈ centralizer ({b * t} : Set G) ↔ d ^ 2 * theta t d = 1 := by
    intro d hd
    have hdA2 : (d ^ 2) ^ 2 = 1 := W.A_sq _ (hsq d hd)
    have hd2inv : (d ^ 2)⁻¹ = d ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hdA2)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : theta t d * d⁻¹ = d := by
        rw [← hbt d hd, ← h]
        group
      have h2 : theta t d = d ^ 2 := by
        calc theta t d = (theta t d * d⁻¹) * d := by group
          _ = d * d := by rw [h1]
          _ = d ^ 2 := (sq d).symm
      rw [h2, ← sq]
      exact hdA2
    · intro h
      have h2 : theta t d = d ^ 2 := by
        rw [eq_inv_of_mul_eq_one_right h, hd2inv]
      have h1 : (b * t) * d * (b * t)⁻¹ = d := by
        rw [hbt d hd, h2]
        group
      calc d * (b * t) = ((b * t) * d * (b * t)⁻¹) * (b * t) := by rw [h1]
        _ = (b * t) * d := by group
  have hker : (D ⊓ centralizer ({b * t} : Set G)).subgroupOf D = ψ.ker := by
    ext d
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, hd2⟩
      exact Subtype.ext ((hiff d d.2).1 hd2)
    · intro h
      exact ⟨d.2, (hiff d d.2).2 (congrArg (fun x : ↥A => (x : G)) h)⟩
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 a.2
    refine ⟨⟨x, hD.Aa_le hx⟩, Subtype.ext ?_⟩
    show x ^ 2 * theta t x = a
    rw [(H.D_theta_eq_one_iff W W2 hD (hD.Aa_le hx)).2 hx, mul_one, hxa]
  rw [hrange, Subgroup.card_top, W.A_card, hD.card] at h1
  have hkc : Nat.card ψ.ker = 2 ^ 8 := by omega
  rw [← hkc, ← hker]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    D ⊓ centralizer ({b * t} : Set G) ≤ D)).toEquiv).symm

theorem ThCyc.D_cases
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7) :
    ((∀ d ∈ D, d ^ 4 = theta t d) ∧ D ⊓ centralizer ({b} : Set G) = A ∧
        D ⊓ centralizer ({b * t} : Set G) = A) ∨
      ((∀ d ∈ D, d ^ 4 = 1) ∧ (∀ d ∈ D, b * d * b⁻¹ = d⁻¹) ∧
        Nat.card ↥(D ⊓ centralizer ({b} : Set G)) = 2 ^ 8 ∧
        Nat.card ↥(D ⊓ centralizer ({b * t} : Set G)) = 2 ^ 8) := by
  rcases H.D_trichotomy W W2 hD with h4 | ⟨h4, hinv⟩ | ⟨h4, hinv⟩
  · exact Or.inl ⟨h4, H.inf_centralizer_b_eq_A W W2 hD h4, H.inf_centralizer_bt_eq_A W W2 hD h4⟩
  · have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
    exact Or.inr ⟨h4, hinv, H.card_inf_centralizer_of_inverts W W2 hD hsq hinv,
      H.card_inf_centralizer_bt W W2 hD hsq hinv⟩
  · exact absurd hinv (H.not_bt_inverts_D W W2 hD hEl
      (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd))

end

end CFSG.EvenSporadicStandard.ThStd
