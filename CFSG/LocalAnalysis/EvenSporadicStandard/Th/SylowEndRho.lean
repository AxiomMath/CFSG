module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem ThLocalIn2.b_inv_eq_self (W2 : ThLocalIn2 B A Aa b) : b⁻¹ = b :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact W2.b_sq)

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.D_rho_mem_A {d : G} (hd : d ∈ D) : d * (b * d * b⁻¹) ∈ A := by
  have hbd : b * d * b⁻¹ ∈ D := H.b_conj_mem_D W W2 hD hd
  have hcomm : d * (b * d * b⁻¹) = (b * d * b⁻¹) * d := hD.comm d hd _ hbd
  have hb2 : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have hb2' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hb2, inv_one]
  have hx : d * (b * d * b⁻¹) ∈ Aa := by
    have : d * (b * d * b⁻¹) = (b * d * b⁻¹ * d⁻¹) * d ^ 2 := by rw [hcomm]; group
    rw [this]
    exact Aa.mul_mem (H.D_alpha_mem W W2 hD hd) (H.D_sq_mem_Aa W W2 hD hd)
  have hbx : b * (d * (b * d * b⁻¹)) * b⁻¹ = d * (b * d * b⁻¹) := by
    calc b * (d * (b * d * b⁻¹)) * b⁻¹ = (b * d * b⁻¹) * (b * b) * d * (b⁻¹ * b⁻¹) := by group
      _ = (b * d * b⁻¹) * d := by rw [hb2, hb2']; group
      _ = d * (b * d * b⁻¹) := hcomm.symm
  have hinv := W2.b_inv _ hx
  rw [hbx] at hinv
  refine W2.mem_A_of_sq_eq_one W hx ?_
  calc (d * (b * d * b⁻¹)) ^ 2 = (d * (b * d * b⁻¹)) * (d * (b * d * b⁻¹)) := sq _
    _ = (d * (b * d * b⁻¹)) * (d * (b * d * b⁻¹))⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel _

@[expose] def rhoD : ↥D →* ↥A :=
  MonoidHom.mk' (fun d => ⟨(d : G) * (b * d * b⁻¹), H.D_rho_mem_A W W2 hD d.2⟩) (fun d d' => by
    apply Subtype.ext
    have h1 : b * (d : G) * b⁻¹ ∈ D := H.b_conj_mem_D W W2 hD d.2
    have hc : (b * (d : G) * b⁻¹) * (d' : G) = (d' : G) * (b * (d : G) * b⁻¹) :=
      hD.comm _ h1 _ d'.2
    show (d : G) * d' * (b * ((d : G) * d') * b⁻¹) =
      ((d : G) * (b * d * b⁻¹)) * ((d' : G) * (b * d' * b⁻¹))
    calc (d : G) * d' * (b * ((d : G) * d') * b⁻¹)
        = (d : G) * ((d' : G) * (b * d * b⁻¹)) * (b * d' * b⁻¹) := by group
      _ = (d : G) * ((b * (d : G) * b⁻¹) * d') * (b * d' * b⁻¹) := by rw [← hc]
      _ = _ := by group)

@[expose] noncomputable def thD : ↥D →* ↥A :=
  (thetaHom H W).comp (Subgroup.inclusion (H.D_le_Bp W W2 hD))

theorem ThCyc.b_conj_equivariant {n : G} (hnL : n ∈ L) (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) {d : G}
    (hd : d ∈ D) : b * (n * d * n⁻¹) * b⁻¹ = n * (b * d * b⁻¹) * n⁻¹ := by
  have hnAa := W2.conj_mem_of_mem_L W hnL hnA
  have hb' : n⁻¹ * b * n ∈ B := by
    have := W.conj_mem_B (h := n⁻¹) (fun a ha => by simpa using hnA a ha)
      (fun y hy => by simpa using L.mul_mem (L.mul_mem (L.inv_mem hnL) (W.B_le hy)) hnL) b
      W2.b_mem
    simpa using this
  have hb'Aa : n⁻¹ * b * n * b ∈ Aa := by
    rcases W2.mem_Aa_or_mul_b W hb' with h | h
    · exfalso
      apply W2.b_not_mem
      have h1 := hnAa _ h
      have e : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
      rwa [e] at h1
    · exact h
  have hbinv := W2.b_inv_eq_self
  have hb'eq : n⁻¹ * b * n = (n⁻¹ * b * n * b) * b := by
    calc n⁻¹ * b * n = (n⁻¹ * b * n * b) * b⁻¹ := by group
      _ = (n⁻¹ * b * n * b) * b := by rw [hbinv]
  have hb_eq : b = n * ((n⁻¹ * b * n * b) * b) * n⁻¹ := by
    rw [← hb'eq]
    group
  have hcomm : (n⁻¹ * b * n * b) * (b * d * b⁻¹) = (b * d * b⁻¹) * (n⁻¹ * b * n * b) :=
    hD.comm _ (hD.Aa_le hb'Aa) _ (H.b_conj_mem_D W W2 hD hd)
  generalize n⁻¹ * b * n * b = a' at hb_eq hcomm
  calc b * (n * d * n⁻¹) * b⁻¹
      = (n * (a' * b) * n⁻¹) * (n * d * n⁻¹) * (n * (a' * b) * n⁻¹)⁻¹ := by
        rw [← hb_eq]
    _ = n * (a' * (b * d * b⁻¹) * a'⁻¹) * n⁻¹ := by group
    _ = n * ((b * d * b⁻¹) * a' * a'⁻¹) * n⁻¹ := by rw [hcomm]
    _ = n * (b * d * b⁻¹) * n⁻¹ := by group

theorem ThCyc.schur_D (ρ : ↥D →* ↥A) (hker : ∀ d : ↥D, (d : G) ∈ Aa → ρ d = 1)
    (hρK : ∀ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) → ∀ (d : ↥D) (h : n * (d : G) * n⁻¹ ∈ D),
      ((ρ ⟨n * d * n⁻¹, h⟩ : ↥A) : G) = n * (ρ d : G) * n⁻¹) :
    ∃ e : ℕ, ∀ d : ↥D, ((ρ d : ↥A) : G) = (theta t (d : G)) ^ e :=
  exists_pow_of_equivariant (A := A) (K := L) (D := D) W.A_comm W.A_sq
    W.A_card W.surj (fun n _ hnA a ha => conj_inv_mem_of_conj_mem hnA ha)
    (fun n hn hnA d hd => hD.norm n (H.mem_normalizer_W5_of_L W hn hnA) d hd)
    (thD H W W2 hD) ρ
    (fun a => by
      obtain ⟨d, hd, hda⟩ := H.D_exists_theta_eq W W2 hD a.2
      exact ⟨⟨d, hd⟩, Subtype.ext hda⟩)
    (fun d hd => hker d ((H.D_theta_eq_one_iff W W2 hD d.2).1
      (congrArg (fun x : ↥A => (x : G)) hd)))
    (fun n hn _ d h => H.theta_conj hn (d : G)) hρK W.z_mem_A W.z_ne_one

theorem ThCyc.D_rho_pow : ∃ e : ℕ, ∀ d ∈ D, d * (b * d * b⁻¹) = (theta t d) ^ e := by
  obtain ⟨e, he⟩ := H.schur_D W W2 hD (rhoD H W W2 hD)
    (fun d h2 => by
      apply Subtype.ext
      show (d : G) * (b * d * b⁻¹) = 1
      rw [W2.b_inv _ h2]
      group)
    (fun n hn hnA d h => by
      show (n * (d : G) * n⁻¹) * (b * (n * (d : G) * n⁻¹) * b⁻¹) =
        n * ((d : G) * (b * d * b⁻¹)) * n⁻¹
      rw [H.b_conj_equivariant W W2 hD hn hnA d.2]
      group)
  exact ⟨e, fun d hd => he ⟨d, hd⟩⟩

theorem ThCyc.D_rho_dichotomy :
    (∀ d ∈ D, d * (b * d * b⁻¹) = 1) ∨ (∀ d ∈ D, d * (b * d * b⁻¹) = theta t d) := by
  obtain ⟨e, he⟩ := H.D_rho_pow W W2 hD
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · left
    intro d hd
    have hθ : theta t d ^ 2 = 1 := W.A_sq _ (H.theta_mem_A W (H.D_le_Bp W W2 hD hd))
    rw [he d hd, hk, pow_mul, hθ, one_pow]
  · right
    intro d hd
    have hθ : theta t d ^ 2 = 1 := W.A_sq _ (H.theta_mem_A W (H.D_le_Bp W W2 hD hd))
    rw [he d hd, hk, pow_succ, pow_mul, hθ, one_pow, one_mul]

theorem ThCyc.D_pow_four_mem_A {d : G} (hd : d ∈ D) : d ^ 4 ∈ A := by
  have h : (d ^ 2) ^ 2 ∈ A := W2.sq_mem_A (H.D_sq_mem_Aa W W2 hD hd)
  have e : (d ^ 2) ^ 2 = d ^ 4 := by rw [← pow_mul]
  rwa [e] at h

@[expose] def fourthD : ↥D →* ↥A :=
  MonoidHom.mk' (fun d => ⟨(d : G) ^ 4, H.D_pow_four_mem_A W W2 hD d.2⟩) (fun d d' =>
    Subtype.ext (by
      show ((d : G) * d') ^ 4 = (d : G) ^ 4 * (d' : G) ^ 4
      exact (show Commute (d : G) d' from hD.comm _ d.2 _ d'.2).mul_pow 4))

theorem ThCyc.D_fourth_dichotomy :
    (∀ d ∈ D, d ^ 4 = 1) ∨ (∀ d ∈ D, d ^ 4 = theta t d) := by
  obtain ⟨e, he⟩ := H.schur_D W W2 hD (fourthD H W W2 hD)
    (fun d h2 => Subtype.ext (W2.Aa_exp _ h2))
    (fun n hn hnA d h => by
      show (n * (d : G) * n⁻¹) ^ 4 = n * (d : G) ^ 4 * n⁻¹
      exact conj_pow)
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · left
    intro d hd
    have hθ : theta t d ^ 2 = 1 := W.A_sq _ (H.theta_mem_A W (H.D_le_Bp W W2 hD hd))
    have := he ⟨d, hd⟩
    rw [hk, pow_mul, hθ, one_pow] at this
    exact this
  · right
    intro d hd
    have hθ : theta t d ^ 2 = 1 := W.A_sq _ (H.theta_mem_A W (H.D_le_Bp W W2 hD hd))
    have := he ⟨d, hd⟩
    rw [hk, pow_succ, pow_mul, hθ, one_pow, one_mul] at this
    exact this

end

end CFSG.EvenSporadicStandard.ThStd
