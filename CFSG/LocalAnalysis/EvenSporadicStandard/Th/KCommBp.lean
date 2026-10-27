module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommT

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G]

abbrev BComm (b : G) (Aa : Subgroup G) (c : G) : Prop := b * c * b⁻¹ * c⁻¹ ∈ Aa

theorem conj_eq_of_mem_centralizer {Aa : Subgroup G} {c x : G} (hc : c ∈ centralizer (Aa : Set G))
    (hx : x ∈ Aa) : c * x * c⁻¹ = x := by
  have h : x * c = c * x := mem_centralizer_iff.1 hc x hx
  rw [← h]
  group

theorem BComm.mul {b : G} {Aa : Subgroup G} {c c' : G} (hc : c ∈ centralizer (Aa : Set G))
    (h1 : BComm b Aa c) (h2 : BComm b Aa c') : BComm b Aa (c * c') := by
  have e : b * (c * c') * b⁻¹ * (c * c')⁻¹ =
      (b * c * b⁻¹ * c⁻¹) * (c * (b * c' * b⁻¹ * c'⁻¹) * c⁻¹) := by group
  show b * (c * c') * b⁻¹ * (c * c')⁻¹ ∈ Aa
  rw [e, conj_eq_of_mem_centralizer hc h2]
  exact Aa.mul_mem h1 h2

variable [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G} {z b : G}

theorem ThLocalIn.exists_conj_of_ne_one (W : ThLocalIn L S A B z) {a a' : G} (ha : a ∈ A)
    (ha' : a' ∈ A) (h1 : a ≠ 1) (h1' : a' ≠ 1) :
    ∃ l ∈ L, (∀ x ∈ A, l * x * l⁻¹ ∈ A) ∧ l * a * l⁻¹ = a' := by
  obtain ⟨n₁, hn₁L, hn₁A, hn₁z⟩ := W.trans a ha h1
  obtain ⟨n₂, hn₂L, hn₂A, hn₂z⟩ := W.trans a' ha' h1'
  refine ⟨n₂ * n₁⁻¹, L.mul_mem hn₂L (L.inv_mem hn₁L), fun x hx => ?_, ?_⟩
  · have h1 := hn₂A _ (conj_inv_mem_of_conj_mem hn₁A hx)
    have e : n₂ * n₁⁻¹ * x * (n₂ * n₁⁻¹)⁻¹ = n₂ * (n₁⁻¹ * x * n₁) * n₂⁻¹ := by group
    rw [e]
    exact h1
  · have hz : n₁⁻¹ * a * n₁ = z := by
      rw [← hn₁z]
      group
    calc n₂ * n₁⁻¹ * a * (n₂ * n₁⁻¹)⁻¹ = n₂ * (n₁⁻¹ * a * n₁) * n₂⁻¹ := by group
      _ = n₂ * z * n₂⁻¹ := by rw [hz]
      _ = a' := hn₂z

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.comm_mem_Aa {x y : G} (hx : x ∈ Csub A Aa t) (hy : y ∈ Csub A Aa t) :
    x * y * x⁻¹ * y⁻¹ ∈ Aa := by
  have := H.Aa_subgroupOf_normal W W2
  have h := E_mul_comm H W W2 (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
  have h' : (QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ :
      ↥(Csub A Aa t)) : Equot A Aa t) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h]
    group
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h'
  exact h'

theorem ThCyc.theta_one : theta t (1 : G) = 1 := by simp [theta]

theorem ThCyc.theta_inv {r : G} (hr : r ∈ Bp A t) : theta t r⁻¹ = (theta t r)⁻¹ := by
  have h := H.theta_mul W hr ((Bp A t).inv_mem hr)
  rw [mul_inv_cancel, H.theta_one W W2] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ThCyc.theta_comm_Bp {r c : G} (hr : r ∈ Bp A t) (hc : c ∈ Bp A t) :
    theta t (r * c * r⁻¹ * c⁻¹) = 1 := by
  have hri := (Bp A t).inv_mem hr
  have hci := (Bp A t).inv_mem hc
  rw [H.theta_mul W ((Bp A t).mul_mem ((Bp A t).mul_mem hr hc) hri) hci,
    H.theta_mul W ((Bp A t).mul_mem hr hc) hri, H.theta_mul W hr hc, H.theta_inv W W2 hr,
    H.theta_inv W W2 hc]
  have hcomm := W.A_comm _ (H.theta_mem_A W hr) _ (H.theta_mem_A W hc)
  calc theta t r * theta t c * (theta t r)⁻¹ * (theta t c)⁻¹
      = theta t c * theta t r * (theta t r)⁻¹ * (theta t c)⁻¹ := by rw [hcomm]
    _ = 1 := by group

theorem ThCyc.mem_Aa_or_mul_t {y : G} (hy : y ∈ Csub A Aa t) (h1 : theta t y = 1) :
    y ∈ Aa ∨ ∃ x ∈ Aa, y = x * t := by
  have hyW : y ∈ centralizer ((W5 A t : Subgroup G) : Set G) ⊓ centralizer (Aa : Set G) :=
    ⟨(H.theta_eq_one_iff W hy.1).1 h1, hy.2⟩
  obtain ⟨x, hx, k, rfl⟩ := (H.mem_centralizer_W5_inf_centralizer_Aa_iff W W2).1 hyW
  rcases zpow_eq_one_or_self H.sq_t k with h | h
  · left
    rw [h, mul_one]
    exact hx
  · right
    exact ⟨x, hx, by rw [h]⟩

theorem ThCyc.bComm_Aa {x : G} (hx : x ∈ Aa) : BComm b Aa x := by
  have h := W2.b_inv x hx
  show b * x * b⁻¹ * x⁻¹ ∈ Aa
  rw [h]
  exact Aa.mul_mem (Aa.inv_mem hx) (Aa.inv_mem hx)

theorem ThCyc.bComm_t : BComm b Aa t := by
  have h : b * t = t * b := (H.comm_of_mem_L (W.B_le W2.b_mem)).symm
  show b * t * b⁻¹ * t⁻¹ ∈ Aa
  rw [h]
  have : t * b * b⁻¹ * t⁻¹ = 1 := by group
  rw [this]
  exact Aa.one_mem

theorem ThCyc.bComm_of_theta {y : G} (hy : y ∈ Csub A Aa t) (h1 : theta t y = 1) :
    BComm b Aa y := by
  rcases H.mem_Aa_or_mul_t W W2 hy h1 with h | ⟨x, hx, rfl⟩
  · exact H.bComm_Aa W W2 h
  · exact BComm.mul (H.Aa_le_inf_centralizer_Aa W W2 hx).2 (H.bComm_Aa W W2 hx)
      (H.bComm_t W W2)

theorem ThCyc.bComm_mem_C {c : G} (hc : c ∈ Csub A Aa t) : b * c * b⁻¹ * c⁻¹ ∈ Csub A Aa t := by
  have hbN : b ∈ normalizer ((W5 A t : Subgroup G) : Set G) := (H.b_mem_Bp W W2).2
  exact (Csub A Aa t).mul_mem (H.conj_mem_inf_centralizer_Aa W W2 hbN hc)
    ((Csub A Aa t).inv_mem hc)

theorem ThCyc.bComm_mul_of_not {c c' : G} (hc : c ∈ Csub A Aa t) (hc' : c' ∈ Csub A Aa t)
    (h1 : ¬ BComm b Aa c) (h2 : ¬ BComm b Aa c') : BComm b Aa (c * c') := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have key : ∀ y ∈ Csub A Aa t, ¬ BComm b Aa y → ∃ x ∈ Aa, b * y * b⁻¹ * y⁻¹ = x * t := by
    intro y hy hny
    rcases H.mem_Aa_or_mul_t W W2 (H.bComm_mem_C W W2 hy)
      (H.theta_comm_Bp W W2 (H.b_mem_Bp W W2) hy.1) with h | h
    · exact absurd h hny
    · exact h
  obtain ⟨x, hx, hxe⟩ := key c hc h1
  obtain ⟨x', hx', hxe'⟩ := key c' hc' h2
  have e : b * (c * c') * b⁻¹ * (c * c')⁻¹ =
      (b * c * b⁻¹ * c⁻¹) * (c * (b * c' * b⁻¹ * c'⁻¹) * c⁻¹) := by group
  show b * (c * c') * b⁻¹ * (c * c')⁻¹ ∈ Aa
  rw [e, hxe, hxe']
  have hct : c * t * c⁻¹ = theta t c * t := by
    simp only [theta]
    group
  have hcx' : c * x' * c⁻¹ = x' := conj_eq_of_mem_centralizer hc.2 hx'
  have e2 : x * t * (c * (x' * t) * c⁻¹) = x * t * (c * x' * c⁻¹) * (c * t * c⁻¹) := by group
  rw [e2, hcx', hct]
  have htx' : t * x' = x' * t := H.comm_of_mem_L (W.B_le (W2.Aa_le hx'))
  have hθA : theta t c ∈ A := H.theta_mem_A W hc.1
  have htθ : t * theta t c = theta t c * t := H.comm_of_mem_L (hA hθA)
  have e3 : x * t * x' * (theta t c * t) = x * x' * theta t c := by
    calc x * t * x' * (theta t c * t) = x * (t * x') * (theta t c * t) := by group
      _ = x * (x' * t) * (theta t c * t) := by rw [htx']
      _ = x * x' * (t * theta t c) * t := by group
      _ = x * x' * (theta t c * t) * t := by rw [htθ]
      _ = x * x' * theta t c * (t * t) := by group
      _ = x * x' * theta t c := by rw [← sq, H.sq_t, mul_one]
  rw [e3]
  exact Aa.mul_mem (Aa.mul_mem hx hx') (W2.A_le hθA)

theorem ThCyc.bComm_conj_iff {l : G} (hlL : l ∈ L) (hlA : ∀ x ∈ A, l * x * l⁻¹ ∈ A) {c : G}
    (hc : c ∈ Csub A Aa t) : BComm b Aa c ↔ BComm b Aa (l⁻¹ * c * l) := by
  have hlN : l ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W hlL hlA
  have hlN' : l⁻¹ ∈ normalizer ((W5 A t : Subgroup G) : Set G) := (normalizer _).inv_mem hlN
  have hAaL : ∀ x, x ∈ Aa ↔ l * x * l⁻¹ ∈ Aa := by
    intro x
    refine ⟨W2.conj_mem_of_mem_L W hlL hlA x, fun hx => ?_⟩
    have hl'L : l⁻¹ ∈ L := L.inv_mem hlL
    have hl'A : ∀ y ∈ A, l⁻¹ * y * l⁻¹⁻¹ ∈ A := fun y hy => by
      simpa using conj_inv_mem_of_conj_mem hlA hy
    have := W2.conj_mem_of_mem_L W hl'L hl'A _ hx
    simpa [mul_assoc] using this
  have hbl : l * b * l⁻¹ ∈ Bp A t := H.Bp_normal W hlN (H.b_mem_Bp W W2)
  obtain ⟨c0, hc0, hbc0⟩ := H.exists_mem_inf_centralizer_Aa W W2 hbl
  have hbc0' : l * b * l⁻¹ = c0 * b := by
    rcases hbc0 with h | h
    · exfalso
      have hbC : b ∈ Csub A Aa t := by
        have e : b = l⁻¹ * c0 * l⁻¹⁻¹ := by
          rw [← h]
          group
        rw [e]
        exact H.conj_mem_inf_centralizer_Aa W W2 hlN' hc0
      exact W2.b_not_mem_centralizer W hbC.2
    · exact h
  have hu : b * c * b⁻¹ * c⁻¹ ∈ Csub A Aa t := H.bComm_mem_C W W2 hc
  have hcc : c0 * c * c0⁻¹ * c⁻¹ ∈ Aa := H.comm_mem_Aa W W2 hc0 hc
  have hc0u : c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹ ∈ Aa ↔ b * c * b⁻¹ * c⁻¹ ∈ Aa := by
    have hh : c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹ * (b * c * b⁻¹ * c⁻¹)⁻¹ ∈ Aa :=
      H.comm_mem_Aa W W2 hc0 hu
    constructor
    · intro h
      have := Aa.mul_mem (Aa.inv_mem h) hh
      have e : (c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹)⁻¹ *
          (c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹ * (b * c * b⁻¹ * c⁻¹)⁻¹) =
          (b * c * b⁻¹ * c⁻¹)⁻¹ := by group
      rw [e] at this
      simpa using Aa.inv_mem this
    · intro h
      have := Aa.mul_mem hh h
      rwa [inv_mul_cancel_right] at this
  have key : (l * b * l⁻¹) * c * (l * b * l⁻¹)⁻¹ * c⁻¹ =
      (c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹) * (c0 * c * c0⁻¹ * c⁻¹) := by
    rw [hbc0']
    group
  have hZ : l * (b * (l⁻¹ * c * l) * b⁻¹ * (l⁻¹ * c * l)⁻¹) * l⁻¹ =
      (c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹) * (c0 * c * c0⁻¹ * c⁻¹) := by
    rw [← key]
    group
  show b * c * b⁻¹ * c⁻¹ ∈ Aa ↔ b * (l⁻¹ * c * l) * b⁻¹ * (l⁻¹ * c * l)⁻¹ ∈ Aa
  rw [← hc0u, hAaL (b * (l⁻¹ * c * l) * b⁻¹ * (l⁻¹ * c * l)⁻¹), hZ]
  constructor
  · intro h
    exact Aa.mul_mem h hcc
  · intro h
    have := Aa.mul_mem h (Aa.inv_mem hcc)
    rwa [mul_inv_cancel_right] at this

theorem ThCyc.bcomm_mem_Aa {c : G} (hc : c ∈ Csub A Aa t) : BComm b Aa c := by
  by_contra hcon
  have hθ1 : theta t c ≠ 1 := fun h1 => hcon (H.bComm_of_theta W W2 hc h1)
  have hB : ∀ c' ∈ Csub A Aa t, theta t c' ≠ 1 → ¬ BComm b Aa c' := by
    intro c' hc' hθ' hbc'
    obtain ⟨l, hlL, hlA, hl⟩ := W.exists_conj_of_ne_one (H.theta_mem_A W hc.1)
      (H.theta_mem_A W hc'.1) hθ1 hθ'
    have hlN := H.mem_normalizer_W5_of_L W hlL hlA
    have hc2 : l * c * l⁻¹ ∈ Csub A Aa t := H.conj_mem_inf_centralizer_Aa W W2 hlN hc
    have hθ2 : theta t (l * c * l⁻¹) = theta t c' := by rw [H.theta_conj hlL, hl]
    have hnb2 : ¬ BComm b Aa (l * c * l⁻¹) := by
      intro h2
      apply hcon
      have := (H.bComm_conj_iff W W2 hlL hlA hc2).1 h2
      have e : l⁻¹ * (l * c * l⁻¹) * l = c := by group
      rwa [e] at this
    have hy : (l * c * l⁻¹)⁻¹ * c' ∈ Csub A Aa t := (Csub A Aa t).mul_mem
      ((Csub A Aa t).inv_mem hc2) hc'
    have hθy : theta t ((l * c * l⁻¹)⁻¹ * c') = 1 := by
      rw [H.theta_mul W ((Csub A Aa t).inv_mem hc2).1 hc'.1, H.theta_inv W W2 hc2.1, hθ2,
        inv_mul_cancel]
    have hyi : ((l * c * l⁻¹)⁻¹ * c')⁻¹ ∈ Csub A Aa t := (Csub A Aa t).inv_mem hy
    have hθyi : theta t ((l * c * l⁻¹)⁻¹ * c')⁻¹ = 1 := by
      rw [H.theta_inv W W2 hy.1, hθy, inv_one]
    have hby := H.bComm_of_theta W W2 hyi hθyi
    apply hnb2
    have := BComm.mul hc'.2 hbc' hby
    have e : c' * ((l * c * l⁻¹)⁻¹ * c')⁻¹ = l * c * l⁻¹ := by group
    rwa [e] at this
  obtain ⟨a₁, a₂, a₃, h1, h2, -, h12, -, -, -⟩ := exists_three_independent W
  obtain ⟨c₁, hc₁, hθ₁⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 a₁.2
  obtain ⟨c₂, hc₂, hθ₂⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 a₂.2
  have hn1 := hB c₁ hc₁ (by rw [hθ₁]; exact fun h => h1 (Subtype.ext h))
  have hn2 := hB c₂ hc₂ (by rw [hθ₂]; exact fun h => h2 (Subtype.ext h))
  have hmul : BComm b Aa (c₁ * c₂) := H.bComm_mul_of_not W W2 hc₁ hc₂ hn1 hn2
  have hθ12 : theta t (c₁ * c₂) ≠ 1 := by
    rw [H.theta_mul W hc₁.1 hc₂.1, hθ₁, hθ₂]
    intro h
    have h' : a₁ * a₂ = 1 := Subtype.ext h
    have ha₁sq : a₁ * a₁ = 1 := Subtype.ext (by simpa [sq] using W.A_sq _ a₁.2)
    exact h12 (mul_left_cancel (h'.trans ha₁sq.symm)).symm
  exact hB _ ((Csub A Aa t).mul_mem hc₁ hc₂) hθ12 hmul

theorem ThCyc.Bp_comm_mem_Aa {r : G} (hr : r ∈ Bp A t) {c : G} (hc : c ∈ Csub A Aa t) :
    r * c * r⁻¹ * c⁻¹ ∈ Aa := by
  obtain ⟨c0, hc0, hrc | hrc⟩ := H.exists_mem_inf_centralizer_Aa W W2 hr
  · rw [hrc]
    exact H.comm_mem_Aa W W2 hc0 hc
  · rw [hrc]
    have e : c0 * b * c * (c0 * b)⁻¹ * c⁻¹ =
        (c0 * (b * c * b⁻¹ * c⁻¹) * c0⁻¹) * (c0 * c * c0⁻¹ * c⁻¹) := by group
    rw [e]
    refine Aa.mul_mem ?_ (H.comm_mem_Aa W W2 hc0 hc)
    rw [conj_eq_of_mem_centralizer hc0.2 (H.bcomm_mem_Aa W W2 hc)]
    exact H.bcomm_mem_Aa W W2 hc

end

end CFSG.EvenSporadicStandard.ThStd
