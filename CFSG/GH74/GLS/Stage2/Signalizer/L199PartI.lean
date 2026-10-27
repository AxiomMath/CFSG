module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GH74.GLS.Stage2.Signalizer.L199Cop
public import CFSG.GH74.GLS.Stage2.Signalizer.L199Quot

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L199

open Subgroup CFSG
open scoped commutatorElement

universe u

theorem part_one_aux : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X = n →
    ∀ {z : X} {r : ℕ} {R : Subgroup X}, SigData X z r R →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ r →
        R ≤ centralizer ((pCore p X : Subgroup X) : Set X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hcard z r R h p hp hp2 hpr
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨h.prime⟩
  set P : Subgroup X := pCore p X with hP
  have hPn : P.Normal := pCore_normal
  have hPp : IsPGroup p P := pCore_isPGroup
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    intro x _
    simp [Subgroup.mem_centralizer_iff]
  let Z : Subgroup X := P ⊓ centralizer (P : Set X)
  have hZP : Z ≤ P := inf_le_left
  have hZnormal : Z.Normal := by
    refine ⟨fun n hn g => ⟨hPn.conj_mem n hn.1 g, ?_⟩⟩
    show g * n * g⁻¹ ∈ centralizer (P : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ P := by
      simpa using hPn.conj_mem y hy g⁻¹
    have hcomm : (g⁻¹ * y * g) * n = n * (g⁻¹ * y * g) := Subgroup.mem_centralizer_iff.1 hn.2 _ hy'
    calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * n * g⁻¹) * y := by group
  have hZne : Z ≠ ⊥ := by
    have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPbot
    have : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center P)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨(c.1 : X), c.1.2, ?_⟩, ?_⟩
    · show ((c.1 : P) : X) ∈ centralizer (P : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.1 c.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    · intro h1
      apply hc
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h1
  have hZp : IsPGroup p Z := hPp.to_le hZP
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 ha.2 b (hZP hb)).symm
  have hZodd : Odd (Nat.card Z) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_z
  have hzR : z ∈ normalizer (R : Set X) := h.inv z (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hRP : Disjoint R P := IsPGroup.disjoint_of_ne r p (Ne.symm hpr) R P h.pgroup hPp
  have hC : ∀ u ∈ Z, u * z = z * u → ∀ ρ ∈ R, u * ρ = ρ * u := by
    intro u hu huz ρ hρ
    have hun : u ∈ normalizer (R : Set X) := h.inv u (Subgroup.mem_centralizer_singleton_iff.2 huz)
    have h1 : u * ρ * u⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hun ρ).1 hρ
    have h2 : ρ * u⁻¹ * ρ⁻¹ ∈ P := hPn.conj_mem u⁻¹ (P.inv_mem (hZP hu)) ρ
    have hcomm : ⁅u, ρ⁆ ∈ R ⊓ P := by
      refine ⟨?_, ?_⟩
      · have : ⁅u, ρ⁆ = (u * ρ * u⁻¹) * ρ⁻¹ := by rw [commutatorElement_def]
        rw [this]; exact R.mul_mem h1 (R.inv_mem hρ)
      · have : ⁅u, ρ⁆ = u * (ρ * u⁻¹ * ρ⁻¹) := by rw [commutatorElement_def]; group
        rw [this]; exact P.mul_mem (hZP hu) h2
    have h3 : ⁅u, ρ⁆ = 1 := by
      have := hRP.le_bot hcomm
      simpa using this
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have : Z.Normal := hZnormal
  have hAL : ⁅Z, R⁆ = ⊥ :=
    abelian_lemma hpr hZp hZab h.pgroup hz2 hzR h.comm hC
  have hRZ : R ≤ centralizer (Z : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hAL
  have hcardZ : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).2 hZne
  have hlt : Nat.card (X ⧸ Z) < n := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hpos : 0 < Nat.card (X ⧸ Z) := Nat.card_pos
    rw [← hcard, this]
    nlinarith
  have hquot := h.quotient Z hZodd
  have key := ih (Nat.card (X ⧸ Z)) hlt (X ⧸ Z) rfl hquot p hp hp2 hpr
  have hPbar : P.map (QuotientGroup.mk' Z) ≤ pCore p (X ⧸ Z) :=
    le_sSup ⟨hPn.map _ (QuotientGroup.mk'_surjective Z), hPp.map _⟩
  have hPR : ⁅P, R⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx ρ hρ
    have h1 : QuotientGroup.mk' Z ρ ∈ centralizer ((pCore p (X ⧸ Z) : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) :=
      key ⟨ρ, hρ, rfl⟩
    have h2 : QuotientGroup.mk' Z x ∈ pCore p (X ⧸ Z) := hPbar ⟨x, hx, rfl⟩
    have h3 := Subgroup.mem_centralizer_iff.1 h1 _ h2
    have h4 : ⁅QuotientGroup.mk' Z x, QuotientGroup.mk' Z ρ⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h3
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_commutatorElement]
    exact h4
  have hn : R ≤ normalizer (P : Set X) := by
    rw [Subgroup.normalizer_eq_top P]; exact le_top
  have hbot := commutator_eq_bot_of_le_centralizer hp h.prime hpr hPp h.pgroup hn hPR hRZ
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hbot

theorem part_one {X : Type u} [Group X] [Finite X] {z : X} {r : ℕ} {R : Subgroup X}
    (h : SigData X z r R) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpr : p ≠ r) :
    R ≤ centralizer ((pCore p X : Subgroup X) : Set X) :=
  part_one_aux _ X rfl h p hp hp2 hpr

end CFSG.GH74.GLS.Stage2.Signalizer.L199
