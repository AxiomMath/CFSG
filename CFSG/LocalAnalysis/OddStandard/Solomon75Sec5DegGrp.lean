module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFin

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

theorem isSolvable_ker_comp {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (φ₁ : G₁ →* G₂) (φ₂ : G₂ →* G₃) (h₁ : Group.IsSolvable φ₁.ker)
    (h₂ : Group.IsSolvable φ₂.ker) : Group.IsSolvable (φ₂.comp φ₁).ker := by
  let g : (φ₂.comp φ₁).ker →* φ₂.ker :=
    (φ₁.comp (φ₂.comp φ₁).ker.subtype).codRestrict φ₂.ker (fun k => k.2)
  have hle : φ₁.ker ≤ (φ₂.comp φ₁).ker := fun x hx => by
    show φ₂ (φ₁ x) = 1
    rw [MonoidHom.mem_ker.1 hx, map_one]
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g ?_
  intro k hk
  refine ⟨⟨k, ?_⟩, rfl⟩
  exact congrArg Subtype.val hk

theorem card_le_factorial_of_solvable_ker {B G Ξ : Type*} [Group B] [Group G] [Fintype Ξ]
    [DecidableEq Ξ] (Q : Subgroup G) [IsSimpleGroup Q] [Finite Q] (hQ : ¬ Group.IsSolvable Q)
    (ψ : B →* G) (hψ : Q ≤ ψ.range) (Θ : B →* Perm Ξ) (hΘ : Group.IsSolvable Θ.ker) :
    Nat.card Q ≤ (Fintype.card Ξ).factorial := by
  classical
  let B₀ : Subgroup B := Q.comap ψ
  let ψ₀ : B₀ →* Q := (ψ.comp B₀.subtype).codRestrict Q (fun b => b.2)
  have hψ₀ : Function.Surjective ψ₀ := by
    intro q
    obtain ⟨b, hb⟩ := hψ q.2
    exact ⟨⟨b, by show ψ b ∈ Q; rw [hb]; exact q.2⟩, Subtype.ext hb⟩
  let Θ₀ : B₀ →* Perm Ξ := Θ.comp B₀.subtype
  have hΘ₀ : Group.IsSolvable Θ₀.ker := by
    let e : Θ₀.ker →* Θ.ker := (B₀.subtype.comp Θ₀.ker.subtype).codRestrict Θ.ker (fun k => k.2)
    refine Group.isSolvable_of_isSolvable_injective (f := e) ?_
    intro a b hab
    have h1 : ((e a : Θ.ker) : B) = ((e b : Θ.ker) : B) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hN₀ : ((Θ₀.ker).map ψ₀).Normal := Subgroup.Normal.map inferInstance ψ₀ hψ₀
  have hker : Θ₀.ker ≤ ψ₀.ker := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Θ₀.ker).map ψ₀) with h0 | h0
    · intro k hk
      have : ψ₀ k ∈ (Θ₀.ker).map ψ₀ := ⟨k, hk, rfl⟩
      rw [h0] at this
      exact this
    · exfalso
      apply hQ
      refine Group.isSolvable_of_surjective (f := ψ₀.comp Θ₀.ker.subtype) ?_
      intro q
      have : q ∈ (Θ₀.ker).map ψ₀ := by rw [h0]; exact Subgroup.mem_top q
      obtain ⟨k, hk, hkq⟩ := this
      exact ⟨⟨k, hk⟩, hkq⟩
  let ψ₁ : B₀ ⧸ Θ₀.ker →* Q := QuotientGroup.lift Θ₀.ker ψ₀ hker
  have hψ₁ : Function.Surjective ψ₁ := by
    intro q
    obtain ⟨b, hb⟩ := hψ₀ q
    exact ⟨QuotientGroup.mk b, by simpa [ψ₁] using hb⟩
  have hfin : Finite (B₀ ⧸ Θ₀.ker) :=
    Finite.of_equiv Θ₀.range (QuotientGroup.quotientKerEquivRange Θ₀).symm.toEquiv
  calc Nat.card Q ≤ Nat.card (B₀ ⧸ Θ₀.ker) := Nat.card_le_card_of_surjective ψ₁ hψ₁
    _ = Nat.card Θ₀.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ₀).toEquiv
    _ ≤ Nat.card (Perm Ξ) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = (Fintype.card Ξ).factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem two_mul_factorial_lt (m : ℕ) (hm : 2 ≤ m) :
    2 * (2 * m).factorial < (4 * m - 2).factorial := by
  have h1 : (2 * m + 2).factorial ≤ (4 * m - 2).factorial :=
    Nat.factorial_le (by omega)
  have h2 : (2 * m + 2).factorial = (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  have h3 : 0 < (2 * m).factorial := Nat.factorial_pos _
  have h4 : 2 * (2 * m).factorial < (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
    calc 2 * (2 * m).factorial < 30 * (2 * m).factorial := by omega
      _ ≤ (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_right _ (by nlinarith)
  omega

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem isSolvable_R (h : PairCtx X n z s A A' M M') (hR : h.RCore) : Group.IsSolvable ↥h.R := by
  let z' : ↥h.R := ⟨s, h.s_mem_R⟩
  have hz' : orderOf z' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.hs
  have hzc : ∀ g : ↥h.R, g * z' = z' * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (h.mem_R_iff.1 g.2).2.1)
  have hall : ∀ g : ↥h.R, (∃ j : ℕ, g ^ (2 ^ j) = 1) → g ∈ zpowers z' := by
    rintro g ⟨j, hj⟩
    have hj' : (g : X) ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (h.R2_of_RCore hR g.2 hj')
    refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    simpa using hk
  have hcard : (Nat.card ↥h.R).factorization 2 = 1 := factorization_two_eq_one_of_hall hz' hall
  obtain ⟨O, hOn, hOodd, hO⟩ := exists_normal_complement_of_central_involution hz' hzc hcard
  have := hOn
  have : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  have key : ∀ a : ↥h.R ⧸ O, a = 1 ∨ a = (QuotientGroup.mk z' : ↥h.R ⧸ O)⁻¹ := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rcases hO g with hg | hg
    · exact Or.inl ((QuotientGroup.eq_one_iff g).2 hg)
    · right
      have h1 : (QuotientGroup.mk (g * z') : ↥h.R ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).2 hg
      rw [QuotientGroup.mk_mul] at h1
      exact eq_inv_of_mul_eq_one_left h1
  have hcomm : ∀ a b : ↥h.R ⧸ O, a * b = b * a := by
    intro a b
    rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> simp
  have : Group.IsSolvable (↥h.R ⧸ O) := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_subgroup_quotient O

end PairCtx

end CFSG.OddStandard.Solomon75
