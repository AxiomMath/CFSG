module

public import CFSG.CGT.PushingUpLit.SolKR2.Defs
public import CFSG.RankThree.GF2n.Tim78Thm1
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

theorem isTI_omegaOneSub {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hTI : IsTI B) :
    IsTI (omegaOneSub B) := by
  intro k
  by_cases hk : omegaOneSub B ⊓ conjSubgroup k (omegaOneSub B) = ⊥
  · exact Or.inl hk
  · right
    have hBk : conjSubgroup k B = B := by
      refine conjSubgroup_eq_of_isTI hTI fun hbot => hk ?_
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have : y ∈ B ⊓ conjSubgroup k B := Subgroup.mem_inf.mpr
        ⟨omegaOneSub_le B hy1, mem_conjSubgroup.mpr (omegaOneSub_le B (mem_conjSubgroup.mp hy2))⟩
      rwa [hbot] at this
    rw [← omegaOneSub_conj hB, hBk, inf_idem]

namespace R2

variable (h : R2 M B)
include h

omit [Finite G] in
theorem omegaOne_omegaTwo : omegaOneSub (omegaTwoSub B) = omegaOneSub B :=
  omegaOneSub_omegaTwoSub h.H.comm

omit [Finite G] in
theorem omegaOne_ne : omegaOneSub B ≠ B := by
  intro heq
  apply h.ne
  refine ⟨⟨⟨fun a b => Subtype.ext (h.H.comm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [← heq] at hx
  rw [sq]
  exact ((mem_omegaOneSub_iff h.H.comm).mp hx).2

theorem s3hyp : S3Hyp M (omegaTwoSub B) where
  max := h.H.max
  fstar := h.H.fstar
  le := le_trans (omegaTwoSub_le _) h.H.le
  normal := h.H.le_normalizer_omegaTwo
  comm := comm_omegaTwoSub h.H.comm
  two := h.H.two.to_le (omegaTwoSub_le _)
  ti := isTI_omegaTwoSub h.H.comm h.H.ti
  exp := fun _ hx => pow_four_of_mem_omegaTwoSub h.H.comm hx
  ne := omegaOneSub_omegaTwoSub_ne h.H.comm h.H.two h.omegaOne_ne
  card4 := by rw [h.omegaOne_omegaTwo, h.card4]

theorem isTI_B0 : IsTI (omegaOneSub B) := isTI_omegaOneSub h.H.comm h.H.ti

omit [Finite G] in
theorem omegaOne_ne_bot : omegaOneSub B ≠ ⊥ := by
  intro hbot
  have := h.card4
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem normalizer_B0 : Subgroup.normalizer (omegaOneSub B : Set G) = M := by
  have := h.s3hyp.normalizer_omega_eq
  rwa [h.omegaOne_omegaTwo] at this

theorem normalizer_U : Subgroup.normalizer (omegaTwoSub B : Set G) = M :=
  h.s3hyp.normalizer_U_eq

end R2

namespace Lam

variable {A : Subgroup G}

omit [Finite G] in
theorem exists_conj (hA : A ∈ Lam M B) : ∃ g : G, A = conjSubgroup g (omegaOneSub B) := by
  obtain ⟨g, hg, -⟩ := hA
  exact ⟨g, hg⟩

omit [Finite G] in
theorem le_M (hA : A ∈ Lam M B) : A ≤ M := by
  obtain ⟨-, -, hM⟩ := hA
  exact hM

omit [Finite G] in
theorem conj_mem (hA : A ∈ Lam M B) {m : G} (hm : m ∈ M) : conjSubgroup m A ∈ Lam M B := by
  obtain ⟨g, rfl, hM⟩ := hA
  refine ⟨m * g, (conjSubgroup_mul m g _).symm, fun z hz => ?_⟩
  rw [mem_conjSubgroup] at hz
  rw [show z = m * (m⁻¹ * z * m) * m⁻¹ by group]
  exact M.mul_mem (M.mul_mem hm (hM hz)) (M.inv_mem hm)

omit [Finite G] in
theorem card_eq (h : R2 M B) (hA : A ∈ Lam M B) : Nat.card ↥A = 4 := by
  obtain ⟨g, rfl⟩ := exists_conj hA
  rw [card_conjSubgroup, h.card4]

omit [Finite G] in
theorem ne_bot (h : R2 M B) (hA : A ∈ Lam M B) : A ≠ ⊥ := by
  intro hbot
  have := card_eq h hA
  rw [hbot, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem mul_self (h : R2 M B) (hA : A ∈ Lam M B) : ∀ a ∈ A, a * a = 1 := by
  obtain ⟨g, rfl⟩ := exists_conj hA
  exact fun a ha => mul_self_of_mem_conj
    (fun v hv => ((mem_omegaOneSub_iff h.H.comm).mp hv).2) ha

omit [Finite G] in
theorem comm_self (h : R2 M B) (hA : A ∈ Lam M B) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  obtain ⟨g, rfl⟩ := exists_conj hA
  exact Tim78.comm_conj (B := omegaOneSub B) (fun x hx y hy =>
    h.H.comm x (omegaOneSub_le B hx) y (omegaOneSub_le B hy)) g

end Lam

section Certificates34

theorem R2.root (h : R2 M B) : IsRootTypeTI (omegaOneSub B) := by
  have := h.s3hyp.root CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
  rwa [h.omegaOne_omegaTwo] at this

theorem R2.comm_B0 (h : R2 M B) {A : Subgroup G} (hA : A ∈ Lam M B) :
    ∀ a ∈ A, ∀ b ∈ omegaOneSub B, a * b = b * a := by
  obtain ⟨g, hg⟩ := Lam.exists_conj hA
  have hAM := Lam.le_M hA
  have hne : conjSubgroup g (omegaOneSub B) ⊓
      Subgroup.normalizer (conjSubgroup 1 (omegaOneSub B) : Set G) ≠ ⊥ := by
    rw [conjSubgroup_one, h.normalizer_B0, ← hg, inf_of_le_left hAM]
    exact Lam.ne_bot h hA
  have hc := commute_of_isRootTypeTI h.root (g := g) (h := 1) hne
  intro a ha b hb
  rw [hg] at ha
  exact hc a ha b (by rwa [conjSubgroup_one])

end Certificates34

end CFSG.CGT.PushingUpLit.SolKR2
