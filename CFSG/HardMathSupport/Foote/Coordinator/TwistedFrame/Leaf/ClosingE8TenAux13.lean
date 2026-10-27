module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux11

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


section Generic

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L]
  (S : Setup K L)

theorem Setup.exists_pair {r₁ r₂ : Fin Tag.E8.rank → ℤ} (h₁ : IsRoot Tag.E8 r₁)
    (h₂ : IsRoot Tag.E8 r₂) :
    ∃ s d : L, s ≠ 0 ∧ S.sg r₁ * S.Fr s = d ∧ S.sg r₂ * S.Fr d = s := by
  obtain ⟨hs₁, -⟩ := S.hm r₁ h₁
  obtain ⟨hs₂, -⟩ := S.hm r₂ h₂
  have hq := card_ge_two K
  obtain ⟨C, hCcard, hCpow⟩ := exists_pair_set K L (S.sg r₁) (S.sg r₂) hs₁ hs₂
  have hκ2 := kappa_sq (Nat.card K) (S.sg r₁) (S.sg r₂) hs₁ hs₂
  have hne : ∃ c ∈ C, c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : C.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by rw [hcon a ha, hcon b hb]
    rw [hCcard] at this
    nlinarith
  obtain ⟨c, hc, hc0⟩ := hne
  refine ⟨c, S.sg r₁ * c ^ Nat.card K, hc0, by rw [S.hFr c], ?_⟩
  have e1 : S.Fr (S.sg r₁ * c ^ Nat.card K) = S.sg r₁ ^ Nat.card K * c ^ (Nat.card K ^ 2) := by
    rw [map_mul, map_pow, S.hFr (S.sg r₁), S.hFr c, ← pow_mul, sq]
  rw [e1, hCpow c hc]
  calc S.sg r₂ * (S.sg r₁ ^ Nat.card K * ((S.sg r₂ * S.sg r₁ ^ Nat.card K) * c))
      = ((S.sg r₂ * S.sg r₁ ^ Nat.card K) * (S.sg r₂ * S.sg r₁ ^ Nat.card K)) * c := by ring
    _ = c := by rw [hκ2, one_mul]

theorem Setup.pair_sfixed {r₁ r₂ : Fin Tag.E8.rank → ℤ} (h₁ : IsRoot Tag.E8 r₁)
    (h₂ : IsRoot Tag.E8 r₂) (hw₁ : S.w • r₁ = r₂) (hw₂ : S.w • r₂ = r₁)
    (hcomm : ∀ s t : L, pinnedX Tag.E8 L r₁ s * pinnedX Tag.E8 L r₂ t =
      pinnedX Tag.E8 L r₂ t * pinnedX Tag.E8 L r₁ s) {s d : L} (hs : S.sg r₁ * S.Fr s = d)
    (hd : S.sg r₂ * S.Fr d = s) :
    S.n * Frob S.Fr (pinnedX Tag.E8 L r₁ s * pinnedX Tag.E8 L r₂ d) * S.n⁻¹ =
      pinnedX Tag.E8 L r₁ s * pinnedX Tag.E8 L r₂ d := by
  obtain ⟨-, hc₁⟩ := S.hm r₁ h₁
  obtain ⟨-, hc₂⟩ := S.hm r₂ h₂
  have e : S.n * (pinnedX Tag.E8 L r₁ (S.Fr s) * pinnedX Tag.E8 L r₂ (S.Fr d)) * S.n⁻¹ =
      (S.n * pinnedX Tag.E8 L r₁ (S.Fr s) * S.n⁻¹) *
        (S.n * pinnedX Tag.E8 L r₂ (S.Fr d) * S.n⁻¹) := by group
  rw [map_mul, Frob_pinnedX, Frob_pinnedX, e, hc₁ (S.Fr s), hc₂ (S.Fr d), hw₁, hw₂, hs, hd]
  exact (hcomm s d).symm

theorem Setup.rat_of_sfixed {x : ModGL Tag.E8 L} (hxA : x ∈ adjointGroup Tag.E8 L)
    (hxσ : S.n * Frob S.Fr x * S.n⁻¹ = x) :
    ∃ l ∈ adjointGroup Tag.E8 K, baseChangeGL (algebraMap K L) l = S.h * x * S.h⁻¹ := by
  have hy : S.h * x * S.h⁻¹ ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem S.hh hxA) (inv_mem S.hh)
  have hF : Frob S.Fr (S.h * x * S.h⁻¹) = S.h * x * S.h⁻¹ := by
    rw [map_mul, map_mul, map_inv, S.hlang]
    calc S.h * S.n * Frob S.Fr x * (S.h * S.n)⁻¹ = S.h * (S.n * Frob S.Fr x * S.n⁻¹) * S.h⁻¹ := by
          group
      _ = S.h * x * S.h⁻¹ := by rw [hxσ]
  exact descent_E8 S.Fr S.hFr S.hbij hy hF

end Generic

section Pos2

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
  (H : Subgroup (ModGL Tag.E8 K))

theorem cL_inv_conj_pinnedX {u β : Fin Tag.E8.rank → ℤ} (hu : IsRoot Tag.E8 u) (hν : νW • u = β)
    (s : D.L) :
    (cL D)⁻¹ * pinnedX Tag.E8 D.L β s * cL D = pinnedX Tag.E8 D.L u (sgn νW u * s) := by
  obtain ⟨hsq, hc⟩ := mono_canonicalRep (L := D.L) νW u hu
  have h1 : cL D * pinnedX Tag.E8 D.L u (sgn νW u * s) * (cL D)⁻¹ =
      pinnedX Tag.E8 D.L β s := by
    have := hc (sgn νW u * s)
    rw [hν, ← mul_assoc, hsq, one_mul] at this
    exact this
  rw [← h1]
  group

theorem pair_pos2 {β₀ β₁ u₀ u₁ : Fin Tag.E8.rank → ℤ} (hu₀ : u₀ ∈ Deg1 Tag.E8)
    (hu₁ : u₁ ∈ Deg1 Tag.E8) (hν₀ : νW • u₀ = β₀) (hν₁ : νW • u₁ = β₁) (hne : u₀ ≠ u₁)
    {s d : D.L} {l : ModGL Tag.E8 K}
    (hl : baseChangeGL (algebraMap K D.L) l =
      gE D * (pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ d) * (gE D)⁻¹) :
    l ∈ Qrat (K := K) (toSetup2 D H).h ∧
      Cc (toSetup2 D H).h l = Pi.single u₀ (sgn νW u₀ * s) + Pi.single u₁ (sgn νW u₁ * d) := by
  have e : (toSetup2 D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup2 D H).h =
      pinnedX Tag.E8 D.L u₀ (sgn νW u₀ * s) * pinnedX Tag.E8 D.L u₁ (sgn νW u₁ * d) := by
    rw [hl, ← cL_inv_conj_pinnedX D (CoordAux.mem_Deg1.1 hu₀).1 hν₀,
      ← cL_inv_conj_pinnedX D (CoordAux.mem_Deg1.1 hu₁).1 hν₁]
    change (gE D * cL D)⁻¹ * (gE D * (pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ d) *
      (gE D)⁻¹) * (gE D * cL D) = _
    group
  have hQ : pinnedX Tag.E8 D.L u₀ (sgn νW u₀ * s) * pinnedX Tag.E8 D.L u₁ (sgn νW u₁ * d) ∈
      Qθ Tag.E8 D.L :=
    mul_mem (pinnedX_mem_Qθ_of_mem_Deg1 hu₀ _) (pinnedX_mem_Qθ_of_mem_Deg1 hu₁ _)
  refine ⟨?_, ?_⟩
  · show (toSetup2 D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup2 D H).h ∈ Qθ Tag.E8 D.L
    rw [e]
    exact hQ
  · unfold Cc
    rw [e, (heisCoord_spec Tag.E8 D.L).mul _ (pinnedX_mem_Qθ_of_mem_Deg1 hu₀ _) _
      (pinnedX_mem_Qθ_of_mem_Deg1 hu₁ _), (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 u₀ hu₀,
      (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 u₁ hu₁]

end Pos2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
