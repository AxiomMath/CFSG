module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Label

variable {Y : Type} [Group Y] [Finite Y] {Ω P : Set (Subgroup Y)}

theorem false_of_same_four_set_label {n : ℕ} (hn : 5 ≤ n) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hPΩ : P ⊆ Ω) (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker)
    {α : Finset (Fin n)} {h : α.card = 4} {A₁ A₂ A₃ A₄ : Subgroup Y} {b₁ b₂ b₃ b₄ : Bool}
    (m₁ : A₁ ∈ P) (m₂ : A₂ ∈ P) (m₃ : A₃ ∈ P) (m₄ : A₄ ∈ P)
    (hl₁ : (A₁.subgroupOf (pSpan P)).map J.φ = memBar α h b₁)
    (hl₂ : (A₂.subgroupOf (pSpan P)).map J.φ = memBar α h b₂)
    (hl₃ : (A₃.subgroupOf (pSpan P)).map J.φ = memBar α h b₃)
    (hl₄ : (A₄.subgroupOf (pSpan P)).map J.φ = memBar α h b₄)
    (ne₁₂ : A₁ ≠ A₂) (ne₁₃ : A₁ ≠ A₃) (ne₁₄ : A₁ ≠ A₄) (ne₂₃ : A₂ ≠ A₃) (ne₂₄ : A₂ ≠ A₄)
    (ne₃₄ : A₃ ≠ A₄) : False := by
  have key : ∀ {B C : Subgroup Y} (hB : B ∈ P) (hC : C ∈ P) {b c : Bool},
      (B.subgroupOf (pSpan P)).map J.φ = memBar α h b →
      (C.subgroupOf (pSpan P)).map J.φ = memBar α h c → b = c → B = C := by
    intro B C hB hC b c hb hc hbc
    subst hbc
    exact TL4.eq_of_map_le_memBar hΩ h2 hn J.φ hk (hPΩ hB) (hPΩ hC) (le_pSpan hB) (le_pSpan hC) hb
      (hb.trans hc.symm).le
  rcases A6d.bool_four b₁ b₂ b₃ b₄ with h' | h' | h' | h' | h' | h'
  · exact ne₁₂ (key m₁ m₂ hl₁ hl₂ h')
  · exact ne₁₃ (key m₁ m₃ hl₁ hl₃ h')
  · exact ne₁₄ (key m₁ m₄ hl₁ hl₄ h')
  · exact ne₂₃ (key m₂ m₃ hl₂ hl₃ h')
  · exact ne₂₄ (key m₂ m₄ hl₂ hl₄ h')
  · exact ne₃₄ (key m₃ m₄ hl₃ hl₄ h')

theorem false_of_four_twins_label {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hPΩ : P ⊆ Ω)
    (J : AELabel P n) (hk : IsPGroup 2 J.φ.ker) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : A6d.FourTwins P z A₁ A₂ A₃ A₄) : False := by
  obtain ⟨α₁, h₁, b₁, hl₁⟩ := J.label A₁ F.m₁
  obtain ⟨α₂, h₂', b₂, hl₂⟩ := J.label A₂ F.m₂
  obtain ⟨α₃, h₃, b₃, hl₃⟩ := J.label A₃ F.m₃
  obtain ⟨α₄, h₄, b₄, hl₄⟩ := J.label A₄ F.m₄
  have e₁ := phi_map_eq_zBar J.φ hn F.m₁ (h8 _ (hPΩ F.m₁)) hl₁ F.z₁
  have e₂ := phi_map_eq_zBar J.φ hn F.m₂ (h8 _ (hPΩ F.m₂)) hl₂ F.z₂
  have e₃ := phi_map_eq_zBar J.φ hn F.m₃ (h8 _ (hPΩ F.m₃)) hl₃ F.z₃
  have e₄ := phi_map_eq_zBar J.φ hn F.m₄ (h8 _ (hPΩ F.m₄)) hl₄ F.z₄
  have a₂ : α₂ = α₁ := AE.eq_of_zBar_eq hn8 (e₂.symm.trans e₁)
  have a₃ : α₃ = α₁ := AE.eq_of_zBar_eq hn8 (e₃.symm.trans e₁)
  have a₄ : α₄ = α₁ := AE.eq_of_zBar_eq hn8 (e₄.symm.trans e₁)
  subst a₂ a₃ a₄
  exact false_of_same_four_set_label hn hΩ h2 hPΩ J hk F.m₁ F.m₂ F.m₃ F.m₄ hl₁ hl₂ hl₃ hl₄ F.ne₁₂
    F.ne₁₃ F.ne₁₄ F.ne₂₃ F.ne₂₄ F.ne₃₄

end Label

section Eight

@[expose] def qs : Fin 8 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1, 2, 6}, {0, 1, 2, 7}, {0, 1, 3, 4}, {0, 1, 3, 5},
    {0, 1, 3, 6}]

theorem qs_card : ∀ i, (qs i).card = 4 := by decide +kernel

theorem qs_zero : ∀ i, (0 : Fin 8) ∈ qs i := by decide +kernel

theorem qs_inj : ∀ i j, qs i = qs j → i = j := by decide +kernel

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem false_of_aeIdent8 (I : AEIdent (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K) 8) : False := by
  have hd := Z.C.H.ex.1.datum
  have hΩ := A6d.hypOf Z.C.H
  have h8 := A6d.h8Of Z.C.H
  set L := ae6L Ω[R] t (tauE t y) (xE t y h) with hLdef
  set P := ae6ConjIn L K with hPdef
  have hPΩ : P ⊆ Ω[R] := A6d.ae6ConjIn_subset hΩ.conjInvariant hd.mem
  choose J hJP hJlab using fun i => I.label_surj (qs i) (qs_card i) true
  choose u hu using fun i => (hΩ.omega1 (J i) (hPΩ (hJP i))).1
  have hmemE : ∀ i, u i ∈ e3 t y h := by
    intro i
    obtain ⟨g, hg, hgJ⟩ := hJP i
    have h1 : IsUniqueInvolution (conjSub g K) (g * t * g⁻¹) := hd.hz.conj g
    rw [hgJ] at h1
    have hug : u i = g * t * g⁻¹ := (hu i).eq h1
    rw [hug]
    exact (Subgroup.mem_normalizer_iff.mp (L_le_normalizer Z hg) t).mp (t_mem_e3 t y h)
  have hφu : ∀ i, I.φ ⟨u i, le_pSpan (hJP i) (hu i).mem⟩ = zBar (qs i) (qs_card i) := fun i =>
    I.map_eq_zBar (by norm_num) (hJP i) (h8 _ (hPΩ (hJP i))) (hJlab i) (hu i)
  have hinj : Function.Injective u := by
    intro i j hij
    have e : zBar (qs i) (qs_card i) = zBar (qs j) (qs_card j) := by
      rw [← hφu i, ← hφu j]
      exact congrArg I.φ (Subtype.ext hij)
    rcases A6d.zBar_eq_cases e with e | e
    · exact qs_inj i j e
    · exact absurd ((e 0).mp (qs_zero i)) (not_not.mpr (qs_zero j))
  let g : Fin 8 → ↥(e3 t y h) := fun i => ⟨u i, hmemE i⟩
  have hginj : Function.Injective g := fun i j e => hinj (congrArg Subtype.val e)
  have hc : Nat.card ↥(e3 t y h) = 8 := by rw [Z.hE.1]; norm_num
  have hbij := Function.Injective.bijective_of_nat_card_le hginj (by rw [hc]; simp)
  obtain ⟨i, hi⟩ := hbij.2 1
  exact (hu i).ne_one (congrArg Subtype.val hi)

end Eight

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
