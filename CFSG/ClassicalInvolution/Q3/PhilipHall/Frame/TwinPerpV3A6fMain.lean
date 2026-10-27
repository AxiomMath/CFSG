module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fE3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fOut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fKer

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

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem fourTwins_KL :
    A6d.FourTwins (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K) t K K' K₃ K₄ := by
  have F₀ := A6d.fourTwins_of Z.C.H
  have mem : ∀ {J : Subgroup Y}, J ∈ ae6Vc Ω[R] t →
      J ∈ ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K := fun hJ =>
    mem_KL_of_inv_mem_E3 Z hJ.1 hJ.2 (t_mem_e3 t y h)
  have hK'v : K' ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inl rfl))
  have hK₃v : K₃ ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hK₄v : K₄ ∈ ae6Vc Ω[R] t := (mem_ae6Vc_iff Z.C).mpr (Or.inr (Or.inr (Or.inr rfl)))
  exact ⟨A6d.mem_ae6ConjIn_self, mem hK'v, mem hK₃v, mem hK₄v, F₀.z₁, F₀.z₂, F₀.z₃, F₀.z₄, F₀.ne₁₂,
    F₀.ne₁₃, F₀.ne₁₄, F₀.ne₂₃, F₀.ne₂₄, F₀.ne₃₄⟩

end Datum

theorem v3AE6L_of {n : ℕ} (hP : TL4.TightBelowRPlus 3 n)
    (hC : V3AE6EComm n) (hDN : V3AE6DNorm n) (hI : V3AE6I n) (hE3 : V3AE6E3 n) : V3AE6L n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hE : V3AE6E n := A6b.v3AE6E_proved
  have hD : V3AE6D n := v3AE6D_of hE hC
  obtain ⟨C⟩ := nonempty_ctx hD hDN hI H fr
  obtain ⟨hab, hEt, hEτ, hEx⟩ := hE3 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  let Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h := ⟨C, hx, hab, hEt, hEτ, hEx⟩
  refine ⟨L_le_normalizer Z, L_lt_top Z, pSpan_KL Z, ?_⟩
  have hd := H.ex.1.datum
  have hΩ := A6d.hypOf H
  have h2 := A6d.h2Of H
  have h8 := A6d.h8Of H
  have hA := A6d.aEmptyOf H
  have hcard : ∀ J ∈ Ω[R], Nat.card J = 2 ^ 3 := fun J hJ => (h8 J hJ).trans (by norm_num)
  have F := fourTwins_KL Z
  have hlt0 := L_lt_top Z
  have hspan := pSpan_KL Z
  have hodd := odd_pSpan_KL Z
  have hE₃L := E3_le_L Z
  have hLN := L_le_normalizer Z
  have hKL := fun {J : Subgroup Y} {u : Y} (hJ : J ∈ ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K)
    (hu : IsUniqueInvolution J u) => inv_mem_e3_of_mem_KL Z hJ hu
  have hker := ker_eq_bot_e29 Z
  have hfalse8 := false_of_aeIdent8 Z
  have hW := fun {W₀ : Subgroup Y} => false_of_wIn_eq Z (W₀ := W₀)
  revert F hodd hspan hKL hker hfalse8 hW
  set L := ae6L Ω[R] t (tauE t y) (xE t y h) with hLdef
  set P := ae6ConjIn L K with hPdef
  intro F hspan hodd hKL hker hfalse8 hW
  have hPΩ : P ⊆ Ω[R] := A6d.ae6ConjIn_subset hΩ.conjInvariant hd.mem
  have hinv : ∀ L' ∈ P, ∀ x ∈ pSpan P, conjSub x L' ∈ P := fun L' hL' x hx' =>
    A6d.conjSub_mem_of_mem_ae6ConjIn (by rw [hspan] at hx'; exact hx') hL'
  have htrans : ∀ L' ∈ P, ∀ L'' ∈ P, ∃ x ∈ pSpan P, conjSub x L' = L'' := by
    intro L' hL' L'' hL''
    obtain ⟨x, hx', hxe⟩ := A6d.exists_conj_of_mem_ae6ConjIn hL' hL''
    exact ⟨x, by rw [hspan]; exact hx', hxe⟩
  have he2 : ∀ L' ∈ P, ∀ u : Y, IsUniqueInvolution L' u → ∃ Q : Subgroup Y, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    intro L' hL' u hu
    refine ⟨e3 t y h, by rw [hspan]; exact hE₃L, ?_, A6d.isPGroup_two_of_sq_eq_one Z.hE.2,
      hKL hL' hu⟩
    intro x hx' q hq
    rw [hspan] at hx'
    exact (Subgroup.mem_normalizer_iff.mp (hLN hx') q).mp hq
  have hlt : Nat.card ↥(pSpan P) < n := by
    rw [hspan, ← H.ex.1.perp.core.card]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
      (ne_of_lt hlt0) ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have hDabs : ThmDAbsAt 3 ↥(pSpan P) := hP.thmD.d2 _ hlt
  rcases thmDGen_at hΩ h2 hcard hA hPΩ hDabs htrans hinv hodd he2 with
    hsing | ⟨W₀, hW₀⟩ | ⟨E, hE'⟩ | hI64 | ⟨m, hm5, hIm⟩ | hI29
  · exact absurd (hsing K F.m₁ K' F.m₂) F.ne₁₂
  · exact (hW hW₀).elim
  ·
    have hS : SecHyp 3 Ω[R] P := ⟨hΩ, h2, hcard, hA, hPΩ, hinv, htrans, hodd, he2⟩
    have hΦ := hS.thmDHyp
    have hE'' := hE'.toTop
    have hmem : ∀ {A : Subgroup Y}, A ∈ P →
        A.subgroupOf (pSpan P) ∈ restrictFamily P (pSpan P) :=
      fun hA' => ⟨_, hA', le_pSpan hA', rfl⟩
    have heq := eq_of_inv_e8 hΦ hE'' (hmem F.m₁) (hmem F.m₂)
      (isUniqueInvolution_subgroupOf F.z₁ (le_pSpan F.m₁))
      (isUniqueInvolution_subgroupOf F.z₂ (le_pSpan F.m₂))
    have h12 := Subgroup.subgroupOf_inj.mp heq
    rw [inf_eq_left.mpr (le_pSpan F.m₁), inf_eq_left.mpr (le_pSpan F.m₂)] at h12
    exact absurd h12 F.ne₁₂
  ·
    obtain ⟨I⟩ := hI64
    exact (false_of_four_twins_label (by norm_num) (by norm_num) hΩ h2 h8 hPΩ I.toLabel
      (I.toLabel.isPGroup_ker hodd) F).elim
  · obtain ⟨I⟩ := hIm
    by_cases hm8 : m = 8
    · subst hm8
      exact (hfalse8 I).elim
    · exact (A6d.false_of_four_twins hm5 hm8 hΩ h2 h8 hPΩ I (I.isPGroup_ker hodd) F).elim
  · obtain ⟨I⟩ := hI29
    exact ⟨I, hker I⟩

theorem v3AE6L_of_parts {n : ℕ} (hP : TL4.TightBelowRPlus 3 n)
    (hC : V3AE6EComm n) (hDN : V3AE6DNorm n) (hI : V3AE6I n) : V3AE6L n :=
  v3AE6L_of hP hC hDN hI (v3AE6E3_of hC hDN hI)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
