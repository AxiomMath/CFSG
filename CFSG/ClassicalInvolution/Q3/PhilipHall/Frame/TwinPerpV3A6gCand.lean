module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gVert
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gCandAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gLside
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE



local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_inv vq_empty E8Pkg A6eCtx zBar_eq_vq ae6E_le_ae6D)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6M₀ ae6Vertex_of_ident AE6Vertex ae6_exists_r ae6_card8 ae6_mem_DSet ae6_conj_of_mem_DSet le_ae6L
    AE6ModelPar ae6Img mem_ae6Img ae6Img_mono ae6Img_le_iff ae6Img_inj card_ae6Img)
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

structure Cand (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y) (K : Subgroup Y) (t τ x : Y)
    (Lj A : Subgroup Y) : Prop where
  le_I : Lj ≤ ae6I Ω W u
  M_le : MGrp Ω W ≤ Lj
  gen : Lj ≤ pSpan (ae6ConjIn Lj K)
  elem : IsElemAbelian2 A 6
  E3_le : Subgroup.closure ({t, τ, x} : Set Y) ≤ A
  A_le_L : A ≤ ae6L Ω t τ x
  L_norm : ae6L Ω t τ x ≤ Subgroup.normalizer (A : Set Y)
  Lj_norm : Lj ≤ Subgroup.normalizer (A : Set Y)
  Lj_eq : ∀ g ∈ ae6I Ω W u, g ∈ Subgroup.normalizer (A : Set Y) → g ∈ Lj
  far : ∃ g ∈ Lj, g * t * g⁻¹ ∉ Subgroup.closure ({t, τ, x} : Set Y)
  A_le : A ≤ Lj

theorem t_tau_mem_D (hD : V3AE6D n) (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    t ∈ ae6D Ω[R] W (u₁ * u₂) ∧ y * t * y⁻¹ ∈ ae6D Ω[R] W (u₁ * u₂) := by
  obtain ⟨-, -, htE, hτE, -⟩ := hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  exact ⟨ae6E_le_ae6D _ _ _ htE, ae6E_le_ae6D _ _ _ hτE⟩

theorem cand_of_goodPair (hD : V3AE6D n) (hE3 : V3AE6E3 n) (hL : V3AE6L n) (hPar : AE6ModelPar)
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h)
    (SD : SData (ae6I Ω[R] W (u₁ * u₂)) (ae6D Ω[R] W (u₁ * u₂))
      (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹))
    {X E : Subgroup (AEQ 8)} (hG : GoodPair X E (SD.pkg.ph (h * (y * t * y⁻¹) * h⁻¹))) :
    Cand Ω[R] W (u₁ * u₂) K t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) (preim SD.pkg X)
      (preim SD.pkg E) := by
  have hd := H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨htD, hτD⟩ := t_tau_mem_D hD H fr
  have hDI : ae6D Ω[R] W (u₁ * u₂) ≤ ae6I Ω[R] W (u₁ * u₂) := A6d.ae6D_le_ae6I Ω[R] W (u₁ * u₂)
  have htI := hDI htD
  have hτI := hDI hτD
  have hxI := SD.hxI
  have v := vertex_I H fr hPar SD.A SD.hspan SD.hker
  have hM₀X := ae6M₀_le_preim SD htI hτI hG.X_le hG.six_le
  have hMX : MGrp Ω[R] W ≤ preim SD.pkg X := (M_le_M₀ H fr).trans hM₀X
  have hcardX : Nat.card (preim SD.pkg X) = 86016 := (card_preim SD.pkg hG.X_le).trans hG.card_X
  have hEle : E ≤ aeBar8 := hG.E_le.trans hG.X_le
  have hElem := isElemAbelian2_preim SD.pkg hEle hG.E_sq hG.card_E
  have hAX : preim SD.pkg E ≤ preim SD.pkg X := preim_mono SD.pkg hG.E_le
  have hNorm := preim_le_normalizer SD.pkg hG.E_norm
  have hA2 := isPGroup_preim SD.pkg hEle hG.E_sq hG.card_E
  have hcard7 : Nat.card (preim SD.pkg X) =
      7 * Nat.card (ae6M₀ (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹)) := by
    rw [hcardX, v.card]
  have hAM₀ := le_of_normal_isPGroup_index_seven hM₀X hAX hNorm hA2 hcard7
  have hAL : preim SD.pkg E ≤ ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) :=
    hAM₀.trans (M₀_le_L H fr _)
  have hE3A : Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) ≤
      preim SD.pkg E := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · refine mem_preim_of_mem SD.pkg htI ?_
      rw [← SD.pkg.ph_of_mem htI, SD.ph_t]
      exact hG.α_mem
    · refine mem_preim_of_mem SD.pkg hτI ?_
      rw [← SD.pkg.ph_of_mem hτI, SD.ph_τ]
      exact hG.β_mem
    · refine mem_preim_of_mem SD.pkg hxI ?_
      rw [← SD.pkg.ph_of_mem hxI]
      exact hG.y_mem
  obtain ⟨hLnorm, -, hLspan, B, hBker⟩ :=
    hL Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  obtain ⟨hE3el, -⟩ := hE3 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hnorm : ∀ l ∈ ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹), ∀ e ∈
      Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y),
      l * e * l⁻¹ ∈ Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) :=
    fun l hl e he => (Subgroup.mem_normalizer_iff.mp (hLnorm hl) e).mp he
  have h8 : ∀ J ∈ ae6ConjIn (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) K,
      Nat.card J = 8 := by
    rintro J ⟨g, -, rfl⟩
    exact ae6_card8 H _ (hinv g K hd.mem)
  have htE3 : t ∈ Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hLn := lside_normal (B := B) (hspan := hLspan) hBker h8 hd.hz hnorm htE3 hE3A hAL hElem
  refine ⟨preim_le_I SD.pkg X, hMX, ?_, hElem, hE3A, hAL, ?_, hNorm, ?_, ?_, hAX⟩
  ·
    refine gen_preim SD v hG.X_le hG.card_X hG.gen hM₀X ⟨1, (ae6I Ω[R] W (u₁ * u₂)).one_mem, conjSub_one K⟩ ?_
    exact le_iSup₂_of_le K ⟨⟨1, (ae6I Ω[R] W (u₁ * u₂)).one_mem, conjSub_one K⟩, Or.inl hd.hz⟩ le_rfl
  ·
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hLn l hl q hq, fun hq => ?_⟩
    have := hLn l⁻¹ ((ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)).inv_mem hl) _ hq
    simpa [mul_assoc] using this
  ·
    intro g hg hgn
    exact mem_preim_of_normalizes SD.pkg hG.X_le hG.E_le hG.norm_le hg hgn
  ·
    obtain ⟨g₀, hg₀X, hfar⟩ := hG.far
    have hg₀ : g₀ ∈ SD.pkg.φ.range := SD.pkg.range_eq ▸ hG.X_le hg₀X
    obtain ⟨⟨g, hgI⟩, rfl⟩ := hg₀
    refine ⟨g, mem_preim_of_mem SD.pkg hgI hg₀X, fun hmem => ?_⟩
    have hz'D : g * t * g⁻¹ ∈ ae6D Ω[R] W (u₁ * u₂) := SD.pkg.conj_mem_D hgI htD
    have hxD := hx.2.1
    have hne := A6Hx.tau_ne_t H fr
    have ht1 : t ≠ 1 := hd.hz.ne_one
    have hτ1 : y * t * y⁻¹ ≠ 1 := fun e => ht1 (by
      have := congrArg (fun z => y⁻¹ * z * y) e
      simpa [mul_assoc] using this)
    have hxE : h * (y * t * y⁻¹) * h⁻¹ ∈
        Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) :=
      Subgroup.subset_closure (by simp)
    have hτE : y * t * y⁻¹ ∈
        Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) :=
      Subgroup.subset_closure (by simp)
    have h4 := inf_E3_D hE3el hxE htD hτD htE3 hτE hxD hne ht1 hτ1 hd.hz.sq _ ⟨hmem, hz'D⟩
    apply hfar
    have e : SD.pkg.φ ⟨g, hgI⟩ * vq α₀ * (SD.pkg.φ ⟨g, hgI⟩)⁻¹ = SD.pkg.ph (g * t * g⁻¹) := by
      rw [SD.pkg.ph_conj hgI htI, SD.pkg.ph_of_mem hgI]
      have e1 : SD.pkg.ph t = vq α₀ := SD.ph_t
      rw [e1]
    rw [e]
    have e1 : SD.pkg.ph t = vq α₀ := SD.ph_t
    have e2 : SD.pkg.ph (y * t * y⁻¹) = vq β₀ := SD.ph_τ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h4 with h5 | h5 | h5 | h5
    · exact Or.inl (by rw [h5, SD.pkg.ph_one])
    · exact Or.inr (Or.inl (by rw [h5, e1]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h5, e2])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h5, SD.pkg.ph_mul htI hτI, e1, e2])))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
