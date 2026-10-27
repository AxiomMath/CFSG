module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Proj

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open scoped commutatorElement MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

section Slice

variable {L : Subgroup H} {u₀ : H}

variable {F : Type} [Field F]

theorem slice_isPComponent₂ [Finite (StatedProj H)] [Finite F]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (hF2 : ringChar F ≠ 2)
    (hF : 4 ≤ Nat.card F) (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1)
    (hLu : ∀ g ∈ L, g * u₀ = u₀ * g)
    {M : Subgroup H} (hLM : L ≤ M) (hMu : ∀ g ∈ M, g * u₀ = u₀ * g)
    (hLn : ∀ m ∈ M, ∀ g ∈ L, m * g * m⁻¹ ∈ L)
    (hnorm : ∀ h : H, h * u₀ = u₀ * h → ∀ m ∈ M, h * m * h⁻¹ ∈ M) :
    IsPComponent 2 ((slice L).subgroupOf
      (B ⊓ centralizer ({conjProjH H u₀} : Set (MulAut (StatedProj H))))) := by
  set u := conjProjH H u₀ with hu
  set S := slice L with hS
  set Hc := B ⊓ centralizer ({u} : Set (MulAut (StatedProj H))) with hHc
  set Inn := (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range with hInn
  set C₁ := (centralizer ({u₀} : Set H)).map (conjProjH H) with hC₁
  have hInnN : Inn.Normal := conj_range_normal
  have hSH : S ≤ Hc := le_inf (slice_le_range.trans hB) (slice_le_centralizer hLu)
  set M₁ := M.map (conjProjH H) with hM₁
  have hSM₁ : S ≤ M₁ := map_mono hLM
  have hnS : ∀ c ∈ M₁, ∀ x ∈ S, c * x * c⁻¹ ∈ S := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨g, hg, rfl⟩
    refine ⟨m * g * m⁻¹, hLn m hm g hg, ?_⟩
    simp only [map_mul, map_inv]
  have hM₁C₁ : M₁ ≤ C₁ := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, mem_centralizer_singleton_iff.2 (hMu g hg), rfl⟩
  have hnM₁ : ∀ c ∈ C₁, ∀ x ∈ M₁, c * x * c⁻¹ ∈ M₁ := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨h * m * h⁻¹, hnorm h (mem_centralizer_singleton_iff.1 hh) m hm, ?_⟩
    simp only [map_mul, map_inv]
  have hC₁C₂ : C₁ ≤ Inn ⊓ Hc := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨_, rfl⟩, hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hu, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hh]
  have hnC₁ : ∀ c ∈ Inn ⊓ Hc, ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁ := by
    rintro c ⟨⟨y, rfl⟩, -, hcu⟩ _ ⟨h, hh, rfl⟩
    obtain ⟨h₁, rfl⟩ := projH_surjective y
    have hcu' : conjProjH H (h₁ * u₀ * h₁⁻¹) = conjProjH H u₀ := by
      have := mem_centralizer_singleton_iff.1 hcu
      change conjProjH H h₁ * conjProjH H u₀ = conjProjH H u₀ * conjProjH H h₁ at this
      rw [map_mul, map_mul, map_inv, this, mul_inv_cancel_right]
    have hz := projH_eq_projH_iff.1 (hinj hcu').symm
    set z := u₀⁻¹ * (h₁ * u₀ * h₁⁻¹) with hzdef
    have hzc : z ∈ center H := scalars_subgroupOf_le_center hz
    have e1 : h₁ * u₀ * h₁⁻¹ = u₀ * z := by rw [hzdef, mul_inv_cancel_left]
    have hhs : h * u₀ = u₀ * h := mem_centralizer_singleton_iff.1 hh
    refine ⟨h₁ * h * h₁⁻¹, mem_centralizer_singleton_iff.2 ?_, by
      simp only [map_mul, map_inv]
      rfl⟩
    set X := h₁ * h * h₁⁻¹ with hX
    have key : X * (h₁ * u₀ * h₁⁻¹) = (h₁ * u₀ * h₁⁻¹) * X := by
      calc X * (h₁ * u₀ * h₁⁻¹) = h₁ * (h * u₀) * h₁⁻¹ := by rw [hX]; group
        _ = h₁ * (u₀ * h) * h₁⁻¹ := by rw [hhs]
        _ = (h₁ * u₀ * h₁⁻¹) * X := by rw [hX]; group
    rw [e1] at key
    have hXz : X * z = z * X := mem_center_iff.1 hzc X
    apply mul_right_cancel (b := z)
    calc X * u₀ * z = X * (u₀ * z) := mul_assoc _ _ _
      _ = u₀ * z * X := key
      _ = u₀ * X * z := by rw [mul_assoc, ← hXz, ← mul_assoc]
  have hC₂ : ((Inn ⊓ Hc).subgroupOf Hc).IsSubnormal := isSubnormal_inf_subgroupOf Hc
  have hC₁s : (C₁.subgroupOf Hc).IsSubnormal :=
    isSubnormal_subgroupOf_of_normalizes hC₁C₂ hnC₁ hC₂
  have hM₁s : (M₁.subgroupOf Hc).IsSubnormal :=
    isSubnormal_subgroupOf_of_normalizes hM₁C₁ hnM₁ hC₁s
  have hSs : (S.subgroupOf Hc).IsSubnormal := isSubnormal_subgroupOf_of_normalizes hSM₁ hnS hM₁s
  have heven : Even (Nat.card S) := by
    rw [even_iff_two_dvd, ← orderOf_sliceInv hinj hLZ hF2 hu₀ e he]
    exact Subgroup.orderOf_dvd_natCard S ⟨u₀, hu₀, rfl⟩
  exact isPComponent_two_of_quasisimple hSH (isQuasisimple_slice hinj hLZ e hF) hSs heven

theorem slice_propAConclusionIn₂ [Finite (StatedProj H)] [Finite F]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (hF2 : ringChar F ≠ 2)
    (hF : 4 ≤ Nat.card F) (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1)
    (hLu : ∀ g ∈ L, g * u₀ = u₀ * g)
    {M : Subgroup H} (hLM : L ≤ M) (hMu : ∀ g ∈ M, g * u₀ = u₀ * g)
    (hLn : ∀ m ∈ M, ∀ g ∈ L, m * g * m⁻¹ ∈ L)
    (hnorm : ∀ h : H, h * u₀ = u₀ * h → ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    {t : MulAut (StatedProj H)} (ht : orderOf t = 2) {Y : Subgroup (MulAut (StatedProj H))}
    (hY : Y ≠ ⊥) (hYO : Y ≤ oddCoreIn B t)
    (htN : t ∈ normalizer (slice L : Set (MulAut (StatedProj H))))
    (htC : ∃ a ∈ slice L, t * a ≠ a * t)
    (hON : oddCoreIn B t ≤ normalizer (slice L : Set (MulAut (StatedProj H))))
    (hOC : ∀ y ∈ oddCoreIn B t, (∀ a ∈ slice L, y * a = a * y) → y = 1) :
    PropAConclusionIn B t Y := by
  obtain ⟨p, n, hp, hp2, hn, ⟨eG⟩⟩ := exists_sl_galoisField hF2
  exact propAConclusionIn_of_core ht hY hYO (hB ⟨_, rfl⟩) (orderOf_sliceInv hinj hLZ hF2 hu₀ e he)
    (slice_le_range.trans hB) (slice_le_centralizer hLu)
    (slice_isPComponent₂ hinj hB hLZ hF2 hF hu₀ e he hLu hLM hMu hLn hnorm)
    ⟨p, n, hp, hp2, hn, ⟨(sliceEquivSL hinj hLZ e).trans eG⟩⟩
    (center_slice hinj hLZ hu₀ e he) htN htC hON hOC

end Slice

end CFSG.ComponentClassification.Burgoyne.Proj
