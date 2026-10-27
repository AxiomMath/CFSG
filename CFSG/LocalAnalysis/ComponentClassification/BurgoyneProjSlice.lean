module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Proj

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open scoped commutatorElement MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem center_eq_zpowers_of_sl {F : Type} [Field F] {L : Type*} [Group L] (e : L ≃* SL(2, F))
    {u : L} (he : ((e u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) :
    center L = zpowers u := by
  apply le_antisymm
  · intro c hc
    have hc' : e c ∈ center SL(2, F) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨c, hc, rfl⟩
    obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc'
    rw [Fintype.card_fin] at hr
    have hfac : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.1 hfac with h | h
    · have h1 : c = 1 := by
        apply e.injective
        apply Subtype.ext
        rw [← hre, sub_eq_zero.1 h, map_one]
        simp
      rw [h1]
      exact one_mem _
    · have h1 : c = u := by
        apply e.injective
        apply Subtype.ext
        rw [← hre, he, eq_neg_of_add_eq_zero_left h]
        ext i j
        by_cases hij : i = j <;> simp [hij, one_apply]
      rw [h1]
      exact mem_zpowers u
  · rw [zpowers_le, mem_center_iff]
    intro g
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      he]
    simp

theorem commute_oddCoreIn_of_normal [Finite (StatedProj H)]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    {t : MulAut (StatedProj H)} (φ : H →* H) (hφ : ∀ g, t (projH H g) = projH H (φ g))
    {Q : Subgroup H} (hQF : Q ≤ MonoidHom.eqLocus φ (MonoidHom.id _))
    (hQn : ∀ f ∈ MonoidHom.eqLocus φ (MonoidHom.id _), ∀ q ∈ Q, f * q * f⁻¹ ∈ Q)
    (hq : IsQuasisimple (Q.map (conjProjH H))) {y : MulAut (StatedProj H)}
    (hy : y ∈ oddCoreIn B t) {g : H} (hg : g ∈ Q) : y (projH H g) = projH H g := by
  obtain ⟨hle, hs⟩ := isSubnormal_map_fixedH hinj hB φ hφ (F := MonoidHom.eqLocus φ
    (MonoidHom.id _)) (fun _ h => h) (fun _ hh _ hg => conj_mem_eqLocus_of_scalarH φ hh hg)
  have hQs : ((Q.map (conjProjH H)).subgroupOf
      (B ⊓ centralizer ({t} : Set (MulAut (StatedProj H))))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_normalizes (map_mono hQF) ?_ hs
    rintro _ ⟨f, hf, rfl⟩ _ ⟨q, hq', rfl⟩
    exact ⟨f * q * f⁻¹, hQn f hf q hq', by simp only [map_mul, map_inv]⟩
  have h := commute_of_mem_pPrimeCore ((map_mono hQF).trans hle) hq hQs
    (even_card_of_isQuasisimple hq) hy ⟨g, hg, rfl⟩
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProjH H g * y⁻¹ = conjProjH H g
  rw [h, mul_inv_cancel_right]

theorem isQuasisimple_map_conjProjH
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {Q : Subgroup H} (hQ : IsQuasisimple Q) : IsQuasisimple (Q.map (conjProjH H)) := by
  refine LocalCores.isQuasisimple_map hQ _ fun hker => ?_
  have hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b _
    have ha' : a ∈ (StatedScalars ι K).subgroupOf H := by
      have h1 : conjProjH H a = 1 := hker ha
      exact (QuotientGroup.eq_one_iff _).1 (hinj (by rw [map_one]; exact h1))
    exact (mem_center_iff.1 (scalars_subgroupOf_le_center ha') b).symm
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  have hcomm : commutator Q = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hab a a.2 b b.2)
  have hperf := hQ.1.commutator_eq_top
  rw [hcomm] at hperf
  exact bot_ne_top hperf

section Slice

variable {L : Subgroup H} {u₀ : H}

theorem conjProjH_injective_of_inf
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) :
    Function.Injective ((conjProjH H).comp L.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
  have h1 : projH H (g : H) = 1 := hinj (by rw [map_one]; exact hg)
  have h2 : (g : H) ∈ (StatedScalars ι K).subgroupOf H := (QuotientGroup.eq_one_iff _).1 h1
  rw [mem_bot]
  exact Subtype.ext (hLZ g g.2 h2)

variable (L) in
abbrev slice : Subgroup (MulAut (StatedProj H)) := L.map (conjProjH H)

@[expose] def sliceEquiv
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) : L ≃* slice L :=
  (MonoidHom.ofInjective (conjProjH_injective_of_inf hinj hLZ)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))

theorem coe_sliceEquiv
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (g : L) :
    ((sliceEquiv hinj hLZ g : slice L) : MulAut (StatedProj H)) = conjProjH H g :=
  rfl

theorem slice_le_range :
    slice L ≤ (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨_, rfl⟩

theorem slice_le_centralizer (hLu : ∀ g ∈ L, g * u₀ = u₀ * g) :
    slice L ≤ centralizer ({conjProjH H u₀} : Set (MulAut (StatedProj H))) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hLu g hg]

variable {F : Type} [Field F]

theorem mul_self_eq_one_of_sl (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) : u₀ * u₀ = 1 := by
  have h : (⟨u₀, hu₀⟩ : L) * ⟨u₀, hu₀⟩ = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, he, map_one,
      Matrix.SpecialLinearGroup.coe_one]
    simp
  exact congrArg Subtype.val h

theorem orderOf_sliceInv
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (hF2 : ringChar F ≠ 2)
    (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) :
    orderOf (conjProjH H u₀) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, ← map_mul, mul_self_eq_one_of_sl hu₀ e he, map_one]
  · intro h1
    have h3 : (⟨u₀, hu₀⟩ : L) = 1 :=
      conjProjH_injective_of_inf hinj hLZ (by rw [MonoidHom.comp_apply, map_one]; exact h1)
    have h4 := congrArg (fun x : L => ((e x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0) h3
    simp only [he, map_one, Matrix.SpecialLinearGroup.coe_one] at h4
    have h5 : (2 : F) = 0 := by
      have : (-1 : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by simp
      rw [this, one_apply_eq] at h4
      linear_combination -h4
    exact Ring.two_ne_zero hF2 h5

theorem center_slice
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1)
    (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) :
    (center (slice L)).map (slice L).subtype = zpowers (conjProjH H u₀) := by
  rw [← Subgroup.map_center_eq (sliceEquiv hinj hLZ), center_eq_zpowers_of_sl e he,
    Subgroup.map_map, MonoidHom.map_zpowers]
  rfl

@[expose] def sliceEquivSL
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (e : L ≃* SL(2, F)) :
    slice L ≃* SL(2, F) :=
  (sliceEquiv hinj hLZ).symm.trans e

theorem isQuasisimple_slice [Finite F]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (e : L ≃* SL(2, F))
    (hF : 4 ≤ Nat.card F) : IsQuasisimple (slice L) :=
  LocalCores.isQuasisimple_of_mulEquiv (sliceEquivSL hinj hLZ e).symm
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr (by omega))
      (Or.inr (by omega)))

theorem slice_isPComponent [Finite (StatedProj H)] [Finite F]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (hF2 : ringChar F ≠ 2)
    (hF : 4 ≤ Nat.card F) (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1)
    (hLu : ∀ g ∈ L, g * u₀ = u₀ * g)
    (hnorm : ∀ h : H, h * u₀ = u₀ * h → ∀ g ∈ L, h * g * h⁻¹ ∈ L) :
    IsPComponent 2 ((slice L).subgroupOf
      (B ⊓ centralizer ({conjProjH H u₀} : Set (MulAut (StatedProj H))))) := by
  set u := conjProjH H u₀ with hu
  set S := slice L with hS
  set Hc := B ⊓ centralizer ({u} : Set (MulAut (StatedProj H))) with hHc
  set Inn := (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range with hInn
  set C₁ := (centralizer ({u₀} : Set H)).map (conjProjH H) with hC₁
  have hInnN : Inn.Normal := conj_range_normal
  have hSH : S ≤ Hc := le_inf (slice_le_range.trans hB) (slice_le_centralizer hLu)
  have hSC₁ : S ≤ C₁ := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, mem_centralizer_singleton_iff.2 (hLu g hg), rfl⟩
  have hnS : ∀ c ∈ C₁, ∀ x ∈ S, c * x * c⁻¹ ∈ S := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨g, hg, rfl⟩
    refine ⟨h * g * h⁻¹, hnorm h (mem_centralizer_singleton_iff.1 hh) g hg, ?_⟩
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
  have hSs : (S.subgroupOf Hc).IsSubnormal := isSubnormal_subgroupOf_of_normalizes hSC₁ hnS hC₁s
  have heven : Even (Nat.card S) := by
    rw [even_iff_two_dvd, ← orderOf_sliceInv hinj hLZ hF2 hu₀ e he]
    exact Subgroup.orderOf_dvd_natCard S ⟨u₀, hu₀, rfl⟩
  exact isPComponent_two_of_quasisimple hSH (isQuasisimple_slice hinj hLZ e hF) hSs heven

theorem slice_propAConclusionIn [Finite (StatedProj H)] [Finite F]
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {B : Subgroup (MulAut (StatedProj H))}
    (hB : (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range ≤ B)
    (hLZ : ∀ g ∈ L, g ∈ (StatedScalars ι K).subgroupOf H → g = 1) (hF2 : ringChar F ≠ 2)
    (hF : 4 ≤ Nat.card F) (hu₀ : u₀ ∈ L) (e : L ≃* SL(2, F))
    (he : ((e ⟨u₀, hu₀⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1)
    (hLu : ∀ g ∈ L, g * u₀ = u₀ * g)
    (hnorm : ∀ h : H, h * u₀ = u₀ * h → ∀ g ∈ L, h * g * h⁻¹ ∈ L)
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
    (slice_isPComponent hinj hB hLZ hF2 hF hu₀ e he hLu hnorm)
    ⟨p, n, hp, hp2, hn, ⟨(sliceEquivSL hinj hLZ e).trans eG⟩⟩
    (center_slice hinj hLZ hu₀ e he) htN htC hON hOC

end Slice

end CFSG.ComponentClassification.Burgoyne.Proj
