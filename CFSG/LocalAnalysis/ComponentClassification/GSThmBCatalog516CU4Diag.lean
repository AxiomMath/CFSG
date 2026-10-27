module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CU4Tools
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUd
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open CFSG.ComponentClassification.CatFactsL4U4 InvClassU

variable {Y : Type} [Group Y] [Finite Y] {p f : ℕ} {K : Type} [Field K]
  (hZ : Nat.card (center Y) = 2) (hp : p.Prime) (hp2 : p ≠ 2) (h : UnitaryFieldData p f K)
  (e : Y ⧸ center Y ≃* hypPSU h 2 0) (α : MulAut Y) {A : GL (HypIndex 2 0) K}
  (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
  (hA : A ∈ hypUnitary h 2 0)
  (hα' : MulAut.congr e (barAut α) = semilinearAutHom h one_le_two zero_le_one ⟨_, hx⟩)

omit [Finite Y] in
include hα' in
theorem fixed_of_commA {G : Type*} [Group G] (ψ : G →* hypSU h 2 0)
    (hψ : ∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (g : G) :
    barAut α ((e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) g) =
      (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) g :=
  barAut_fixed_of_congr e α hα' (fixed_of_comm h (by norm_num) (by norm_num) hx ψ hψ _ ⟨g, rfl⟩)

theorem mod_four_of_odd (hp2 : p ≠ 2) (hp : p.Prime) : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  omega

include hZ hp hp2 hA hα' in
theorem diagU_t2 {l : K} {v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => l) (fun _ => -l) i • v i) :
    Concl516 Y α (p ^ f) := by
  have := h.finite
  obtain ⟨ψ, hψ1, hψA⟩ := exists_t2Hom h hp2 hA hv hAv
  obtain ⟨hx4, hw2, hxw, hne⟩ := t2_z4z2 h hp2 (ρ := (hypProj h 2 0).comp ψ) hψ1
  obtain ⟨B, hBM, hBab, hB8, hBinv⟩ := z4z2_of_iso e.symm
    (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) rfl rfl hx4 hw2 hxw hne
  exact concl516_abelian hZ α _ (fixed_of_commA h e α hx hα' ψ hψA)
    (hgood_SL2SL2 hp hp2 h.card_fixedField) hBM hBab hB8 hBinv

include hZ hp hp2 hA hα' in
theorem diagU_D1 {d : K} (hd : h.norm d = 1) {v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => d) (fun _ => -d) i • v i) :
    Concl516 Y α (p ^ f) := by
  have := h.finite
  obtain ⟨ψ, hψ1, hψA⟩ := exists_D1Hom h hA hv hAv
  have hperf := perfect_SU3 h hp2
  have hfix := fixed_of_commA h e α hx hα' ψ hψA
  rcases mod_four_of_odd hp2 hp with hq | hq
  · have hout := outer_of_congr e α hα' (not_inner_D1 h hx hA hp2 hq hd hv hAv)
    have hw := D1_involution h (ρ := (hypProj h 2 0).comp ψ) hψ1 hp2
    have h2d := two_dvd_range (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) (x := wD1 h)
      (by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hw)
      (dvd_refl 2)
    exact concl516_outer hZ α _ hfix (Or.inl hperf) hout
      (four_dvd_card_of_perfect (range_perfect _) h2d)
  · obtain ⟨i, hi, hiN⟩ := exists_sqrt_neg_one_norm_one h hq
    obtain ⟨hx4, hw2, hxw, hne⟩ := D1_z4z2 h (ρ := (hypProj h 2 0).comp ψ) hψ1 hp2 hi hiN
    obtain ⟨B, hBM, hBab, hB8, hBinv⟩ := z4z2_of_iso e.symm
      (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) rfl rfl hx4 hw2 hxw hne
    exact concl516_abelian hZ α _ hfix (Or.inl hperf) hBM hBab hB8 hBinv

include hZ hp hp2 hA hα' in
theorem diagU_pair [Group.IsPerfect Y]
    (hcov : p ^ f % 4 = 1 → ∃ σ : hypSU h 2 0 →* Y, Function.Injective σ ∧
      ∀ g, piZ (σ g) = e.symm (hypProj h 2 0 g))
    {l : K} (hl : h.norm l = -1) {e' g' : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e' i = l • e' i)
    (hAg : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g' i = (-l) • g' i)
    (hee : ∀ i j, hypForm h 2 0 (e' i) (e' j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g' i) (g' j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e' i) (g' j) = if i = j then 1 else 0) :
    Concl516 Y α (p ^ f) := by
  have := h.finite
  obtain ⟨ψ, hψs, hψA⟩ := exists_pairFrameHom h hA hAe hAg hee hgg heg
  have hψ1 : ∀ x, hypProj h 2 0 (ψ x) = 1 ↔ ∃ c : K, pairHom h x = c • 1 := fun x =>
    (hypProj_eq_one_iff h (ψ x)).trans (exists_congr fun c => hψs x c)
  have hperf := perfect_SL2_sq h hp2
  have hfix := fixed_of_commA h e α hx hα' ψ hψA
  rcases mod_four_of_odd hp2 hp with hq | hq
  · obtain ⟨σ', hσ'i, hσ'⟩ := hcov hq
    have hψ0 : ((ψ (slQuatI K ^ 2) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (-1 : K) • 1 :=
      (hψs _ _).mpr (pairHom_sq_quatI h)
    have hcen : σ' (ψ (slQuatI K ^ 2)) ∈ center Y := by
      have h1 : piZ (σ' (ψ (slQuatI K ^ 2))) = 1 := by
        rw [hσ', (hypProj_eq_one_iff h _).mpr ⟨-1, hψ0⟩, map_one]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hne : σ' (ψ (slQuatI K ^ 2)) ≠ 1 := by
      intro h1
      rw [← map_one σ'] at h1
      have h2 := congrArg (fun g : hypSU h 2 0 => ((g : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) (Sum.inl 0) (Sum.inl 0)) (hσ'i h1)
      simp only [hψ0, OneMemClass.coe_one, Units.val_one, Matrix.smul_apply, one_apply_eq,
        smul_eq_mul, mul_one] at h2
      exact two_ne_zero_of_odd h hp2 (by linear_combination -h2)
    exact concl516_center hZ α _ hfix (Or.inl hperf) (σ'.comp ψ) (fun g => hσ' (ψ g))
      (slQuatI K ^ 2) hcen hne
  · have hout := outer_of_congr e α hα' (not_inner_pair h hx hA hp2 hq hl hAe hAg hee hgg heg)
    have hw := pair_involution h (ρ := (hypProj h 2 0).comp ψ) hψ1
    have h2d := two_dvd_range (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ))
      (x := slQuatI K)
      (by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hw)
      (dvd_refl 2)
    exact concl516_outer hZ α _ hfix (Or.inl hperf) hout
      (four_dvd_card_of_perfect (range_perfect _) h2d)

end CFSG.ComponentClassification.GSThmB.Cent516
