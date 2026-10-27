module

public import CFSG.LieType.SpecialLinear.TypeLabel.Basic
public import CFSG.LieType.SpecialLinear.TypeLabel.Period
public import CFSG.RepresentationTheory.FixedBaseChange
public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.SpecialLinear
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups TensorProduct

noncomputable section

theorem chi_mem_range_of_isCoverType_extendScalars (m : ℕ) {F : Type} [Field F] [Fintype F]
    [CharP F 2] {E : Type} [Field E] [Finite E] {k : Type} [Field k] [CharP k 2] [Algebra E k]
    [Algebra F k] {X : Type} [AddCommGroup X] [Module E X] [FiniteDimensional E X]
    (σ : Representation E (SpecialLinearGroup (Fin (m + 1)) F) X)
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) (CFSG.Theory.Representation.extendScalars k σ) y χ J) :
    ∀ g ∈ (curtisDatum m F 2).H, ∃ c : E, χ g = algebraMap E k c := by
  classical
  let G := SpecialLinearGroup (Fin (m + 1)) F
  let D := curtisDatum m F 2
  let Cc := (coverId m F 2).datum
  let W := CFSG.Theory.Representation.extendScalars k σ
  let C : Submodule E X := fixSub σ Cc.U
  let CW : Submodule k (k ⊗[E] X) := fixSub W Cc.U
  have : Finite ((RootSystem.coxeterMatrix (isFiniteType_A m)).Group) :=
    Finite.of_equiv (Equiv.Perm (Fin (m + 1))) (CFSG.StandardType.typeAWeylEquiv m).toEquiv
  have hsplit : SplitOver k (D.H.comap (MonoidHom.id G)) := splitOver m F 2 k
  obtain ⟨μ, htC⟩ := ht.exists_mu hsimp hsplit
  have hspanW : CW = Submodule.span k {y} := Cc.fixU_eq_span hsimp htC
  have hdimW : finrank k CW = 1 := by
    rw [hspanW, finrank_span_singleton htC.2.1]
  have hdimC : finrank E C = 1 := by
    change finrank E (fixSub σ Cc.U) = 1
    rw [← CFSG.Theory.Representation.finrank_fixSub_extendScalars (F := E) (F' := k) σ Cc.U]
    exact hdimW
  let : Module.Free E C := Module.Free.of_divisionRing E C
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp hdimC
  have hvne : (v : X) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hmemW : ((1 : k) ⊗ₜ[E] (v : X)) ∈ CW := by
    intro u hu
    show W u ((1 : k) ⊗ₜ[E] (v : X)) = (1 : k) ⊗ₜ[E] (v : X)
    rw [show W u = (σ u).baseChange k from rfl, LinearMap.baseChange_tmul, v.2 u hu]
  have h1t : (1 : k) ⊗ₜ[E] (v : X) ≠ 0 := by
    intro hz
    exact hvne ((Module.FaithfullyFlat.one_tmul_eq_zero_iff E X (A := k) (v : X)).mp hz)
  have hCW : CW = k ∙ ((1 : k) ⊗ₜ[E] (v : X)) := by
    refine (Submodule.eq_of_le_of_finrank_eq
      (S₁ := k ∙ ((1 : k) ⊗ₜ[E] (v : X))) (S₂ := CW) ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hmemW
    · rw [finrank_span_singleton h1t, hdimW]
  intro g hg
  have hg' : g ∈ Cc.H := by
    show g ∈ (curtisDatum m F 2).H.comap (MonoidHom.id G)
    exact hg
  have hnorm : ∀ u ∈ Cc.U, g⁻¹ * u * g ∈ Cc.U := Cc.H_normU' g hg'
  have hψmem : ∀ w : C, σ g (w : X) ∈ C := fun w => act_mem_fixSub σ hnorm w.2
  let ψ : C →ₗ[E] C :=
    { toFun := fun w => ⟨σ g (w : X), hψmem w⟩
      map_add' := fun x y => by ext; exact map_add (σ g) x.1 y.1
      map_smul' := fun a x => by ext; exact LinearMap.map_smul (σ g) a x.1 }
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdimC ψ
  have hmem : ∀ w ∈ C, σ g (w : X) = c • w := by
    intro w hw
    have h := congrArg (fun f : C →ₗ[E] C => f ⟨w, hw⟩) hc
    simpa [ψ] using h
  refine ⟨c, ?_⟩
  have hscalar (d : E) (x : X) :
      (1 : k) ⊗ₜ[E] (d • x) = algebraMap E k d • ((1 : k) ⊗ₜ[E] x) := by
    rw [TensorProduct.tmul_smul]
    simp
  have hx : W g ((1 : k) ⊗ₜ[E] (v : X)) =
      algebraMap E k c • ((1 : k) ⊗ₜ[E] (v : X)) := by
    rw [show W g = (σ g).baseChange k from rfl, LinearMap.baseChange_tmul, hmem v v.2]
    exact hscalar c (v : X)
  have hy : y ∈ k ∙ ((1 : k) ⊗ₜ[E] (v : X)) := by
    rw [← hCW]
    exact ht.1
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  have hWy : W g y = algebraMap E k c • y := by
    rw [← ha, map_smul, hx, smul_comm]
  have hχ : χ g • y = algebraMap E k c • y := by
    rw [← ht.2.2.1 g hg, hWy]
  exact smul_left_injective k ht.2.1 hχ

theorem le_mul_card_active_of_isCoverType_extendScalars (m : ℕ) {F : Type} [Field F]
    [Fintype F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {E : Type} [Field E] [Finite E] {s : ℕ} (hE : Nat.card E = 2 ^ s)
    {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
    {X : Type} [AddCommGroup X] [Module E X] [FiniteDimensional E X]
    (σ : Representation E (SpecialLinearGroup (Fin (m + 1)) F) X)
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) (CFSG.Theory.Representation.extendScalars k σ) y χ J)
    {ε : Fin f → Finset (Fin (m + 1))} (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r)
    (hε : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g)
    (hne : ∃ r, ε r ≠ ∅) :
    f ≤ s * (Finset.univ.filter fun r => ε r ≠ ∅).card := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨r₀, hr₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hr₀
  have hj₀0 : j₀ ≠ 0 := fun h => h0 r₀ (h ▸ hj₀)
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj₀0
  have hj : (i.succ : Fin (m + 1)) ∈ ε r₀ := hi ▸ hj₀
  have hb : bDigit ε i.succ ≠ 0 := by
    intro h
    exact ((bDigit_eq_zero_iff ε i.succ).mp h) r₀ hj
  have hD4 : ∀ h ∈ (curtisDatum m F 2).H, ∃ c : E, χ h = algebraMap E k c :=
    chi_mem_range_of_isCoverType_extendScalars m σ hsimp ht
  have hval : ∀ u : Fˣ,
      (algebraMap F k) (u : F) ^ bDigit ε i.succ ∈ (algebraMap E k).range := by
    intro u
    obtain ⟨c, hc⟩ := hD4 (hdiag m F i u) (hdiag_mem_H m F i u)
    refine ⟨c, ?_⟩
    rw [← hc, hε (hdiag m F i u) (hdiag_mem_H m F i u), slChiEps_hdiag]
  have hE' : Fintype.card E = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  have hs1 : 1 ≤ s := by
    have h2 : 1 < Nat.card E := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hE] at h2
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    rw [hs0] at h2
    exact lt_irrefl 1 h2
  have hperiod := le_mul_card_of_values_mem (m := m) (F := F) (f := f) (k := k) (E := E)
    hF hE' hs1 (algebraMap F k) ε i.succ hb hval
  have hsub : (Finset.univ.filter fun r : Fin f => i.succ ∈ ε r) ⊆
      (Finset.univ.filter fun r => ε r ≠ ∅) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact Finset.nonempty_iff_ne_empty.mp ⟨i.succ, hr⟩
  exact le_trans hperiod (Nat.mul_le_mul_left s (Finset.card_le_card hsub))

end

end CFSG.LieType.SpecialLinear
