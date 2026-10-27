module

public import CFSG.LieType.Steinberg.Minuscule.Unipotent
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.LevelFiltration

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section Shift

variable {d : ℕ} {k : Type*} [Field k] {dg : Fin d → ℤ}

def Shift (dg : Fin d → ℤ) (s : ℤ) (φ : Module.End k (Fin d →₀ k)) : Prop :=
  ∀ (m : ℤ) (w : Fin d →₀ k), w ∈ filt dg m → φ w ∈ filt dg (m + s)

theorem Shift.zero (s : ℤ) : Shift dg s (0 : Module.End k (Fin d →₀ k)) := fun m w _ => by
  rw [LinearMap.zero_apply]; exact zero_mem _

theorem Shift.add {s : ℤ} {φ ψ : Module.End k (Fin d →₀ k)} (hφ : Shift dg s φ)
    (hψ : Shift dg s ψ) : Shift dg s (φ + ψ) := fun m w hw => by
  rw [LinearMap.add_apply]; exact add_mem (hφ m w hw) (hψ m w hw)

theorem Shift.neg {s : ℤ} {φ : Module.End k (Fin d →₀ k)} (hφ : Shift dg s φ) :
    Shift dg s (-φ) := fun m w hw => by
  rw [LinearMap.neg_apply]; exact neg_mem (hφ m w hw)

theorem Shift.sub {s : ℤ} {φ ψ : Module.End k (Fin d →₀ k)} (hφ : Shift dg s φ)
    (hψ : Shift dg s ψ) : Shift dg s (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

theorem Shift.smul {s : ℤ} {φ : Module.End k (Fin d →₀ k)} (c : k) (hφ : Shift dg s φ) :
    Shift dg s (c • φ) := fun m w hw => by
  rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ c (hφ m w hw)

theorem Shift.mono {s t : ℤ} {φ : Module.End k (Fin d →₀ k)} (h : t ≤ s) (hφ : Shift dg s φ) :
    Shift dg t φ := fun m w hw => filt_mono (by omega) (hφ m w hw)

theorem Shift.mul {s t : ℤ} {φ ψ : Module.End k (Fin d →₀ k)} (hφ : Shift dg s φ)
    (hψ : Shift dg t ψ) : Shift dg (s + t) (φ * ψ) := fun m w hw => by
  rw [Module.End.mul_apply]
  have := hφ _ _ (hψ m w hw)
  rwa [show m + t + s = m + (s + t) by ring] at this

theorem mem_filt_of_forall {m : ℤ} {w : Fin d →₀ k} (h : ∀ b, w b ≠ 0 → m ≤ dg b) :
    w ∈ filt dg m := by
  have : w = ∑ b ∈ w.support, w b • Finsupp.single b (1 : k) := by
    conv_lhs => rw [← Finsupp.sum_single w]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [this]
  exact Submodule.sum_mem _ fun b hb =>
    Submodule.smul_mem _ _ (single_mem_filt (h b (Finsupp.mem_support_iff.1 hb)))

@[expose] def leadWts (F : Fin d → ℤ) (S : Submodule k (Fin d →₀ k)) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun μ => ∃ v ∈ S, v μ ≠ 0 ∧ ∀ ν, v ν ≠ 0 → F μ ≤ F ν

theorem finrank_le_card_leadWts (F : Fin d → ℤ) (S : Submodule k (Fin d →₀ k)) :
    Module.finrank k S ≤ (leadWts F S).card := by
  classical
  let ψ : S →ₗ[k] (leadWts F S → k) :=
    LinearMap.pi fun μ => (Finsupp.lapply (R := k) μ.1).comp S.subtype
  have hker0 : ∀ v : S, (∀ μ : leadWts F S, (v : Fin d →₀ k) μ.1 = 0) → v = 0 := by
    intro v hv
    by_contra hne
    have hv' : (v : Fin d →₀ k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨μ, hμ, hmin⟩ := Finset.exists_min_image (v : Fin d →₀ k).support F
      (Finsupp.support_nonempty_iff.2 hv')
    have hμ' : v.1 μ ≠ 0 := Finsupp.mem_support_iff.1 hμ
    have hmem : μ ∈ leadWts F S := by
      simp only [leadWts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v.1, v.2, hμ', fun ν hν => hmin ν (Finsupp.mem_support_iff.2 hν)⟩
    exact hμ' (hv ⟨μ, hmem⟩)
  have hinj : Function.Injective ψ := by
    intro v w hvw
    have h1 : ∀ μ : leadWts F S, ((v : Fin d →₀ k) - w) μ.1 = 0 := fun μ => by
      have := congrFun hvw μ
      simp only [ψ, LinearMap.pi_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
        Submodule.subtype_apply] at this
      rw [Finsupp.sub_apply, this, sub_self]
    exact sub_eq_zero.1 (hker0 (v - w) h1)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

theorem isSign_ne_zero {σ : k} (h : IsSign σ) : σ ≠ 0 := by
  rcases h with rfl | rfl <;> simp

end Shift

section Min

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
  (f : (Fin τ.rank → ℤ) →+ ℤ)

@[expose] def posRoots : Set (Fin τ.rank → ℤ) := {γ | IsRoot τ γ ∧ 0 < f γ}

@[expose] def lvlU (r : ℤ) : Subgroup (hV.minGroup k) := lvl (hV.rootGroup k) (posRoots f) f r

variable {hV k f}

theorem isRoot_finite : {γ : Fin τ.rank → ℤ | IsRoot τ γ}.Finite := by
  have h1 : (List.ofFn '' {γ : Fin τ.rank → ℤ | IsRoot τ γ}) ⊆ {l | l ∈ τ.artifactRoots} := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact isRoot_iff_mem_artifactRoots.1 hγ
  exact Set.Finite.of_finite_image ((List.finite_toSet _).subset h1)
    (List.ofFn_injective.injOn)

theorem posRoots_finite : (posRoots f : Set (Fin τ.rank → ℤ)).Finite :=
  isRoot_finite.subset fun _ h => h.1

include hV

theorem levelData (hfinj : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → f γ = f δ → γ = δ) :
    LevelData (hV.rootGroup k) (posRoots f) f where
  pos γ hγ := hγ.2
  inj γ hγ δ hδ h := hfinj γ δ hγ.1 hδ.1 h
  comm γ hγ δ hδ x hx y hy := by
    obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
    obtain ⟨d, rfl⟩ := (hV.mem_rootGroup k).1 hy
    have hpos : 0 < f (γ + δ) := by rw [map_add]; have := hγ.2; have := hδ.2; omega
    have hne : γ + δ ≠ 0 := fun h => by rw [h, map_zero] at hpos; exact lt_irrefl _ hpos
    obtain ⟨hroot, hcomm⟩ := hV.commutator_xm k hγ.1 hδ.1 hne
    by_cases hr : IsRoot τ (γ + δ)
    · obtain ⟨σ, -, h⟩ := hroot hr
      rw [h]
      refine le_lvl (hV.rootGroup k) (posRoots f) f (γ := γ + δ) ⟨hr, hpos⟩ (by rw [map_add]) ?_
      exact hV.xm_mem_rootGroup k _ _
    · rw [hcomm hr]
      exact one_mem _

theorem card_rootGroup_le [Finite k] (γ : Fin τ.rank → ℤ) :
    Nat.card ↥(hV.rootGroup k γ) ≤ Nat.card k := by
  have hs : Function.Surjective (hV.xHom k γ).rangeRestrict := (hV.xHom k γ).rangeRestrict_surjective
  calc Nat.card ↥(hV.rootGroup k γ) ≤ Nat.card (Multiplicative k) :=
        Nat.card_le_card_of_surjective _ hs
    _ = Nat.card k := Nat.card_congr Multiplicative.toAdd

theorem finite_minGroup [Finite k] : Finite ↥(hV.minGroup k) := by
  have : Finite (Module.End k (Fin D.d →₀ k)) := Module.finite_of_finite k
  infer_instance

theorem shift_rootOp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    Shift (D.fgrade f) (τ.cartan.det * f γ) (D.rootOp k γ) := fun _ _ hw =>
  (hV.isSignedMap_rootOp hγ).mem_filt (fun a b h => (D.isGrading_fgrade f a b γ h).ge) hw

theorem endo_xm_sub_one (γ : Fin τ.rank → ℤ) (u : k) :
    hV.endo k (hV.xm k γ u) - 1 = u • D.rootOp k γ := by
  rw [hV.endo_xm, add_sub_cancel_left]

theorem shift_of_mem_lvlU (hc0 : 0 < τ.cartan.det) {r : ℤ} (hr : 0 ≤ r)
    {g : hV.minGroup k} (hg : g ∈ lvlU hV k f r) :
    Shift (D.fgrade f) (τ.cartan.det * r) (hV.endo k g - 1) := by
  refine lvl_induction (C := fun g => Shift (D.fgrade f) (τ.cartan.det * r) (hV.endo k g - 1))
    hg (fun δ hδ hrδ z hz => ?_) ?_ (fun a b ha hb => ?_)
  · obtain ⟨u, rfl⟩ := (hV.mem_rootGroup k).1 hz
    rw [endo_xm_sub_one]
    exact ((shift_rootOp (hV := hV) hδ.1).smul u).mono (mul_le_mul_of_nonneg_left hrδ hc0.le)
  · rw [hV.endo_one, sub_self]; exact Shift.zero _
  · have e : hV.endo k (a * b) - 1 =
        (hV.endo k a - 1) * (hV.endo k b - 1) + (hV.endo k a - 1) + (hV.endo k b - 1) := by
      rw [hV.endo_mul]; noncomm_ring
    rw [e]
    have hm := (ha.mul hb).mono (t := τ.cartan.det * r) (by nlinarith)
    exact (hm.add ha).add hb

theorem lead_decomp (hLD : LevelData (hV.rootGroup k) (posRoots f) f) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ posRoots f) {a : hV.minGroup k} (ha : a ∈ lvlU hV k f (f γ))
    (hna : a ∉ lvlU hV k f (f γ + 1)) :
    ∃ c : k, c ≠ 0 ∧ ∃ κ ∈ lvlU hV k f (f γ + 1), a = hV.xm k γ c * κ := by
  obtain ⟨x, hx, κ, hκ, rfl⟩ := hLD.lvl_decomp hγ ha
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
  refine ⟨c, ?_, κ, hκ, rfl⟩
  rintro rfl
  rw [hV.xm_zero, one_mul] at hna
  exact hna hκ

theorem shift_sub_lead (hc0 : 0 < τ.cartan.det) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots f)
    (c : k) {κ : hV.minGroup k} (hκ : κ ∈ lvlU hV k f (f γ + 1)) :
    Shift (D.fgrade f) (τ.cartan.det * (f γ + 1))
      (hV.endo k (hV.xm k γ c * κ) - 1 - c • D.rootOp k γ) := by
  have hf := hγ.2
  have e : hV.endo k (hV.xm k γ c * κ) - 1 - c • D.rootOp k γ =
      (hV.endo k κ - 1) + (c • D.rootOp k γ) * (hV.endo k κ - 1) := by
    rw [hV.endo_mul, hV.endo_xm]; noncomm_ring
  rw [e]
  have h1 := shift_of_mem_lvlU hc0 (by omega) hκ
  refine h1.add ?_
  have h2 := ((shift_rootOp (hV := hV) (k := k) hγ.1 (f := f)).smul c).mul h1
  refine h2.mono ?_
  nlinarith

theorem not_isRoot_add_of_lead (hc0 : 0 < τ.cartan.det)
    (hLD : LevelData (hV.rootGroup k) (posRoots f) f) (hP : (posRoots f).Finite)
    {A : Subgroup (hV.minGroup k)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ leadSet (X := hV.rootGroup k) (lev := f) hP A)
    (hδ : δ ∈ leadSet (X := hV.rootGroup k) (lev := f) hP A) : ¬ IsRoot τ (γ + δ) := by
  intro hr
  obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
  obtain ⟨hδP, -⟩ := mem_leadSet.1 hδ
  obtain ⟨a, haA, ha1, ha2⟩ := exists_of_mem_leadSet hγ
  obtain ⟨b, hbA, hb1, hb2⟩ := exists_of_mem_leadSet hδ
  obtain ⟨c, hc, κ, hκ, rfl⟩ := lead_decomp hLD hγP ha1 ha2
  obtain ⟨d, hd, κ', hκ', rfl⟩ := lead_decomp hLD hδP hb1 hb2
  have hfγ := hγP.2
  have hfδ := hδP.2
  have hne : γ + δ ≠ 0 := fun h => by
    have := congrArg f h
    rw [map_add, map_zero] at this
    omega
  set c0 := τ.cartan.det with hc0def
  have hab := hAc _ haA _ hbA
  have hab' : hV.endo k (hV.xm k γ c * κ) * hV.endo k (hV.xm k δ d * κ') =
      hV.endo k (hV.xm k δ d * κ') * hV.endo k (hV.xm k γ c * κ) := by
    rw [← hV.endo_mul, ← hV.endo_mul, hab]
  set Ea := c • D.rootOp k γ with hEa
  set Eb := d • D.rootOp k δ with hEb
  set φa := hV.endo k (hV.xm k γ c * κ) - 1 - Ea with hφa
  set φb := hV.endo k (hV.xm k δ d * κ') - 1 - Eb with hφb
  have hsa : Shift (D.fgrade f) (c0 * (f γ + 1)) φa := shift_sub_lead hc0 hγP c hκ
  have hsb : Shift (D.fgrade f) (c0 * (f δ + 1)) φb := shift_sub_lead hc0 hδP d hκ'
  have ea : hV.endo k (hV.xm k γ c * κ) = 1 + Ea + φa := by rw [hφa]; abel
  have eb : hV.endo k (hV.xm k δ d * κ') = 1 + Eb + φb := by rw [hφb]; abel
  have hmain : (Ea * Eb - Eb * Ea) + ((Ea * φb - φb * Ea) + (φa * Eb - Eb * φa) +
      (φa * φb - φb * φa)) = 0 := by
    have h := sub_eq_zero.2 hab'
    rw [ea, eb] at h
    rw [← h]
    noncomm_ring
  have hEaS : Shift (D.fgrade f) (c0 * f γ) Ea := (shift_rootOp (hV := hV) hγP.1).smul c
  have hEbS : Shift (D.fgrade f) (c0 * f δ) Eb := (shift_rootOp (hV := hV) hδP.1).smul d
  set s' : ℤ := c0 * (f γ + f δ) + 1 with hs'
  have hrest : Shift (D.fgrade f) s'
      ((Ea * φb - φb * Ea) + (φa * Eb - Eb * φa) + (φa * φb - φb * φa)) := by
    have t1 := (hEaS.mul hsb).mono (t := s') (by rw [hs']; nlinarith)
    have t2 := (hsb.mul hEaS).mono (t := s') (by rw [hs']; nlinarith)
    have t3 := (hsa.mul hEbS).mono (t := s') (by rw [hs']; nlinarith)
    have t4 := (hEbS.mul hsa).mono (t := s') (by rw [hs']; nlinarith)
    have t5 := (hsa.mul hsb).mono (t := s') (by rw [hs']; nlinarith)
    have t6 := (hsb.mul hsa).mono (t := s') (by rw [hs']; nlinarith)
    exact ((t1.sub t2).add (t3.sub t4)).add (t5.sub t6)
  obtain ⟨⟨σ, hσ, hcomm⟩, -, -⟩ := (hV.pairRel (R := k) hγP.1 hδP.1 hne).1 hr
  have hE : Ea * Eb - Eb * Ea = (c * d * σ) • D.rootOp k (γ + δ) := by
    rw [hEa, hEb, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm d c, ← smul_sub, hcomm,
      smul_smul]
  have hS : Shift (D.fgrade f) s' ((c * d * σ) • D.rootOp k (γ + δ)) := by
    rw [← hE, eq_neg_of_add_eq_zero_left hmain]
    exact hrest.neg
  obtain ⟨a0, b0, ε, hε, hab0, hwt⟩ := hV.exists_rootOp_single_ne_zero k hr
  have hmem := hS (D.fgrade f a0) (Finsupp.single a0 1) (single_mem_filt le_rfl)
  rw [LinearMap.smul_apply, hab0, smul_smul] at hmem
  have hF := D.isGrading_fgrade f a0 b0 (γ + δ) hwt
  rw [map_add] at hF
  have h0 := apply_eq_zero_of_mem_filt hmem (b := b0) (by rw [hF, hs']; linarith)
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hd) (isSign_ne_zero hσ)) (isSign_ne_zero hε) h0

@[expose] def fixedSub (A : Subgroup (hV.minGroup k)) : Submodule k (Fin D.d →₀ k) where
  carrier := {v | ∀ a ∈ A, hV.endo k a v = v}
  add_mem' := by
    intro v w hv hw a ha
    rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := by
    intro c v hv a ha
    rw [map_smul, hv a ha]

theorem rootOp_eq_zero_of_lead (hc0 : 0 < τ.cartan.det)
    (hLD : LevelData (hV.rootGroup k) (posRoots f) f) (hP : (posRoots f).Finite)
    {A : Subgroup (hV.minGroup k)} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ leadSet (X := hV.rootGroup k) (lev := f) hP A) {v : Fin D.d →₀ k}
    (hv : v ∈ fixedSub (hV := hV) (k := k) A) {μ : Fin D.d} (hμ : v μ ≠ 0)
    (hmin : ∀ ν, v ν ≠ 0 → D.fgrade f μ ≤ D.fgrade f ν) :
    D.rootOp k γ (Finsupp.single μ 1) = 0 := by
  by_contra hne
  obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
  obtain ⟨a, haA, ha1, ha2⟩ := exists_of_mem_leadSet hγ
  obtain ⟨c, hc, κ, hκ, rfl⟩ := lead_decomp hLD hγP ha1 ha2
  have hfγ := hγP.2
  set c0 := τ.cartan.det with hc0def
  obtain ⟨t, hwt, ε, hε, hEμ⟩ : ∃ t : Fin D.d, D.wt t = D.wt μ + MinData.toWeight γ ∧ ∃ ε : k, IsSign ε ∧
      D.rootOp k γ (Finsupp.single μ 1) = ε • Finsupp.single t 1 := by
    rcases hV.isSignedMap_rootOp (R := k) hγP.1 μ with h0 | ⟨t, hwt, hs | hs⟩
    · exact absurd h0 hne
    · exact ⟨t, hwt, 1, isSign_one, by rw [hs, one_smul]⟩
    · exact ⟨t, hwt, -1, isSign_neg_one, by rw [hs, neg_one_smul]⟩
  have hcoef : ∀ w : Fin D.d →₀ k, D.rootOp k γ w t = ε * w μ := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]
    | single ν x =>
      have e : (Finsupp.single ν x : Fin D.d →₀ k) = x • Finsupp.single ν 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [e, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
      by_cases hνμ : ν = μ
      · subst hνμ
        rw [hEμ, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
        simp [mul_comm]
      · have h0 : D.rootOp k γ (Finsupp.single ν 1) t = 0 := by
          rcases hV.isSignedMap_rootOp (R := k) hγP.1 ν with h0 | ⟨b, hb, hs | hs⟩
          · rw [h0]; rfl
          · rw [hs, Finsupp.single_apply, ite_eq_right]
            rintro rfl
            apply hνμ
            apply hV.wt_injective
            simp only at hb hwt ⊢
            have := hb.symm.trans hwt
            exact add_right_cancel this
          · rw [hs, Finsupp.neg_apply, Finsupp.single_apply, ite_eq_right, neg_zero]
            rintro rfl
            apply hνμ
            apply hV.wt_injective
            simp only at hb hwt ⊢
            have := hb.symm.trans hwt
            exact add_right_cancel this
        rw [h0, mul_zero, Finsupp.single_apply, ite_eq_right hνμ, mul_zero, mul_zero]
  have hvF : v ∈ filt (D.fgrade f) (D.fgrade f μ) := mem_filt_of_forall hmin
  have hsa : Shift (D.fgrade f) (c0 * (f γ + 1))
      (hV.endo k (hV.xm k γ c * κ) - 1 - c • D.rootOp k γ) := shift_sub_lead hc0 hγP c hκ
  have hφ := hsa _ v hvF
  have hF := D.isGrading_fgrade f μ t γ hwt
  have hφt := apply_eq_zero_of_mem_filt hφ (b := t) (by rw [hF]; nlinarith)
  have hfix := hv _ haA
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hfix, sub_self,
    zero_sub, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul, neg_eq_zero, hcoef] at hφt
  exact mul_ne_zero hc (mul_ne_zero (isSign_ne_zero hε) hμ) hφt

theorem exists_leading_data [Finite k] (hc0 : 0 < τ.cartan.det)
    (hfinj : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → f γ = f δ → γ = δ)
    {A : Subgroup (hV.minGroup k)} (hAU : A ≤ lvlU hV k f 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ (X : Finset (Fin τ.rank → ℤ)) (Y : Finset (Fin D.d)),
      (∀ γ ∈ X, IsRoot τ γ ∧ 0 < f γ) ∧ (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot τ (γ + δ)) ∧
      (∀ γ ∈ X, ∀ μ ∈ Y, D.rootOp k γ (Finsupp.single μ 1) = 0) ∧
      Nat.card A ≤ Nat.card k ^ X.card ∧
      Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ Y.card ∧
      (A ≠ ⊥ → X.Nonempty) := by
  have hLD := levelData (hV := hV) (k := k) hfinj
  have hP := posRoots_finite (τ := τ) (f := f)
  have := finite_minGroup (hV := hV) (k := k)
  have hq1 : 1 ≤ Nat.card k := Nat.card_pos
  have hcard := card_le_pow_leadSet hLD hP hq1 (fun γ _ => card_rootGroup_le (hV := hV) (k := k) γ)
    hAU
  refine ⟨leadSet (X := hV.rootGroup k) (lev := f) hP A, leadWts (D.fgrade f) (fixedSub (hV := hV) (k := k) A),
    fun γ hγ => (mem_leadSet.1 hγ).1, fun γ hγ δ hδ => not_isRoot_add_of_lead hc0 hLD hP hAc hγ hδ,
    fun γ hγ μ hμ => ?_, hcard, ?_, fun hne => ?_⟩
  · simp only [leadWts, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
    obtain ⟨v, hv, hvμ, hmin⟩ := hμ
    exact rootOp_eq_zero_of_lead hc0 hLD hP hγ hv hvμ hmin
  · rw [Module.natCard_eq_pow_finrank (K := k)]
    exact Nat.pow_le_pow_right hq1 (finrank_le_card_leadWts _ _)
  · by_contra hX
    rw [Finset.not_nonempty_iff_eq_empty] at hX
    rw [hX, Finset.card_empty, pow_zero] at hcard
    exact hne ((Subgroup.card_le_one_iff_eq_bot A).1 hcard)

end Min

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
