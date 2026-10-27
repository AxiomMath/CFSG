module

public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Steinberg.BruhatWeyl
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

section Triangular

variable {k : Type*} [Field k] {d : ℕ}

@[expose] def IsTri (dg : Fin d → ℤ) (g : Module.End k (Fin d →₀ k)) : Prop :=
  ∀ m (w : Fin d →₀ k), w ∈ filt dg m → g w ∈ filt dg m

theorem IsTri.mul {dg : Fin d → ℤ} {g h : Module.End k (Fin d →₀ k)} (hg : IsTri dg g)
    (hh : IsTri dg h) : IsTri dg (g * h) := fun m w hw => hg m _ (hh m w hw)

theorem isTri_one (dg : Fin d → ℤ) : IsTri dg (1 : Module.End k (Fin d →₀ k)) :=
  fun _ _ hw => hw

theorem isTri_diagOp (dg : Fin d → ℤ) (μ : Fin d → k) : IsTri dg (diagOp μ) := fun m w hw => by
  have := mem_filt_of_basis (s := 0) (f := diagOp μ) (dg := dg) (fun a => by
    rw [diagOp_single, add_zero]
    exact Submodule.smul_mem _ _ (single_mem_filt le_rfl)) hw
  rwa [add_zero] at this

theorem IsUni.isTri {dg : Fin d → ℤ} {g : Module.End k (Fin d →₀ k)} (hg : IsUni dg g) :
    IsTri dg g := fun m w hw => by
  have := add_mem (filt_mono (by omega) (hg m w hw)) hw
  rwa [sub_add_cancel] at this

theorem eq_one_of_isTri_of_isUni {dg dg' : Fin d → ℤ} (hdg : ∀ a, dg' a = -dg a)
    {g : Module.End k (Fin d →₀ k)} (ht : IsTri dg g) (hu : IsUni dg' g) : g = 1 := by
  refine ext_single fun a => ?_
  rw [Module.End.one_apply, ← sub_eq_zero]
  refine Finsupp.ext fun b => ?_
  have h1 : g (Finsupp.single a 1) - Finsupp.single a 1 ∈ filt dg (dg a) :=
    sub_mem (ht _ _ (single_mem_filt le_rfl)) (single_mem_filt le_rfl)
  have h2 := hu _ _ (single_mem_filt (dg := dg') (a := a) le_rfl)
  rw [Finsupp.zero_apply]
  rcases lt_or_ge (dg b) (dg a) with h | h
  · exact apply_eq_zero_of_mem_filt h1 h
  · refine apply_eq_zero_of_mem_filt h2 ?_
    rw [hdg, hdg]
    omega

end Triangular

namespace MinData

namespace Valid

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
include hV

theorem isTri_of_mem_borel {g : hV.minGroup k}
    (hg : g ∈ (⨆ i, hV.torus k i) ⊔ ⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ) :
    IsTri (D.sdeg 1) (hV.endo k g) := by
  rw [Subgroup.sup_eq_closure] at hg
  have hmem : ∀ x ∈ ((⨆ i, hV.torus k i : Subgroup (hV.minGroup k)) : Set (hV.minGroup k)) ∪
      ((⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ : Subgroup (hV.minGroup k)) :
        Set (hV.minGroup k)), IsTri (D.sdeg 1) (hV.endo k x) := by
    rintro x (hx | hx)
    · obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus k hx
      rw [hμ]
      exact isTri_diagOp _ μ
    · have hx' : x ∈ ⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ := hx
      exact (hV.isUni_of_mem k (η := 1) (by simpa only [one_mul] using hx')).isTri
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact hmem x hx
  | inv_mem x hx =>
    refine hmem x⁻¹ ?_
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · exact Or.inr (inv_mem hx)
  | one => exact isTri_one _
  | mul x y _ _ hx hy => exact hx.mul hy

variable (hA : TauCeti.IsFiniteType τ.cartan)

theorem minDatum_bruhatExtras : BruhatExtras (hV.minDatum hA k) (hV.torus k) where
  borel_inf_negUnipotent := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hb, hn⟩ := hg
    rw [borel, posUnipotent, setOf_pos_eq] at hb
    rw [negUnipotent, setOf_neg_eq] at hn
    have ht := hV.isTri_of_mem_borel k hb
    have hu := hV.isUni_of_mem k (η := -1) (by
      simpa only [neg_one_mul, Left.neg_pos_iff] using hn)
    rw [Subgroup.mem_bot]
    exact hV.endo_injective k (eq_one_of_isTri_of_isUni (fun a => by simp [sdeg]) ht hu)

end Valid

end MinData

theorem e6Datum_bruhatExtras (k : Type*) [Field k] :
    BruhatExtras (e6Datum k) (e6Data_valid.torus k) :=
  e6Data_valid.minDatum_bruhatExtras k isFiniteType_cartan_E6

theorem e7Datum_bruhatExtras (k : Type*) [Field k] :
    BruhatExtras (e7Datum k) (e7Data_valid.torus k) :=
  e7Data_valid.minDatum_bruhatExtras k isFiniteType_cartan_E7

end CFSG.LieType.Steinberg.Minuscule
