module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4E3Plus

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.Blueprint

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem TightSepAlpha.conj (hα : TightSepAlpha R t) (g : Y) :
    TightSepAlpha (conjSub g R) (g * t * g⁻¹) := by
  intro J' hJ' v hv
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  rw [hfam, ← conjSub_tightCore] at hJ'
  have hΩ : ConjInvariant (CoreAssembly.conjClass (tightCore R)) := by
    rintro h _ ⟨a, rfl⟩
    exact ⟨h * a, conjSub_mul h a _⟩
  have h1 := omegaNbr_conj hΩ hJ' g⁻¹
  rw [conjSub_inv_conjSub] at h1
  have hv' : IsUniqueInvolution (conjSub g⁻¹ J') (g⁻¹ * v * g⁻¹⁻¹) := hv.conj g⁻¹
  have h2 := hα _ h1 _ hv'
  have h3 := congrArg (conjSub g) h2
  rw [← alphaOf_conjSub, conjSub_closure_pair] at h3
  simpa [mul_assoc, conjSub] using h3

@[expose] def ModelL3U3Acts3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    TightDatum R S z → TightClsR 3 X R S z →
      (LieModel X .PSL 3 3 1 ∨ LieModel X .PSU 3 3 1) → TightActs3 R z

section Cit3

theorem TightLargeHypR.toL (h : TightLargeHypR 3 n Y R S t) : TightLargeHyp n Y R S t :=
  ⟨h.below, h.tbelow, h.card, h.datum, h.cls, h.notInO2, h.fstar, h.large, h.edge, h.center⟩

theorem E3Frame.exists_std8 {J : Subgroup Y} {u : Y} (hF : E3Frame n R S t J u) :
    ∃ (g : Y) (Sd : Sylow 2 ↥(conjSub g R)) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
      conjSub g (tightCore R) = J ∧ g * t * g⁻¹ = u ∧
        TightStd8R 3 n (conjSub g R) Sd u (tightCore R) S' R' T W t := by
  have hd := hF.large.datum
  have hΩ := hd.hypOmegaGen
  have hJn := hF.maxAdj.1.2
  obtain ⟨g, hg⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg
  obtain ⟨Sd, hLd⟩ := (TightLargeHypR.toL hF.large).conj g
  have hu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hF.inv
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hK₀ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hF.maxAdj.1.1 hJn.1 hJn
  rw [hu] at hLd
  obtain ⟨S', R', T, W, hs⟩ :=
    TightLargeHypR.exists_std8 hLd.toR hK₀ hd.isUniqueInvolution_core
  exact ⟨g, Sd, S', R', T, W, hgJ, hu, hs⟩

@[expose] def TightE3MuPass (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → TightEdgeless (secR R u) →
      (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W ∨
            MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def TightE3Z2Fin (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          C264Two (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) u t →
            TightInO2 (E3.secT htu ht)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
