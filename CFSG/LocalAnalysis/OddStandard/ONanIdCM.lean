module

public import Certificates.Data.ChengHeldCover
public import CFSG.LocalAnalysis.OddStandard.ONanDefs
public import Certificates.Certificate6148
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealNFBase

public section

namespace CFSG.OddStandard.ONanRec.IdCM

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.OddStandard.ChengHeldData
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

structure CMCertParts : Prop where
  rels : ∀ d ∈ relData, (nfOf d.1.toWord).2 = false
  invA : (nfOf invA).2 = false
  invB : (nfOf invB).2 = false
  invU : (nfOf invU).2 = true
  specs : ∀ s ∈ cmSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)

theorem cmCertParts : CMCertParts :=
  ⟨Certificates.certificate6148.1, Certificates.certificate6148.2.1,
    Certificates.certificate6148.2.2.1, Certificates.certificate6148.2.2.2.1,
    Certificates.certificate6148.2.2.2.2⟩

theorem cv_cmSpec
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ cmSpecs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  cmCertParts.specs s hs

theorem relData_inK : ∀ d ∈ relData, inK (kapOf 0) (d.2.1 : ZMod 4) (d.2.2.1 : ZMod 4) := by
  decide

theorem mem_relData_of_mem_relsM {r : FreeGroup (Fin 6)} (hr : r ∈ relsM) :
    ∃ d ∈ relData, d.1 = r := by
  simp only [relsM, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  simp only [relData, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left]
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h <;> simp [h]

section Hom

variable {G : Type*} [Group G] (Φ : Cover →* G) (u : G)

@[expose] def upow (e : Bool) : G := if e then u else 1

@[expose] noncomputable def val (p : List (Fin 2 × Bool) × Bool) : G := Φ (cv p.1) * upow u p.2

@[expose] noncomputable def genG (i : Fin 6) : G := val Φ u (genW i.val)

variable {Φ u}

theorem upow_mul (hu : u * u = 1) (e e' : Bool) : upow u e * upow u e' = upow u (xor e e') := by
  cases e <;> cases e' <;> simp [upow, hu]

theorem upow_inv (hu : u * u = 1) (e : Bool) : (upow u e)⁻¹ = upow u e := by
  cases e
  · simp [upow]
  · exact inv_eq_of_mul_eq_one_right hu

theorem alphaIf_comm (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (e : Bool) (w : List (Fin 2 × Bool)) :
    Φ (cv (alphaIf e w)) * upow u e = upow u e * Φ (cv w) := by
  cases e
  · simp [alphaIf, upow]
  · simp only [alphaIf, upow, ite_true, hα]
    rw [mul_assoc, hu, mul_one]

theorem val_nfStep (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (p : List (Fin 2 × Bool) × Bool) (x : Fin 6 × Bool) :
    val Φ u (nfStep p x) = val Φ u p * cond x.2 (genG Φ u x.1) (genG Φ u x.1)⁻¹ := by
  obtain ⟨w, e⟩ := p
  obtain ⟨i, b⟩ := x
  set g := genW i.val with hg
  cases b
  ·
    show Φ (cv (w ++ alphaIf (xor e g.2) (FreeGroup.invRev g.1))) * upow u (xor e g.2) =
      Φ (cv w) * upow u e * (Φ (cv g.1) * upow u g.2)⁻¹
    rw [cv_append, map_mul, mul_assoc, alphaIf_comm hu hα, cv_invRev, map_inv, mul_inv_rev,
      upow_inv hu, ← upow_mul hu]
    group
  ·
    show Φ (cv (w ++ alphaIf e g.1)) * upow u (xor e g.2) =
      Φ (cv w) * upow u e * (Φ (cv g.1) * upow u g.2)
    rw [cv_append, map_mul, ← upow_mul hu, mul_assoc, ← mul_assoc (Φ (cv (alphaIf e g.1))),
      alphaIf_comm hu hα]
    group

theorem val_foldl (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (L : List (Fin 6 × Bool)) (p : List (Fin 2 × Bool) × Bool) :
    val Φ u (L.foldl nfStep p) =
      val Φ u p * (L.map fun x => cond x.2 (genG Φ u x.1) (genG Φ u x.1)⁻¹).prod := by
  induction L generalizing p with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, val_nfStep hu hα, List.map_cons, List.prod_cons, mul_assoc]

theorem val_nil : val Φ u ([], false) = 1 := by
  simp only [val, upow, Bool.false_eq_true, ite_false, mul_one]
  exact map_one Φ

theorem val_nfOf (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (L : List (Fin 6 × Bool)) :
    FreeGroup.lift (genG Φ u) (FreeGroup.mk L) = val Φ u (nfOf L) := by
  rw [FreeGroup.lift_mk, nfOf, val_foldl hu hα, val_nil, one_mul]

theorem lift_eq_val (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (r : FreeGroup (Fin 6)) : FreeGroup.lift (genG Φ u) r = val Φ u (nfOf r.toWord) := by
  rw [← val_nfOf hu hα, FreeGroup.mk_toWord]

theorem exists_cmHom
    (hu : u * u = 1) (hα : ∀ w, Φ (cv (alphaU w)) = u * Φ (cv w) * u)
    (hK : ∀ p q r : ℕ, inK (kapOf 0) (p : ZMod 4) (q : ZMod 4) → Φ (cv (zword p q r)) = 1) :
    ∃ ψ : CModel →* G, (∀ i, ψ (PresentedGroup.of i) = genG Φ u i) ∧ Φ.range ≤ ψ.range ∧
      u ∈ ψ.range := by
  have hrel : ∀ r ∈ relsM, FreeGroup.lift (genG Φ u) r = 1 := by
    intro r hr
    obtain ⟨d, hd, rfl⟩ := mem_relData_of_mem_relsM hr
    have hs : ((nfOf d.1.toWord).1, d.2) ∈ cmSpecs :=
      List.mem_append_left _ (List.mem_map_of_mem (f := fun d : FreeGroup (Fin 6) × ℕ × ℕ × ℕ =>
        ((nfOf d.1.toWord).1, d.2)) hd)
    rw [lift_eq_val hu hα, val, cmCertParts.rels d hd, cv_cmSpec hs]
    simp only [upow, Bool.false_eq_true, ite_false, mul_one]
    exact hK _ _ _ (relData_inK d hd)
  set ψ : CModel →* G := PresentedGroup.toGroup hrel
  have hψ : ∀ L : List (Fin 6 × Bool), ψ (PresentedGroup.mk relsM (FreeGroup.mk L)) =
      val Φ u (nfOf L) := by
    intro L
    rw [← val_nfOf hu hα]
    rfl
  have hspec : ∀ {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ}, s ∈ cmSpecs →
      inK (kapOf 0) (s.2.1 : ZMod 4) (s.2.2.1 : ZMod 4) → Φ (cv s.1) = 1 := by
    intro s hs hk
    rw [cv_cmSpec hs]
    exact hK _ _ _ hk
  have hmemA : ((nfOf invA).1 ++ [(0, false)], 0, 0, 1) ∈ cmSpecs :=
    List.mem_append_right _ (by simp)
  have hmemB : ((nfOf invB).1 ++ [(1, false)], 1, 2, 0) ∈ cmSpecs :=
    List.mem_append_right _ (by simp)
  have hmemU : ((nfOf invU).1, 0, 0, 0) ∈ cmSpecs := List.mem_append_right _ (by simp)
  have hgen : ∀ (L : List (Fin 6 × Bool)) (w : List (Fin 2 × Bool)) (p q r : ℕ),
      ((nfOf L).1 ++ FreeGroup.invRev w, p, q, r) ∈ cmSpecs → (nfOf L).2 = false →
      inK (kapOf 0) (p : ZMod 4) (q : ZMod 4) → Φ (cv w) ∈ ψ.range := by
    intro L w p q r hs he hk
    refine ⟨PresentedGroup.mk relsM (FreeGroup.mk L), ?_⟩
    have h1 := hspec hs hk
    rw [cv_append, cv_invRev, map_mul, map_inv, mul_inv_eq_one] at h1
    rw [hψ, val, he]
    simp only [upow, Bool.false_eq_true, ite_false, mul_one]
    exact h1
  have hA : Φ (cv [(0, true)]) ∈ ψ.range :=
    hgen invA [(0, true)] 0 0 1 hmemA cmCertParts.invA (by decide)
  have hB : Φ (cv [(1, true)]) ∈ ψ.range :=
    hgen invB [(1, true)] 1 2 0 hmemB cmCertParts.invB (by decide)
  refine ⟨ψ, fun i => PresentedGroup.toGroup.of hrel, ?_, ?_⟩
  · have htop : ψ.range.comap Φ = ⊤ := by
      rw [eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hA
      · exact hB
    rintro _ ⟨c, rfl⟩
    have : c ∈ ψ.range.comap Φ := htop ▸ mem_top c
    exact this
  · refine ⟨PresentedGroup.mk relsM (FreeGroup.mk invU), ?_⟩
    have h1 := hspec hmemU (by decide)
    rw [hψ, val, cmCertParts.invU, h1]
    simp [upow]

end Hom

end CFSG.OddStandard.ONanRec.IdCM
