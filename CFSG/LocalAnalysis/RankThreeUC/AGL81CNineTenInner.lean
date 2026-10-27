module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

open scoped Pointwise

@[expose] def compNormalizer (X : Type*) [Group X] : Subgroup X :=
  ⨅ (C : Subgroup X) (_ : CFSG.IsComponent C), normalizer (C : Set X)

variable {X : Type*} [Group X]

theorem mem_compNormalizer_iff {x : X} :
    x ∈ compNormalizer X ↔ ∀ C : Subgroup X, CFSG.IsComponent C → x ∈ normalizer (C : Set X) := by
  simp only [compNormalizer, Subgroup.mem_iInf]

variable [Finite X]

theorem compNormalizer_normal : (compNormalizer X).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_compNormalizer_iff] at hx ⊢
  intro D hD
  have hC : CFSG.IsComponent (D.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hD
  have hkey : (normalizer ((D.map (MulAut.conj g⁻¹).toMonoidHom) : Set X)).map
      (MulAut.conj g).toMonoidHom = normalizer (D : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    congr 1
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id X := by
      ext y
      simp [MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  rw [← hkey]
  simpa [MulAut.conj_apply] using
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hx _ hC)

theorem layer_le_compNormalizer : CFSG.layer X ≤ compNormalizer X := by
  intro x hx
  rw [mem_compNormalizer_iff]
  intro C hC
  have hl : CFSG.layer X ≤ normalizer (C : Set X) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK hC with h | h
    · subst h
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le_normalizer _)
  exact hl hx

theorem centralizer_layer_le_compNormalizer :
    centralizer (CFSG.layer X : Set X) ≤ compNormalizer X := by
  intro x hx
  rw [mem_compNormalizer_iff]
  intro C hC
  exact Subgroup.centralizer_le_normalizer (C : Set X)
    (Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hC) hx)

theorem iInf_sup_centralizer_eq :
    (⨅ (C : Subgroup X) (_ : CFSG.IsComponent C), C ⊔ centralizer (C : Set X)) =
      CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    simp only [Subgroup.mem_iInf] at hx
    have key : ∀ S : Finset (Subgroup X), (∀ C ∈ S, CFSG.IsComponent C) →
        ∃ l : X, l ∈ sSup (S : Set (Subgroup X)) ∧
          ∀ C ∈ S, x * l⁻¹ ∈ centralizer (C : Set X) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          intro _
          exact ⟨1, by simp, fun C hC => (Finset.notMem_empty C hC).elim⟩
      | insert D S hD ih =>
          intro hS
          have hDcomp : CFSG.IsComponent D := hS D (Finset.mem_insert_self D S)
          have hScomp : ∀ C ∈ S, CFSG.IsComponent C :=
            fun C hC => hS C (Finset.mem_insert_of_mem hC)
          obtain ⟨l, hlmem, hlcent⟩ := ih hScomp
          have hlD : l ∈ centralizer (D : Set X) := by
            have hle : sSup (S : Set (Subgroup X)) ≤ centralizer (D : Set X) :=
              sSup_le fun C hCS => by
                have hCcomp : CFSG.IsComponent C := hScomp C hCS
                rcases CFSG.LocalCores.distinct_components_commute hCcomp hDcomp with h | h
                · exact absurd (h ▸ hCS) hD
                · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
            exact hle hlmem
          have hxl : x * l⁻¹ ∈ D ⊔ centralizer (D : Set X) :=
            mul_mem (hx D hDcomp) (Subgroup.mem_sup_right (inv_mem hlD))
          have hmemMul : x * l⁻¹ ∈ (D : Set X) * (centralizer (D : Set X) : Set X) := by
            rw [← Subgroup.coe_mul_of_right_le_normalizer_left D (centralizer (D : Set X))
              (Subgroup.centralizer_le_normalizer (D : Set X))]
            exact hxl
          obtain ⟨d, hd, y, hy, hxy⟩ := hmemMul
          have hxld : x * (d * l)⁻¹ = y := by
            have hdy : d * y * d⁻¹ = y := by
              rw [(Subgroup.mem_centralizer_iff.mp hy) d hd]
              group
            calc x * (d * l)⁻¹ = (x * l⁻¹) * d⁻¹ := by rw [mul_inv_rev]; group
              _ = (d * y) * d⁻¹ := by rw [← hxy]
              _ = y := hdy
          refine ⟨d * l, ?_, ?_⟩
          · refine mul_mem ?_ ?_
            · exact le_sSup (Finset.mem_insert_self D S) hd
            · have hle : sSup (S : Set (Subgroup X)) ≤
                  sSup ((insert D S : Finset (Subgroup X)) : Set (Subgroup X)) :=
                sSup_le_sSup fun C hC => Finset.mem_insert_of_mem hC
              exact hle hlmem
          · intro C hC
            rcases Finset.mem_insert.mp hC with hCD | hCS
            · subst hCD
              rw [hxld]
              exact hy
            · have hDC : d ∈ centralizer (C : Set X) := by
                have hCcomp : CFSG.IsComponent C := hScomp C hCS
                have hne : C ≠ D := fun h => hD (h ▸ hCS)
                rcases CFSG.LocalCores.distinct_components_commute hCcomp hDcomp with h | h
                · exact absurd h hne
                · exact (Subgroup.le_centralizer_iff.mp
                    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)) hd
              rw [show x * (d * l)⁻¹ = (x * l⁻¹) * d⁻¹ by rw [mul_inv_rev]; group]
              exact mul_mem (hlcent C hCS) (inv_mem hDC)
    have hSfall : ∀ C ∈ (Set.toFinite {C : Subgroup X | CFSG.IsComponent C}).toFinset,
        CFSG.IsComponent C := by
      intro C hC
      simpa using hC
    obtain ⟨l, hl, hlcent⟩ := key _ hSfall
    rw [Set.Finite.coe_toFinset] at hl
    rw [← CFSG.layer.eq_sSup X] at hl
    have hcent_all : ∀ C : Subgroup X, CFSG.IsComponent C →
        x * l⁻¹ ∈ centralizer (C : Set X) :=
      fun C hC => hlcent C (by simpa using hC)
    have hgcl : x * l⁻¹ ∈ centralizer (CFSG.layer X : Set X) := by
      have hsub : CFSG.layer X ≤ centralizer ({x * l⁻¹} : Set X) := by
        rw [CFSG.layer.eq_sSup]
        refine sSup_le fun C hC => ?_
        intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hcent_all C hC)) c hc
      have h2 : Subgroup.closure ({x * l⁻¹} : Set X) ≤
          centralizer (CFSG.layer X : Set X) := by
        rw [← Subgroup.centralizer_closure ({x * l⁻¹} : Set X)] at hsub
        exact (Subgroup.le_centralizer_iff).mp hsub
      exact h2 (Subgroup.subset_closure (Set.mem_singleton _))
    have hmem : (x * l⁻¹) * l ∈ CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X) :=
      mul_mem (Subgroup.mem_sup_right hgcl) (Subgroup.mem_sup_left hl)
    simpa using hmem
  · refine le_iInf fun C => le_iInf fun hC => ?_
    refine sup_le ?_ ?_
    · rw [CFSG.layer.eq_sSup]
      refine sSup_le fun K hK => ?_
      rcases CFSG.LocalCores.distinct_components_commute hK hC with h | h
      · subst h
        exact le_sup_left
      · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans le_sup_right
    · exact (Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hC)).trans le_sup_right

theorem isPClosedMod_layer_sup_centralizer_subgroupOf {p : ℕ} [Fact p.Prime]
    (h : ∀ C : Subgroup X, CFSG.IsComponent C →
      IsPClosedMod p ((C ⊔ centralizer (C : Set X)).subgroupOf (normalizer (C : Set X)))) :
    IsPClosedMod p ((CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X)).subgroupOf
      (compNormalizer X)) := by
  classical
  have hmemN : ∀ C : Subgroup X, CFSG.IsComponent C →
      compNormalizer X ≤ normalizer (C : Set X) :=
    fun C hC x hx => (mem_compNormalizer_iff.mp hx) C hC
  have hsupnorm : ∀ C : Subgroup X, CFSG.IsComponent C →
      ((C ⊔ centralizer (C : Set X)).subgroupOf (normalizer (C : Set X))).Normal := by
    intro C _
    haveI h1 : (C.subgroupOf (normalizer (C : Set X))).Normal := Subgroup.normal_in_normalizer
    haveI h2 : ((centralizer (C : Set X)).subgroupOf (normalizer (C : Set X))).Normal :=
      Subgroup.normal_subgroupOf_centralizer_normalizer (C : Set X)
    rw [Subgroup.subgroupOf_sup (Subgroup.le_normalizer)
      (Subgroup.centralizer_le_normalizer (C : Set X))]
    infer_instance
  have hUn : ∀ C : Subgroup X, CFSG.IsComponent C →
      ((C ⊔ centralizer (C : Set X)).subgroupOf (compNormalizer X)).Normal := by
    intro C hC
    have hCN : compNormalizer X ≤ normalizer (C : Set X) := hmemN C hC
    rw [← Subgroup.comap_inclusion_subgroupOf hCN (C ⊔ centralizer (C : Set X))]
    exact Subgroup.Normal.comap (hsupnorm C hC) (Subgroup.inclusion hCN)
  have hU : ∀ C : Subgroup X, CFSG.IsComponent C →
      IsPClosedMod p ((C ⊔ centralizer (C : Set X)).subgroupOf (compNormalizer X)) := by
    intro C hC
    have hCN : compNormalizer X ≤ normalizer (C : Set X) := hmemN C hC
    haveI := hsupnorm C hC
    have hcom := IsPClosedMod.comap (h C hC) (Subgroup.inclusion hCN)
    rwa [Subgroup.comap_inclusion_subgroupOf hCN (C ⊔ centralizer (C : Set X))] at hcom
  have hfin := IsPClosedMod.finset_inf
    (Finset.univ : Finset (CFSG.LocalCores.ComponentIndex X))
    (fun K => (K.1 ⊔ centralizer (K.1 : Set X)).subgroupOf (compNormalizer X))
    (fun K _ => hUn K K.2) (fun K _ => hU K K.2)
  have heq : (Finset.univ.inf (fun K : CFSG.LocalCores.ComponentIndex X =>
        (K.1 ⊔ centralizer (K.1 : Set X)).subgroupOf (compNormalizer X))) =
      (CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X)).subgroupOf (compNormalizer X) := by
    rw [Finset.inf_eq_iInf]
    simp only [Finset.mem_univ, iInf_true]
    change (⨅ K : CFSG.LocalCores.ComponentIndex X,
        Subgroup.comap (compNormalizer X).subtype (K.1 ⊔ centralizer (K.1 : Set X))) =
      Subgroup.comap (compNormalizer X).subtype
        (CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X))
    rw [← Subgroup.comap_iInf (compNormalizer X).subtype
      (fun K : CFSG.LocalCores.ComponentIndex X => K.1 ⊔ centralizer (K.1 : Set X))]
    rw [iInf_subtype]
    rw [← iInf_sup_centralizer_eq]
  rwa [heq] at hfin

theorem not_dvd_index_of_isSylowOf_le {p : ℕ} [Fact p.Prime] {P N : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) (hPN : P ≤ N) : ¬ p ∣ N.index := by
  have hP' := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
  rw [Subgroup.relIndex_top_right] at hP'
  exact fun hdiv => hP' (hdiv.trans (Subgroup.index_dvd_of_le hPN))

theorem isPClosedMod_layer_sup_centralizer {p : ℕ} [Fact p.Prime]
    (h : ∀ C : Subgroup X, CFSG.IsComponent C →
      IsPClosedMod p ((C ⊔ centralizer (C : Set X)).subgroupOf (normalizer (C : Set X))))
    (hN : ¬ p ∣ (compNormalizer X).index) :
    IsPClosedMod p (CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X)) := by
  haveI hNn : (compNormalizer X).Normal := compNormalizer_normal
  haveI hLc : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : (CFSG.layer X).Normal := inferInstance
  haveI hCn : (centralizer (CFSG.layer X : Set X)).Normal := inferInstance
  haveI hUn : (CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X)).Normal := inferInstance
  have hUN : CFSG.layer X ⊔ centralizer (CFSG.layer X : Set X) ≤ compNormalizer X :=
    sup_le layer_le_compNormalizer centralizer_layer_le_compNormalizer
  exact IsPClosedMod.of_subgroupOf hUN hN
    (isPClosedMod_layer_sup_centralizer_subgroupOf h)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
