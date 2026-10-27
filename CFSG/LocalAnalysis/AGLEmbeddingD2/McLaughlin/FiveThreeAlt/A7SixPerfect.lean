module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixBlock

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem commutator_eq_top_of_equiv_alt7 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 7)) :
    commutator Q = ⊤ := by
  have hs7 := isSimpleGroupAlt7
  have hs : IsSimpleGroup Q := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := exists_nonComm_alt7
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    apply hab
    have h1 : ⁅e.symm a, e.symm b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    have := congrArg e h1
    simpa using this
  · exact h

section Module

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem commOn_le_commOn_commOn (ρ : Representation (ZMod 2) G W) {L : Subgroup G}
    (hperf : commutator ↥L = ⊤) {U : Submodule (ZMod 2) W} :
    commOn ρ L U ≤ commOn ρ L (commOn ρ L U) := by
  rw [Replacement.commOn_le_iff]
  intro a ha u hu
  set P := commOn ρ L U with hP
  set Q := commOn ρ L P with hQ
  have hPmem : ∀ (g : G), g ∈ L → ρ g u - u ∈ P := fun g hg => Replacement.mem_commOn_of hg hu
  let ψ : ↥L →* Multiplicative (W ⧸ Q) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (Submodule.Quotient.mk (ρ g u - u)))
      fun g h => by
        have h1 : ρ ((g * h : ↥L) : G) u - u =
            ρ (g : G) (ρ (h : G) u - u) + (ρ (g : G) u - u) := by
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
          abel
        have h2 : ρ (g : G) (ρ (h : G) u - u) - (ρ (h : G) u - u) ∈ Q :=
          Replacement.mem_commOn_of g.2 (hPmem h h.2)
        have h3 : (Submodule.Quotient.mk (ρ (g : G) (ρ (h : G) u - u)) : W ⧸ Q) =
            Submodule.Quotient.mk (ρ (h : G) u - u) := by
          rw [Submodule.Quotient.eq]
          exact h2
        show Multiplicative.ofAdd (Submodule.Quotient.mk (ρ ((g * h : ↥L) : G) u - u)) = _
        rw [h1, Submodule.Quotient.mk_add, h3]
        show _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
        rw [← ofAdd_add, add_comm]
  have hψ : ψ ⟨a, ha⟩ = 1 :=
    MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ψ
      (by rw [hperf]; exact Subgroup.mem_top _))
  have h4 : (Submodule.Quotient.mk (ρ a u - u) : W ⧸ Q) = 0 := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk (ρ a u - u) : W ⧸ Q) = 1 at hψ
    rwa [ofAdd_eq_one] at hψ
  exact (Submodule.Quotient.mk_eq_zero Q).1 h4

end Module

section Dict

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem subOf_commOn_gen (L : Subgroup (X ⧸ gnC T)) (W' : Subgroup X) (hW' : W' ≤ gnV T) :
    subOf hV (commOn (gnRep hV) L (modOf hV W')) =
      ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆ := by
  apply le_antisymm
  · have hle : commOn (gnRep hV) L (modOf hV W') ≤
        modOf hV ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆ := by
      rw [commOn, Submodule.span_le]
      rintro _ ⟨a, ha, u, hu, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
      change elt hV (gnRep hV (QuotientGroup.mk g) u - u) ∈
        ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆
      rw [elt_sub, elt_gnRep]
      have hc := Subgroup.commutator_mem_commutator (show elt hV u ∈ W' from hu)
        (show g ∈ L.comap (QuotientGroup.mk' (gnC T)) from ha)
      have e : g * elt hV u * g⁻¹ * (elt hV u)⁻¹ = ⁅elt hV u, g⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.inv_mem _ hc
    have hW'' : ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ gnV T :=
      (Subgroup.commutator_mono hW' le_rfl).trans (commutator_gnV_le _)
    calc subOf hV (commOn (gnRep hV) L (modOf hV W'))
        ≤ subOf hV (modOf hV ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆) :=
          (subOf_le_subOf_iff hV).mpr hle
      _ = ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆ := subOf_modOf hV hW''
  · rw [Subgroup.commutator_le]
    intro v hv g hg
    obtain ⟨w, rfl⟩ := exists_elt hV (hW' hv)
    refine ⟨-(gnRep hV (QuotientGroup.mk g) w - w), Submodule.neg_mem _
      (Submodule.subset_span ⟨QuotientGroup.mk g, hg, w, hv, rfl⟩), ?_⟩
    rw [elt_neg, elt_sub, elt_gnRep, commutatorElement_def]
    group

end Dict

theorem comm_le_comm_comm {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
    {L : Subgroup (X ⧸ gnC T)} (hperf : commutator ↥L = ⊤) {W : Subgroup X} (hW : W ≤ gnV T) :
    ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤
      ⁅⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆, L.comap (QuotientGroup.mk' (gnC T))⁆ := by
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have h1 := commOn_le_commOn_commOn (gnRep hV) hperf (U := modOf hV W)
  have e1 := subOf_commOn_gen hV L W hW
  set C1 := commOn (gnRep hV) L (modOf hV W) with hC1
  have e2 : ⁅subOf hV C1, L.comap (QuotientGroup.mk' (gnC T))⁆ =
      subOf hV (commOn (gnRep hV) L C1) := by
    rw [← subOf_commOn_gen hV L (subOf hV C1) (subOf_le_gnV hV C1), modOf_subOf]
  rw [← e1, e2]
  exact (subOf_le_subOf_iff hV).2 h1

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
