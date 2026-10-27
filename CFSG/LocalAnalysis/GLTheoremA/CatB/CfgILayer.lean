module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.Lemma44

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Perfect

variable {M : Type*} [Group M]

theorem commutator_eq_top_of_self_eq {B : Subgroup M} (h : ⁅B, B⁆ = B) :
    commutator B = ⊤ := by
  apply Subgroup.map_injective (f := B.subtype) B.subtype_injective
  have hB : (⊤ : Subgroup B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_def, Subgroup.map_commutator, hB, h]

theorem self_eq_of_commutator_eq_top {B : Subgroup M} (h : commutator B = ⊤) :
    ⁅B, B⁆ = B := by
  have hB : (⊤ : Subgroup B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (commutator B).map B.subtype = ⁅B, B⁆ := by
    rw [commutator_def, Subgroup.map_commutator, hB]
  rw [h, hB] at h1
  exact h1.symm

theorem commutator_eq_top_of_mulEquiv {A C : Type*} [Group A] [Group C] (e : A ≃* C)
    (h : commutator C = ⊤) : commutator A = ⊤ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  exact h

end Perfect

section Layer

variable {G : Type} [Group G] [Finite G]

theorem barX_layer_le_of_forall {p : ℕ} {X : Subgroup G}
    {J : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (hJ : ∀ K : Subgroup G, GLAPComponent p X K → barX p X K ≤ J) :
    barX p X (GLAPLayer p X) ≤ J := by
  set Jc : Subgroup G := (J.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype with hJc
  have hIJ : GLAPLayer p X ≤ Jc := by
    refine sSup_le ?_
    intro K hK k hk
    have hkX : k ∈ X := hK.1 hk
    refine ⟨⟨k, hkX⟩, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hkX⟩ ∈ J
    exact hJ K hK ⟨⟨k, hkX⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hIJ (Subgroup.mem_subgroupOf.1 hy)
  have hzeq : z = y := Subtype.ext hzy
  rw [← hzeq]
  exact hz

theorem commutator_barX_layer_self (p : ℕ) (X : Subgroup G) :
    ⁅barX p X (GLAPLayer p X), barX p X (GLAPLayer p X)⁆ = barX p X (GLAPLayer p X) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (barX p X (GLAPLayer p X)).mul_mem
      ((barX p X (GLAPLayer p X)).mul_mem
        ((barX p X (GLAPLayer p X)).mul_mem ha hb) ((barX p X (GLAPLayer p X)).inv_mem ha))
      ((barX p X (GLAPLayer p X)).inv_mem hb)
  · apply barX_layer_le_of_forall
    intro K hK
    have hKI : K ≤ GLAPLayer p X := le_sSup hK
    have hq : CFSG.Open.IsQuasisimple ↥(barX p X K) := hK.2.2.1.2.2
    have hself := self_eq_of_commutator_eq_top hq.1
    calc barX p X K = ⁅barX p X K, barX p X K⁆ := hself.symm
      _ ≤ ⁅barX p X (GLAPLayer p X), barX p X (GLAPLayer p X)⁆ :=
        Subgroup.commutator_mono (barX_mono p hKI) (barX_mono p hKI)

theorem glaPLayer_isComponent_of_isSimple {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hs : IsSimpleGroup (PSimple p (GLAPLayer p X))) :
    GLAPComponent p X (GLAPLayer p X) := by
  have hIX : GLAPLayer p X ≤ X := sSup_le fun K hK => hK.1
  have hnorm : X ≤ Subgroup.normalizer (GLAPLayer p X : Set G) := fun g hg =>
    mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hsn : IsSubnormal (GLAPLayer p X) X := IsSubnormal.step hIX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hIX).2 hnorm) (IsSubnormal.refl X)
  have hperf : commutator (PQuot p (GLAPLayer p X)) = ⊤ :=
    commutator_eq_top_of_mulEquiv (quotEquivBarX hp hIX hsn)
      (commutator_eq_top_of_self_eq (commutator_barX_layer_self p X))
  have hQ : CFSG.Open.IsQuasisimple (PQuot p (GLAPLayer p X)) := ⟨hperf, hs⟩
  obtain ⟨hL, huniq, -⟩ := glaPLayer_of_isQuasisimple hQ
  have hLX : GLAPComponent p X (GLAPLayer p (GLAPLayer p X)) :=
    glaPComponent_of_isSubnormal' hp hsn hL
  have hall : ∀ K : Subgroup G, GLAPComponent p X K → K = GLAPLayer p (GLAPLayer p X) :=
    fun K hK => huniq K (glaPComponent_of_le hp hK (le_sSup hK) hIX)
  have hIL : GLAPLayer p X = GLAPLayer p (GLAPLayer p X) :=
    le_antisymm (sSup_le fun K hK => (hall K hK).le) (le_sSup hLX)
  rw [hIL]
  exact hLX

end Layer

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
