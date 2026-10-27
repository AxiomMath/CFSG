module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Psi
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4N1
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4R
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

theorem isSylowOf_of_secPsi [Fact p.Prime] (hXJ : X ≤ J) (hker : (secPsi a X J).ker = ⊥)
    (hS : CFSG.ABGLocalTools.IsSylowOf p (secX a X J) (secJ a X J)) :
    CFSG.ABGLocalTools.IsSylowOf p X J := by
  obtain ⟨Q, hQ⟩ := hS
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hS' : (X.subgroupOf J).map (secPsi a X J) = (Q : Subgroup ↥(secJ a X J)) := by
    apply Subgroup.map_injective (secJ a X J).subtype_injective
    rw [hQ, ← secPsi_map_X hXJ]
  have hcardQ := Q.card_eq_multiplicity
  have hcardJ : Nat.card ↥J = Nat.card ↥(secJ a X J) :=
    Nat.card_congr (MulEquiv.ofBijective (secPsi a X J) ⟨hinj, secPsi_surjective⟩).toEquiv
  have hcard : Nat.card ↥(X.subgroupOf J) = p ^ (Nat.card ↥J).factorization p := by
    rw [hcardJ, ← hcardQ, ← hS']
    exact (Subgroup.card_map_of_injective hinj).symm
  refine ⟨Sylow.ofCard (X.subgroupOf J) hcard, ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hXJ

theorem sl2_final (F : E4Hyp G z k) {c : E4Ctx G z A a p X} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J))
    (hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J) :
    C43b p X ∨ C43e X := by
  have : Fact p.Prime := ⟨c.A4.prime⟩
  have hJK : J ≤ ncl X := comp_le_ncl d.comp d.JX
  have hnclN : (ncl X).Normal := Subgroup.normalClosure_normal
  have hJn : J.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : J.map (MulAut.conj g).toMonoidHom = J := by
      refine hcomp _ (isComponent_conj d.comp g) ?_
      rintro _ ⟨m, hm, rfl⟩
      exact hnclN.conj_mem m (hJK hm) g
    have : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    rwa [hconj] at this
  have hR := d.R_comm F h
  have hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A) := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR)
    · exact c.a41 q hq hq2
  have hncl : ncl X = J :=
    ncl_eq_of_single_comp c.A4.prime c.A4.pgroup c.op d.comp hJn hJK (d.X_le_sup h) hcomp hF
  have hXJ : X ≤ J := hncl ▸ (Subgroup.le_normalClosure : X ≤ ncl X)
  obtain ⟨F₀, hF₀, hFin, hodd, h3, ⟨eK⟩, h9⟩ := Sl2Cl.model c.A4.prime c.A4.odd h
  obtain ⟨eS⟩ := secJ_equiv d.hyp
  have hN1 : pPrimeCoreOf 2 J = ⊥ :=
    pPrimeCoreOf_eq_bot_of_sl2 d.comp hJn hodd h3 (eS.symm.trans eK) (fun h9' => (h9 h9') ▸ c.op)
  have hker := secPsi_ker_eq_bot d.hyp hN1
  have e : ↥J ≃* ↥(secJ a X J) := secPsiEquiv d.hyp hN1
  rcases h with ha | hb
  · obtain ⟨hSL, hX3, -, -, -⟩ := ha
    refine Or.inr ⟨?_, ?_⟩
    · rw [hncl]
      exact Transport.hasSL2Model_of_mulEquiv e.symm hSL
    · exact (card_X_eq_secX hXJ hker).trans hX3
  · obtain ⟨n, hn3, hSL, hSyl, -⟩ := hb
    refine Or.inl ⟨n, hn3, ?_, ?_⟩
    · rw [hncl]
      exact Transport.hasSL2Model_of_mulEquiv e.symm hSL
    · rw [hncl]
      exact isSylowOf_of_secPsi hXJ hker hSyl

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
