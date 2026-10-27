module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Hyp3Aux
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section CaseThree
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem hyp3_n (h : Setup28 W K S) (h3 : Hyp28Three W K S) :
    ∃ (n : ℕ) (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))),
      5 ≤ n ∧ ActsLikeSubRootFourCQ (bar W S) (bar W K) n e := by
  obtain ⟨⟨⟨hperf, hsimple, -⟩, -⟩, -, n, e, hact⟩ := h3
  refine ⟨n, e, ?_, hact⟩
  by_contra hlt
  have hn4 : n ≤ 4 := by omega
  haveI : Group.IsSolvable ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simpa using hn4)
  haveI : Group.IsSolvable (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsPerfect ↥(bar W K) := hperf
  haveI : Nontrivial (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) := hsimple.toNontrivial
  exact Group.IsPerfect.not_isSolvable (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) inferInstance

theorem glue_basic (h : Setup28 W K S) (hR : Red28 W K S) :
    ⁅khOf hR, khOf hR⁆ = khOf hR ∧ khOf hR ≠ ⊥ ∧ CFSG.pCore 2 ↥(khOf hR) = ⊥ :=
  ⟨Hyp3Aux.khOf_perfect h hR, Hyp3Aux.khOf_ne_bot hR, Hyp3Aux.pCore_khOf h hR⟩

theorem glue_pi (h : Setup28 W K S) (hR : Red28 W K S) {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    ∃ π : ↥(khOf hR) →* ↥(alternatingGroup (Fin n)), Function.Surjective π ∧
      π.ker = Subgroup.center ↥(khOf hR) ∧ ∀ k : ↥K, π (kToKh hR k) = e (modC W K k) := by
  obtain ⟨hsurj, hker⟩ := BlocksChief.piOf_props_aux (W := W) (K := K) e
  have hle : (kToKh hR).ker ≤ (piOf e).ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    exact (hker k).2 (Hyp3Aux.mem_zPre_of_kToKh_eq_one hR hk)
  let π : ↥(khOf hR) →* ↥(alternatingGroup (Fin n)) :=
    MonoidHom.liftOfSurjective (kToKh hR) (Hyp3Aux.kToKh_surjective hR) ⟨piOf e, hle⟩
  have hcomp : ∀ k, π (kToKh hR k) = piOf e k := fun k => by
    simp [π]
  refine ⟨π, ?_, ?_, fun k => (hcomp k).trans rfl⟩
  · intro a
    obtain ⟨k, hk⟩ := hsurj a
    exact ⟨kToKh hR k, by rw [hcomp, hk]⟩
  · ext x
    obtain ⟨k, rfl⟩ := Hyp3Aux.kToKh_surjective hR x
    rw [MonoidHom.mem_ker, hcomp, hker]
    exact ⟨fun hz => Hyp3Aux.kToKh_mem_center_of_zPre hR hz,
      fun hc => Hyp3Aux.mem_zPre_of_kToKh_mem_center hR hc⟩

theorem glue_act (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A)
    {n : ℕ} (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n)))
    (hact : ActsLikeSubRootFourCQ (bar W S) (bar W K) n e)
    (π : ↥(khOf hR) →* ↥(alternatingGroup (Fin n)))
    (hπ : ∀ k : ↥K, π (kToKh hR k) = e (modC W K k)) :
    ∃ Vv V₄ : Subgroup ↥(alternatingGroup (Fin n)), IsRootFour V₄ ∧ Vv ≤ V₄ ∧
      (∀ ε ∈ ehOf hR A, ∃ v ∈ Vv, ∀ k k' : ↥(khOf hR),
        (k' : MulAut ↥(vOf W K S)) = ε * k * ε⁻¹ → π k' = v * π k * v⁻¹) ∧
      (∀ v ∈ Vv, ∃ ε ∈ ehOf hR A, ∀ k k' : ↥(khOf hR),
        (k' : MulAut ↥(vOf W K S)) = ε * k * ε⁻¹ → π k' = v * π k * v⁻¹) := by
  have hAS : A ≤ S := hA.isMax.1
  obtain ⟨V₄, Vs, hV₄, hle, hcq⟩ := hact
  refine ⟨Hyp3Aux.vvOf W K (hAS.trans h.hN) e Vs, V₄, hV₄, fun v hv => hle hv.1, ?_, ?_⟩
  · intro ε hε
    obtain ⟨a, ha, haA, rfl⟩ := (Hyp3Aux.mem_ehOf_iff hR ε).1 hε
    obtain ⟨v, hvVs, hv⟩ := Hyp3Aux.exists_v_of_act h hcq.1 (hAS haA)
    exact ⟨v, ⟨hvVs, a, haA, hv⟩,
      (Hyp3Aux.act_transfer hR e π hπ ha (h.hN (hAS haA)) v).1 hv⟩
  · rintro v ⟨hvVs, a, haA, hv⟩
    have ha : a ∈ K ⊔ S := Subgroup.mem_sup_right (hAS haA)
    exact ⟨vAct hR ⟨a, ha⟩, (Hyp3Aux.mem_ehOf_iff hR _).2 ⟨a, ha, haA, rfl⟩,
      (Hyp3Aux.act_transfer hR e π hπ ha (h.hN (hAS haA)) v).1 hv⟩

theorem glue_misc (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A) :
    IsElemAbelian 2 (ehOf hR A) ∧ ehOf hR A ≤ Subgroup.normalizer (khOf hR : Set _) ∧
      (∀ ε ∈ ehOf hR A, (∀ k ∈ khOf hR, ε * k = k * ε) → ε = 1) ∧
      (fixV' (ehOf hR A)).index ≤ Nat.card ↥(ehOf hR A) :=
  ⟨(IsElemAbelian.subgroupOf (hA.isMax.2.1 : IsElemAbelian 2 A) (K ⊔ S)).map (vAct hR),
    Hyp3Aux.ehOf_le_normalizer h hR hA.isMax.1,
    fun ε hε hc => Hyp3Aux.ehOf_faithful h hR hA.isMax.1 hε hc,
    Hyp3Aux.fixV'_index_le hR hA⟩

theorem glue_card (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A) :
    Nat.card ↥(ehOf hR A) = Nat.card ↥(indAut W K A) := by
  rw [Hyp3Aux.card_ehOf hR hA.isMax.1, Hyp3Aux.card_indAut_eq h hA.isMax.1]

theorem glue_a7 (h : Setup28 W K S) (hR : Red28 W K S) (hs : A7Struct (khOf hR)) : A7X W K S :=
  Hyp3Aux.a7x_of_struct h hR hs

theorem rootFour_of_card (h : Setup28 W K S) {n : ℕ}
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))}
    (hact : ActsLikeSubRootFourCQ (bar W S) (bar W K) n e)
    (hge : 4 ≤ Nat.card ↥(indAut W K S)) : ActsLikeRootFourCQ (bar W S) (bar W K) n e :=
  Hyp3Aux.rootFour_of_card_aux h hact hge

end CaseThree

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
