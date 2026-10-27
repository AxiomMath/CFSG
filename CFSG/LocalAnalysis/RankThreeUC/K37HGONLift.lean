module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.LocalAnalysis.GLTheoremB (quotientCenterAut' quotientCenterAut'_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def k37GAct (K : Subgroup X) [K.Normal] :
    X →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (quotientCenterAut' ↥K).comp MulAut.conjNormal

theorem k37GAct_mk (K : Subgroup X) [K.Normal] (x : X) (k : ↥K) :
    k37GAct K x (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal x k) :=
  rfl

theorem k37GAct_coe (K : Subgroup X) [K.Normal] (k : ↥K) :
    k37GAct K (k : X) = MulAut.conj (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [k37GAct_mk, MulAut.conjNormal_val, MulAut.conj_apply]
    rfl

theorem k37GAct_eq_one_iff (K : Subgroup X) [K.Normal] (hperf : commutator ↥K = ⊤) (x : X) :
    k37GAct K x = 1 ↔ x ∈ Subgroup.centralizer (K : Set X) := by
  constructor
  · intro h
    have h1 : (MulAut.conjNormal x : MulAut ↥K) = 1 :=
      quotientCenterAut'_injective hperf (h.trans (map_one (quotientCenterAut' ↥K)).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc k * x = (x * k * x⁻¹) * x := by rw [h2]
      _ = x * k := by group
  · intro hx
    have h1 : (MulAut.conjNormal x : MulAut ↥K) = 1 := by
      ext k
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.mp hx k k.2
      rw [← this]
      group
    show quotientCenterAut' ↥K (MulAut.conjNormal x) = 1
    rw [h1, map_one]

theorem k37G_inf_centralizer_eq_bot {K E S : Subgroup X} (hs : K37Setting X K E S) :
    E ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  by_contra hBC
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBC
  have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  have hKcent : K ≤ Subgroup.centralizer ({e} : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp he.2 k hk
  exact hs.not_le (hKcent.trans
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma hs.elem he.1 he1'))

theorem k37G_exists_lift {K E S : Subgroup X} (hs : K37Setting X K E S)
    (hout : ¬ 3 ∣ Nat.card (Outer (↥K ⧸ Subgroup.center ↥K))) {e : X} (he : e ∈ E) :
    ∃ k : ↥K, (k : X)⁻¹ * e ∈ Subgroup.centralizer (K : Set X) := by
  haveI := hs.normal
  have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp hs.quasi.1
  have hα3 : (k37GAct K e) ^ 3 = 1 := by
    rw [← map_pow, hs.elem.2 e he, map_one]
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_range_conj_of_pow_three hout hα3
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨k, (k37GAct_eq_one_iff K hperf _).mp ?_⟩
  rw [map_mul, map_inv, k37GAct_coe, ← ha]
  exact inv_mul_cancel _

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
