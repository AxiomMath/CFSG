module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Pa
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11T
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_perm_normalized [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∃ (Alt : Subgroup (Equiv.Perm (Fin 6))) (φ : (Fin 6 → ZMod 2) → G),
      (Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) ∧
        Sec11Perm (secA t S L) (secM t S L) Alt φ ∧
        t = φ (Pi.single 0 1) ∧ t * z = φ (Pi.single 1 1) := by
  classical
  obtain ⟨-, -, -, ht1, hz1, -, -, -, -⟩ := sec11L114_data hp hctx
  rcases hp.r10.l1011 G t L S z K1 K2 hctx.toSec10Ctx with h1 | h2
  · exact absurd h1 (sec11_not_alt1 hctx.hyp)
  obtain ⟨-, -, -, hcard6, hperm⟩ := h2
  obtain ⟨Alt, hAlt, φ0, hφ0⟩ : ∃ Alt : Subgroup (Equiv.Perm (Fin 6)),
      (Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) ∧ ∃ φ0 : (Fin 6 → ZMod 2) → G,
        IsPermModuleMod (n := 6) (fun _ => True) ({0, fun _ => 1} : Set (Fin 6 → ZMod 2))
          φ0 (secA t S L) ⊥ (secM t S L) Alt := by
    rcases hperm with ⟨φ0, h⟩ | ⟨φ0, h⟩
    · exact ⟨_, Or.inl rfl, φ0, h⟩
    · exact ⟨_, Or.inr rfl, φ0, h⟩
  have hm0 := Sec11Perm.of_isPermModuleMod hφ0
  have htA : t ∈ secA t S L := mem_sup_right (mem_zpowers t)
  obtain ⟨a, ha⟩ := sec11_cls_of_card hm0 hAlt htA ht1 hcard6
  obtain ⟨-, hcl, -, -⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  obtain ⟨m, hmT, hm⟩ : t * z ∈ conjClassIn T t := by
    rw [hcl]
    simp
  have hmM : m ∈ secM t S L := hctx.sylowT.1 hmT
  have hb := hm0.conj_single hmM a
  have htz : t * z = φ0 (Pi.single (hm0.rho m a) 1) := by
    calc t * z = m * t * m⁻¹ := hm
      _ = m * φ0 (Pi.single a 1) * m⁻¹ := by rw [← ha]
      _ = φ0 (Pi.single (hm0.rho m a) 1) := hb
  have hab : a ≠ hm0.rho m a := by
    intro h
    apply hz1
    have h2 : t * z = t * 1 := by rw [htz, ← h, ← ha, mul_one]
    exact mul_left_cancel h2
  obtain ⟨π, hπ0, hπ1⟩ := sec11_relabel_exists a (hm0.rho m a) hab
  haveI hN : Alt.Normal := by
    rcases hAlt with rfl | rfl
    · infer_instance
    · infer_instance
  refine ⟨Alt, fun v => φ0 (permVec π v), hAlt, hm0.relabel π, ?_, ?_⟩
  · show t = φ0 (permVec π (Pi.single 0 1))
    rw [sec11_permVec_single, hπ0]
    exact ha
  · show t * z = φ0 (permVec π (Pi.single 1 1))
    rw [sec11_permVec_single, hπ1]
    exact htz

theorem sec11_mem_B [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Perm (secA t S L) (secM t S L) Alt φ)
    (hAlt : Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) (ht : t = φ (Pi.single 0 1)) :
    ∀ v, φ v ∈ secB S L ↔ ∑ i, v i = 0 := by
  classical
  obtain ⟨-, -, htL, -, -, -⟩ := hp.basic G t L S z hctx.toSec10Z
  have htt : t * t = 1 := by
    rw [ht]
    exact hm.sq _
  have hzm : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hw : ∀ a : Fin 6, φ (Pi.single 0 1 + Pi.single a 1) ∈ secB S L := by
    intro a
    obtain ⟨σ, hσ1, hσa⟩ := sec11_trans 0 a
    have hσ : σ ∈ Alt := by
      rcases hAlt with rfl | rfl
      · exact Equiv.Perm.mem_alternatingGroup.mpr hσ1
      · exact Subgroup.mem_top _
    obtain ⟨m, hmM, hact⟩ := hm.act_surj σ hσ
    have h1 : m * t * m⁻¹ = φ (Pi.single a 1) := by
      rw [ht, hact, sec11_permVec_single, hσa]
    have hA : (m⁻¹)⁻¹ * t * m⁻¹ ∈ secA t S L := by
      rw [inv_inv, h1]
      exact hm.mem _
    obtain ⟨b, hb, hbe⟩ := (hp.r10.l1010 G t L S z K1 K2 hctx).2 m⁻¹ hA
    rw [inv_inv, h1] at hbe
    have hv : φ (Pi.single 0 1 + Pi.single a 1) = b := by
      rw [hm.mul, ← ht, hbe]
      calc t * (t * b) = (t * t) * b := by group
        _ = b := by rw [htt, one_mul]
    rw [hv]
    exact hb
  have hsum : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → φ v ∈ secB S L := by
    intro v hv
    let Bv : AddSubgroup (Fin 6 → ZMod 2) :=
      { carrier := {v | φ v ∈ secB S L}
        add_mem' := fun {x y} hx hy => by
          show φ (x + y) ∈ secB S L
          rw [hm.mul]
          exact (secB S L).mul_mem hx hy
        zero_mem' := by
          show φ 0 ∈ secB S L
          rw [hm.map_zero]
          exact (secB S L).one_mem
        neg_mem' := fun {x} hx => by
          show φ (-x) ∈ secB S L
          have hneg : -x = x := by
            funext i
            have key : ∀ c : ZMod 2, -c = c := by decide
            exact key _
          rw [hneg]
          exact hx }
    have hmem : ∑ i : Fin 5, v i.succ • (Pi.single 0 1 + Pi.single i.succ 1 : Fin 6 → ZMod 2) ∈
        Bv := by
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rcases hzm (v i.succ) with h | h
      · rw [h, zero_smul]
        exact Bv.zero_mem
      · rw [h, one_smul]
        exact hw i.succ
    rw [← sec11_decomp v hv] at hmem
    exact hmem
  intro v
  refine ⟨fun hv => ?_, hsum v⟩
  by_contra hne
  have hodd : ∑ i, v i = 1 := by
    rcases hzm (∑ i, v i) with h | h
    · exact absurd h hne
    · exact h
  have hev : ∑ i, (v + (Pi.single 0 1 : Fin 6 → ZMod 2)) i = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hodd]
    simp [Pi.single_apply]
    decide
  have hB' := hsum _ hev
  have htB : t ∈ secB S L := by
    have h3 : t = (φ v)⁻¹ * φ (v + Pi.single 0 1) := by
      rw [hm.mul, ← ht]
      group
    rw [h3]
    exact (secB S L).mul_mem ((secB S L).inv_mem hv) hB'
  exact htL (secB_le_L S L htB)

end CFSG.OddStandard.SmallF3.Omega
