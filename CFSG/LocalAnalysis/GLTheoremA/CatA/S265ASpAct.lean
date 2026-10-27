module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.PLayer.Transport
import CFSG.LieType.Universal.Symplectic
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
import CFSG.Open.StatedAPI
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {Ω : Type} [Group Ω] [Finite Ω] {J : Subgroup Ω} {n : ℕ}

private theorem centralizer_eq_fixSubgroup_conj {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) = fixSubgroup (MulAut.conj x) := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem layer_centralizer_iff_of_congr {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] {e : G ≃* H} {α : MulAut G} {s : H} (h : MulAut.congr e α = MulAut.conj s) :
    GLAPLayer 3 (Subgroup.centralizer ({s} : Set H)) = ⊥ ↔ GLAPLayer 3 (fixSubgroup α) = ⊥ := by
  rw [centralizer_eq_fixSubgroup_conj, ← h, CFSG.glaPLayer_fixSubgroup_congr Nat.prime_three e α]
  exact Subgroup.map_eq_bot_iff_of_injective _ e.injective

private theorem conjSp_injective (n : ℕ) :
    Function.Injective (MulAut.conj : StatedSp n (ZMod 2) →* MulAut (StatedSp n (ZMod 2))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (StatedSp n (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := congrArg (fun α : MulAut (StatedSp n (ZMod 2)) => α y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hy
    exact (mul_inv_eq_iff_eq_mul.1 hy).symm
  rwa [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.mem_bot] at hc

private noncomputable def conjSpEquiv (hn : 3 ≤ n) :
    StatedSp n (ZMod 2) ≃* MulAut (StatedSp n (ZMod 2)) :=
  MulEquiv.ofBijective MulAut.conj ⟨conjSp_injective n, fun α => by
    obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d.all_inner_spTwo hn α
    exact ⟨g, hg.symm⟩⟩

theorem exists_spHom (hn : 3 ≤ n) (e : PSimple 3 J ≃* StatedSp n (ZMod 2)) :
    ∃ ψ : ↥(Subgroup.normalizer (J : Set Ω)) →* StatedSp n (ZMod 2),
      (∀ g, MulAut.congr e (chevAut 3 J g) = MulAut.conj (ψ g)) ∧
      (∀ g, ψ g = 1 ↔ chevAut 3 J g = 1) ∧
      ∀ g, GLAPLayer 3 (Subgroup.centralizer ({ψ g} : Set (StatedSp n (ZMod 2)))) = ⊥ ↔
        GLAPLayer 3 (fixSubgroup (chevAut 3 J g)) = ⊥ := by
  let c := conjSpEquiv hn
  let ψ : ↥(Subgroup.normalizer (J : Set Ω)) →* StatedSp n (ZMod 2) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (chevAut 3 J))
  have h1 : ∀ g, MulAut.congr e (chevAut 3 J g) = MulAut.conj (ψ g) := fun g =>
    (c.apply_symm_apply (MulAut.congr e (chevAut 3 J g))).symm
  exact ⟨ψ, h1, fun g => (c.symm.map_eq_one_iff (x := MulAut.congr e (chevAut 3 J g))).trans
    (MulAut.congr e).map_eq_one_iff, fun g => layer_centralizer_iff_of_congr (h1 g)⟩

theorem exists_spImage {X B D : Subgroup Ω} (hn : 3 ≤ n) (e : PSimple 3 J ≃* StatedSp n (ZMod 2))
    (hN : NLAct 3 X J B D) (hB : IsElemAbelian 3 B) :
    ∃ Ab : Subgroup (StatedSp n (ZMod 2)), IsElemAbelian 3 Ab ∧
      Nat.card Ab * Nat.card D = Nat.card B ∧
      ∀ s ∈ Ab, s ≠ 1 →
        GLAPLayer 3 (Subgroup.centralizer ({s} : Set (StatedSp n (ZMod 2)))) = ⊥ := by
  obtain ⟨ψ, -, h2, h3⟩ := exists_spHom hn e
  let φ : ↥B →* StatedSp n (ZMod 2) := ψ.comp (Subgroup.inclusion hN.norm)
  have hker : φ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (h2 (Subgroup.inclusion hN.norm b)).trans (hN.ker b b.2 (hN.norm b.2))
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hB.subgroupOf B).map φ
  · rw [← Subgroup.card_ker_mul_card_range φ, hker, mul_comm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.le).toEquiv]
  · rintro _ ⟨b, rfl⟩ hs
    have hbD : (b : Ω) ∉ D := fun hbD =>
      hs ((h2 (Subgroup.inclusion hN.norm b)).2 ((hN.ker b b.2 (hN.norm b.2)).2 hbD))
    exact (h3 (Subgroup.inclusion hN.norm b)).2 (hN.layer b b.2 hbD (hN.norm b.2))

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
