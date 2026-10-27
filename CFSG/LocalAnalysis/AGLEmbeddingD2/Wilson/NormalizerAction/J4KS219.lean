module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0Struct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.SylowExp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.PartTwo.Sec21 CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2
  CFSG.AGLEmbeddingD2.Wilson.Census219 Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem pow_three_of_conj {G : Type*} [Group G] {a b g : G} (h : g * a * g⁻¹ = b)
    (hb : b ^ 3 = 1) : a ^ 3 = 1 := by
  have : a = g⁻¹ * b * g := by rw [← h]; group
  have h3 := conj_pow (a := g⁻¹) (b := b) (i := 3)
  rw [this]
  simpa [hb] using h3

theorem layer_centralizer_transport {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X)
    (hK : CFSG.inSubgroup CFSG.layer (centralizer ({φ x} : Set Y)) = centralizer ({φ x} : Set Y)) :
    CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) = centralizer ({x} : Set X) ∧
      Nonempty (↥(centralizer ({x} : Set X)) ≃* ↥(centralizer ({φ x} : Set Y))) := by
  have hmap := Proving.map_inSubgroup_layer_centralizer φ x
  rw [hK] at hmap
  have hCmap := Proving.centralizer_map_mulEquiv_wilson φ x
  refine ⟨?_, ⟨(φ.subgroupMap _).trans (MulEquiv.subgroupCongr hCmap)⟩⟩
  exact Subgroup.map_injective φ.injective (hmap.trans hCmap.symm)

theorem card_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) :
    Nat.card ↥(center A) = Nat.card ↥(center B) := by
  rw [← Coordinator.KS219.map_center_mulEquiv f]
  exact (Subgroup.card_map_of_injective f.injective).symm

theorem qs_centralizer_transport {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X)
    (h : CFSG.IsQuasisimple ↥(centralizer ({x} : Set X))) :
    CFSG.IsQuasisimple ↥(centralizer ({φ x} : Set Y)) := by
  have e : ↥(centralizer ({x} : Set X)) ≃* ↥(centralizer ({φ x} : Set Y)) :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (Proving.centralizer_map_mulEquiv_wilson φ x))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e h

noncomputable def centralizerEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    ↥(centralizer ({x} : Set X)) ≃* ↥(centralizer ({φ x} : Set Y)) :=
  (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (Proving.centralizer_map_mulEquiv_wilson φ x))

theorem ks219J4_of_data {X A : Type*} [Group X] [Group A] (x : X) (E : Subgroup X) (hxE : x ∈ E)
    (F : ↥E ≃* A) (hc6 : Nat.card ↥(center A) = 6)
    (hM : Nonempty ((A ⧸ center A) ≃* ↥CFSG.Blueprint.NativeSporadic.M22)) :
    x ∈ E ∧ Nat.card ↥(center ↥E) = 6 ∧
      Nonempty (↥E ⧸ center ↥E ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  refine ⟨hxE, ?_, ?_⟩
  · rw [card_center_of_mulEquiv F]; exact hc6
  · obtain ⟨m⟩ := hM
    exact ⟨(QuotientGroup.congr _ _ F (Coordinator.KS219.map_center_mulEquiv F)).trans m⟩

section Final

theorem tE_pow_three {k : ℕ} (hk : k < 27) : tE (70 + k) ^ 3 = 1 := by
  by_cases h0 : k = 0
  · subst h0
    rw [show 70 + 0 = 70 from rfl, e0_eq_one]
    exact one_pow 3
  · exact pow_three_of_conj (G := J) (g_conj hk h0) (cE_pow_three matFacts)

theorem Q3J_pow_three {q : J} (hq : q ∈ Q3J) : q ^ 3 = 1 := by
  obtain ⟨m, rfl⟩ := hq
  exact tE_pow_three m.2

theorem pow_three_of_pPower_J {y : J} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pow_eq_one_of_pPower_of_exp 3 3 Q3J card_Q3J not_three_pow_four_dvd
    (fun q hq => Q3J_pow_three hq) hy

theorem centralizer_data_J (hF : J4Facts) (y : J) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({y} : Set J)) ∧
      Nonempty (↥(Subgroup.centralizer ({y} : Set J)) ≃* ↥LL) := by
  obtain ⟨g, hg⟩ := exists_conj_cE_of_orderThree y hy3 hy1
  have hcj : (MulAut.conj g) y = cE := by rw [MulAut.conj_apply]; exact hg
  have hC : Subgroup.centralizer ({(MulAut.conj g) y} : Set J) = LL := by
    rw [hcj]; exact (L0_eq_centralizer hF).symm
  have F : ↥(Subgroup.centralizer ({y} : Set J)) ≃* ↥LL :=
    (centralizerEquiv (MulAut.conj g) y).trans (MulEquiv.subgroupCongr hC)
  have hq0 : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({cE} : Set J)) := by
    rw [← L0_eq_centralizer hF]; exact isQuasisimple_LL hF
  have hq1 := qs_centralizer_transport (MulAut.conj g).symm cE hq0
  have hy : (MulAut.conj g).symm cE = y := by
    rw [← hcj]; exact (MulAut.conj g).symm_apply_apply y
  rw [hy] at hq1
  exact ⟨hq1, ⟨F⟩⟩

theorem ks219J4 (hF : J4Facts) : KS219J4 := by
  intro X _ _ ⟨e⟩ x hx1 hxc
  obtain ⟨S, -, -, k, hk⟩ := Census219.isCentral218_data hxc
  obtain ⟨eJ⟩ : Nonempty (X ≃* J) := ⟨e.trans (seedEquiv hF.mat)⟩
  have hy3 : (eJ x) ^ 3 = 1 := pow_three_of_pPower_J (k := k) (by rw [← map_pow, hk, map_one])
  have hy1 : eJ x ≠ 1 := fun h => hx1 (eJ.injective (h.trans (map_one eJ).symm))
  obtain ⟨hq, ⟨F0⟩⟩ := centralizer_data_J hF (eJ x) hy3 hy1
  have hlay := Proving.inSubgroup_layer_eq_self hq
  obtain ⟨hlayer, ⟨f'⟩⟩ := @layer_centralizer_transport X J _ inferInstance eJ x hlay
  have hxE : x ∈ CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set X)) := by
    rw [hlayer]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have FE : ↥(CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set X))) ≃* ↥LL :=
    (MulEquiv.subgroupCongr hlayer).trans (f'.trans F0)
  have hc6 : Nat.card ↥(center ↥LL) = 6 := card_center_LL hF
  have hM : Nonempty ((↥LL ⧸ center ↥LL) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) :=
    ⟨quotEquivM22 hF⟩
  exact @ks219J4_of_data X ↥LL _ _ x _ hxE FE hc6 hM

theorem ks219J4_holds : KS219J4 := ks219J4 j4Facts

end Final

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
