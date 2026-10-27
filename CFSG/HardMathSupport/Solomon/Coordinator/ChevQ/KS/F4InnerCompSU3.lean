module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4SU3

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem alpha_eq_one_of_beta_eq_one {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) (hperf : commutator K = ⊤) (hβ : β = 1) : α = 1 := by
  have hfix : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ fixSubgroup α := by
    rw [Subgroup.commutator_le]
    intro k₁ _ k₂ _
    exact comm_mem_fixSubgroup π hker α β hαβ (by rw [mem_fixSubgroup, hβ]; rfl)
      (by rw [mem_fixSubgroup, hβ]; rfl)
  rw [← _root_.commutator_def, hperf] at hfix
  refine MulEquiv.ext fun k => ?_
  exact mem_fixSubgroup.1 (hfix (Subgroup.mem_top k))

theorem mem_centralizer_of_actHom_eq_one {X : Type} [Group X] {J : Subgroup X}
    (hperf : ⁅J, J⁆ = J) {s : X} (hs : s ∈ Subgroup.normalizer (J : Set X))
    (h : actHom J ⟨s, hs⟩ = 1) : s ∈ Subgroup.centralizer (J : Set X) := by
  have hJp : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  have hker : (QuotientGroup.mk' (Subgroup.center ↥J)).ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
  have hα := alpha_eq_one_of_beta_eq_one (QuotientGroup.mk' (Subgroup.center ↥J)) hker
    (J.normalizerMonoidHom ⟨s, hs⟩) (actHom J ⟨s, hs⟩) (fun k => by
      change _ = actHom J ⟨s, hs⟩ (QuotientGroup.mk k)
      rw [actHom_mk]
      rfl) hJp.commutator_eq_top h
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := congrArg (fun f : MulAut ↥J => (f ⟨j, hj⟩ : X)) hα
  have h2 : s * j * s⁻¹ = j := by simpa using h1
  calc j * s = (s * j * s⁻¹) * s := by rw [h2]
    _ = s * j := by group

@[expose] def IsU3EightIndexTwo (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ d = .twistedA 2 q

theorem nonempty_equiv_projSU_of_model {G : Type} [Group G]
    (h : StatedClassicalModel G .PSU 3 2 3) : Nonempty (G ≃* CFSG.PGLModel.projSU 3 2 3) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let L := GaloisField 2 (2 * 3)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * 3) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (2 ^ 3))
    (glCongr_statedScalars φ)
  exact ⟨(e.trans e1).trans (CFSG.PGLModel.projSUEquivStatedProj 3 2 3).symm⟩

theorem nonempty_equiv_projSU_of_isLieQuot {Y : Type} [Group Y]
    (h : IsLieQuot Y IsU3EightIndexTwo) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* CFSG.PGLModel.projSU 3 2 3) := by
  obtain ⟨⟨d, hv⟩, ⟨q, hq, rfl⟩, ⟨φ⟩⟩ := h
  obtain ⟨hp2, he3⟩ := hq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv φ
  rw [hp2, he3] at hm
  obtain ⟨e⟩ := nonempty_equiv_projSU_of_model hm
  exact ⟨e⟩

@[expose] def AutImageRankThree {X : Type} [Group X] (B J : Subgroup X) : Prop :=
  ∃ E : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)), E ≤ autImage B J ∧
    CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27

section K0

set_option linter.unusedSectionVars false

theorem centralizes_of_autImageRankThree {X : Type} [Group X] [Finite X] {B J S : Subgroup X}
    (hperf : ⁅J, J⁆ = J)
    (hJ : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* CFSG.PGLModel.projSU 3 2 3))
    (hE : AutImageRankThree B J) (hSN : S ≤ Subgroup.normalizer (J : Set X))
    (hS3 : Nat.Coprime 3 (Nat.card S))
    (hBS : B ⊓ Subgroup.normalizer (J : Set X) ≤ Subgroup.normalizer (S : Set X)) :
    S ≤ Subgroup.centralizer (J : Set X) := by
  obtain ⟨E, hEA, hEel, hE27⟩ := hE
  set N := Subgroup.normalizer (J : Set X) with hN
  set Y : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    (S.subgroupOf N).map (actHom J) with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    have h1 : Nat.card Y ∣ Nat.card (S.subgroupOf N) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (S.subgroupOf N) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    have h4 : 3 ∣ Nat.card S := h2 ▸ h3.trans h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hS3 h4
  have hstable : ∀ e ∈ E, ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
    intro e he y hy
    obtain ⟨x, hxN, hxB, rfl⟩ := mem_autImage.1 (hEA he)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
    have hxS : x ∈ Subgroup.normalizer (S : Set X) := hBS ⟨hxB, hxN⟩
    have hnS : (n : X) ∈ S := Subgroup.mem_subgroupOf.1 hn
    have hconj : x * (n : X) * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hxS _).1 hnS
    have hconjN : x * (n : X) * x⁻¹ ∈ N := by
      have h1 : x ∈ N := hxN
      have h2 : (n : X) ∈ N := n.2
      exact N.mul_mem (N.mul_mem h1 h2) (N.inv_mem h1)
    refine Subgroup.mem_map.2 ⟨⟨x * (n : X) * x⁻¹, hconjN⟩,
      Subgroup.mem_subgroupOf.2 hconj, ?_⟩
    rw [show (⟨x * (n : X) * x⁻¹, hconjN⟩ : N) = ⟨x, hxN⟩ * n * ⟨x, hxN⟩⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hEY : E ≤ Subgroup.normalizer (Y : Set (MulAut (↥J ⧸ Subgroup.center ↥J))) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hstable e he y hy, fun hy => ?_⟩
    have := hstable e⁻¹ (E.inv_mem he) _ hy
    simpa [mul_assoc] using this
  have hY1 : Y = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.Item434U38.u38K0 (↥J ⧸ Subgroup.center ↥J) hJ E hEel hE27 Y hY3
      hEY
  intro s hs
  refine mem_centralizer_of_actHom_eq_one hperf (hSN hs) ?_
  have hmem : actHom J ⟨s, hSN hs⟩ ∈ Y :=
    Subgroup.mem_map.2 ⟨⟨s, hSN hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  rw [hY1] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem isStronglyLocallyOneBalanced_of_autImageRankThree {X : Type} [Group X] [Finite X]
    {B J : Subgroup X} {b : X} (hperf : ⁅J, J⁆ = J) (hL : IsLieQuot ↥J IsU3EightIndexTwo)
    (hE : AutImageRankThree B J) : IsStronglyLocallyOneBalanced 3 B b J :=
  KSF4Kit.isStronglyLocallyOneBalanced_of_centralizes fun S hS hcop hBS =>
    centralizes_of_autImageRankThree hperf (nonempty_equiv_projSU_of_isLieQuot hL) hE
      (hS.trans inf_le_left) hcop hBS

end K0

end KSF4SU3

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
