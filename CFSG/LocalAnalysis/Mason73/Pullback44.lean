module

public import CFSG.ClassicalInvolution.QuaternionStructure.WitnessCore
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG CFSG.ClassicalInvolution.QuaternionStructure Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

abbrev preimageOddCore (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y)) : Subgroup G :=
  (M.comap (QuotientGroup.mk' (oddCore Y))).map Y.subtype

theorem preimageOddCore_le (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y)) :
    preimageOddCore Y M ≤ Y :=
  map_subtype_le _

theorem mem_preimageOddCore {Y : Subgroup G} {M : Subgroup (Y ⧸ oddCore Y)} {y : Y}
    (hy : QuotientGroup.mk' (oddCore Y) y ∈ M) : (y : G) ∈ preimageOddCore Y M :=
  ⟨y, hy, rfl⟩

theorem preimageOddCore_subgroupOf_normal (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y))
    [M.Normal] : ((preimageOddCore Y M).subgroupOf Y).Normal := by
  have h : (preimageOddCore Y M).subgroupOf Y = M.comap (QuotientGroup.mk' (oddCore Y)) :=
    comap_map_eq_self_of_injective Y.subtype_injective _
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

theorem exists_surjective_preimageOddCore (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y))
    [M.Normal] :
    ∃ θ : preimageOddCore Y M →* M, Function.Surjective θ ∧
      θ.ker = oddCore (preimageOddCore Y M) := by
  classical
  let π : Y →* Y ⧸ oddCore Y := QuotientGroup.mk' (oddCore Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let K : Subgroup Y := M.comap π
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance π
  have hOK : oddCore Y ≤ K := by
    intro x hx
    change π x ∈ M
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let eJ : preimageOddCore Y M ≃* K :=
    (Subgroup.equivMapOfInjective K Y.subtype Y.subtype_injective).symm
  let θ₀ : K →* M := (π.comp K.subtype).codRestrict M (fun x => x.2)
  have hθ₀ : Function.Surjective θ₀ := by
    intro m
    obtain ⟨x, hx⟩ := hπ (m : Y ⧸ oddCore Y)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ M
    rw [hx]
    exact m.2
  have hθ₀ker : θ₀.ker = (oddCore Y).subgroupOf K := by
    ext x
    change (θ₀ x = 1) ↔ _
    rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (x : Y)]
    exact Subtype.ext_iff
  have hOcoreK : oddCore K = (oddCore Y).subgroupOf K := oddCore_eq_subgroupOf K hOK
  refine ⟨θ₀.comp eJ.toMonoidHom, hθ₀.comp eJ.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hθ₀ker, ← hOcoreK,
    ← oddCore_map_mulEquiv eJ]
  have hinj : Function.Injective eJ.toMonoidHom := eJ.injective
  exact Subgroup.mem_map_iff_mem hinj

theorem nonempty_preimageOddCore_quotient_mulEquiv (Y : Subgroup G)
    (M : Subgroup (Y ⧸ oddCore Y)) [M.Normal] :
    Nonempty (preimageOddCore Y M ⧸ oddCore (preimageOddCore Y M) ≃* M) := by
  obtain ⟨θ, hθ, hker⟩ := exists_surjective_preimageOddCore Y M
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ)⟩

theorem witness_preimageOddCore_of_sl2 (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y))
    [M.Normal] {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) (e : M ≃* SL(2, F)) :
    CFSG.Open.classicalInvolutionWitness (preimageOddCore Y M) ∧
      ∃ S' : Sylow 2 (preimageOddCore Y M), ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup (preimageOddCore Y M)) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  classical
  obtain ⟨θ, hθ, hker⟩ := exists_surjective_preimageOddCore Y M
  let eQ : preimageOddCore Y M ⧸ oddCore (preimageOddCore Y M) ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  have hFodd : Odd (Nat.card F) := odd_natCard_of_ringChar_ne_two F hF
  refine ⟨Or.inl ?_, ?_⟩
  · have : Fintype F := Fintype.ofFinite F
    have hp : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
    have : Fintype (GaloisField (ringChar F) n) := Fintype.ofFinite _
    let eF : F ≃+* GaloisField (ringChar F) n :=
      FiniteField.ringEquivOfCardEq (by
        rw [hn, Fintype.card_eq_nat_card (α := GaloisField (ringChar F) n),
          GaloisField.card _ _ hn0])
    exact ⟨ringChar F, n, hp, hF, n.pos, ⟨(eQ.trans e).trans (slRingEquiv eF)⟩⟩
  · obtain ⟨S'⟩ : Nonempty (Sylow 2 (preimageOddCore Y M)) := inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow 2 SL(2, F)) := inferInstance
    let Θ : preimageOddCore Y M →* SL(2, F) := e.toMonoidHom.comp θ
    have hΘ : Function.Surjective Θ := e.surjective.comp hθ
    have hΘker : Θ.ker = θ.ker := by
      ext x
      change e (θ x) = 1 ↔ θ x = 1
      exact MulEquiv.map_eq_one_iff e
    obtain ⟨f⟩ := nonempty_sylow_equiv_of_surjective Θ hΘ
      (by rw [hΘker, hker]; exact odd_natCard_oddCore _) S' U
    obtain ⟨r, hr3, ⟨q⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hFodd U
    exact ⟨S', r, hr3, ⟨f.trans q⟩⟩

theorem openIsQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨?_, ?_⟩
  · have hs : Function.Surjective e.toMonoidHom := e.surjective
    rw [eq_top_iff, ← map_top_of_surjective _ hs, ← hperf, _root_.commutator_def,
      _root_.commutator_def, map_commutator, map_top_of_surjective _ hs]
  · exact (QuotientGroup.congr (center A) (center B) e
      (Subgroup.map_center_eq e)).symm.isSimpleGroup

theorem witness_preimageOddCore_of_a7 (Y : Subgroup G) (M : Subgroup (Y ⧸ oddCore Y))
    [M.Normal] (hq : CFSG.Open.IsQuasisimple M) (hc : Nat.card (center M) = 2)
    (e : M ⧸ center M ≃* alternatingGroup (Fin 7)) :
    CFSG.Open.classicalInvolutionWitness (preimageOddCore Y M) ∧
      ∃ S' : Sylow 2 (preimageOddCore Y M), ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup (preimageOddCore Y M)) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨eQ⟩ := nonempty_preimageOddCore_quotient_mulEquiv Y M
  have hw : CFSG.ClassicalInvolution.A7Witness (preimageOddCore Y M) := by
    refine ⟨openIsQuasisimple_of_mulEquiv eQ.symm hq, ?_, ⟨?_⟩⟩
    · rw [← hc]
      exact Nat.card_congr (Subgroup.centerCongr eQ).toEquiv
    · exact (QuotientGroup.congr _ _ eQ (Subgroup.map_center_eq eQ)).trans e
  obtain ⟨S'⟩ : Nonempty (Sylow 2 (preimageOddCore Y M)) := inferInstance
  exact ⟨Or.inr hw, S', CFSG.ClassicalInvolution.Hat2A7.exists_quaternion_sylow_of_witness hw S'⟩

end CFSG.LocalAnalysis.Mason73
