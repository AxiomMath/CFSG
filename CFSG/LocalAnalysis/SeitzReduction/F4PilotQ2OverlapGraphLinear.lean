module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphBlock
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapGen
public import CFSG.GroupTheory.GL52.InvolutionsTransvection
public import CFSG.GroupTheory.GL52.InvolutionsTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp nsElt complSp complSpEquiv q2Embed q2Block
  q2Embed_mem_q2Block_iff spBlock_compl_singleton coe_complSpEquiv_apply planeCoordsQ2 q2Coord
  perfectCore_q2Block_inf_centralizer commutator_q2Block_eq card_planeCoordsQ2)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.Quasithin (perfectCore)

section Sub

variable {G : Type*} [Group G]

theorem map_subtype_centralizer_eq_inf (H : Subgroup G) (A : Subgroup H) :
    (centralizer (A : Set H)).map H.subtype = H ⊓ centralizer ((A.map H.subtype : Subgroup G) :
      Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hy a ha)
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, mem_centralizer_iff.2 fun a ha => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.1 hx a ⟨a, ha, rfl⟩

theorem centralizer_zpowers_twoLin (c : G) :
    centralizer ((zpowers c : Subgroup G) : Set G) = centralizer ({c} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

end Sub

section Iota

variable {K : Type} [Field K]

@[expose] noncomputable def twoLinIota (ε : ℕ) (hK : Nat.card K = 2) :
    StatedSp 3 K →* q2Block ε K ({3} : Finset (Fin 4)) :=
  ((q2Embed ε hK).comp ((complSp K (3 : Fin 4)).subtype.comp
    (complSpEquiv (K := K) (3 : Fin 4)).toMonoidHom)).codRestrict _ fun g =>
      (q2Embed_mem_q2Block_iff hK).2 (by
        rw [spBlock_compl_singleton]
        exact (complSpEquiv (K := K) (3 : Fin 4) g).2)

theorem coe_twoLinIota (ε : ℕ) (hK : Nat.card K = 2) (g : StatedSp 3 K) :
    ((twoLinIota ε hK g : q2Block ε K ({3} : Finset (Fin 4))) :
      SpecialLinearGroup (Fin (2 * 4 + ε)) K) =
      q2Embed ε hK (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective g) := by
  rw [← coe_complSpEquiv_apply]
  rfl

theorem coe_twoLinIota_nsElt (ε : ℕ) (hK : Nat.card K = 2) :
    ((twoLinIota ε hK (nsElt (0 : Fin 3)) : q2Block ε K ({3} : Finset (Fin 4))) :
      SpecialLinearGroup (Fin (2 * 4 + ε)) K) = q2Embed ε hK (nsElt (K := K) (0 : Fin 4)) := by
  rw [coe_twoLinIota, CFSG.SeitzReduction.SymplecticPilot.nsElt, spEmbed_longBlock]
  rfl

theorem coe_twoLinIota_elt_positiveLong (ε : ℕ) (hK : Nat.card K = 2) (c : K) :
    ((twoLinIota ε hK (elt (.positiveLong 1) c) : q2Block ε K ({3} : Finset (Fin 4))) :
      SpecialLinearGroup (Fin (2 * 4 + ε)) K) =
      q2Embed ε hK (elt (.positiveLong (1 : Fin 4)) c) := by
  rw [coe_twoLinIota, CFSG.SeitzReduction.SymplecticPilot.spEmbed_elt_positiveLong]
  rfl

end Iota

section Roots

variable {F : Type} [Field F]

theorem spEmbed_elt_positiveSum_of_lt {m n : ℕ} {σ : Fin m → Fin n}
    (hσ : Function.Injective σ) {a b : Fin m} (hab : a < b) (hab' : σ a < σ b) (c : F) :
    spEmbed σ hσ (elt (.positiveSum a b hab) c) = elt (.positiveSum (σ a) (σ b) hab') c := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_elt, mat_elt]
  have e : (1 + c • E F (.positiveSum a b hab) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) - 1 =
      c • E F (.positiveSum a b hab) := add_sub_cancel_left _ _
  rw [spEmbedMat, e]
  simp only [E, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    spIncl_mul_single_mul_transpose, Sum.map_inl, Sum.map_inr]

variable [Finite F]

theorem centralizer_map_rootGroup_eq {n : ℕ} (hF : Nat.card F = 2) {M : Type*} [Group M]
    (ι : StatedSp n F →* M) {γ : Fin n → ℤ} {r : TauCeti.GLSymplecticFin.RootSubgroupIndex n}
    (hr : Symplectic.stdVec r = Symplectic.toStd n γ) :
    centralizer (((Symplectic.rootGroup n F γ).map ι : Subgroup M) : Set M) =
      centralizer ({ι (elt r 1)} : Set M) := by
  ext x
  constructor
  · intro hx
    exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hx (ι (elt r 1))
      ⟨elt r 1, (mem_rootGroup_iff hr).2 ⟨1, rfl⟩, rfl⟩).symm)
  · intro hx
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hy
    rcases CFSG.SeitzReduction.SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hF c with
      rfl | rfl
    · rw [elt_zero, map_one, one_mul, mul_one]
    · exact (mem_centralizer_singleton_iff.1 hx).symm

end Roots

section IotaRoots

variable {K : Type} [Field K]

theorem coe_twoLinIota_elt_positiveSum (ε : ℕ) (hK : Nat.card K = 2) (c : K) :
    ((twoLinIota ε hK (elt (.positiveSum 1 2 (by decide)) c) :
      q2Block ε K ({3} : Finset (Fin 4))) : SpecialLinearGroup (Fin (2 * 4 + ε)) K) =
      q2Embed ε hK (elt (.positiveSum (1 : Fin 4) 2 (by decide)) c) := by
  rw [coe_twoLinIota, spEmbed_elt_positiveSum_of_lt _ (by decide) (by decide)]
  rfl

theorem stdVec_positiveLong_one :
    Symplectic.stdVec (.positiveLong (1 : Fin 3)) = Symplectic.toStd 3 twoOverlapRootL := by
  decide

theorem stdVec_positiveSum_one_two :
    Symplectic.stdVec (.positiveSum (1 : Fin 3) 2 (by decide)) =
      Symplectic.toStd 3 twoOverlapRootS := by
  decide

end IotaRoots

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_compl_planeCoordsQ2_three_zero (ε : ℕ) :
    ((planeCoordsQ2 ε ({3, 0} : Finset (Fin 4)))ᶜ).card = 4 + ε := by
  rw [Finset.card_compl, card_planeCoordsQ2, Fintype.card_fin,
    Finset.card_pair (by decide : (3 : Fin 4) ≠ 0)]
  omega

theorem map_centralizerPerfectCore_twoLinIota (ε : ℕ) (hK : Nat.card K = 2) :
    (centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoLinIota ε hK))).map
        (q2Block ε K ({3} : Finset (Fin 4))).subtype =
      q2Block ε K ({3, 0} : Finset (Fin 4)) := by
  rw [centralizerPerfectCore, CFSG.Quasithin.map_perfectCore, map_subtype_centralizer_eq_inf,
    Subgroup.map_map, CFSG.SeitzReduction.SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers,
    MonoidHom.comp_apply, coe_subtype, coe_twoLinIota_nsElt,
    centralizer_zpowers_twoLin]
  exact perfectCore_q2Block_inf_centralizer hK (by decide)
    (commutator_q2Block_eq (by rw [card_compl_planeCoordsQ2_three_zero]; omega))

end Levi

section Coords

@[expose] noncomputable def coordEquivOfList {n r : ℕ} (I : Finset (Fin n)) (σ : Fin r → Fin n)
    (hσ : Function.Injective σ) (hI : ∀ x, x ∈ I ↔ ∃ a, σ a = x) : I ≃ Fin r :=
  (Equiv.ofBijective (fun a => (⟨σ a, (hI _).2 ⟨a, rfl⟩⟩ : I))
    ⟨fun a b h => hσ (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := (hI x).1 x.2
      exact ⟨a, Subtype.ext ha⟩⟩).symm

theorem coe_coordEquivOfList_symm {n r : ℕ} (I : Finset (Fin n)) (σ : Fin r → Fin n)
    (hσ : Function.Injective σ) (hI : ∀ x, x ∈ I ↔ ∃ a, σ a = x) (a : Fin r) :
    ((coordEquivOfList I σ hσ hI).symm a : Fin n) = σ a := by
  rw [coordEquivOfList, Equiv.symm_symm]
  rfl

@[expose] def twoLinCoords7 : Fin 5 → (Fin 4 ⊕ Fin 4) ⊕ Fin 1 :=
  ![.inl (.inl 1), .inl (.inl 2), .inr 0, .inl (.inr 2), .inl (.inr 1)]

@[expose] def twoLinCoords6 : Fin 4 → (Fin 4 ⊕ Fin 4) ⊕ Fin 0 :=
  ![.inl (.inl 1), .inl (.inl 2), .inl (.inr 2), .inl (.inr 1)]

theorem twoLinCoords7_injective : Function.Injective twoLinCoords7 := by
  decide

theorem twoLinCoords6_injective : Function.Injective twoLinCoords6 := by
  decide

theorem mem_compl_planeCoordsQ2_iff7 (x : Fin (2 * 4 + 1)) :
    x ∈ (planeCoordsQ2 1 ({3, 0} : Finset (Fin 4)))ᶜ ↔
      ∃ a, (q2Coord 4 1 ∘ twoLinCoords7) a = x := by
  obtain ⟨y, rfl⟩ := (q2Coord 4 1).surjective x
  rw [Finset.mem_compl, CFSG.SeitzReduction.SymplecticPilot.q2Coord_mem_planeCoordsQ2]
  simp only [Function.comp_apply, (q2Coord 4 1).injective.eq_iff]
  revert y
  decide

theorem mem_compl_planeCoordsQ2_iff6 (x : Fin (2 * 4 + 0)) :
    x ∈ (planeCoordsQ2 0 ({3, 0} : Finset (Fin 4)))ᶜ ↔
      ∃ a, (q2Coord 4 0 ∘ twoLinCoords6) a = x := by
  obtain ⟨y, rfl⟩ := (q2Coord 4 0).surjective x
  rw [Finset.mem_compl, CFSG.SeitzReduction.SymplecticPilot.q2Coord_mem_planeCoordsQ2]
  simp only [Function.comp_apply, (q2Coord 4 0).injective.eq_iff]
  revert y
  decide

end Coords

section Seven

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def twoRingEquiv (hK : Nat.card K = 2) : K ≃+* ZMod 2 :=
  letI := Fintype.ofFinite K
  FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hK])

@[expose] noncomputable def twoLinEquiv7 :
    ((planeCoordsQ2 1 ({3, 0} : Finset (Fin 4)))ᶜ : Finset (Fin (2 * 4 + 1))) ≃ Fin 5 :=
  coordEquivOfList _ (q2Coord 4 1 ∘ twoLinCoords7)
    ((q2Coord 4 1).injective.comp twoLinCoords7_injective) mem_compl_planeCoordsQ2_iff7

theorem card_q2Block_three_zero_seven (hK : Nat.card K = 2) :
    Nat.card (q2Block 1 K ({3, 0} : Finset (Fin 4))) = 9999360 := by
  rw [q2Block, card_blockSpecialLinear_eq _ twoLinEquiv7 (twoRingEquiv hK), Matrix.card_GL_field]
  simp [Fin.prod_univ_five, ZMod.card]

theorem q2Embed_elt_positiveLong_mem_seven (hK : Nat.card K = 2) :
    q2Embed 1 hK (elt (.positiveLong (1 : Fin 4)) (1 : K)) ∈
      q2Block 1 K ({3, 0} : Finset (Fin 4)) :=
  (q2Embed_mem_q2Block_iff hK).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveLong_mem_spBlock (by decide) 1)

theorem q2Embed_elt_positiveSum_mem_seven (hK : Nat.card K = 2) :
    q2Embed 1 hK (elt (.positiveSum (1 : Fin 4) 2 (by decide)) (1 : K)) ∈
      q2Block 1 K ({3, 0} : Finset (Fin 4)) :=
  (q2Embed_mem_q2Block_iff hK).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveSum_mem_spBlock (by decide) (by decide)
      (by decide) 1)

set_option linter.unusedSimpArgs false in
theorem card_centralizer_transvection_seven (hK : Nat.card K = 2) :
    Nat.card (centralizer ({q2Embed 1 hK (elt (.positiveLong (1 : Fin 4)) (1 : K))} :
        Set (SpecialLinearGroup (Fin (2 * 4 + 1)) K)) ⊓ q2Block 1 K ({3, 0} : Finset (Fin 4)) :
      Subgroup (SpecialLinearGroup (Fin (2 * 4 + 1)) K)) = 21504 := by
  rw [q2Block, card_centralizer_inf_blockSpecialLinear_eq _ twoLinEquiv7 (twoRingEquiv hK)
    (q2Embed_elt_positiveLong_mem_seven hK) (g := CFSG.GroupTheory.GL52.invT0) ?_,
    CFSG.GroupTheory.GL52.inv_card_centralizer_t0]
  · norm_num
  intro a b
  rw [twoLinEquiv7, coe_coordEquivOfList_symm, coe_coordEquivOfList_symm, Function.comp_apply,
    Function.comp_apply, CFSG.SeitzReduction.SymplecticPilot.q2Embed_apply_q2Coord, mat_elt]
  fin_cases a <;> fin_cases b <;>
    simp [twoLinCoords7, E, CFSG.GroupTheory.GL52.invT0, CFSG.GroupTheory.GL52.invT0M,
      Matrix.one_apply, Matrix.single_apply]

set_option linter.unusedSimpArgs false in
theorem card_centralizer_rankTwo_seven (hK : Nat.card K = 2) :
    Nat.card (centralizer ({q2Embed 1 hK (elt (.positiveSum (1 : Fin 4) 2 (by decide)) (1 : K))} :
        Set (SpecialLinearGroup (Fin (2 * 4 + 1)) K)) ⊓ q2Block 1 K ({3, 0} : Finset (Fin 4)) :
      Subgroup (SpecialLinearGroup (Fin (2 * 4 + 1)) K)) = 1536 := by
  rw [q2Block, card_centralizer_inf_blockSpecialLinear_eq _ twoLinEquiv7 (twoRingEquiv hK)
    (q2Embed_elt_positiveSum_mem_seven hK) (g := CFSG.GroupTheory.GL52.invU0) ?_,
    CFSG.GroupTheory.GL52.inv_card_centralizer_u0]
  · norm_num
  intro a b
  rw [twoLinEquiv7, coe_coordEquivOfList_symm, coe_coordEquivOfList_symm, Function.comp_apply,
    Function.comp_apply, CFSG.SeitzReduction.SymplecticPilot.q2Embed_apply_q2Coord, mat_elt]
  fin_cases a <;> fin_cases b <;>
    simp [twoLinCoords7, E, CFSG.GroupTheory.GL52.invU0, CFSG.GroupTheory.GL52.invU0M,
      Matrix.one_apply, Matrix.single_apply]

theorem twoGraphModelValues_linear7 (hK : Nat.card K = 2) :
    TwoGraphModelValues .linear7 K (q2Block 1 K ({3} : Finset (Fin 4))) (twoLinIota 1 hK) := by
  have hO := map_centralizerPerfectCore_twoLinIota (K := K) 1 hK
  have hinj := (q2Block 1 K ({3} : Finset (Fin 4))).subtype_injective
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.card_map_of_injective hinj, hO, card_q2Block_three_zero_seven hK]
    rfl
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveLong_one,
      MonoidHom.comp_apply, coe_subtype, coe_twoLinIota_elt_positiveLong,
      card_centralizer_transvection_seven hK]
    rfl
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveSum_one_two,
      MonoidHom.comp_apply, coe_subtype, coe_twoLinIota_elt_positiveSum,
      card_centralizer_rankTwo_seven hK]
    rfl

end Seven

end CFSG.SeitzReduction.F4Pilot
