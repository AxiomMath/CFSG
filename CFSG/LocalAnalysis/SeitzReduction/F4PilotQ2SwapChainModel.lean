module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapOverlap

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect
  perfectCore_mono)
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp complSp spBlock)

theorem eq_one_of_mem_centralizer_of_index_two {M : Type*} [Group M] {H O : Subgroup M}
    (hidx : (O.subgroupOf H).index = 2)
    (hZO : ∀ o ∈ O, (∀ o' ∈ O, o * o' = o' * o) → o = 1)
    (hZH : ∀ h ∈ H, (∀ h' ∈ H, h * h' = h' * h) → h = 1)
    {n : M} (hn : n ∈ H) (hc : ∀ o ∈ O, n * o = o * n) : n = 1 := by
  by_cases hnO : n ∈ O
  · exact hZO n hnO hc
  refine hZH n hn fun h hh => ?_
  by_cases hhO : h ∈ O
  · exact hc h hhO
  have hmem : (⟨n, hn⟩⁻¹ * ⟨h, hh⟩ : H) ∈ O.subgroupOf H := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, mem_subgroupOf, mem_subgroupOf]
    simp only [InvMemClass.coe_inv, inv_mem_iff]
    exact iff_of_false hnO hhO
  rw [mem_subgroupOf] at hmem
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hmem
  have hc' := hc _ hmem
  calc n * h = n * (n * (n⁻¹ * h)) := by group
    _ = n * ((n⁻¹ * h) * n) := by rw [hc']
    _ = h * n := by group

section Sp

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem perfectCore_centralizer_nsTorusSp_eq_complSp (hK : Nat.card K = 2) {n : ℕ} (k : Fin n) :
    perfectCore (centralizer (nsTorusSp K k : Set (StatedSp n K))) = perfectCore (complSp K k) := by
  set H := centralizer (nsTorusSp K k : Set (StatedSp n K)) with hH
  have hcomm : ⁅H, H⁆ ≤ complSp K k := by
    refine commutator_le.2 fun g hg g' hg' => ?_
    rw [commutatorElement_def]
    exact SymplecticPilot.commutator_mem_complSp_of_mem_centralizer_nsTorusSp hK k hg hg'
  apply le_antisymm
  · refine le_perfectCore_of_perfect ?_ (perfectCore_perfect H)
    calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := hcomm
  · exact perfectCore_mono (SymplecticPilot.complSp_le_centralizer_nsTorusSp k)

theorem perfectCore_complSp_facts (hK : Nat.card K = 2) :
    IsSimpleGroup (perfectCore (complSp K (0 : Fin 3))) ∧
      center (perfectCore (complSp K (0 : Fin 3))) = ⊥ ∧
      ((perfectCore (complSp K (0 : Fin 3))).subgroupOf (complSp K (0 : Fin 3))).index = 2 := by
  have hN : (({0}ᶜ : Finset (Fin 3))).card = 2 := by decide
  have hsp : spBlock K ({0}ᶜ : Finset (Fin 3)) = complSp K (0 : Fin 3) :=
    SymplecticPilot.spBlock_compl_singleton 0
  obtain ⟨hS, hZ, hle⟩ := SymplecticPilot.perfectCore_spBlock_of_card_two hK (N := {0}ᶜ)
    (by rw [hN])
  rw [hsp] at hS hZ hle
  refine ⟨hS, hZ, ?_⟩
  set H := complSp K (0 : Fin 3) with hHdef
  obtain ⟨e6⟩ := SymplecticPilot.nonempty_statedSp_mulEquiv_perm_of_eq hK hN
  have eH : H ≃* Equiv.Perm (Fin 6) :=
    ((MulEquiv.subgroupCongr hsp).symm.trans
      (SymplecticPilot.spBlockEquiv ({0}ᶜ : Finset (Fin 3))).symm).trans e6
  obtain ⟨ψ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating eH
  have hcore : perfectCore H = ⁅H, H⁆ :=
    le_antisymm (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1) hle
  have hcardH : Nat.card H = 2 * Nat.card (perfectCore H) := by
    rw [Nat.card_congr eH.toEquiv, hcore, Nat.card_congr ψ.toEquiv,
      two_mul_nat_card_alternatingGroup]
  have h1 := Subgroup.card_mul_index ((perfectCore H).subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (perfectCore_le H)).toEquiv, hcardH,
    mul_comm 2] at h1
  have hpos : 0 < Nat.card (perfectCore H) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem centralizer_perfectCore_inf_centralizer_le (hK : Nat.card K = 2) :
    centralizer (perfectCore (complSp K (0 : Fin 3)) : Set (StatedSp 3 K)) ⊓
        centralizer (nsTorusSp K (0 : Fin 3) : Set (StatedSp 3 K)) ≤ nsTorusSp K (0 : Fin 3) := by
  obtain ⟨-, hZO, hidx⟩ := perfectCore_complSp_facts hK
  rintro z ⟨hzO, hzX⟩
  have hz := (mem_centralizer_iff.1 hzX _ (SymplecticPilot.nsElt_mem_nsTorusSp (K := K) 0)).symm
  obtain ⟨a, ha, y, hy, rfl⟩ := SymplecticPilot.exists_eq_mul_of_commute_nsElt hK hz
  have hya : ∀ o ∈ perfectCore (complSp K (0 : Fin 3)), a * o = o * a := fun o ho =>
    (mem_centralizer_iff.1 (SymplecticPilot.complSp_le_centralizer_nsTorusSp 0
      (perfectCore_le _ ho)) a ha)
  have hyO : ∀ o ∈ perfectCore (complSp K (0 : Fin 3)), y * o = o * y := by
    intro o ho
    have h1 := mem_centralizer_iff.1 hzO o ho
    have h2 := hya o ho
    calc y * o = a⁻¹ * (a * y * o) := by group
      _ = a⁻¹ * (o * (a * y)) := by rw [h1]
      _ = a⁻¹ * (o * a) * y := by group
      _ = a⁻¹ * (a * o) * y := by rw [h2]
      _ = o * y := by group
  have hZH : ∀ h ∈ complSp K (0 : Fin 3), (∀ h' ∈ complSp K (0 : Fin 3), h * h' = h' * h) →
      h = 1 := by
    intro h hh hc
    have hZ := SymplecticPilot.center_spBlock_eq_bot (F := K) ({0}ᶜ : Finset (Fin 3))
    rw [SymplecticPilot.spBlock_compl_singleton] at hZ
    have hm : (⟨h, hh⟩ : complSp K (0 : Fin 3)) ∈ center (complSp K (0 : Fin 3)) :=
      mem_center_iff.2 fun g => Subtype.ext (hc g g.2).symm
    rw [hZ, mem_bot] at hm
    exact congrArg Subtype.val hm
  have hZO' : ∀ o ∈ perfectCore (complSp K (0 : Fin 3)),
      (∀ o' ∈ perfectCore (complSp K (0 : Fin 3)), o * o' = o' * o) → o = 1 := by
    intro o ho hc
    have hm : (⟨o, ho⟩ : perfectCore (complSp K (0 : Fin 3))) ∈
        center (perfectCore (complSp K (0 : Fin 3))) :=
      mem_center_iff.2 fun g => Subtype.ext (hc g g.2).symm
    rw [hZO, mem_bot] at hm
    exact congrArg Subtype.val hm
  have hy1 : y = 1 := eq_one_of_mem_centralizer_of_index_two hidx hZO' hZH hy hyO
  rw [hy1, mul_one]
  exact ha

end Sp

section Map

variable {M N : Type*} [Group M] [Group N]

theorem map_inf_centralizer_map {f : M →* N} (hf : Function.Injective f) (A B : Subgroup M) :
    A.map f ⊓ centralizer ((B.map f : Subgroup N) : Set N) =
      (A ⊓ centralizer (B : Set M)).map f := by
  ext g
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    have hc' := mem_centralizer_iff.1 hc
    refine ⟨a, ⟨ha, mem_centralizer_iff.2 fun x hx => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc' _ ⟨x, hx, rfl⟩
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    have hc' := mem_centralizer_iff.1 hc
    refine ⟨⟨a, ha, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hc' x hx]

theorem le_normalizer_perfectCore_self [Finite M] (H : Subgroup M) :
    H ≤ normalizer (perfectCore H : Set M) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  have hH : H.map (MulAut.conj h).toMonoidHom = H := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hh hz) (inv_mem hh)
    · intro hy
      refine ⟨h⁻¹ * y * h, mul_mem (mul_mem (inv_mem hh) hy) hh, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hP : (perfectCore H).map (MulAut.conj h).toMonoidHom = perfectCore H := by
    rw [CFSG.Quasithin.map_perfectCore, hH]
  constructor
  · intro hx
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hP] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzx
    have : z = x := mul_left_cancel (mul_right_cancel hzx)
    rwa [← this]

end Map

section Std


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def stdX : Subgroup (adjointGroup .F4 K) :=
  (nsTorusSp K (0 : Fin 3)).map (c3LeviHom K)

@[expose] noncomputable def stdB : Subgroup (adjointGroup .F4 K) :=
  (complSp K (0 : Fin 3)).map (c3LeviHom K)

theorem twoStdPairFacts_std (hK : Nat.card K = 2) : TwoStdPairFacts K (stdX K) (stdB K) := by
  set ι := c3LeviHom K with hι
  have hinj : Function.Injective ι := c3LeviHom_injective
  have hD : C3Levi K = (⊤ : Subgroup (StatedSp 3 K)).map ι := by
    rw [← MonoidHom.range_eq_map, range_c3LeviHom]
  have : Finite (StatedSp 3 K) := inferInstance
  have hO : stdOverlap K (stdX K) = (perfectCore (complSp K (0 : Fin 3))).map ι := by
    rw [stdOverlap, stdX, hD, map_inf_centralizer_map hinj, top_inf_eq,
      ← CFSG.Quasithin.map_perfectCore, perfectCore_centralizer_nsTorusSp_eq_complSp hK]
  have hZ : stdOverlapCentralizer K (stdX K) =
      (centralizer (perfectCore (complSp K (0 : Fin 3)) : Set (StatedSp 3 K)) ⊓
        centralizer (nsTorusSp K (0 : Fin 3) : Set (StatedSp 3 K))).map ι := by
    rw [stdOverlapCentralizer, hO, stdX, hD, map_inf_centralizer_map hinj, top_inf_eq,
      map_inf_centralizer_map hinj]
  obtain ⟨hS, hZO, -⟩ := perfectCore_complSp_facts hK
  have hle := centralizer_perfectCore_inf_centralizer_le hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stdX, hD]
    exact Subgroup.map_mono le_top
  · rw [stdB, hD]
    exact Subgroup.map_mono le_top
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul,
      mem_centralizer_iff.1 (SymplecticPilot.complSp_le_centralizer_nsTorusSp 0 hy) x hx]
  · rw [hO]
    exact ((perfectCore (complSp K (0 : Fin 3))).equivMapOfInjective ι hinj).symm.isSimpleGroup
  · rw [hO]
    exact center_eq_bot_congr
      ((perfectCore (complSp K (0 : Fin 3))).equivMapOfInjective ι hinj) hZO
  · rw [hZ, Nat.card_congr ((centralizer (perfectCore (complSp K (0 : Fin 3)) :
      Set (StatedSp 3 K)) ⊓ centralizer (nsTorusSp K (0 : Fin 3) :
        Set (StatedSp 3 K))).equivMapOfInjective ι hinj).toEquiv.symm]
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [SymplecticPilot.card_nsTorusSp] at hdvd
    exact Odd.of_dvd_nat (by decide) hdvd
  · rw [stdB, hO]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨o, ho, rfl⟩
      refine ⟨y * o * y⁻¹, (mem_normalizer_iff.1 (le_normalizer_perfectCore_self _ hy) o).1 ho, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hg
      obtain ⟨o, ho, hoe⟩ := hg
      refine ⟨y⁻¹ * o * y, ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.1 (le_normalizer_perfectCore_self _ (inv_mem hy)) o).1 ho
        rwa [inv_inv] at h1
      · apply mul_left_cancel (a := ι y)
        apply mul_right_cancel (b := (ι y)⁻¹)
        rw [← hoe, map_mul, map_mul, map_inv]
        group
  · rw [stdB, hZ]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul,
      mem_centralizer_iff.1 (SymplecticPilot.complSp_le_centralizer_nsTorusSp 0 hy) z (hle hz)]

end Std

end CFSG.SeitzReduction.F4Pilot
