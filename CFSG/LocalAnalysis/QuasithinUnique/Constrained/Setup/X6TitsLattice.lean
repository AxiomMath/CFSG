module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Tits
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.GroupActions.IndexFiveTwoSolvable

public noncomputable section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat

namespace TitsLat

open scoped Pointwise

theorem titsFlagStab_le_line
    : titsFlagStab ≤ titsLineStab := by
  intro g hg
  have h1 : titsDFlagAct g 0 = 0 := hg
  have hk := titsKappa_dflag g 0
  rw [h1, titsKappa_zero] at hk
  exact hk.symm

theorem index_flag_line
    : (titsFlagStab.subgroupOf titsLineStab).index = 3 := by
  have h := Subgroup.card_mul_index (titsFlagStab.subgroupOf titsLineStab)
  rw [card_subgroupOf_le titsFlagStab_le_line, card_titsFlagStab, card_titsLineStab] at h
  have h' : 2048 * (titsFlagStab.subgroupOf titsLineStab).index = 2048 * 3 := by omega
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem isPGroup_flagStab_sub
    {P : Subgroup titsD} (h : titsFlagStab ≤ P) :
    IsPGroup 2 (titsFlagStab.subgroupOf P) :=
  IsPGroup.of_card (n := 11) (by rw [card_subgroupOf_le h, card_titsFlagStab]; norm_num)

theorem solvable_titsPointStab
    : Group.IsSolvable titsPointStab :=
  CFSG.GroupActions.index_five_two_subgroup_solvable _ (isPGroup_flagStab_sub titsFlagStab_le_point)
    index_flag_point

theorem solvable_titsLineStab
    : Group.IsSolvable titsLineStab :=
  index_three_two_subgroup_solvable _ (isPGroup_flagStab_sub titsFlagStab_le_line)
    index_flag_line

theorem isSylowTwoOf_flagStab
    : CFSG.QuasithinUnique.IsSylowTwoOf titsFlagStab ⊤ := by
  have h8 : Nat.card titsFlagStab = 2 ^ 11 := by rw [card_titsFlagStab]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card h8, ?_⟩
  rw [show (titsFlagStab.subgroupOf ⊤).index = titsFlagStab.index from
    Subgroup.relIndex_top_right titsFlagStab, titsFlagStab_index]
  decide

section Transfer

variable {X Y : Type} [Group X] [Group Y]

theorem card_comap_equiv (ψ : X ≃* Y) (K : Subgroup Y) :
    Nat.card (K.comap ψ.toMonoidHom) = Nat.card K := by
  rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ψ.symm.injective]

theorem solvable_comap_equiv (ψ : X ≃* Y) (K : Subgroup Y) (h : Group.IsSolvable K) :
    Group.IsSolvable (K.comap ψ.toMonoidHom) := by
  rw [Subgroup.comap_equiv_eq_map_symm']
  have : Group.IsSolvable K := h
  exact Group.isSolvable_of_surjective
    (f := (K.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).toMonoidHom)
    (K.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).surjective

theorem lattice_comap (ψ : X ≃* Y) {S₀ H₀ N₀ : Subgroup Y}
    (hlat : ∀ M : Subgroup Y, S₀ ≤ M → M = S₀ ∨ M = H₀ ∨ M = N₀ ∨ M = ⊤) (M : Subgroup X)
    (hM : S₀.comap ψ.toMonoidHom ≤ M) :
    M = S₀.comap ψ.toMonoidHom ∨ M = H₀.comap ψ.toMonoidHom ∨ M = N₀.comap ψ.toMonoidHom ∨
      M = ⊤ := by
  have hS : S₀ ≤ M.map ψ.toMonoidHom := by
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective S₀]
    exact Subgroup.map_mono hM
  have hM' : M = (M.map ψ.toMonoidHom).comap ψ.toMonoidHom :=
    (Subgroup.comap_map_eq_self_of_injective ψ.injective M).symm
  rcases hlat _ hS with h | h | h | h
  · left
    rw [hM', h]
  · right; left
    rw [hM', h]
  · right; right; left
    rw [hM', h]
  · right; right; right
    rw [hM', h, Subgroup.comap_top]

end Transfer

theorem exists_conj_sylow {Y : Type} [Group Y] [Finite Y] {S U : Subgroup Y} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) :
    ∃ m : Y, ∀ x : Y, x ∈ U ↔ m⁻¹ * x * m ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 Y := hS.toSylow hSi
  let U' : Sylow 2 Y := hU.toSylow hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S' U'
  refine ⟨g, fun x => ?_⟩
  have hU' : (U : Subgroup Y) = MulAut.conj g • (S : Subgroup Y) := by
    have h1 : ((g • S' : Sylow 2 Y) : Subgroup Y) = MulAut.conj g • (S' : Subgroup Y) :=
      Sylow.coe_subgroup_smul
    rw [hg] at h1
    exact h1
  rw [hU', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

end TitsLat

theorem titsSylowOvergroupLattice
    : TitsSylowOvergroupLattice := by
  intro X _ _ hX U hU
  obtain ⟨e⟩ := titsModelEquiv X 2 1 hX
  obtain ⟨hU2, hUi⟩ : IsPGroup 2 U ∧ ¬ 2 ∣ U.index := by
    refine ⟨hU.2.1, ?_⟩
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  obtain ⟨hS2, hSi⟩ : IsPGroup 2 titsFlagStab ∧ ¬ 2 ∣ titsFlagStab.index := by
    refine ⟨isSylowTwoOf_flagStab.2.1, ?_⟩
    have := isSylowTwoOf_flagStab.2.2
    rwa [show (titsFlagStab.subgroupOf ⊤).index = titsFlagStab.index from
      Subgroup.relIndex_top_right titsFlagStab] at this
  have hU' : IsPGroup 2 (U.map e.toMonoidHom) := hU2.map _
  have hU'i : ¬ 2 ∣ (U.map e.toMonoidHom).index := by
    have h3 : (U.map e.toMonoidHom).index = U.index := Subgroup.index_map_equiv U e
    rw [h3]
    exact hUi
  obtain ⟨m, hm⟩ := exists_conj_sylow hS2 hSi hU' hU'i
  let ψ : X ≃* titsD := e.trans (MulAut.conj m⁻¹)
  have hUψ : titsFlagStab.comap ψ.toMonoidHom = U := by
    ext x
    have hx : x ∈ U ↔ e x ∈ U.map e.toMonoidHom :=
      ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by rwa [← e.injective hyx]⟩
    rw [hx, hm]
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ψ, MulEquiv.trans_apply,
      MulAut.conj_apply, inv_inv]
  refine ⟨titsPointStab.comap ψ.toMonoidHom, titsLineStab.comap ψ.toMonoidHom, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← hUψ, card_comap_equiv, card_titsFlagStab]
  · rw [← hUψ]
    exact Subgroup.comap_mono titsFlagStab_le_point
  · rw [← hUψ]
    exact Subgroup.comap_mono titsFlagStab_le_line
  · rw [card_comap_equiv, card_titsPointStab]
  · rw [card_comap_equiv, card_titsLineStab]
  · intro M hM
    rw [← hUψ] at hM ⊢
    exact lattice_comap ψ tits_overgroups M hM
  · exact solvable_comap_equiv ψ _ solvable_titsPointStab
  · exact solvable_comap_equiv ψ _ solvable_titsLineStab

end CFSG.QuasithinUnique.Setup.X6
