module

public import CFSG.GF2Type.Smith1980Orth.Order
public import CFSG.LargeExtraspecial.PSL10Fix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open

private theorem card_alternatingGroup_fin_three :
    Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem isMulCommutative_alternatingGroup_fin_three :
    IsMulCommutative (alternatingGroup (Fin 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := isCyclic_of_prime_card card_alternatingGroup_fin_three
  infer_instance

private theorem centralizer_le_of_isSimpleGroup_timmesfeldFStar {Y : Type} [Group Y] [Finite Y]
    (hF : IsSimpleGroup (timmesfeldFStar Y)) {K : Subgroup Y} (hK : K.Normal)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK1 : K ≠ ⊥) :
    Subgroup.centralizer (K : Set Y) ≤ K := by
  have hKF : K ≤ timmesfeldFStar Y := S14.PSLPSU10.le_timmesfeldFStar_of_normal hK hKc
  have hFK : timmesfeldFStar Y ≤ K := by
    have : (K.subgroupOf (timmesfeldFStar Y)).Normal := hK.subgroupOf _
    rcases hF.eq_bot_or_eq_top_of_normal (K.subgroupOf (timmesfeldFStar Y)) with h | h
    · refine absurd ?_ hK1
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hKF hx⟩ : timmesfeldFStar Y) ∈ K.subgroupOf (timmesfeldFStar Y) :=
        Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
    · intro x hx
      have hx' : (⟨x, hx⟩ : timmesfeldFStar Y) ∈ K.subgroupOf (timmesfeldFStar Y) := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hx'
  have hcent : Subgroup.centralizer (timmesfeldFStar Y : Set Y) ≤ timmesfeldFStar Y :=
    CFSG.Adapters.generalized_fitting_self_centralizing Y
  intro y hy
  exact hFK (hcent (Subgroup.mem_centralizer_iff.2 fun f hf =>
    Subgroup.mem_centralizer_iff.1 hy f (hFK hf)))

theorem not_isSimpleGroup_timmesfeldFStar_of_mulEquiv {Y X : Type} [Group Y] [Group X] [Finite Y]
    [Nontrivial X] (e : Y ≃* Equiv.Perm (Fin 3) × X) :
    ¬ IsSimpleGroup (CFSG.Open.timmesfeldFStar Y) := by
  intro hF
  have := isMulCommutative_alternatingGroup_fin_three
  let K : Subgroup Y := ((alternatingGroup (Fin 3)).prod ⊥).comap e.toMonoidHom
  have hKmem : ∀ y, y ∈ K ↔ (e y).1 ∈ alternatingGroup (Fin 3) ∧ (e y).2 = 1 := fun y => by
    rw [Subgroup.mem_comap, Subgroup.mem_prod, Subgroup.mem_bot]
    rfl
  have hKnormal : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := (hKmem a).1 ha
    obtain ⟨hb1, hb2⟩ := (hKmem b).1 hb
    apply e.injective
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · exact setLike_mul_comm ha1 hb1
    · simp only [Prod.snd_mul, ha2, hb2, mul_one]
  have hK1 : K ≠ ⊥ := by
    obtain ⟨c, hc⟩ : ∃ c : alternatingGroup (Fin 3), c ≠ 1 := by
      have : Nontrivial (alternatingGroup (Fin 3)) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [card_alternatingGroup_fin_three]; norm_num)
      exact exists_ne 1
    intro h
    have hmem : e.symm ((c : Equiv.Perm (Fin 3)), 1) ∈ K := by
      rw [hKmem]
      simp
    rw [h, Subgroup.mem_bot] at hmem
    apply hc
    apply Subtype.ext
    have := congrArg (fun y => (e y).1) hmem
    simpa using this
  have hcent := centralizer_le_of_isSimpleGroup_timmesfeldFStar hF hKnormal hKc hK1
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hmem : e.symm (1, x) ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk2 := ((hKmem k).1 hk).2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · exact (mul_one _).trans (one_mul _).symm
    · show (e k).2 * x = x * (e k).2
      rw [hk2, one_mul, mul_one]
  have h2 := ((hKmem _).1 (hcent hmem)).2
  rw [MulEquiv.apply_symm_apply] at h2
  exact hx h2

private theorem nontrivial_of_one_lt_natCard {α : Type*} (h : 1 < Nat.card α) : Nontrivial α := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.1 h

section Data

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem OrthData.one_lt_card_omega (O : OrthData S) :
    1 < Nat.card (timmesfeldOmega O.q) := by
  obtain ⟨r, hr, hcard⟩ := O.card_omega
  have h4 := O.four_le
  have hk : S.width / 2 * (S.width / 2 - 1) ≠ 0 :=
    (Nat.mul_pos (by omega) (by omega)).ne'
  rw [hcard]
  exact lt_of_lt_of_le (Nat.one_lt_two_pow hk) (Nat.le_mul_of_pos_right _ hr.pos)

private theorem OrthData.one_lt_card_isometries (O : OrthData S) :
    1 < Nat.card (timmesfeldIsometries O.q) := by
  have := O.one_lt_card_omega
  have := O.card_isometries
  omega

end Data

theorem OrthData.not_isSimpleGroup_Mbar0 {G : Type} [Group G] [Finite G]
    {S : CFSG.LargeExtraspecial.Setting G} (O : OrthData S) :
    ¬ IsSimpleGroup (CFSG.LargeExtraspecial.S14.Mbar0 S) := by
  have := CFSG.LargeExtraspecial.Bridge.finite_Mbar S
  rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := nontrivial_of_one_lt_natCard O.one_lt_card_omega
    exact not_isSimpleGroup_timmesfeldFStar_of_mulEquiv e
  · have := nontrivial_of_one_lt_natCard O.one_lt_card_isometries
    exact not_isSimpleGroup_timmesfeldFStar_of_mulEquiv e

end CFSG.GF2Type.Smith1980Orth
