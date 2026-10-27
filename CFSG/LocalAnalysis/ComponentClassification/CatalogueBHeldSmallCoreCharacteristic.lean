module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.SubgroupRectangular

public section

namespace CFSG.ComponentClassification.CatalogueBHeldSmallCore

theorem exists_minimal_characteristic (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ A : Subgroup G, A.Characteristic ∧ A ≠ ⊥ ∧
      ∀ B : Subgroup G, B.Characteristic → B ≤ A → B ≠ ⊥ → B = A := by
  classical
  have hex : ∃ n : ℕ, ∃ A : Subgroup G, A.Characteristic ∧ A ≠ ⊥ ∧ Nat.card A = n :=
    ⟨Nat.card G, ⊤, inferInstance, top_ne_bot, Subgroup.card_top⟩
  obtain ⟨A, hAchar, hAnonzero, hAcard⟩ := Nat.find_spec hex
  refine ⟨A, hAchar, hAnonzero, ?_⟩
  intro B hBchar hBA hBnonzero
  have hminimal : Nat.find hex ≤ Nat.card B :=
    Nat.find_min' hex ⟨B, hBchar, hBnonzero, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hBA (hAcard ▸ hminimal)

theorem minimal_characteristic_is_characteristically_simple
    {G : Type*} [Group G] (A : Subgroup G) [A.Characteristic]
    (hminimal : ∀ B : Subgroup G, B.Characteristic → B ≤ A → B ≠ ⊥ → B = A)
    (B : Subgroup A) [B.Characteristic] : B = ⊥ ∨ B = ⊤ := by
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  · right
    have hnonzero : B.map A.subtype ≠ ⊥ := by
      intro hzero
      exact hbot ((B.map_eq_bot_iff_of_injective A.subtype_injective).mp hzero)
    have htop := hminimal (B.map A.subtype) inferInstance
      (Subgroup.map_subtype_le B) hnonzero
    apply Subgroup.map_injective A.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact htop

theorem characteristically_simple_solvable_isMulCommutative
    (H : Type*) [Group H] [Nontrivial H] [Group.IsSolvable H]
    (hchar : ∀ B : Subgroup H, B.Characteristic → B = ⊥ ∨ B = ⊤) :
    IsMulCommutative H := by
  have hderived : commutator H = ⊥ :=
    (hchar (commutator H) inferInstance).resolve_right
      (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne
  apply IsMulCommutative.of_comm
  intro x y
  have hcentralizer : (⊤ : Subgroup H) ≤ Subgroup.centralizer (⊤ : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hderived
  exact (Subgroup.mem_centralizer_iff.mp (hcentralizer (Subgroup.mem_top y)))
    x (Subgroup.mem_top x)

theorem characteristically_simple_solvable_isElementaryAbelian
    (H : Type*) [Group H] [Finite H] [Nontrivial H] [Group.IsSolvable H]
    (hchar : ∀ B : Subgroup H, B.Characteristic → B = ⊥ ∨ B = ⊤) :
    ∃ p : ℕ, p.Prime ∧ CFSG.IsElementaryAbelian p H := by
  classical
  let : IsMulCommutative H :=
    characteristically_simple_solvable_isMulCommutative H hchar
  let : CommGroup H := IsMulCommutative.instCommGroup
  obtain ⟨p, hp, hpdivides⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (show 1 < Nat.card H from Finite.one_lt_card))
  let : Fact p.Prime := ⟨hp⟩
  let T := (powMonoidHom p : H →* H).ker
  have hTchar : T.Characteristic := CFSG.Wielandt.powMonoidHom_ker_characteristic p
  have hTnonzero : T ≠ ⊥ := by
    obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' p hpdivides
    intro hbot
    have hxT : x ∈ T := by
      change x ^ p = 1
      rw [← hxorder]
      exact pow_orderOf_eq_one x
    have hxone : x = 1 := Subgroup.mem_bot.mp (hbot ▸ hxT)
    rw [hxone, orderOf_one] at hxorder
    exact hp.ne_one hxorder.symm
  have hTtop : T = ⊤ := (hchar T hTchar).resolve_left hTnonzero
  refine ⟨p, hp, { exponent_dvd_p := ?_ }⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  exact show x ∈ T from hTtop ▸ Subgroup.mem_top x

theorem exists_characteristic_elementaryAbelian (G : Type*) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ (A : Subgroup G) (p : ℕ), A.Characteristic ∧ A ≠ ⊥ ∧ p.Prime ∧
      CFSG.IsElementaryAbelian p A := by
  obtain ⟨A, hAchar, hAnonzero, hminimal⟩ := exists_minimal_characteristic G
  let : A.Characteristic := hAchar
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAnonzero
  obtain ⟨p, hp, hAelementary⟩ := characteristically_simple_solvable_isElementaryAbelian A
    (fun B hBchar => by
      let : B.Characteristic := hBchar
      exact minimal_characteristic_is_characteristically_simple A hminimal B)
  exact ⟨A, p, hAchar, hAnonzero, hp, hAelementary⟩

end CFSG.ComponentClassification.CatalogueBHeldSmallCore
