module

public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.GraphFixedD4Middle

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem two_le_order_twistTag (t : TwistTag) : 2 ≤ t.order := by
  cases t <;> decide

theorem pow_apply_eq_pow {q : ℕ} (hσ : ∀ c, σ c = c ^ q) (k : ℕ) (c : K) :
    (σ ^ k) c = c ^ (q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, hσ, ← pow_mul, pow_succ]

theorem E6_orbitMin_of_card_eq_one {a : Fin TwistTag.E6.foldedTag.rank}
    (h : (TwistTag.E6.orbit a).card = 1) :
    (TwistTag.E6.orbitMin a).val = 1 ∨ (TwistTag.E6.orbitMin a).val = 3 := by
  revert a
  decide

theorem D4_orbitMin_of_card_eq_one {a : Fin TwistTag.D4.foldedTag.rank}
    (h : (TwistTag.D4.orbit a).card = 1) : (TwistTag.D4.orbitMin a).val = 2 := by
  revert a
  decide

theorem coe_orbitX_of_card_eq_one
    {a : Fin t.foldedTag.rank} (h : (t.orbit a).card = 1)
    (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) = xUnit t.tag K (t.orbitMin a) c := by
  rw [coe_orbitX, h]
  simp

variable {p f : ℕ}

theorem orbitX_mem_commutator_of_finite
    (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈
      ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ := by
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have : Fintype K := Fintype.ofFinite K
  rcases t.card_orbit a with h1 | hm
  ·
    have hc : σ (c : K) = c := by
      have := (mem_orbitField (t := t) (σ := σ) (a := a)).1 c.2
      rwa [h1, pow_one] at this
    rw [coe_orbitX_of_card_eq_one h1]
    cases t with
    | E6 =>
      exact (E6_fixed_singletons_derived K σ _ (E6_orbitMin_of_card_eq_one h1) c hc).1
    | D4 =>
      have hj : TwistTag.D4.orbitMin a = ⟨2, by decide⟩ := Fin.ext (D4_orbitMin_of_card_eq_one h1)
      rw [hj]
      exact (D4_fixed_middle_derived hp hf K hK σ hσ c hc).1
  ·
    have hmem : ∀ x : K, x ∈ orbitField t K σ a := fun x => by
      rw [mem_orbitField, hm, pow_apply_eq_pow hσ, ← hK, Nat.card_eq_fintype_card,
        FiniteField.pow_card]
    have hL : ∃ s : Finset (orbitField t K σ a), 4 ≤ s.card := by
      refine ⟨(Finset.univ : Finset K).map ⟨fun x => ⟨x, hmem x⟩, fun x y h =>
        congrArg Subtype.val h⟩, ?_⟩
      rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq2 2
        _ ≤ (p ^ f) ^ t.order := Nat.pow_le_pow_right (by omega) (two_le_order_twistTag t)
    exact ((fixed_orbit_rank_one_scalar_perfectness t K σ).2.2 a hL c).1

theorem finite_fixed_root_group_perfect
    (t : TwistTag) (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ = graphFixedRootGroup t K σ ∧
    (∃ x ∈ graphFixedRootGroup t K σ, ∃ y ∈ graphFixedRootGroup t K σ, x * y ≠ y * x) ∧
    ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = graphFixedRootGroup t K σ ∧
    Nontrivial (graphFixedRootGroup t K σ ⧸ Subgroup.center (graphFixedRootGroup t K σ)) ∧
    commutator (graphFixedRootGroup t K σ ⧸ Subgroup.center (graphFixedRootGroup t K σ)) = ⊤ := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  set C := graphFixedRootGroup t K σ
  have hperf : ⁅C, C⁆ = C := by
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
    refine (le_of_eq (graphFixedRootGroup_eq_closure σ hsurj)).trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨w, hw, a, c, rfl⟩
    exact conj_mem_commutator_self (canonicalRep_mem_graphFixedRootGroup hw)
      (orbitX_mem_commutator_of_finite hp hf hK hσ a c)
  obtain ⟨i₀⟩ : Nonempty (Fin t.tag.rank) := ⟨⟨0, by cases t <;> decide⟩⟩
  set a := t.orbitIndex i₀
  have hx1 : (orbitX t K σ a 1 : ModGL t.tag K) ≠ 1 := fun h => by
    have h' : orbitX t K σ a 1 = orbitX t K σ a 0 := by
      rw [orbitX_zero]
      exact Subtype.ext h
    exact one_ne_zero (orbitX_injective σ a h')
  have hxC : (orbitX t K σ a 1 : ModGL t.tag K) ∈ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ (orbitX_mem_graphFixedPosUnipotent t σ a 1)
  have hnab : ∃ x ∈ C, ∃ y ∈ C, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hbot : ⁅C, C⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).2 fun x hx y hy =>
      (h y hy x hx)
    rw [hperf] at hbot
    exact hx1 (by rw [hbot] at hxC; exact (Subgroup.mem_bot).1 hxC)
  have hΓ : ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = C := by
    refine le_antisymm (commutator_twistedFixedGroup_le hsurj) ?_
    calc C = ⁅C, C⁆ := hperf.symm
      _ ≤ _ := Subgroup.commutator_mono (graphFixedRootGroup_le t K σ)
        (graphFixedRootGroup_le t K σ)
  refine ⟨hperf, hnab, hΓ, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    refine nontrivial_of_ne (QuotientGroup.mk (⟨x, hx⟩ : C)) 1 fun h => hxy ?_
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    exact (congrArg Subtype.val (h ⟨y, hy⟩)).symm
  ·
    have htop : commutator C = ⊤ := by
      refine (Subgroup.map_injective C.subtype_injective) ?_
      rw [Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hrange : (⊤ : Subgroup (C ⧸ Subgroup.center C)) =
        (⊤ : Subgroup C).map (QuotientGroup.mk' (Subgroup.center C)) := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    rw [commutator_def, hrange, ← Subgroup.map_commutator, ← commutator_def, htop]

end CFSG.LieType.Chevalley
