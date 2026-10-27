module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Tits
public import CFSG.LieType.BorelTits.Ree

public section

namespace CFSG.QuasithinUnique.A5.Kc3F4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem sixty_dvd_card {L M : Type} [Group L] [Group M] [Finite L] [Finite M] (g : L →* M)
    (hg : IsPGroup 2 g.ker) (α : L →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) : 60 ∣ Nat.card M := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hker : g.ker ≤ α.ker := by
    have hN : (g.ker.map α).Normal := Subgroup.Normal.map inferInstance α hα
    have hN2 : IsPGroup 2 (g.ker.map α) := hg.map α
    rcases hN.eq_bot_or_eq_top with h | h
    · intro x hx
      have : α x ∈ g.ker.map α := Subgroup.mem_map_of_mem α hx
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      rw [h] at hN2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hN2.of_equiv Subgroup.topEquiv)
      rw [CFSG.QuasithinUnique.A5.Delta5.a5_card] at hn
      have : (60 : ℕ) = 2 ^ n := hn
      have h3 : 3 ∣ 2 ^ n := this ▸ (by norm_num : 3 ∣ 60)
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3)
      omega
  let ab : L ⧸ g.ker →* ↥(alternatingGroup (Fin 5)) := QuotientGroup.lift g.ker α hker
  have hab : Function.Surjective ab := by
    intro y
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨QuotientGroup.mk x, rfl⟩
  let e : L ⧸ g.ker ≃* g.range := QuotientGroup.quotientKerEquivRange g
  have hsurj : Function.Surjective (ab.comp e.symm.toMonoidHom) := hab.comp e.symm.surjective
  have h1 := Subgroup.card_dvd_of_surjective hsurj
  rw [CFSG.QuasithinUnique.A5.Delta5.a5_card] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card g.range)

open CFSG.QuasithinUnique.Setup.X6 in
theorem no_block_of_lattice
    {S : Type} [Group S] [Finite S] {U : Subgroup S}
    {P : Fin 2 → Subgroup S} (hres : ResidualOvergroupsAt S U P)
    (hLevi : ∀ j, ∃ (M : Type) (_ : Group M) (_ : Finite M) (g : ↥(dInf (P j)) →* M),
      Function.Surjective g ∧ IsPGroup 2 g.ker ∧ ¬ 60 ∣ Nat.card M)
    {L Pm : Subgroup S} (hUPm : U ≤ Pm) (hPm : Pm ≠ ⊤) (hLP : L ≤ Pm) (hperf : Group.IsPerfect ↥L)
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α) : False := by
  have hns : ¬ Group.IsSolvable ↥Pm := by
    intro hs
    have hL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLP)
        (Subgroup.inclusion_injective _)
    exact not_isSolvable_alt5 (Group.isSolvable_of_surjective hα)
  obtain ⟨j, -, hd⟩ := hres.2.2.2.2.1 Pm hUPm hPm hns
  have hLd : L ≤ dInf (P j) := hd ▸ le_dInf_of_perfect hperf hLP
  obtain ⟨M, _, _, g, -, hk, h60⟩ := hLevi j
  let g₀ : ↥L →* M := g.comp (Subgroup.inclusion hLd)
  have hk0 : IsPGroup 2 g₀.ker :=
    hk.comap_of_injective (Subgroup.inclusion hLd) (Subgroup.inclusion_injective hLd)
  exact h60 (sixty_dvd_card g₀ hk0 α hα)

theorem q_mod_five (a : ℕ) :
    ((2 ^ (2 * a + 1) : ℕ) : ZMod 5) = 2 ∨ ((2 ^ (2 * a + 1) : ℕ) : ZMod 5) = 3 := by
  push_cast
  have h4 : (2 : ZMod 5) ^ (2 * a + 1) = (-1) ^ a * 2 := by
    rw [pow_succ, pow_mul]
    have : (2 : ZMod 5) ^ 2 = -1 := by decide
    rw [this]
  rw [h4]
  rcases neg_one_pow_eq_or (ZMod 5) a with h | h <;> rw [h]
  · left; simp
  · right; decide

theorem q_mod_three (a : ℕ) : ((2 ^ (2 * a + 1) : ℕ) : ZMod 3) = 2 := by
  push_cast
  rw [pow_succ, pow_mul]
  have : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [this, one_pow, one_mul]

theorem not_sixty_dvd_sl2 (a : ℕ) :
    ¬ 60 ∣ 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  have hr := q_mod_five a
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * a + 1) = q at hr hq1 ⊢
  intro h
  have h5 : 5 ∣ q * (q ^ 2 - 1) := dvd_trans (by norm_num) h
  have h0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_pow, Nat.cast_one] at h0
  rcases hr with hr | hr <;> rw [hr] at h0 <;> revert h0 <;> decide

theorem not_sixty_dvd_sz (a : ℕ) :
    ¬ 60 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hr := q_mod_three a
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * a + 1) = q at hr hq1 ⊢
  intro h
  have h3 : 3 ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := dvd_trans (by norm_num) h
  have h0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    hr] at h0
  revert h0
  decide

section Model

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

variable {k : Type} [Field k] [Finite k] [CharP k F4.prime] {a : ℕ}

theorem levi_no60
    (ha : 1 ≤ a) (hk : Nat.card k = 2 ^ (2 * a + 1)) (j : Fin 2) :
    ∃ (M : Type) (_ : Group M) (_ : Finite M)
      (g : ↥(perfectCore ((F4.reeParabolic k a {f4Index j}).subgroupOf
        (F4.reeGamma k a))) →* M),
      Function.Surjective g ∧ IsPGroup 2 g.ker ∧ ¬ 60 ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag k) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a k w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent k a ≤ F4.reeGamma k a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent k a)
      (F4.reeGamma k a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent k a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hk
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (f4Index j) with hj | hj
  · have : IsSimpleGroup ↥(rankOneGroupOne k a) := (isSimpleGroup_rankOneGroupOne ha hk).1
    obtain ⟨g, hg, hker⟩ := ree_levi_hom (K := k) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne k a) (by rw [hj]; exact h0eq)
      (isSimpleGroup_rankOneGroupOne ha hk).2
    refine ⟨↥(rankOneGroupOne k a), inferInstance, inferInstance, g, hg, hker, ?_⟩
    rw [card_rankOneGroupOne hk]
    exact not_sixty_dvd_sl2 a
  · have : IsSimpleGroup ↥(rankOneGroupTwo k a) := (isSimpleGroup_rankOneGroupTwo ha hk).1
    obtain ⟨g, hg, hker⟩ := ree_levi_hom (K := k) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo k a) (by rw [hj]; exact h1eq)
      (isSimpleGroup_rankOneGroupTwo ha hk).2
    refine ⟨↥(rankOneGroupTwo k a), inferInstance, inferInstance, g, hg, hker, ?_⟩
    rw [card_rankOneGroupTwo ha hk]
    exact not_sixty_dvd_sz a

end Model

end CFSG.QuasithinUnique.A5.Kc3F4

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.A5.Kc3F4 CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.LieType.Chevalley CFSG.Blueprint CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

theorem kc3ForS_f4
    : Kc3ForS Kc3F4 := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hD hperf hSL hS hT hST hTK hTS
  exfalso
  obtain ⟨f, hodd, hf3, hmodel⟩ := hmod
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  set V' : Subgroup ↥K := V.subgroupOf K with hV'
  have hV'2 : IsPGroup 2 V' := by
    have : IsPGroup 2 ↥V := hQ2.to_le hVQ
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  have hV'ne : V' ≠ ⊥ := by
    intro h
    apply d5_V_ne_bot β
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVK hv⟩ : ↥K) ∈ V' := Subgroup.mem_subgroupOf.2 hv
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨S, P, hP, hN, -, -, hSP⟩ :=
    CFSG.LieType.BorelTits.holds_of_reeTitsModel hmodel (by decide) V' hV'ne hV'2
  have hS2 : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥K) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    have h1 : ((S : Subgroup ↥K).subgroupOf ⊤).index = (S : Subgroup ↥K).index :=
      Subgroup.relIndex_top_right _
    rw [h1]
    exact S.not_dvd_index
  have hSle : (S : Subgroup ↥K) ≤ P := Subgroup.le_normalizer.trans hSP
  have hLP : L.subgroupOf K ≤ P := by
    refine le_trans ?_ hN
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have := Subgroup.mem_normalizer_iff.1 (hLV hl') (x : G)
    show (x : G) ∈ V ↔ ((l * x * l⁻¹ : ↥K) : G) ∈ V
    simpa using this
  have hperf' : Group.IsPerfect ↥(L.subgroupOf K) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLK, hperf]
  let α' : ↥(L.subgroupOf K) →* ↥(alternatingGroup (Fin 5)) :=
    α.comp (Subgroup.subgroupOfEquivOfLe hLK).toMonoidHom
  have hα' : Function.Surjective α' := hα.comp (Subgroup.subgroupOfEquivOfLe hLK).surjective
  obtain ⟨a, k, _, _, _, φ, ha, hfa, hcard, hφ, hres, -⟩ :=
    even_rank_two_residual_largeRee hmodel hS2
  have hcard' : Nat.card k = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  have hLevi : ∀ j : Fin 2, ∃ (M : Type) (_ : Group M) (_ : Finite M)
      (g : ↥(dInf (((F4.reeParabolic k a {f4Index j}).subgroupOf (F4.reeGamma k a)).map
        φ.symm.toMonoidHom)) →* M),
      Function.Surjective g ∧ IsPGroup 2 g.ker ∧ ¬ 60 ∣ Nat.card M := by
    intro j
    obtain ⟨M, _, _, g, hg, hk, h60⟩ := levi_no60 (k := k) (a := a) ha hcard' j
    have h1 : dInf (((F4.reeParabolic k a {f4Index j}).subgroupOf (F4.reeGamma k a)).map
          φ.symm.toMonoidHom) =
        (perfectCore ((F4.reeParabolic k a {f4Index j}).subgroupOf (F4.reeGamma k a))).map
          φ.symm.toMonoidHom := by
      rw [dInf_map_equiv, dInf_eq_perfectCore]
    let e : ↥(dInf (((F4.reeParabolic k a {f4Index j}).subgroupOf (F4.reeGamma k a)).map
        φ.symm.toMonoidHom)) ≃*
          ↥(perfectCore ((F4.reeParabolic k a {f4Index j}).subgroupOf (F4.reeGamma k a))) :=
      (MulEquiv.subgroupCongr h1).trans
        (Subgroup.equivMapOfInjective _ φ.symm.toMonoidHom φ.symm.injective).symm
    exact ⟨M, inferInstance, inferInstance, g.comp e.toMonoidHom, hg.comp e.surjective,
      hk.comap_of_injective e.toMonoidHom e.injective, h60⟩
  exact no_block_of_lattice hres hLevi hSle hP hLP hperf' α' hα'

theorem kc3For_f4
    : Kc3For Kc3F4 := kc3For_of_simple isoInv_f4 kc3ForS_f4

end CFSG.QuasithinUnique.A5
