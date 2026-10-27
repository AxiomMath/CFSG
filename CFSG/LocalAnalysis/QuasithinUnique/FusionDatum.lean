module

public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

structure UniqueFusionDatum {G : Type} [Group G] [Finite G] (T M U : Subgroup G) (z : G) :
    Prop where
  setting : UniqueSetting G T M
  le_T : U ≤ T
  ne_bot : U ≠ ⊥
  elem : IsElemAbelian 2 U
  normal : M ≤ Subgroup.normalizer (U : Set G)
  irreducible : ∀ V : Subgroup G, V ≤ U → M ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = U
  normalizer_eq : Subgroup.normalizer (U : Set G) = M
  stronglyClosed : fusionStronglyClosed (U : Set G) T
  control : ∀ x : G, x ∈ M → (∃ k : ℕ, x ^ 2 ^ k = 1) → ∀ g : G, g⁻¹ * x * g ∈ M →
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m
  z_mem : z ∈ U
  z_center : z ∈ Subgroup.centralizer (T : Set G)
  z_ne_one : z ≠ 1
  centralizer_le : Subgroup.centralizer ({z} : Set G) ≤ M

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_normal_central_involution {T M : Subgroup G} (h : UniqueSetting G T M) :
    ∃ (U : Subgroup G) (z : G), U ≤ T ∧ U ≠ ⊥ ∧ IsElemAbelian 2 U ∧
      M ≤ Subgroup.normalizer (U : Set G) ∧
      (∀ V : Subgroup G, V ≤ U → M ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = U) ∧
      Subgroup.normalizer (U : Set G) = M ∧ z ∈ U ∧ z ∈ Subgroup.centralizer (T : Set G) ∧
      z ≠ 1 ∧ Subgroup.centralizer ({z} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOne : pCoreOf 2 M ≠ ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_pCoreOf_ne_bot M h.isTwoLocal
  have hOM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hOp : IsPGroup 2 (pCoreOf 2 M) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  obtain ⟨U, ⟨hUO, hU1, hMU⟩, hUmin⟩ := Set.exists_min_image
    {V : Subgroup G | V ≤ pCoreOf 2 M ∧ V ≠ ⊥ ∧ M ≤ Subgroup.normalizer (V : Set G)}
    (fun V => Nat.card V) (Set.toFinite _) ⟨pCoreOf 2 M, le_rfl, hOne, hMO⟩
  have hmin : ∀ V : Subgroup G, V ≤ U → M ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = U := by
    intro V hVU hMV
    by_cases hV1 : V = ⊥
    · exact Or.inl hV1
    · refine Or.inr (Subgroup.eq_of_le_of_card_ge hVU ?_)
      exact hUmin V ⟨hVU.trans hUO, hV1, hMV⟩
  have hUp : IsPGroup 2 U := hOp.to_le hUO
  have hUM : U ≤ M := hUO.trans hOM
  have hUn : (U.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mpr hMU
  have hUnt : Nontrivial U := by
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
    exact ⟨⟨u, 1, hu⟩⟩
  have hZne : U ⊓ Subgroup.centralizer (U : Set G) ≠ ⊥ := by
    intro hZ
    have hcn : Nontrivial (Subgroup.center U) := hUp.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center U)
    have hcmem : ((c : U) : G) ∈ U ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨(c : U).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.2) ⟨u, hu⟩)
    rw [hZ] at hcmem
    apply hc
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hcmem
  have hMZ : M ≤
      Subgroup.normalizer ((U ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf M U _ hMU
      (hMU.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer U))
  have hZU : U ⊓ Subgroup.centralizer (U : Set G) = U := by
    rcases hmin _ inf_le_left hMZ with hb | hb
    · exact absurd hb hZne
    · exact hb
  have hUcomm : U ≤ Subgroup.centralizer (U : Set G) := by
    intro u hu
    have : u ∈ U ⊓ Subgroup.centralizer (U : Set G) := hZU.symm ▸ hu
    exact this.2
  have hcomm : IsMulCommutative U := Subgroup.le_centralizer_iff_isMulCommutative.mp hUcomm
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ U ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨U.mul_mem ha.1 hb.1, ?_⟩
        have hab : Commute a b := Subgroup.mem_centralizer_iff.mp (hUcomm hb.1) a ha.1
        rw [hab.mul_pow, ha.2, hb.2, one_mul]
      one_mem' := ⟨U.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩU : Ω ≤ U := fun x hx => hx.1
  have hΩconj : ∀ m ∈ M, ∀ y ∈ Ω, m * y * m⁻¹ ∈ Ω := by
    intro m hm y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMU hm) y).mp hy.1, ?_⟩
    have := conj_pow (a := m) (b := y) (i := 2)
    rw [this, hy.2]
    group
  have hMΩ : M ≤ Subgroup.normalizer (Ω : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hΩconj m hm y, fun hy => ?_⟩
    have := hΩconj m⁻¹ (M.inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hΩne : Ω ≠ ⊥ := by
    intro hΩ
    have h2 : 2 ∣ Nat.card U := by
      rcases hUp.card_eq_or_dvd with hc | hc
      · exfalso
        apply hU1
        rw [Subgroup.eq_bot_iff_card]
        exact hc
      · exact hc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 h2
    have hx2 : ((x : G)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hxΩ : (x : G) ∈ Ω := ⟨x.2, hx2⟩
    rw [hΩ] at hxΩ
    have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hxΩ
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hΩ : Ω = U := by
    rcases hmin Ω hΩU hMΩ with hb | hb
    · exact absurd hb hΩne
    · exact hb
  have helem : IsElemAbelian 2 U := by
    refine ⟨hcomm, fun x hx => ?_⟩
    have : x ∈ Ω := hΩ.symm ▸ hx
    exact this.2
  have hUT : U ≤ T := BenderStart.le_of_normal_isPGroup h.sylow h.le hUM hUn hUp
  have hNU : Subgroup.normalizer (U : Set G) = M :=
    h.maxLocal.2 _ ⟨U, hU1, hUp, rfl⟩ hMU
  have hTnil : Group.IsNilpotent T := h.isPGroup.isNilpotent
  have hUTn : (U.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr (h.le.trans hMU)
  have hUTne : U.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hU1
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have : (⟨u, hUT hu⟩ : T) ∈ U.subgroupOf T := hu
    rw [hb] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  obtain ⟨c, hc⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hUTne)
  have hcU : ((c : T) : G) ∈ U := c.2.1
  have hcT : ((c : T) : G) ∈ Subgroup.centralizer (T : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.2.2) ⟨t, ht⟩)
  have hc1 : ((c : T) : G) ≠ 1 := by
    intro h1
    apply hc
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  set z : G := ((c : T) : G) with hz
  refine ⟨U, z, hUT, hU1, helem, hMU, hmin, hNU, hcU, hcT, hc1, ?_⟩
  have hzne : Subgroup.zpowers z ≠ ⊥ := by
    intro hb
    apply hc1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hb] at this
    exact Subgroup.mem_bot.mp this
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := hUp.to_le (Subgroup.zpowers_le.2 hcU)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hTL : T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine le_trans (fun t ht => ?_) hCz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (Subgroup.mem_centralizer_iff.mp hcT t ht).symm
  obtain ⟨M', ⟨hM'loc, hM'max⟩, hLM'⟩ : ∃ M' : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M' ∧
        Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M' := by
    obtain ⟨M', hM', hmax⟩ := Set.exists_max_image
      {H : Subgroup G | CFSG.Open.IsTwoLocal H ∧
        Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ H}
      (fun H => Nat.card H) (Set.toFinite _)
      ⟨Subgroup.normalizer (Subgroup.zpowers z : Set G), ⟨Subgroup.zpowers z, hzne, hzp, rfl⟩,
        le_rfl⟩
    refine ⟨M', ⟨hM'.1, fun H hH hM'H => ?_⟩, hM'.2⟩
    exact (Subgroup.eq_of_le_of_card_ge hM'H (hmax H ⟨hH, hM'.2.trans hM'H⟩)).symm
  have hM'M : M' = M := h.unique M' ⟨hM'loc, hM'max⟩ (hTL.trans hLM')
  exact hCz.trans (hLM'.trans hM'M.le)

theorem exists_uniqueFusionDatum {T M : Subgroup G} (h : UniqueSetting G T M)
    (hδ : ∀ D : Subgroup G, ¬ IsEscaping M D) :
    ∃ (U : Subgroup G) (z : G), UniqueFusionDatum T M U z := by
  obtain ⟨U, z, hUT, hU1, helem, hMU, hmin, hNU, hzU, hzT, hz1, hCz⟩ :=
    exists_minimal_normal_central_involution h
  have hev := h.qtke.2.1
  have hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ M :=
    fun D hD => normalizer_le_of_forall_not_isEscaping hev h.sylow h.le hδ hD
  have hUp : IsPGroup 2 U := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 U helem
  have hUM : U ≤ M := hUT.trans h.le
  have hUn : (U.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mpr hMU
  exact ⟨U, z, ⟨h, hUT, hU1, helem, hMU, hmin, hNU,
    (stronglyClosed_of_ag h.sylow h.le hAG hUM hUn hUp).2,
    fun x hx hx2 g hxg => exists_conj_eq_of_ag h.sylow h.le hAG hx hx2 hxg,
    hzU, hzT, hz1, hCz⟩⟩

end CFSG.QuasithinUnique
