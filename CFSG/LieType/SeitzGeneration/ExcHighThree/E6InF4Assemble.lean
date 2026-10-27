module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Torus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Close
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Pilot
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6


theorem range_embE6F4 (K : Type) [Field K] : (embE6F4 K).range = fixE6 K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (isoE6F4 K y).2
  · intro hx
    exact ⟨(isoE6F4 K).symm ⟨x, hx⟩, by simp [embE6F4]⟩

theorem embE6F4_injective (K : Type) [Field K] : Function.Injective (embE6F4 K) :=
  Subtype.val_injective.comp (isoE6F4 K).injective

theorem card_fixE6 (K : Type) [Field K] [Finite K] :
    Nat.card (fixE6 K) = CFSG.Open.ordF4 (Nat.card K) := by
  rw [Nat.card_congr (isoE6F4 K).symm.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]

theorem index_fixE6 (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    (fixE6 K).index = Nat.card K ^ 12 * (Nat.card K ^ 9 - 1) * (Nat.card K ^ 5 - 1) := by
  have hcard := Subgroup.card_mul_index (fixE6 K)
  rw [card_fixE6, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
    ordE6_eq_ordF4_mul_of_mod_two hK] at hcard
  have hpos : 0 < CFSG.Open.ordF4 (Nat.card K) := by
    rw [← card_fixE6]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hcard

theorem not_dvd_three_index_fixE6 (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    ¬ 3 ∣ (fixE6 K).index := by
  rw [index_fixE6 K hK]
  exact not_dvd_three_mod_two hK

theorem conj_into_fixE6_two (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup .E6 K)} (hexp : ∀ x ∈ E₀, x ^ 3 = 1) :
    ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E₀ := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    simpa using hexp x x.2⟩
  obtain ⟨c, hc⟩ :=
    exists_conj_le_of_not_dvd_index (fixE6 K) (not_dvd_three_index_fixE6 K hK) hP
  refine ⟨c⁻¹, fun x hx => ?_⟩
  rw [range_embE6F4]
  simpa [inv_inv] using hc x hx

theorem xE_node4_mem_fixE6 (K : Type) [Field K] (c : K) :
    xE Tag.E6 K (e6Index 3) c ∈ fixE6 K ∧ yE Tag.E6 K (e6Index 3) c ∈ fixE6 K := by
  have h := xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c
  exact ⟨Subgroup.mem_subgroupOf.mpr h.1, Subgroup.mem_subgroupOf.mpr h.2⟩

theorem closure_fixE6_union_centralizer_eq_top (K : Type) [Field K] (t : adjointGroup .E6 K)
    (ht : ∀ (i : Fin Tag.E6.rank), i ≠ e6Index 3 → ∀ c : K,
      Commute t (xE Tag.E6 K i c) ∧ Commute t (yE Tag.E6 K i c)) :
    Subgroup.closure ((embE6F4 K).range ∪
      (Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) = ⊤ := by
  classical
  apply eq_top_of_simpleRootOps_gen
  intro i c
  by_cases hi : i = e6Index 3
  · subst hi
    have h4 : ∀ c : K, xE Tag.E6 K (e6Index 3) c ∈ (embE6F4 K).range ∧
        yE Tag.E6 K (e6Index 3) c ∈ (embE6F4 K).range := fun c => by
      rw [range_embE6F4]
      exact xE_node4_mem_fixE6 K c
    exact ⟨Subgroup.subset_closure (Or.inl (h4 c).1), Subgroup.subset_closure (Or.inl (h4 c).2)⟩
  · obtain ⟨hx, hy⟩ := ht i hi c
    refine ⟨Subgroup.subset_closure (Or.inr ?_), Subgroup.subset_closure (Or.inr ?_)⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hy.symm

theorem e6HighInF4_of_closing_emb {ε : ℕ}
    (hConj : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
      ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        ¬ NormalizesRNative .E6 K E₀ →
        ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range)
    (hClose : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((embE6F4 K).range ∪
          (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤) :
    E6HighInF4 ε := by
  intro K _ _ hK E₀ hexp hcard hn
  obtain ⟨g, hg⟩ := hConj K hK E₀ hexp hcard hn
  set E₁ : Subgroup (adjointGroup .E6 K) := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁le : E₁ ≤ (embE6F4 K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hι := embE6F4_injective K
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (embE6F4 K) with hE₃def
  have hE₃map : E₃.map (embE6F4 K) = E₁ := Subgroup.map_comap_eq_self hE₁le
  have hcardE₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map (embE6F4 K)) = Nat.card E₃ :=
      Subgroup.card_map_of_injective hι
    rw [← h1, hE₃map, hcardE₁]
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : (embE6F4 K) x ∈ E₀.map (MulAut.conj g).toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRNative .F4 K E₃ :=
    not_normalizesRIn_comap_of_map (embE6F4 K) hι g hn E₃ hE₃map
  obtain ⟨e, he, he1, hcl⟩ := hClose K hK E₃ hexp₃ hcardE₃ hnF
  exact ⟨g, embE6F4 K, E₃, hι, hE₃map, e, he, he1, hcl⟩

theorem hReg_of_NR (hNR : LangPlaneKillsRoot Tag.F4) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ D : LangPlaneData .F4 K E₃, ∀ α, IsRoot .F4 α → ¬ D.Kills α := by
  intro K _ _ hK E₃ hexp hcard hnF
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  have hor : Nonempty (LangPlaneData .F4 K E₃) ∨ NormalizesRNative .F4 K E₃ :=
    langToralOrParabolic_of_langToralPlane
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K hnd E₃ hexp hcard
  rcases hor with hD | hN
  · obtain ⟨D⟩ := hD
    refine ⟨D, fun α hα hk => ?_⟩
    obtain ⟨u, hu1, ⟨n, hn⟩, hcomm⟩ := hNR K E₃ D α hα hk
    apply hnF
    show NormalizesRIn (ringChar K) E₃
    refine ⟨Subgroup.zpowers u, fun h => hu1 (Subgroup.zpowers_eq_bot.mp h), ?_, ?_⟩
    · intro g
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨n, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
        one_zpow]
      rfl
    · intro x hx
      have hxu : x * u * x⁻¹ = u := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((hcomm x hx).eq).symm
      have hconj : ∀ k : ℤ, x * u ^ k * x⁻¹ = u ^ k := by
        intro k
        rw [← conj_zpow, hxu]
      have hconj' : ∀ k : ℤ, x⁻¹ * u ^ k * x = u ^ k := by
        intro k
        calc x⁻¹ * u ^ k * x = x⁻¹ * (x * u ^ k * x⁻¹) * x := by rw [hconj k]
          _ = u ^ k := by group
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        rw [← hk, hconj k]
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have hh' : h = x⁻¹ * (x * h * x⁻¹) * x := by group
        rw [hh', ← hk, hconj']
  · exact absurd hN hnF

theorem hClose_one_of_purity_emb
    (hReg : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ D : LangPlaneData .F4 K E₃, ∀ α, IsRoot .F4 α → ¬ D.Kills α)
    (hPure : F4PureSplit) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((embE6F4 K).range ∪
          (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤ := by
  intro K _ _ hK E₃ hexp hcard hnF
  obtain ⟨ω, hω⟩ := exists_units_orderOf_three K hK
  obtain ⟨D, hD⟩ := hReg K hK E₃ hexp hcard hnF
  have hnt : Nontrivial E₃ := by
    haveI : Fintype E₃ := Fintype.ofFinite E₃
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨x, hx⟩ := exists_ne (1 : E₃)
  have he1 : (x : adjointGroup .F4 K) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨g, hg⟩ := hPure K hK ω hω E₃ hexp hcard D hD x x.2 he1
  refine ⟨x, x.2, he1, ?_⟩
  have hez : embE6F4 K x = (embE6F4 K g)⁻¹ * embE6F4 K (zSplit K ω) * embE6F4 K g := by
    have hx' : (x : adjointGroup .F4 K) = g⁻¹ * zSplit K ω * g := by
      rw [← hg]
      group
    rw [hx', map_mul, map_mul, map_inv]
  rw [hez]
  have hk : embE6F4 K g ∈ (embE6F4 K).range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hfix := closure_fixE6_union_centralizer_eq_top K (embE6F4 K (zSplit K ω))
    (fun i hi c => hCent_proved K hK ω hω i hi c)
  exact closure_conj_eq_top K (embE6F4 K).range (embE6F4 K g) hk _ hfix

@[expose] def ConjOne : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .E6 K E₀ →
      ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range

@[expose] def TwistedFrameTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
      ¬ NormalizesRNative .F4 K E₃ →
      ∃ e ∈ E₃, e ≠ 1 ∧ ∃ X : Subgroup (adjointGroup .E6 K),
        X ≤ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) ∧
        (∀ H : Subgroup (adjointGroup .E6 K), X ≤ H →
          ¬ H ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)) → H = ⊤) ∧
        ¬ (fixE6 K ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)))

theorem closure_of_frame {K : Type} [Field K] (R : Subgroup (adjointGroup .E6 K))
    (t : adjointGroup .E6 K) (X : Subgroup (adjointGroup .E6 K))
    (hX : X ≤ Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)))
    (hclose : ∀ H : Subgroup (adjointGroup .E6 K), X ≤ H →
      ¬ H ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)) → H = ⊤)
    (hR : ¬ R ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K))) :
    Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) = ⊤ := by
  apply hclose
  · intro x hx
    exact Subgroup.subset_closure (Or.inr (hX hx))
  · intro hle
    apply hR
    intro r hr
    exact hle (Subgroup.subset_closure (Or.inl hr))

theorem hClose_two_of_frame (hF : TwistedFrameTwo) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((embE6F4 K).range ∪
          (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤ := by
  intro K _ _ hK E₃ hexp hcard hnF
  obtain ⟨e, he, he1, X, hX, hclose, hnorm⟩ := hF K hK E₃ hexp hcard hnF
  refine ⟨e, he, he1, ?_⟩
  rw [range_embE6F4]
  exact closure_of_frame (fixE6 K) (embE6F4 K e) X hX hclose hnorm

theorem e6HighInF4_one (hConj : ConjOne) (hNR : LangPlaneKillsRoot Tag.F4) (hPure : F4PureSplit) :
    E6HighInF4 1 :=
  e6HighInF4_of_closing_emb hConj (hClose_one_of_purity_emb (hReg_of_NR hNR) hPure)

theorem e6HighInF4_two (hF : TwistedFrameTwo) : E6HighInF4 2 :=
  e6HighInF4_of_closing_emb (fun K _ _ hK E₀ hexp _ _ => conj_into_fixE6_two K hK hexp)
    (hClose_two_of_frame hF)

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
