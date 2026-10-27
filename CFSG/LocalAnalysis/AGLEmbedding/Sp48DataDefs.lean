module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Pkg

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

structure Sp48InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ K A₀ : Subgroup Y) : Prop where
  card_T : Nat.card T = 3 ^ 5
  center_pow : ∀ z ∈ centerOf T, z ^ 3 = 1
  card_center : Nat.card (centerOf T) = 3 ^ 2
  card_TK : Nat.card (T ⊓ K : Subgroup Y) = 3 ^ 4
  A_le : A₀ ≤ T
  A_pow : ∀ a ∈ A₀, a ^ 3 = 1
  A_comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a
  card_A : Nat.card A₀ = 3 ^ 3
  center_le_A : centerOf T ≤ A₀
  sylow_normal : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    centerOf T ≤ W → T ⊓ W = centerOf T ∨ T ⊓ W = A₀ ∨ T ⊓ W = T ⊓ K ∨ T ⊓ W = T
  homocyclic : ∃ u v : Y, u ∈ T ⊓ K ∧ v ∈ T ⊓ K ∧ orderOf u = 9 ∧ orderOf v = 9 ∧
    u * v = v * u ∧ Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥
  orbit_nine : ∀ a ∈ A₀, a ∉ centerOf T → ∀ W : Fin 3 → Subgroup Y,
    ∃ u ∈ T ⊓ K, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i

@[expose] def KFactSp48Data : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpFourEightIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      Group.IsSolvable Y₀ → ∃ A₀ : Subgroup Y, Sp48InSitu (T : Subgroup Y) Y₀ K A₀

@[expose] def StmtSp48Data₂ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
    Group.IsSolvable (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∃ A : Subgroup G, D1Sp48Data₂ P M H R (centerOf R) (d1LiftX 3 H R K) A

section Transfer

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem le_of_map_le_of_normal {p : ℕ} [Fact p.Prime] {M X Y : Subgroup G}
    (hNM : GLBPrimeCore p H ≤ M) (hXH : X ≤ H) (hX : IsPGroup p X)
    (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G))
    (hle : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) : X ≤ Y := by
  have hON : primeComplementCore (G := H) p ≤
      Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H) := by
    intro o ho
    have hoN : (o : G) ∈ GLBPrimeCore p H :=
      (mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)
    exact Subgroup.le_normalizer_comap H.subtype (hYN ⟨o.2, hNM hoN⟩)
  have hXY : X.subgroupOf H ≤ Y.subgroupOf H := by
    refine le_of_le_sup_of_isPGroup_of_coprime hX.comap_subtype (primeComplementCore_coprime p)
      hON ?_
    rw [sup_comm, ← QuotientGroup.comap_map_mk']
    exact Subgroup.map_le_iff_le_comap.mp hle
  intro x hx
  exact Subgroup.mem_subgroupOf.mp
    (hXY (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H))

theorem map_inf_eq_of_normal {p : ℕ} [Fact p.Prime] {M R Y : Subgroup G}
    (hNM : GLBPrimeCore p H ≤ M) (hR : IsPGroup p R)
    (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G)) :
    ((R ⊓ Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  refine le_antisymm (le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
    (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))) ?_
  rintro _ ⟨⟨r, hr, rfl⟩, hrY⟩
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hz : Subgroup.zpowers (r : G) ≤ Y := by
    refine le_of_map_le_of_normal hNM (Subgroup.zpowers_le.mpr r.2)
      (hR.to_le (Subgroup.zpowers_le.mpr hrR)) hYN ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_subgroupOf.mp hx
    have : x = r ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem _ hrY n
  exact ⟨r, Subgroup.mem_subgroupOf.mpr ⟨hrR, hz (Subgroup.mem_zpowers _)⟩, rfl⟩

omit [Finite G] in
theorem map_inf_preimage {p : ℕ} {R : Subgroup G}
    {B : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hB : B ≤ (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    ((R ⊓ (B.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype).subgroupOf
      H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, ⟨y, hy, hyx⟩⟩ := Subgroup.mem_subgroupOf.mp hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro b hb
    obtain ⟨r, hr, rfl⟩ := hB hb
    exact ⟨r, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hr, ⟨r, hb, rfl⟩⟩, rfl⟩

theorem injective_mk_of_isPGroup {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRH : R ≤ H)
    (hR : IsPGroup p R) :
    Function.Injective ((QuotientGroup.mk' (primeComplementCore (G := H) p)).comp
      (Subgroup.inclusion hRH)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) (Subgroup.inclusion hRH x) = 1 := hx
  have hN : ((Subgroup.inclusion hRH x : H) : G) ∈ GLBPrimeCore p H :=
    (mem_glbPrimeCore_iff_mk_eq_one _).mpr h1
  have hbot := inf_eq_bot_of_isPGroup (Fact.out : p.Prime) hR (glbPrimeCore_coprime p H)
  have hmem : (x : G) ∈ R ⊓ GLBPrimeCore p H := ⟨x.2, hN⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext hmem)


omit [Finite G] in
theorem map_perfect_subgroupOf {p : ℕ} {Y : Subgroup G} (hYH : Y ≤ H) (hYY : ⁅Y, Y⁆ = Y) :
    ⁅(Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))⁆ =
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hY' : ⁅Y.subgroupOf H, Y.subgroupOf H⁆ = Y.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYH, hYY]
  rw [← Subgroup.map_commutator, hY']

theorem eq_of_map_eq_of_isPGroup' {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRH : R ≤ H)
    (hR : IsPGroup p R) {x y : G} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hx⟩ =
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨y, hRH hy⟩) : x = y := by
  have h := injective_mk_of_isPGroup hRH hR (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val h

theorem orderOf_mk_eq_of_isPGroup {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRH : R ≤ H)
    (hR : IsPGroup p R) {x : G} (hx : x ∈ R) :
    orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hx⟩) = orderOf x := by
  have := orderOf_injective _ (injective_mk_of_isPGroup hRH hR) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at this
  exact this

end Transfer

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Transfer2

variable {G : Type} [Group G] {H : Subgroup G}

theorem map_zpowers_subgroupOf {p : ℕ} {a : G} (ha : a ∈ H) :
    ((Subgroup.zpowers a).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨a, ha⟩) := by
  have e1 : (Subgroup.zpowers a).subgroupOf H = Subgroup.zpowers (⟨a, ha⟩ : H) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr ha), MonoidHom.map_zpowers]
    rfl
  rw [e1, MonoidHom.map_zpowers]

end Transfer2

end CFSG.AGLEmbedding
