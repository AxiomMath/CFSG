module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.IndexCases

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def IsD2SeitzException (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d = .A 1 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d = .A 2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d = .twistedA 3 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ (d = .B 3 q ∨ d = .B 4 q)) ∨
    d = .tits)) ∨
  (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

@[expose] def KFactSeitzRankTwo : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 →
    ∀ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group), IsElemAbelian p E →
      Nat.card E = p ^ 2 →
      Subgroup.closure {k : (TauCeti.CFSGIndex.lie d).Group | ∃ e ∈ E, e ≠ 1 ∧ e k = k} = ⊤

@[expose] def D2IndexCaseAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ), Pp p → ∀ (P : Sylow p G) (M A H R : Subgroup G), D2Escape p P M A H R →
    D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

@[expose] def D2IndexCaseFor {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M A R : Subgroup G) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ H : Subgroup G, D2Escape p P M A H R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

theorem D2IndexCaseAt.for {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h : D2IndexCaseAt i Pp)
    {G : Type} [Group G] [Finite G] (hglob : D2Global G) (hD1 : D1For G) {p : ℕ} (hp : Pp p)
    {P : Sylow p G} {M A R : Subgroup G} (hmax : D2EscapeMax p P M R)
    (hβ : p ∈ GLBBetaFour G) : D2IndexCaseFor p P M A R i :=
  fun H hesc Rbar K hRbar hK he => h G hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he

theorem d2IndexCaseFor_cyclic {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A R : Subgroup G} (q : ℕ) (hq : q.Prime) : D2IndexCaseFor p P M A R (.cyclic q hq) :=
  fun _ _ _ _ _ hK ⟨e⟩ => hK.false_of_cyclic q hq e

theorem d2IndexCase_of_cases {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h₁ : D2IndexCaseAt i Pp)
    (h₂ : D2IndexCaseAt i fun p => ¬ Pp p) : D2IndexCase i := by
  intro G _ _ hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK he
  by_cases hp : Pp p
  · exact h₁ G hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  · exact h₂ G hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he

theorem D2AlmostSimple.le_of_closure_fixed {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (h : D2AlmostSimple p X R A X₀ K)
    (hgen : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k} = ⊤) : K ≤ X₀ := by
  have hsub : {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k} ⊆ (X₀.subgroupOf K : Set K) := by
    rintro k ⟨a, haA, ha1, hak⟩
    have hcent : (k : X) ∈ Subgroup.centralizer ({a} : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mul_inv_eq_iff_eq_mul.mp hak
    have hne : Subgroup.zpowers a ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
    exact h.normalizer_le_of_le_A _ (Subgroup.zpowers_le.mpr haA) hne
      (centralizer_singleton_le_normalizer_zpowers a hcent)
  have htop : (⊤ : Subgroup K) ≤ X₀.subgroupOf K := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hsub
  exact fun k hk => htop (Subgroup.mem_top (⟨k, hk⟩ : K))

theorem D2AlmostSimple.false_of_seitz {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (h : D2AlmostSimple p X R A X₀ K)
    (hS : KFactSeitzRankTwo) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hp : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) : False := by
  have : K.Normal := h.normal
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [h.centralizer_eq_bot] at hxc
    exact Subgroup.mem_bot.mp hxc
  let ψ : X →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := fun x y hxy => hφ ((MulAut.congr e).injective hxy)
  have hfix : ∀ (a : X) (k : K), ψ a (e k) = e k ↔ a * (k : X) * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (MulAut.conjNormal (H := K) a k) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  have hclos := hS d p h.prime h.ne_two hp hex (A.map ψ) (elementary_abelian_map p h.elem ψ)
    (by rw [Subgroup.card_map_of_injective hψ, h.card_A])
  have hgen : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e k ∈ Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ A.map ψ, ε ≠ 1 ∧ ε k = k} := by
      rw [hclos]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ A.map ψ, ε ≠ 1 ∧ ε k = k} ≤
        (Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k}).map e.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro t ⟨_, ⟨a, haA, rfl⟩, hε1, hεt⟩
      refine ⟨e.symm t, Subgroup.subset_closure ⟨a, haA, ?_, ?_⟩, by simp⟩
      · rintro rfl
        exact hε1 (map_one ψ)
      · refine (hfix a (e.symm t)).mp ?_
        simpa using hεt
    obtain ⟨y, hy, hyk⟩ := hle hk
    exact (e.injective hyk) ▸ hy
  exact h.not_le (h.le_of_closure_fixed hgen)

@[expose] def D2SeitzCross : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
        ¬ IsD2SeitzException p d.1 → False

theorem KFactSeitzRankTwo.seitzCross (hS : KFactSeitzRankTwo) : D2SeitzCross :=
  fun _ _ _ _ _ _ _ _ hK d ⟨e⟩ hp hex => hK.false_of_seitz hS d e hp hex

instance : Coe KFactSeitzRankTwo D2SeitzCross := ⟨KFactSeitzRankTwo.seitzCross⟩

theorem D2AlmostSimple.false_of_seitzCross {X : Type} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (h : D2AlmostSimple p X R A X₀ K)
    (hS : D2SeitzCross) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hp : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) : False :=
  hS X p R A X₀ K h d ⟨e⟩ hp hex

theorem d2IndexCaseAt_lie_cross (hS : D2SeitzCross) (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt (.lie d) fun p => p ≠ d.1.characteristic ∧ ¬ IsD2SeitzException p d.1 := by
  intro G _ _ _ _ p hp P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  exact hK.false_of_seitzCross hS d e hp.1 hp.2

theorem d2LieCase_of (hS : D2SeitzCross)
    (hchar : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => p = d.1.characteristic)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1) :
    D2LieCase := by
  intro d
  refine d2IndexCase_of_cases (hchar d)
    fun G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he => ?_
  by_cases hexcp : IsD2SeitzException p d.1
  · exact hexc d G hglob hD1 p hexcp P M A H R hesc hmax hβ Rbar K hRbar hK he
  · exact d2IndexCaseAt_lie_cross hS d G hglob hD1 p ⟨hp, hexcp⟩ P M A H R hesc hmax hβ Rbar K hRbar
      hK he

end CFSG.AGLEmbeddingD2
