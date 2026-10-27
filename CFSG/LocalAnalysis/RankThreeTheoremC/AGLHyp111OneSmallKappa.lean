module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111B3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111StarAt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AConfig

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

section AutTwo

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mul_conj_mul_inv (f : MulAut K) (x : K) :
    f * MulAut.conj x * f⁻¹ = MulAut.conj (f x) := by
  ext y
  simp [MulAut.conj_apply]

omit [Finite K] in
theorem aut_twoGroup_eq_bot (hZ : Subgroup.center K = ⊥) {T : Subgroup K}
    (hNo2 : ∀ U : Subgroup K, IsPGroup 2 U → T ≤ Subgroup.normalizer (U : Set K) → U = ⊥)
    (hCent : ∀ V : Subgroup (MulAut K), IsPGroup 2 V → (∀ v ∈ V, ∀ t ∈ T, v t = t) → V = ⊥)
    (V : Subgroup (MulAut K)) (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ T, MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) : V = ⊥ := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut K => f g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = (x * g * x⁻¹) * x := by rw [h]
        _ = x * g := by group
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact hxZ
  set U : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hUdef
  have hU2 : IsPGroup 2 U := hV.comap_of_injective _ hinj
  have hTU : T ≤ Subgroup.normalizer (U : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro u
    simp only [hUdef, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hTV t ht) (MulAut.conj u)
  have hU := hNo2 U hU2 hTU
  refine hCent V hV fun v hv t ht => ?_
  have hc : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ ∈ V := by
    have h1 : MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTV t ht) v⁻¹).mp (V.inv_mem hv)
    have e : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ =
        v * (MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h1
  have e2 : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ = MulAut.conj (v t * t⁻¹) := by
    rw [map_mul, map_inv, mul_conj_mul_inv]
  rw [e2] at hc
  have hmem : v t * t⁻¹ ∈ U := hc
  rw [hU, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

end AutTwo

@[expose] def KFactSmallCentNoTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 3 ∧ IsLinThreeFour K) →
      ¬ (p = 5 ∧ IsFi22 K) → ∀ V : Subgroup (MulAut K), IsPGroup 2 V →
        (∀ v ∈ V, ∀ t ∈ (T : Subgroup K), v t = t) → V = ⊥

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem b3_of_oneSmall3 (hNo2 : KFactSmallNoTwo) (hCent : KFactSmallCentNoTwo)
    (hd : D1OneSmall3Data p P M H R Rbar K) (hL34 : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hFi : ¬ (p = 5 ∧ IsFi22 K)) : Hyp111B3 p H R K := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : K.Normal := hd.toCore.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  refine b3_of_normal_of_aut fun V hV hTV => ?_
  refine aut_twoGroup_eq_bot hd.center (T := (T₁ : Subgroup K))
    (fun U hU hTU => hNo2 K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hFi T₁ U hU hTU)
    (hCent K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hL34 hFi) V hV fun t ht => hTV t ?_
  have htR : (t : H ⧸ primeComplementCore (G := H) p) ∈
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    have : (t : H ⧸ primeComplementCore (G := H) p) ∈ (T₁ : Subgroup K).map K.subtype :=
      ⟨t, ht, rfl⟩
    rw [hT₁] at this
    exact this.1
  rw [hd.cfg.rbar] at htR
  exact htR

@[expose] noncomputable def d1KBar (p : ℕ) (M H : Subgroup G) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  ⨆ (L : Subgroup (H ⧸ primeComplementCore (G := H) p))
    (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M H), L

@[expose] noncomputable def d1Kappa (p : ℕ) (M H : Subgroup G) : ℕ := Nat.card (d1KBar p M H)

omit [Finite G] in
theorem le_d1KBar {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) : L ≤ d1KBar p M H :=
  le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl

omit [Finite G] in
theorem d1KBar_eq_of_unique {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (h₁ : IsComponentOf L₁ ⊤) (hL₁ : ¬ L₁ ≤ d1X0 p M H)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H → L = L₁) : d1KBar p M H = L₁ :=
  le_antisymm (iSup₂_le fun L hL => (huniq L hL.1 hL.2).le) (le_d1KBar h₁ hL₁)

theorem d1Kappa_le_card (p : ℕ) (M H : Subgroup G) : d1Kappa p M H ≤ Nat.card G :=
  (Subgroup.card_le_card_group _).trans
    ((Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
      (Subgroup.card_le_card_group H))

@[expose] def D1KMaxR (p : ℕ) (M H R : Subgroup G) : Prop :=
  ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → R ≤ N → d1Kappa p M N ≤ d1Kappa p M H

theorem false_of_kappa_step {α : Type*} (Pair : α → Prop) (κ : α → ℕ) (B : ℕ)
    (hB : ∀ a, Pair a → κ a ≤ B)
    (step : ∀ a, Pair a → (∀ b, Pair b → κ a < κ b → False) → False) :
    ∀ a, Pair a → False := by
  suffices h : ∀ n, ∀ a, Pair a → B - κ a = n → False from fun a ha => h _ a ha rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hn
    exact step a ha fun b hb hlt => ih (B - κ b) (by have := hB b hb; omega) b hb rfl

theorem d1KMaxR_of_ih {H₀ : Subgroup G} (hext : D1Extremal p P M H R)
    (hih : ∀ N R' : Subgroup G, D1Extremal p P M N R' → d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) : D1KMaxR p M H R := by
  intro N hN hNM hRN
  by_contra hlt
  exact hih N R (extremal_of_competitor hext hN hNM hRN) (lt_of_le_of_lt hk (not_le.mp hlt))

@[expose] def Hyp917R (p : ℕ) (M H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → R ≤ N → AGLCovers p H N K →
    (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) ∨ d1Kappa p M H < d1Kappa p M N

omit [Finite G] in
theorem factorAt_of_kMax {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hk : D1KMaxR p M H R) (h917 : Hyp917R p M H R K) : AGLCompetitorFactorAt p M H K R :=
  fun N hN hNM hRN hcov => (h917 N hN hNM hRN hcov).resolve_right (not_lt.mpr (hk N hN hNM hRN))

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
